// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                     // aleph // mesh_poc — IORING_OP_MSG_RING validation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// The load-bearing question before any mesh abstraction: does MSG_RING give us
// a working shared-nothing inter-core wire with the FAST flags?
//
//   1. Two rings, each CREATED ON and pinned to its own core, each with
//      DEFER_TASKRUN | SINGLE_ISSUER — the shared-nothing config. NOTE: these
//      flags bind a ring to its creating thread; a ring must be created (and
//      only ever submitted-to) by its owner core.
//   2. Core 0 posts an IORING_MSG_DATA to core 1's ring. Does core 1, blocked
//      in submit_and_wait, WAKE promptly? (The whole design rests on this.)
//   3. Core 0 passes a pipe fd to core 1 via IORING_MSG_SEND_FD (auto-index).
//      Core 1 recovers the registered-file index from the delivered CQE and
//      READS from the migrated fd with IOSQE_FIXED_FILE. Bytes must match.
//
//   cc -std=gnu11 mesh_poc.c -luring -lpthread -o mesh && ./mesh

#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <liburing.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MSG_TAG_DATA 0x0100
#define MSG_TAG_FD 0x0200
#define TAG_READ 0x0300
#define RING_ENTRIES 256
#define REG_FILES 64

static const char* PAYLOAD = "hello from core 0 across the mesh";

// published by the worker once ring1 is created ON core 1
static _Atomic int worker_ring_fd = -1;

static void pin(int cpu) {
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET(cpu, &s);
  pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
}

// MESH_PLAIN=1 in the env forces plain rings, to isolate the DEFER_TASKRUN
// cross-core wakeup from everything else.
static unsigned FAST =
    IORING_SETUP_DEFER_TASKRUN | IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_COOP_TASKRUN;

static int setup_ring(struct io_uring* r) {
  struct io_uring_params p;
  memset(&p, 0, sizeof(p));
  p.flags = FAST;
  int rc = io_uring_queue_init_params(RING_ENTRIES, r, &p);
  if (rc < 0) {
    FAST = 0;
    rc = io_uring_queue_init(RING_ENTRIES, r, 0);
  }
  return rc;
}

static double now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec / 1e6;
}

// ── core 1: OWNS ring1 (creates it here). Blocks on it; MSG_RING deliveries
// and its own read-completion all arrive on this one ring. Shared-nothing.
static void* worker(void* arg) {
  (void)arg;
  pin(1);
  struct io_uring ring1;
  if (setup_ring(&ring1) < 0) {
    fprintf(stderr, "worker ring init failed\n");
    return 0;
  }
  // registered-file table to RECEIVE migrated fds
  if (io_uring_register_files_sparse(&ring1, REG_FILES) < 0) {
    fprintf(stderr, "register_files_sparse failed\n");
    return 0;
  }
  atomic_store(&worker_ring_fd, ring1.ring_fd); // publish for the sender

  int got_data = 0, got_fd = 0, read_ok = 0;
  char rbuf[64];
  while (!(got_data && read_ok)) {
    int rc = io_uring_submit_and_wait(&ring1, 1); // does MSG_RING wake us under DEFER_TASKRUN?
    if (rc < 0 && rc != -ETIME && rc != -EINTR) {
      fprintf(stderr, "worker wait: %s\n", strerror(-rc));
      break;
    }
    struct io_uring_cqe* cqe;
    unsigned head, n = 0;
    io_uring_for_each_cqe(&ring1, head, cqe) {
      uint64_t ud = cqe->user_data;
      if (ud == MSG_TAG_DATA) {
        got_data = 1;
        printf("  [core1] MSG_DATA received: res=%d (sender put 0x%x in len)\n", cqe->res, 0xBEEF);
      } else if (ud == MSG_TAG_FD) {
        got_fd = 1;
        // auto-alloc: the delivered CQE res carries the registered-file index
        // the kernel assigned in THIS ring's table.
        int idx = cqe->res;
        printf("  [core1] MSG_SEND_FD received: migrated to registered index %d\n", idx);
        struct io_uring_sqe* sqe = io_uring_get_sqe(&ring1);
        io_uring_prep_read(sqe, idx, rbuf, sizeof(rbuf), 0);
        sqe->flags |= IOSQE_FIXED_FILE; // read through the fixed-file table
        io_uring_sqe_set_data64(sqe, TAG_READ);
      } else if (ud == TAG_READ) {
        if (cqe->res > 0) {
          rbuf[cqe->res] = 0;
          read_ok = (strcmp(rbuf, PAYLOAD) == 0);
          printf("  [core1] read migrated fd (%d bytes): \"%s\" %s\n", cqe->res, rbuf,
                 read_ok ? "OK" : "MISMATCH");
        }
      }
      ++n;
    }
    io_uring_cq_advance(&ring1, n);
  }
  io_uring_queue_exit(&ring1);
  return (void*)(intptr_t)(got_data && got_fd && read_ok);
}

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  if (getenv("MESH_PLAIN")) {
    FAST = 0;
  }
  pin(0);
  struct io_uring ring0;
  if (setup_ring(&ring0) < 0) {
    fprintf(stderr, "ring0 init failed\n");
    return 1;
  }
  if (!FAST) {
    printf("(fell back to plain rings)\n");
  }

  // sender needs a registered file table too: IORING_MSG_SEND_FD's source is a
  // REGISTERED index, not a raw fd (UAPI: "send a registered fd").
  if (io_uring_register_files_sparse(&ring0, REG_FILES) < 0) {
    fprintf(stderr, "register_files_sparse(ring0) failed\n");
    return 1;
  }

  pthread_t th;
  pthread_create(&th, NULL, worker, NULL);
  int target;
  while ((target = atomic_load(&worker_ring_fd)) < 0) {
    sched_yield();
  }

  struct io_uring_cqe* c;
  double t0 = now_ms();

  // ── 1. data message: len→res, data→user_data on the target ──
  struct io_uring_sqe* sqe = io_uring_get_sqe(&ring0);
  io_uring_prep_msg_ring(sqe, target, 0xBEEF, MSG_TAG_DATA, 0);
  io_uring_sqe_set_data64(sqe, 0x0400);
  io_uring_submit(&ring0);
  io_uring_wait_cqe(&ring0, &c);
  printf("  [core0] MSG_DATA send completion: res=%d (0=ok)\n", c->res);
  io_uring_cqe_seen(&ring0, c);

  // ── 2. fd handoff: fill a pipe, pass the read end to core 1 ──
  int pfd[2];
  assert(socketpair(AF_UNIX, SOCK_STREAM, 0, pfd) == 0);
  assert(write(pfd[1], PAYLOAD, strlen(PAYLOAD)) == (ssize_t)strlen(PAYLOAD));
  // install the client fd into core 0's registered table, then hand the INDEX
  // (not the raw fd) to core 1, which auto-allocates a slot in its own table.
  int src_index = 0;
  assert(io_uring_register_files_update(&ring0, src_index, &pfd[0], 1) == 1);
  sqe = io_uring_get_sqe(&ring0);
  io_uring_prep_msg_ring_fd_alloc(sqe, target, src_index, MSG_TAG_FD, 0);
  io_uring_sqe_set_data64(sqe, 0x0500);
  io_uring_submit(&ring0);
  io_uring_wait_cqe(&ring0, &c);
  printf("  [core0] MSG_SEND_FD send completion: res=%d (0=ok)\n", c->res);
  io_uring_cqe_seen(&ring0, c);
  // keep pfd[0] open until join — target holds its own ref via the reg table

  void* wret;
  pthread_join(th, &wret);
  double dt = now_ms() - t0;
  io_uring_queue_exit(&ring0);
  close(pfd[1]);

  if ((intptr_t)wret) {
    printf("mesh_poc: OK — MSG_RING data + fd handoff across 2 pinned cores%s (%.2f ms)\n",
           FAST ? " with DEFER_TASKRUN|SINGLE_ISSUER" : "", dt);
    return 0;
  }
  printf("mesh_poc: FAIL\n");
  return 1;
}
