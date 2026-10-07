// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//              // aleph // mesh_bench — the inter-core typed-message ceiling
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// The general mesh wire is NOT bespoke: a typed message is `Box.serialize` into
// a heap buffer, and MSG_RING carries the POINTER across cores (shared address
// space, exclusive ownership handoff — shared-nothing at the concurrency level,
// zero-copy at the data level). The receiver decodes in place and returns the
// buffer to the sender for reuse.
//
// This measures the ceiling: sustained one-way typed messages/sec across two
// pinned cores, with a credit window (buffers returned so allocation is O(1)
// off a fixed pool — no malloc/free on the hot path). This is the number the
// Lean distributed-machine substrate must approach at "wire saturation".
//
//   cc -std=gnu11 -O2 mesh_bench.c -luring -lpthread -o mb && ./mb

#define _GNU_SOURCE
#include <liburing.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define RING_ENTRIES 4096
#define POOL 2048    // fixed buffer pool (the credit window)
#define MSG_BYTES 64 // a small serialized message
#define RUN_SEC 3

// a pooled message buffer: what a serialized codec message looks like on the wire
typedef struct {
  uint64_t seq;
  uint64_t sum;
  uint8_t pad[MSG_BYTES - 16];
} msg_t;

static msg_t* pool; // shared address space: both cores see it
static _Atomic int consumer_ring_fd = -1;
static _Atomic int producer_ring_fd = -1;
static _Atomic long delivered = 0; // consumer's verified count
static _Atomic int stop = 0;

static void pin(int c) {
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET(c, &s);
  pthread_setaffinity_np(pthread_self(), sizeof s, &s);
}
static unsigned FAST =
    IORING_SETUP_DEFER_TASKRUN | IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_COOP_TASKRUN;
static int mkring(struct io_uring* r) {
  struct io_uring_params p;
  memset(&p, 0, sizeof p);
  p.flags = FAST;
  int rc = io_uring_queue_init_params(RING_ENTRIES, r, &p);
  if (rc < 0) {
    FAST = 0;
    rc = io_uring_queue_init(RING_ENTRIES, r, 0);
  }
  return rc;
}
static double now() {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec / 1e9;
}

// tags in cqe.res distinguish DATA(msg) from RETURN(credit); user_data = pool index
enum { R_MSG = 1, R_RET = 2 };

// ── consumer core: receive msg pointers, verify, return the buffer index ──
static void* consumer(void* a) {
  (void)a;
  pin(3);
  struct io_uring ring;
  if (mkring(&ring) < 0) {
    return 0;
  }
  atomic_store(&consumer_ring_fd, ring.ring_fd);
  int prod;
  while ((prod = atomic_load(&producer_ring_fd)) < 0) {
    sched_yield();
  }
  long got = 0;
  while (!atomic_load(&stop)) {
    if (io_uring_submit_and_wait(&ring, 1) < 0) {
      break;
    }
    struct io_uring_cqe* c;
    unsigned h, n = 0;
    io_uring_for_each_cqe(&ring, h, c) {
      if (c->res == R_MSG) {
        uint32_t idx = (uint32_t)c->user_data;
        msg_t* m = &pool[idx];
        if ((m->seq ^ 0x9E3779B97F4A7C15ull) == m->sum) {
          got++; // verify checksum
        }
        // return the buffer to the producer for reuse (credit)
        struct io_uring_sqe* s = io_uring_get_sqe(&ring);
        io_uring_prep_msg_ring(s, prod, R_RET, idx, 0);
      }
      n++;
    }
    io_uring_cq_advance(&ring, n);
  }
  atomic_store(&delivered, got);
  io_uring_queue_exit(&ring);
  return 0;
}

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  pin(1);
  pool = aligned_alloc(64, (size_t)POOL * sizeof(msg_t));
  struct io_uring ring;
  if (mkring(&ring) < 0) {
    fprintf(stderr, "ring init\n");
    return 1;
  }
  atomic_store(&producer_ring_fd, ring.ring_fd);
  pthread_t th;
  pthread_create(&th, NULL, consumer, NULL);
  int cons;
  while ((cons = atomic_load(&consumer_ring_fd)) < 0) {
    sched_yield();
  }

  // free-list of pool indices; all start free
  uint32_t* freelist = malloc(POOL * sizeof(uint32_t));
  int top = POOL;
  for (int i = 0; i < POOL; i++) {
    freelist[i] = i;
  }

  uint64_t seq = 0;
  long sent = 0;
  double t0 = now(), deadline = t0 + RUN_SEC;
  while (now() < deadline) {
    // fill the window: send while we have free buffers and SQ space
    while (top > 0 && io_uring_sq_space_left(&ring) > 1) {
      uint32_t idx = freelist[--top];
      msg_t* m = &pool[idx];
      m->seq = seq++;
      m->sum = m->seq ^ 0x9E3779B97F4A7C15ull; // "serialize" the message
      struct io_uring_sqe* s = io_uring_get_sqe(&ring);
      io_uring_prep_msg_ring(s, cons, R_MSG, idx, 0); // pointer-pass: user_data=idx
      sent++;
    }
    io_uring_submit_and_wait(&ring, 1);
    // reap returned credits (buffers the consumer finished with)
    struct io_uring_cqe* c;
    unsigned h, n = 0;
    io_uring_for_each_cqe(&ring, h, c) {
      if (c->res == R_RET) {
        freelist[top++] = (uint32_t)c->user_data; // recycle
      }
      n++;
    }
    io_uring_cq_advance(&ring, n);
  }
  double dt = now() - t0;
  atomic_store(&stop, 1);
  // nudge the consumer so it observes stop
  struct io_uring_sqe* s = io_uring_get_sqe(&ring);
  io_uring_prep_msg_ring(s, cons, R_RET, 0, 0);
  io_uring_submit(&ring);
  pthread_join(th, NULL);
  io_uring_queue_exit(&ring);

  long got = atomic_load(&delivered);
  printf("mesh_bench: %.2fM msg/s one-way (%ld msgs in %.2fs, %d-byte payload, %s), %.2f GB/s "
         "payload; verified %ld\n",
         sent / dt / 1e6, sent, dt, MSG_BYTES, FAST ? "DEFER_TASKRUN" : "plain",
         (double)sent * MSG_BYTES / dt / 1e9, got);
  return got > 0 ? 0 : 1;
}
