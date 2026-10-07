// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                       // aleph // evring_loop_test — live-ring proof (pure C)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Standalone gate for the proactor core, no Lean anywhere:
//
//   1. loop init (buffer ring + inflight table)
//   2. listener + multishot accept armed
//   3. client connects over loopback, sends N messages
//   4. server echoes each via buffer-ring recv → slab send
//   5. client verifies every echo byte-identical; teardown clean
//
//   cc -std=gnu11 evring_loop.c evring_loop_test.c -luring -o t && ./t
//
// (evring_loop.c compiled WITHOUT EVRING_WITH_LEAN here — the pure core.)

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <assert.h>
#include <errno.h>
#include <liburing.h>
#include <netinet/in.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

// pull the core's API (kept in-file to avoid a header for a 2-file project)
typedef struct er_loop er_loop;
er_loop* er_loop_init(uint32_t entries, uint32_t nbufs, uint32_t buf_size, uint32_t evout_cap);
void er_loop_cleanup(er_loop* l);
int32_t er_listen(uint16_t port, uint32_t backlog);
int32_t er_prep_accept(er_loop* l, int32_t listen_fd, uint64_t lean_ud);
int32_t er_prep_recv(er_loop* l, int32_t fd, uint64_t lean_ud);
int32_t er_prep_send(er_loop* l, int32_t fd, const void* data, uint32_t len, uint64_t lean_ud);
int32_t er_prep_close(er_loop* l, int32_t fd, uint64_t lean_ud);
int32_t er_submit_wait(er_loop* l, uint32_t min_complete);
const uint8_t* er_events(const er_loop* l);
int32_t er_take(er_loop* l, uint32_t buf_id, uint32_t len, void* dst);
uint32_t er_sq_space(const er_loop* l);

#define REC 24
#define K_ACCEPT 1
#define K_RECV 2
#define K_SEND 3
#define K_CLOSE 4

typedef struct {
  uint64_t ud;
  int64_t res;
  uint32_t flags;
  uint8_t kind;
} rec_t;

static rec_t rec_at(const uint8_t* evs, uint32_t i) {
  rec_t r;
  memcpy(&r.ud, evs + (size_t)i * REC, 8);
  memcpy(&r.res, evs + (size_t)i * REC + 8, 8);
  memcpy(&r.flags, evs + (size_t)i * REC + 16, 4);
  r.kind = evs[(size_t)i * REC + 20];
  return r;
}

enum { MSGS = 64, CLIENTS = 4 };
static uint16_t g_port;

static void* client_main(void* arg) {
  long id = (long)arg;
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  assert(fd >= 0);
  struct sockaddr_in a = {0};
  a.sin_family = AF_INET;
  a.sin_port = htons(g_port);
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  assert(connect(fd, (struct sockaddr*)&a, sizeof(a)) == 0);
  char msg[128], echo[128];
  for (int i = 0; i < MSGS; ++i) {
    int len = snprintf(msg, sizeof(msg), "client %ld message %d — echo me", id, i);
    assert(write(fd, msg, (size_t)len) == len);
    int got = 0;
    while (got < len) {
      ssize_t r = read(fd, echo + got, (size_t)(len - got));
      assert(r > 0);
      got += (int)r;
    }
    assert(memcmp(msg, echo, (size_t)len) == 0);
  }
  close(fd);
  return NULL;
}

int main(void) {
  er_loop* l = er_loop_init(256, 128, 4096, 1024);
  if (!l) {
    fprintf(stderr, "SKIP: io_uring unavailable\n");
    return 0;
  }

  int32_t lfd = er_listen(0, 64); // port 0: kernel assigns
  assert(lfd >= 0);
  struct sockaddr_in bound;
  socklen_t blen = sizeof(bound);
  assert(getsockname(lfd, (struct sockaddr*)&bound, &blen) == 0);
  g_port = ntohs(bound.sin_port);

  assert(er_prep_accept(l, lfd, 1) == 0); // ud 1 = listener

  pthread_t clients[CLIENTS];
  for (long c = 0; c < CLIENTS; ++c) {
    assert(pthread_create(&clients[c], NULL, client_main, (void*)c) == 0);
  }

  // ── server loop: ud for connections = 1000 + connfd ──
  int done_msgs = 0, open_conns = 0, accepted = 0, closing = 0;
  while (accepted < CLIENTS || open_conns > 0 || closing > 0) {
    int32_t n = er_submit_wait(l, 1);
    assert(n >= 0);
    const uint8_t* evs = er_events(l);
    for (int32_t i = 0; i < n; ++i) {
      rec_t r = rec_at(evs, i);
      switch (r.kind) {
        case K_ACCEPT: {
          assert(r.res >= 0);
          int connfd = (int)r.res;
          assert(er_prep_recv(l, connfd, 1000u + (uint64_t)connfd) == 0);
          ++accepted;
          ++open_conns;
          break;
        }
        case K_RECV: {
          int connfd = (int)(r.ud - 1000);
          if (r.res == 0 || (r.res < 0 && r.res != -ENOBUFS)) {
            // peer closed (or hard error): close our side
            er_prep_close(l, connfd, 2000u + (uint64_t)connfd);
            --open_conns;
            ++closing;
            break;
          }
          if (r.res == -ENOBUFS) { // pool momentarily dry: re-arm
            assert(er_prep_recv(l, connfd, r.ud) == 0);
            break;
          }
          assert(r.flags & IORING_CQE_F_BUFFER);
          uint32_t buf_id = r.flags >> IORING_CQE_BUFFER_SHIFT;
          uint8_t data[4096];
          assert(er_take(l, buf_id, (uint32_t)r.res, data) == 0);
          assert(er_prep_send(l, connfd, data, (uint32_t)r.res, 3000u + (uint64_t)connfd) == 0);
          if (!(r.flags & IORING_CQE_F_MORE)) { // multishot chain ended: re-arm
            assert(er_prep_recv(l, connfd, r.ud) == 0);
          }
          break;
        }
        case K_SEND:
          assert(r.res > 0);
          ++done_msgs;
          break;
        case K_CLOSE:
          --closing;
          break;
        default:
          break;
      }
    }
  }

  for (long c = 0; c < CLIENTS; ++c) {
    pthread_join(clients[c], NULL);
  }
  er_loop_cleanup(l);
  close(lfd);

  printf(
      "evring_loop: OK — %d clients × %d msgs echoed (%d sends), multishot accept+recv, buf_ring\n",
      CLIENTS, MSGS, done_msgs);
  return 0;
}
