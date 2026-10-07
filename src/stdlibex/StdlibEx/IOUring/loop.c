// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // StdlibEx // IOUring // Loop — io_uring proactor
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// The SERIOUS ring: a batched proactor for the Lean event loop, mirroring
// libevring-cpp's ring.h (enqueue / submit_and_wait / harvest) with the
// hot-path choices that made evring-wai fast:
//
//   • C-owned INFLIGHT TABLE — sqe->user_data is an index into it; Lean's
//     logical user_data (connection id, op tag) travels inside the entry, so
//     the kernel-facing correlation space never leaks into Lean and C knows
//     the op kind of every completion (slab frees, buffer recycling).
//   • MULTISHOT accept + recv — one SQE arms a listener / connection for many
//     completions; the SQ carries only sends, closes, and re-arms.
//   • PROVIDED BUFFER RING — the kernel picks recv buffers from a fixed pool
//     (also used for file reads via BUFFER_SELECT); Lean copies bytes out
//     exactly once (`er_loop_take`) and the buffer recycles into the ring.
//   • SEND SLABS — send payloads are memcpy'd at prep time into pooled slabs,
//     so Lean ByteArrays have no cross-completion lifetime.
//   • FLAT EVENT RECORDS — completions drain into a contiguous record buffer
//     (24 B each) handed to Lean as one ByteArray per loop iteration: two FFI
//     crossings + one syscall per batch, regardless of event count.
//
// Layering matches evring.c: er_loop_* is pure C (testable standalone);
// uloop_* Lean-ABI wrappers compile under URING_WITH_LEAN.

#define _GNU_SOURCE
#include <errno.h>
#include <liburing.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

// ─────────────────────────────────────────────────────────────────────────────
// Constants and record layout
// ─────────────────────────────────────────────────────────────────────────────

// Op kinds — carried in the inflight entry and echoed in the event record so
// the Lean side can turn a raw completion into a typed `Completion` without
// guessing. Keep in sync with StdlibEx/IOUring/Loop.lean.
enum {
  ER_K_NOP = 0,
  ER_K_ACCEPT = 1, // multishot
  ER_K_RECV = 2,   // multishot, buffer-select
  ER_K_SEND = 3,   // single-shot, slab-backed
  ER_K_CLOSE = 4,
  ER_K_TIMEOUT = 5,
  ER_K_CANCEL = 6,
  ER_K_OPEN = 7,
  ER_K_READ = 8,  // single-shot, buffer-select
  ER_K_WRITE = 9, // single-shot, slab-backed
  // ── mesh deliveries (a peer MSG_RING landed on THIS ring; NOT an inflight
  //    op). Folded in from evring_mesh so one ring does socket I/O AND mesh. ──
  ER_K_MESH_DATA = 10, // peer MSG_DATA arrived (ud = slab ptr, res = len, flags = channel)
  ER_K_MESH_FD = 11,   // peer MSG_SEND_FD arrived (res = reg index, flags = channel)
  // ── outbound (upstream client) — appended so the mesh values above never
  //    shift. res = 0 on success | -errno; the connected fd is the slot's fd. ──
  ER_K_CONNECT = 12, // single-shot; TCP_NODELAY set on success in the drain
};

// ── MESH-on-the-loop-ring markers ───────────────────────────────────────────
// A mesh delivery must be told apart from our own inflight completions on the
// SAME ring without ambiguity:
//
//   • DATA_RECV: the sender uses IORING_MSG_RING_FLAGS_PASS to copy EM_MARK into
//     the target cqe->flags. EM_MARK (bit 14) sits above the low CQE flag bits
//     (F_BUFFER/F_MORE/…) and below the provided-buffer-id shift (bit 16), so it
//     never collides with a real socket/file completion on this ring.
//   • FD_RECV: MSG_SEND_FD cannot pass flags (sqe->file_index carries the target
//     index — see liburing: FLAGS_PASS is "applicable for IORING_MSG_DATA,
//     obviously"). So the fd delivery is marked in the HIGH bits of user_data
//     instead: ER_FD_MARK | channel. Inflight slot indices are small positive
//     integers, so bit 63 is never set on a real inflight user_data.
//   • our OWN mesh sends are IOSQE_CQE_SKIP_SUCCESS (silent); a FAILED send still
//     posts a CQE — marked ER_MSEND_MARK in user_data so the drain can recognise
//     and drop it rather than mistaking it for an inflight slot.
#define EM_MARK 0x4000u                     // → target cqe->flags (DATA_RECV)
#define ER_FD_MARK 0x8000000000000000ull    // → target user_data high bit (FD_RECV)
#define ER_MSEND_MARK 0x4000000000000000ull // → our own send user_data (failed send)

// On-wire header prepended to every mesh MSG_DATA payload (channel travels here
// because the target cqe carries only the pointer + len). Mirrors evring_mesh's
// em_hdr; the buffer is `sizeof(erm_hdr) + len` bytes, ownership → receiver.
typedef struct {
  uint32_t channel;
  uint32_t len;
  // payload follows immediately
} erm_hdr;

// One drained completion, as seen by Lean. 24 bytes, little-endian.
//   [0..8)   u64 lean user_data
//   [8..16)  i64 res        (bytes / fd / -errno)
//   [16..20) u32 flags      (raw CQE flags: F_BUFFER | F_MORE | buffer id)
//   [20]     u8  kind       (ER_K_*)
//   [21..24) pad
#define ER_REC_SIZE 24

typedef struct {
  uint64_t lean_ud;
  void* slab;   // send/write payload to free on completion (may be NULL)
  int32_t fd;   // target fd — or REGISTERED index when .fixed (send continuation)
  uint32_t len; // total payload length (send)
  uint32_t off; // bytes already sent (send continuation)
  uint8_t kind;
  uint8_t live;  // 1 while an SQE/multishot chain references this entry
  uint8_t fixed; // send targets a REGISTERED index — short-send resubmit must
                 // re-arm with IOSQE_FIXED_FILE (fd is the reg index, not raw)
} er_inflight;

typedef struct {
  struct io_uring ring;
  int active;

  // inflight table + freelist
  er_inflight* inflight;
  uint32_t* freelist;
  uint32_t cap, free_top;

  // provided buffer ring (recv + file reads)
  struct io_uring_buf_ring* br;
  unsigned char* buf_base;
  uint32_t nbufs, buf_size;
  int bgid;

  // flat drained-event records
  uint8_t* evout;
  uint32_t evout_cap; // in records

  // sparse registered-file table (mesh fd send/recv). Best-effort: if the
  // kernel rejects registration, nfiles stays 0 and only socket I/O + mesh DATA
  // work — the HTTP proactor path never depends on this.
  uint32_t nfiles;    // registered-file table size (0 = unavailable)
  uint32_t next_file; // next free slot for er_register_fd
} er_loop;

// ─────────────────────────────────────────────────────────────────────────────
// Mesh send-buffer slab pool — the fast path for er_mesh_post/er_mesh_take,
// folded in from evring_mesh (em_buf_*). A process-global fixed-slab allocator,
// cross-thread BY DESIGN: any core pops (post) and any core pushes (take),
// because the peer that receives a buffer is the one that frees it. Slabs are
// recognised by arena address range; oversized payloads fall back to malloc.
//
// This pool is DISTINCT from evring_mesh's (separate TU, file-static symbols):
// a loop-ring buffer is always allocated AND freed on the loop side, so the two
// pools never cross. Symbols are erm_*-prefixed to keep that boundary obvious.
// ─────────────────────────────────────────────────────────────────────────────
#define ERM_SLAB_SIZE 256
#define ERM_POOL_SLABS (1u << 16) // 64k * 256 B = 16 MiB

static uint8_t* g_erm_arena = NULL;
static uint8_t* g_erm_arena_end = NULL;
static void* g_erm_free_list = NULL;
static atomic_flag g_erm_pool_lock = ATOMIC_FLAG_INIT;
static pthread_once_t g_erm_pool_once = PTHREAD_ONCE_INIT;

static void erm_pool_init(void) {
  g_erm_arena = malloc((size_t)ERM_POOL_SLABS * ERM_SLAB_SIZE);
  if (!g_erm_arena) {
    return;
  }
  g_erm_arena_end = g_erm_arena + (size_t)ERM_POOL_SLABS * ERM_SLAB_SIZE;
  void* head = NULL;
  for (uint32_t i = 0; i < ERM_POOL_SLABS; ++i) {
    void* slab = g_erm_arena + (size_t)i * ERM_SLAB_SIZE;
    *(void**)slab = head; // intrusive next-pointer while free
    head = slab;
  }
  g_erm_free_list = head;
}
static inline void erm_pool_lock(void) {
  while (atomic_flag_test_and_set_explicit(&g_erm_pool_lock, memory_order_acquire)) { /* spin */
  }
}
static inline void erm_pool_unlock(void) {
  atomic_flag_clear_explicit(&g_erm_pool_lock, memory_order_release);
}
// Allocate `need` bytes: a pooled slab if it fits and one is free, else malloc.
static void* erm_buf_alloc(uint32_t need) {
  pthread_once(&g_erm_pool_once, erm_pool_init);
  if (need <= ERM_SLAB_SIZE && g_erm_arena) {
    erm_pool_lock();
    void* p = g_erm_free_list;
    if (p) {
      g_erm_free_list = *(void**)p;
      erm_pool_unlock();
      return p;
    }
    erm_pool_unlock();
  }
  return malloc(need ? need : 1);
}
// Free a buffer: return a slab to the pool, or free a malloc fallback.
static void erm_buf_free(void* p) {
  if ((uint8_t*)p >= g_erm_arena && (uint8_t*)p < g_erm_arena_end) {
    erm_pool_lock();
    *(void**)p = g_erm_free_list;
    g_erm_free_list = p;
    erm_pool_unlock();
  } else {
    free(p);
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) Pure-C core
// ─────────────────────────────────────────────────────────────────────────────

static int er_loop_grow_inflight(er_loop* l) {
  uint32_t ncap = l->cap ? l->cap * 2 : 256;
  er_inflight* ni = realloc(l->inflight, ncap * sizeof(er_inflight));
  uint32_t* nf = realloc(l->freelist, ncap * sizeof(uint32_t));
  if (!ni || !nf) {
    free(ni ? ni : l->inflight);
    l->inflight = NULL;
    return -ENOMEM;
  }
  l->inflight = ni;
  l->freelist = nf;
  for (uint32_t i = ncap; i-- > l->cap;) {
    l->inflight[i].live = 0;
    l->freelist[l->free_top++] = i;
  }
  l->cap = ncap;
  return 0;
}

static int64_t er_slot_alloc(er_loop* l, uint64_t lean_ud, uint8_t kind, void* slab) {
  if (l->free_top == 0 && er_loop_grow_inflight(l) < 0) {
    return -ENOMEM;
  }
  uint32_t idx = l->freelist[--l->free_top];
  l->inflight[idx] = (er_inflight){
      .lean_ud = lean_ud, .slab = slab, .fd = -1, .len = 0, .off = 0, .kind = kind, .live = 1};
  return (int64_t)idx;
}

static void er_slot_free(er_loop* l, uint32_t idx) {
  if (idx >= l->cap || !l->inflight[idx].live) {
    return;
  }
  free(l->inflight[idx].slab);
  l->inflight[idx].slab = NULL;
  l->inflight[idx].live = 0;
  l->freelist[l->free_top++] = idx;
}

// Initialize the proactor. entries = SQ depth; nbufs/buf_size = provided
// buffer pool; evout_cap = max records drained per wait. Returns NULL on
// failure. Tries DEFER_TASKRUN|SINGLE_ISSUER first (the fast single-threaded
// configuration), falling back to a plain ring for older kernels.
er_loop* er_loop_init(uint32_t entries, uint32_t nbufs, uint32_t buf_size, uint32_t evout_cap) {
  if (entries == 0) {
    entries = 1024;
  }
  if (nbufs == 0) {
    nbufs = 1024;
  }
  if (buf_size == 0) {
    buf_size = 16384;
  }
  if (evout_cap == 0) {
    evout_cap = 4096;
  }
  // buffer ring size must be a power of two
  while (nbufs & (nbufs - 1)) {
    nbufs &= nbufs - 1;
  }

  er_loop* l = calloc(1, sizeof(er_loop));
  if (!l) {
    return NULL;
  }

  struct io_uring_params p;
  memset(&p, 0, sizeof(p));
  p.flags = IORING_SETUP_DEFER_TASKRUN | IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_COOP_TASKRUN |
            IORING_SETUP_CQSIZE;
  p.cq_entries = entries * 4;
  int rc = io_uring_queue_init_params(entries, &l->ring, &p);
  if (rc < 0) {
    memset(&p, 0, sizeof(p));
    rc = io_uring_queue_init(entries, &l->ring, 0);
    if (rc < 0) {
      free(l);
      return NULL;
    }
  }
  l->active = 1;

  l->bgid = 0;
  int bres = 0;
  l->br = io_uring_setup_buf_ring(&l->ring, nbufs, l->bgid, 0, &bres);
  if (!l->br) {
    goto fail;
  }
  l->buf_base = malloc((size_t)nbufs * buf_size);
  if (!l->buf_base) {
    goto fail;
  }
  l->nbufs = nbufs;
  l->buf_size = buf_size;
  int mask = io_uring_buf_ring_mask(nbufs);
  for (uint32_t i = 0; i < nbufs; ++i) {
    io_uring_buf_ring_add(l->br, l->buf_base + (size_t)i * buf_size, buf_size, (unsigned short)i,
                          mask, (int)i);
  }
  io_uring_buf_ring_advance(l->br, (int)nbufs);

  l->evout_cap = evout_cap;
  l->evout = malloc((size_t)evout_cap * ER_REC_SIZE);
  if (!l->evout) {
    goto fail;
  }
  if (er_loop_grow_inflight(l) < 0) {
    goto fail;
  }

  // Sparse registered-file table so this ring can send/receive fds over the
  // mesh (evring_mesh does the same). BEST-EFFORT: on failure we keep going
  // with nfiles = 0 — socket I/O and mesh DATA still work; only fd handoff is
  // unavailable. The HTTP proactor path must never regress on account of mesh.
  if (io_uring_register_files_sparse(&l->ring, 1024) == 0) {
    l->nfiles = 1024;
    l->next_file = 0;
  } else {
    l->nfiles = 0;
    l->next_file = 0;
  }
  return l;

fail:
  if (l->br) {
    io_uring_free_buf_ring(&l->ring, l->br, l->nbufs ? l->nbufs : nbufs, l->bgid);
  }
  free(l->buf_base);
  free(l->evout);
  if (l->active) {
    io_uring_queue_exit(&l->ring);
  }
  free(l);
  return NULL;
}

// Idempotent teardown (also the Lean finalizer).
void er_loop_cleanup(er_loop* l) {
  if (!l || !l->active) {
    return;
  }
  if (l->br) {
    io_uring_free_buf_ring(&l->ring, l->br, l->nbufs, l->bgid);
  }
  io_uring_queue_exit(&l->ring);
  for (uint32_t i = 0; i < l->cap; ++i) {
    if (l->inflight[i].live) {
      free(l->inflight[i].slab);
    }
  }
  free(l->inflight);
  free(l->freelist);
  free(l->buf_base);
  free(l->evout);
  l->inflight = NULL;
  l->freelist = NULL;
  l->buf_base = NULL;
  l->evout = NULL;
  l->active = 0;
}

// Plain (non-ring) listener setup — cold path.
// Returns listening fd or -errno.
int32_t er_listen(uint16_t port, uint32_t backlog) {
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (fd < 0) {
    return -errno;
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one));
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons(port);
  if (bind(fd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
    int e = -errno;
    close(fd);
    return e;
  }
  if (listen(fd, (int)(backlog ? backlog : 1024)) < 0) {
    int e = -errno;
    close(fd);
    return e;
  }
  return fd;
}

// Create an outbound TCP socket (nonblocking, cloexec) for er_prep_connect —
// the client makes its own sockets (er_listen only binds+listens). The
// nonblocking connect is driven to completion asynchronously by io_uring.
// Returns the fd or -errno.
int32_t er_socket(void) {
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (fd < 0) {
    return -errno;
  }
  return fd;
}

// Pin the CALLING thread to `cpu` (single-cpu affinity), BEFORE it creates the
// ring it will own — the loop-ring analogue of evring_mesh's em_pin. Each core
// of the M×N proxy fabric owns its ring on one dedicated pinned thread; a
// DEFER_TASKRUN|SINGLE_ISSUER ring must be created on the thread that drives it,
// so we pin first, then init. Returns 0 or -errno.
int32_t er_pin(uint32_t cpu) {
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET((int)cpu, &s);
  int rc = pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
  return rc == 0 ? 0 : -rc;
}

// SQE acquisition with an inline flush when the SQ is full.
static struct io_uring_sqe* er_get_sqe(er_loop* l) {
  struct io_uring_sqe* sqe = io_uring_get_sqe(&l->ring);
  if (!sqe) {
    io_uring_submit(&l->ring);
    sqe = io_uring_get_sqe(&l->ring);
  }
  return sqe;
}

// ── prep functions: enqueue only; nothing hits the kernel until submit ──────
// All return 0 or -errno.

int32_t er_prep_accept(er_loop* l, int32_t listen_fd, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_ACCEPT, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_multishot_accept(sqe, listen_fd, NULL, NULL, SOCK_CLOEXEC);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_recv(er_loop* l, int32_t fd, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_RECV, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_recv_multishot(sqe, fd, NULL, 0, 0);
  sqe->flags |= IOSQE_BUFFER_SELECT;
  sqe->buf_group = (unsigned short)l->bgid;
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_send(er_loop* l, int32_t fd, const void* data, uint32_t len, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  void* slab = malloc(len ? len : 1);
  if (!slab) {
    return -ENOMEM;
  }
  memcpy(slab, data, len);
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_SEND, slab);
  if (slot < 0) {
    free(slab);
    return (int32_t)slot;
  }
  er_inflight* in = &l->inflight[(uint32_t)slot];
  in->fd = fd;
  in->len = len;
  in->off = 0;
  io_uring_prep_send(sqe, fd, slab, len, MSG_NOSIGNAL);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

// Async connect on an already-created socket `fd` (see er_socket) to
// `ipv4_be`:`port_be` (both network byte order). The kernel reads the sockaddr
// when the op runs — AFTER submit — so it must outlive the prep: it rides the
// inflight slot's slab (freed with the slot when the completion retires, like a
// send payload). res = 0 on success | -errno; the drain sets TCP_NODELAY.
int32_t er_prep_connect(er_loop* l, int32_t fd, uint32_t ipv4_be, uint16_t port_be,
                        uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  struct sockaddr_in* addr = malloc(sizeof(*addr));
  if (!addr) {
    return -ENOMEM;
  }
  memset(addr, 0, sizeof(*addr));
  addr->sin_family = AF_INET;
  addr->sin_addr.s_addr = ipv4_be; // already network byte order
  addr->sin_port = port_be;        // already network byte order
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_CONNECT, addr);
  if (slot < 0) {
    free(addr);
    return (int32_t)slot;
  }
  l->inflight[(uint32_t)slot].fd = fd; // so the drain can NODELAY it
  io_uring_prep_connect(sqe, fd, (struct sockaddr*)addr, sizeof(*addr));
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_close(er_loop* l, int32_t fd, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_CLOSE, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_close(sqe, fd);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_timeout(er_loop* l, uint64_t nanos, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  // the kernel reads the timespec at submit; keep it in the slab
  struct __kernel_timespec* ts = malloc(sizeof(*ts));
  if (!ts) {
    return -ENOMEM;
  }
  ts->tv_sec = (long long)(nanos / 1000000000ull);
  ts->tv_nsec = (long long)(nanos % 1000000000ull);
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_TIMEOUT, ts);
  if (slot < 0) {
    free(ts);
    return (int32_t)slot;
  }
  io_uring_prep_timeout(sqe, ts, 0, 0);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

// Cancel every pending op on an fd (connection teardown).
int32_t er_prep_cancel_fd(er_loop* l, int32_t fd, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_CANCEL, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_cancel_fd(sqe, fd, IORING_ASYNC_CANCEL_ALL);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_open(er_loop* l, const char* path, int32_t flags, uint32_t mode, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  // openat reads the path at submit time; keep a copy in the slab
  char* p = strdup(path);
  if (!p) {
    return -ENOMEM;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_OPEN, p);
  if (slot < 0) {
    free(p);
    return (int32_t)slot;
  }
  io_uring_prep_openat(sqe, AT_FDCWD, p, (int)flags, (mode_t)mode);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_read(er_loop* l, int32_t fd, uint32_t max_len, uint64_t off, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_READ, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  uint32_t len = max_len > l->buf_size ? l->buf_size : max_len;
  io_uring_prep_read(sqe, fd, NULL, len, off);
  sqe->flags |= IOSQE_BUFFER_SELECT;
  sqe->buf_group = (unsigned short)l->bgid;
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

// ── FIXED-FILE ops: recv / send / close on a REGISTERED index ────────────────
// The counterparts to er_prep_recv/send/close for an fd that has been MIGRATED
// onto this ring over the mesh (MSG_SEND_FD, er_mesh_send_fd). A migrated fd has
// NO raw descriptor on this core — it lives only at a kernel-allocated slot in
// this ring's registered file table, recovered from the ER_K_MESH_FD event's
// `res`. IOSQE_FIXED_FILE (sqe fd = the slot index) is the ONLY way to drive I/O
// on it. Completions surface as the SAME ER_K_RECV / ER_K_SEND / ER_K_CLOSE
// kinds as the raw-fd ops (the take/slab paths are identical); `ud` demuxes.

int32_t er_prep_recv_fixed(er_loop* l, uint32_t reg_index, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_RECV, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_recv_multishot(sqe, (int)reg_index, NULL, 0, 0);
  sqe->flags |= IOSQE_BUFFER_SELECT | IOSQE_FIXED_FILE;
  sqe->buf_group = (unsigned short)l->bgid;
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

int32_t er_prep_send_fixed(er_loop* l, uint32_t reg_index, const void* data, uint32_t len,
                           uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  void* slab = malloc(len ? len : 1);
  if (!slab) {
    return -ENOMEM;
  }
  memcpy(slab, data, len);
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_SEND, slab);
  if (slot < 0) {
    free(slab);
    return (int32_t)slot;
  }
  er_inflight* in = &l->inflight[(uint32_t)slot];
  in->fd = (int32_t)reg_index; // reg index; short-send resubmit reuses it (.fixed)
  in->len = len;
  in->off = 0;
  in->fixed = 1;
  io_uring_prep_send(sqe, (int)reg_index, slab, len, MSG_NOSIGNAL);
  sqe->flags |= IOSQE_FIXED_FILE;
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

// Release a migrated fd's REGISTERED slot (close_direct frees the table entry,
// not a raw fd). Completes as ER_K_CLOSE.
int32_t er_prep_close_fixed(er_loop* l, uint32_t reg_index, uint64_t lean_ud) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  int64_t slot = er_slot_alloc(l, lean_ud, ER_K_CLOSE, NULL);
  if (slot < 0) {
    return (int32_t)slot;
  }
  io_uring_prep_close_direct(sqe, reg_index);
  io_uring_sqe_set_data64(sqe, (uint64_t)slot);
  return 0;
}

// ── submit + drain ──────────────────────────────────────────────────────────

// Submit everything enqueued, wait for ≥ min_complete completions, then drain
// up to evout_cap records. Returns the record count (≥0) or -errno.
// Slab frees, inflight retirement, and TCP_NODELAY on accepted sockets all
// happen here, so Lean only ever sees finished facts.
int32_t er_submit_wait(er_loop* l, uint32_t min_complete) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  int rc = io_uring_submit_and_wait(&l->ring, min_complete);
  if (rc < 0 && rc != -ETIME && rc != -EINTR) {
    return rc;
  }

  uint32_t n = 0, drained = 0, continued = 0;
  unsigned head;
  struct io_uring_cqe* cqe;
  io_uring_for_each_cqe(&l->ring, head, cqe) {
    if (n >= l->evout_cap) {
      break;
    }
    ++drained;

    // ── MESH DELIVERIES FIRST ────────────────────────────────────────────────
    // A peer MSG_RING landed on this ring — NOT one of our inflight ops, so it
    // must be decoded BEFORE the inflight-table path (its user_data is a buffer
    // pointer / cookie, not a slot index). See the marker rationale above.
    if (cqe->flags & EM_MARK) {
      // DATA_RECV: user_data = slab ptr, res = payload len, channel from header.
      const erm_hdr* h = (const erm_hdr*)(uintptr_t)cqe->user_data;
      uint64_t ud = cqe->user_data;
      int64_t res64 = (int64_t)(uint32_t)cqe->res;
      uint32_t chan = h ? h->channel : 0;
      uint8_t* rec = l->evout + (size_t)n * ER_REC_SIZE;
      memcpy(rec, &ud, 8);
      memcpy(rec + 8, &res64, 8);
      memcpy(rec + 16, &chan, 4);
      rec[20] = ER_K_MESH_DATA;
      rec[21] = rec[22] = rec[23] = 0;
      ++n;
      continue;
    }
    if (cqe->user_data & ER_FD_MARK) {
      // FD_RECV: res = assigned reg index, channel = low 32 bits of the cookie.
      uint64_t ud = 0;
      int64_t res64 = (int64_t)(int)cqe->res;
      uint32_t chan = (uint32_t)cqe->user_data;
      uint8_t* rec = l->evout + (size_t)n * ER_REC_SIZE;
      memcpy(rec, &ud, 8);
      memcpy(rec + 8, &res64, 8);
      memcpy(rec + 16, &chan, 4);
      rec[20] = ER_K_MESH_FD;
      rec[21] = rec[22] = rec[23] = 0;
      ++n;
      continue;
    }
    if (cqe->user_data & ER_MSEND_MARK) {
      // Our own mesh send: success is IOSQE_CQE_SKIP_SUCCESS (never seen here);
      // a FAILED send surfaces — drop it (it is not an inflight completion) so
      // it can never corrupt the inflight table. Errors remain observable to
      // the peer as a missing message; the loop stream stays clean.
      continue;
    }

    uint32_t idx = (uint32_t)cqe->user_data;
    uint8_t kind = ER_K_NOP;
    uint64_t lean_ud = 0;
    er_inflight* in = NULL;
    if (idx < l->cap && l->inflight[idx].live) {
      in = &l->inflight[idx];
      kind = in->kind;
      lean_ud = in->lean_ud;
    }

    if (kind == ER_K_ACCEPT && cqe->res >= 0) {
      int one = 1;
      setsockopt(cqe->res, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    }
    // CONNECT success: the connected fd is the slot's fd (cqe->res is 0 here,
    // not the fd) — disable Nagle on the outbound socket like accept does.
    if (kind == ER_K_CONNECT && in && cqe->res >= 0) {
      int one = 1;
      setsockopt(in->fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    }

    // SHORT SEND: the kernel took part of the slab — resubmit the remainder
    // on the same inflight slot and emit NOTHING; Lean sees one completion
    // per logical send, always for the full payload.
    if (kind == ER_K_SEND && in && cqe->res >= 0) {
      in->off += (uint32_t)cqe->res;
      if (in->off < in->len) {
        struct io_uring_sqe* sqe = er_get_sqe(l);
        if (sqe) {
          io_uring_prep_send(sqe, in->fd, (const char*)in->slab + in->off, in->len - in->off,
                             MSG_NOSIGNAL);
          if (in->fixed) {
            sqe->flags |= IOSQE_FIXED_FILE; // in->fd is a reg index
          }
          io_uring_sqe_set_data64(sqe, (uint64_t)idx);
          ++continued;
          continue; // slot stays live; no record
        }
        // SQ exhausted mid-drain (should not happen: er_get_sqe flushes) —
        // fall through and report the short send honestly.
      }
    }

    uint8_t* rec = l->evout + (size_t)n * ER_REC_SIZE;
    memcpy(rec, &lean_ud, 8);
    int64_t res64 = (int64_t)cqe->res;
    if (kind == ER_K_SEND && in && cqe->res >= 0) {
      res64 = (int64_t)in->off; // total bytes across continuations
    }
    memcpy(rec + 8, &res64, 8);
    uint32_t flags = cqe->flags;
    memcpy(rec + 16, &flags, 4);
    rec[20] = kind;
    rec[21] = rec[22] = rec[23] = 0;
    ++n;

    // retire single-shot entries and dead multishot chains
    int more = (cqe->flags & IORING_CQE_F_MORE) != 0;
    if (!more) {
      er_slot_free(l, idx);
    }
  }
  io_uring_cq_advance(&l->ring, drained);
  // send continuations were enqueued during the drain: push them now rather
  // than waiting for the next loop iteration.
  if (continued > 0) {
    io_uring_submit(&l->ring);
  }
  return (int32_t)n;
}

const uint8_t* er_events(const er_loop* l) {
  return l->evout;
}

// Copy a provided buffer's bytes out and recycle it into the ring.
// dst must have room for len bytes. Returns 0 or -errno.
int32_t er_take(er_loop* l, uint32_t buf_id, uint32_t len, void* dst) {
  if (!l || !l->active || buf_id >= l->nbufs || len > l->buf_size) {
    return -EINVAL;
  }
  memcpy(dst, l->buf_base + (size_t)buf_id * l->buf_size, len);
  io_uring_buf_ring_add(l->br, l->buf_base + (size_t)buf_id * l->buf_size, l->buf_size,
                        (unsigned short)buf_id, io_uring_buf_ring_mask(l->nbufs), 0);
  io_uring_buf_ring_advance(l->br, 1);
  return 0;
}

// Recycle a provided buffer without copying (drop the data).
int32_t er_recycle(er_loop* l, uint32_t buf_id) {
  if (!l || !l->active || buf_id >= l->nbufs) {
    return -EINVAL;
  }
  io_uring_buf_ring_add(l->br, l->buf_base + (size_t)buf_id * l->buf_size, l->buf_size,
                        (unsigned short)buf_id, io_uring_buf_ring_mask(l->nbufs), 0);
  io_uring_buf_ring_advance(l->br, 1);
  return 0;
}

uint32_t er_sq_space(const er_loop* l) {
  return l && l->active ? io_uring_sq_space_left(&((er_loop*)l)->ring) : 0;
}

uint32_t er_buf_size(const er_loop* l) {
  return l ? l->buf_size : 0;
}

// Bound port of a listening socket (host order), or -errno.
int32_t er_local_port(int32_t fd) {
  struct sockaddr_in a;
  socklen_t len = sizeof(a);
  if (getsockname(fd, (struct sockaddr*)&a, &len) < 0) {
    return -errno;
  }
  return (int32_t)ntohs(a.sin_port);
}

// ── blocking client helpers (test gates only — NOT the hot path) ────────────

// Connect to loopback:port. Returns fd or -errno.
int32_t er_connect_local(uint16_t port) {
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (fd < 0) {
    return -errno;
  }
  struct sockaddr_in a;
  memset(&a, 0, sizeof(a));
  a.sin_family = AF_INET;
  a.sin_port = htons(port);
  a.sin_addr.s_addr = htonl(0x7f000001u); // 127.0.0.1
  if (connect(fd, (struct sockaddr*)&a, sizeof(a)) < 0) {
    int e = -errno;
    close(fd);
    return e;
  }
  return fd;
}

// Blocking full write. Returns len or -errno.
int64_t er_send_all(int32_t fd, const void* data, uint32_t len) {
  uint32_t off = 0;
  while (off < len) {
    ssize_t w = write(fd, (const char*)data + off, len - off);
    if (w < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -errno;
    }
    off += (uint32_t)w;
  }
  return (int64_t)len;
}

// Blocking single read. Returns bytes (0 = EOF) or -errno.
int64_t er_recv_some(int32_t fd, void* buf, uint32_t cap) {
  for (;;) {
    ssize_t r = read(fd, buf, cap);
    if (r < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -errno;
    }
    return (int64_t)r;
  }
}

// ── mesh on the loop ring (folded in from evring_mesh's em_*) ───────────────
// One ring does BOTH socket I/O (above) AND inter-core MSG_RING (here): an
// outbound core drives its upstream socket AND receives routed requests on the
// SAME ring; an inbound core terminates a client AND forwards over the mesh.
// Enqueue-only; nothing hits the kernel until er_submit_wait. Our own sends are
// IOSQE_CQE_SKIP_SUCCESS (silent on success) so they never clutter the drain.

// This ring's fd — a peer targets it with MSG_RING. Publish so peers reach us.
int32_t er_ring_fd(const er_loop* l) {
  return (l && l->active) ? l->ring.ring_fd : -1;
}

// Install a raw fd into this ring's sparse table; returns the slot index or
// -errno. Use the index as the source for er_mesh_send_fd.
//
// Slots RECYCLE modulo the table size: the acceptor in the fd-passing proxy
// only needs a slot TRANSIENTLY — MSG_SEND_FD dup's the file into the WORKER's
// table at send time, so once the send is enqueued the acceptor's slot holds a
// now-redundant reference. Wrapping next_file (register_files_update replacing
// an old slot just drops that stale reference; the migrated file stays alive on
// the worker) lets an acceptor migrate unboundedly many connections through a
// fixed 1024-slot table. An unbounded next_file++ overflowed the table under
// proxy load and failed with -ENOSPC. A slot is only reused after `nfiles`
// (1024) further registrations, by which point its send is long flushed.
int32_t er_register_fd(er_loop* l, int32_t raw_fd) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  if (l->nfiles == 0) {
    return -ENOSYS;
  }
  int fd = (int)raw_fd;
  uint32_t idx = l->next_file % l->nfiles;
  int rc = io_uring_register_files_update(&l->ring, idx, &fd, 1);
  if (rc < 0) {
    return rc;
  }
  l->next_file++;
  return (int32_t)idx;
}

// Enqueue a MSG_DATA send to `target_ring_fd`. Bytes are COPIED into a C-owned
// slab NOW (Lean ByteArrays are GC-managed, must not cross threads); the slab
// pointer is the target's user_data and ownership transfers to the receiver,
// which frees it via er_mesh_take. `channel` travels in the slab header; EM_MARK
// rides target cqe->flags via IORING_MSG_RING_FLAGS_PASS. Returns 0 or -errno.
int32_t er_mesh_post(er_loop* l, int32_t target_ring_fd, const void* bytes, uint32_t len,
                     uint32_t channel) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  erm_hdr* buf = erm_buf_alloc((uint32_t)(sizeof(erm_hdr) + len));
  if (!buf) {
    return -ENOMEM;
  }
  buf->channel = channel;
  buf->len = len;
  if (len) {
    memcpy((uint8_t*)buf + sizeof(erm_hdr), bytes, len);
  }

  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    erm_buf_free(buf);
    return -EAGAIN;
  }
  // len → target cqe->res, (u64)buf → target cqe->user_data, EM_MARK → flags.
  io_uring_prep_msg_ring_cqe_flags(sqe, (int)target_ring_fd, len, (uint64_t)(uintptr_t)buf, 0,
                                   EM_MARK);
  io_uring_sqe_set_data64(sqe, ER_MSEND_MARK | channel); // our own completion
  sqe->flags |= IOSQE_CQE_SKIP_SUCCESS;
  return 0;
}

// Enqueue a MSG_SEND_FD: hand the registered fd at `reg_index` (a slot in THIS
// ring's table) to the peer, which auto-allocates a slot in its own table and
// recovers the index from its ER_K_MESH_FD event. `channel` is the cookie; it
// is marked ER_FD_MARK in the delivered user_data so the peer's drain can tell
// the fd delivery apart from an inflight completion. Returns 0 or -errno.
int32_t er_mesh_send_fd(er_loop* l, int32_t target_ring_fd, uint32_t reg_index, uint32_t channel) {
  if (!l || !l->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = er_get_sqe(l);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_msg_ring_fd_alloc(sqe, (int)target_ring_fd, (int)reg_index,
                                  ER_FD_MARK | (uint64_t)channel, 0);
  io_uring_sqe_set_data64(sqe, ER_MSEND_MARK | channel);
  sqe->flags |= IOSQE_CQE_SKIP_SUCCESS;
  return 0;
}

// Copy `len` payload bytes out of the received slab at `ptr` into `dst`, then
// FREE the slab (ownership ends here). `ptr` is the pointer delivered in an
// ER_K_MESH_DATA event's `ud`. Returns 0.
int32_t er_mesh_take(uint64_t ptr, uint32_t len, void* dst) {
  erm_hdr* buf = (erm_hdr*)(uintptr_t)ptr;
  if (len) {
    memcpy(dst, (uint8_t*)buf + sizeof(erm_hdr), len);
  }
  erm_buf_free(buf);
  return 0;
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) Lean-ABI wrappers
// ─────────────────────────────────────────────────────────────────────────────
#ifdef URING_WITH_LEAN
#  include <lean/lean.h>

static lean_external_class* g_loop_class = NULL;

static void uloop_finalize(void* p) {
  er_loop_cleanup((er_loop*)p);
  free(p);
}
static void uloop_foreach(void* p, b_lean_obj_arg f) {
  (void)p;
  (void)f;
}

static lean_external_class* loop_class(void) {
  if (g_loop_class == NULL) {
    g_loop_class = lean_register_external_class(uloop_finalize, uloop_foreach);
  }
  return g_loop_class;
}

static inline lean_obj_res loop_io_err(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
static inline er_loop* the_loop(b_lean_obj_arg h) {
  return (er_loop*)lean_get_external_data(h);
}
// prep results: 0 on success, -errno on failure → IO Int32 (caller checks)
static inline lean_obj_res ok_i32(int32_t v) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)v));
}

// uloop_init : UInt32 → UInt32 → UInt32 → UInt32 → IO LoopHandle
LEAN_EXPORT lean_obj_res uloop_init(uint32_t entries, uint32_t nbufs, uint32_t buf_size,
                                    uint32_t evout_cap, lean_obj_arg w) {
  (void)w;
  er_loop* l = er_loop_init(entries, nbufs, buf_size, evout_cap);
  if (!l) {
    return loop_io_err("evring: loop init failed");
  }
  return lean_io_result_mk_ok(lean_alloc_external(loop_class(), l));
}

// uloop_cleanup : @& LoopHandle → IO Unit
LEAN_EXPORT lean_obj_res uloop_cleanup(b_lean_obj_arg lh, lean_obj_arg w) {
  (void)w;
  er_loop_cleanup(the_loop(lh));
  return lean_io_result_mk_ok(lean_box(0));
}

// uloop_listen : UInt16 → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res uloop_listen(uint16_t port, uint32_t backlog, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_listen(port, backlog));
}

// uloop_pin : UInt32 → IO Int32  (pin the calling thread to `cpu`, before init)
LEAN_EXPORT lean_obj_res uloop_pin(uint32_t cpu, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_pin(cpu));
}

// uloop_prep_* : @& LoopHandle → … → IO Int32   (0 | -errno)
LEAN_EXPORT lean_obj_res uloop_prep_accept(b_lean_obj_arg lh, uint32_t fd, uint64_t ud,
                                           lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_accept(the_loop(lh), (int32_t)fd, ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_recv(b_lean_obj_arg lh, uint32_t fd, uint64_t ud,
                                         lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_recv(the_loop(lh), (int32_t)fd, ud));
}
// uloop_prep_send : @& LoopHandle → UInt32 → @& ByteArray → UInt64 → IO Int32
LEAN_EXPORT lean_obj_res uloop_prep_send(b_lean_obj_arg lh, uint32_t fd, b_lean_obj_arg bytes,
                                         uint64_t ud, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_send(the_loop(lh), (int32_t)fd, lean_sarray_cptr((lean_object*)bytes),
                             (uint32_t)lean_sarray_size((lean_object*)bytes), ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_close(b_lean_obj_arg lh, uint32_t fd, uint64_t ud,
                                          lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_close(the_loop(lh), (int32_t)fd, ud));
}
// uloop_socket : IO Int32  (fresh outbound socket, -errno on failure)
LEAN_EXPORT lean_obj_res uloop_socket(lean_obj_arg w) {
  (void)w;
  return ok_i32(er_socket());
}
// uloop_prep_connect : @& LoopHandle → UInt32 → UInt16 → UInt64 → IO Int32
// Loopback connect (127.0.0.1:port) — the outbound-client counterpart to
// er_connect_local, but async on the ring. `port` is host order.
LEAN_EXPORT lean_obj_res uloop_prep_connect(b_lean_obj_arg lh, uint32_t fd, uint16_t port,
                                            uint64_t ud, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_connect(the_loop(lh), (int32_t)fd, htonl(0x7f000001u), htons(port), ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_timeout(b_lean_obj_arg lh, uint64_t nanos, uint64_t ud,
                                            lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_timeout(the_loop(lh), nanos, ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_cancel_fd(b_lean_obj_arg lh, uint32_t fd, uint64_t ud,
                                              lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_cancel_fd(the_loop(lh), (int32_t)fd, ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_open(b_lean_obj_arg lh, b_lean_obj_arg path, uint32_t flags,
                                         uint32_t mode, uint64_t ud, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_open(the_loop(lh), lean_string_cstr(path), (int32_t)flags, mode, ud));
}
LEAN_EXPORT lean_obj_res uloop_prep_read(b_lean_obj_arg lh, uint32_t fd, uint32_t max_len,
                                         uint64_t off, uint64_t ud, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_read(the_loop(lh), (int32_t)fd, max_len, off, ud));
}

// ── fixed-file ops on a migrated fd's REGISTERED index ───────────────────────
// uloop_prep_recv_fixed : @& LoopHandle → UInt32 → UInt64 → IO Int32
LEAN_EXPORT lean_obj_res uloop_prep_recv_fixed(b_lean_obj_arg lh, uint32_t reg_index, uint64_t ud,
                                               lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_recv_fixed(the_loop(lh), reg_index, ud));
}
// uloop_prep_send_fixed : @& LoopHandle → UInt32 → @& ByteArray → UInt64 → IO Int32
LEAN_EXPORT lean_obj_res uloop_prep_send_fixed(b_lean_obj_arg lh, uint32_t reg_index,
                                               b_lean_obj_arg bytes, uint64_t ud, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_send_fixed(the_loop(lh), reg_index, lean_sarray_cptr((lean_object*)bytes),
                                   (uint32_t)lean_sarray_size((lean_object*)bytes), ud));
}
// uloop_prep_close_fixed : @& LoopHandle → UInt32 → UInt64 → IO Int32
LEAN_EXPORT lean_obj_res uloop_prep_close_fixed(b_lean_obj_arg lh, uint32_t reg_index, uint64_t ud,
                                                lean_obj_arg w) {
  (void)w;
  return ok_i32(er_prep_close_fixed(the_loop(lh), reg_index, ud));
}

// uloop_submit_wait : @& LoopHandle → UInt32 → IO (Array Event)
// One batch: submit, wait for ≥min, drain. Event objects are constructed HERE
// (hot path): one ctor per completion, scalar fields packed in declaration
// order — ud : UInt64 @0, res : Int64 @8, flags : UInt32 @16, kind : OpKind
// (enum ⇒ u8 tag) @20. MUST match `structure Event` in StdlibEx/IOUring/Loop.lean.
LEAN_EXPORT lean_obj_res uloop_submit_wait(b_lean_obj_arg lh, uint32_t min_complete,
                                           lean_obj_arg w) {
  (void)w;
  er_loop* l = the_loop(lh);
  int32_t n = er_submit_wait(l, min_complete);
  if (n < 0) {
    return loop_io_err("evring: submit_and_wait failed");
  }
  lean_object* arr = lean_alloc_array((size_t)n, (size_t)n);
  const uint8_t* evs = er_events(l);
  for (int32_t i = 0; i < n; ++i) {
    const uint8_t* rec = evs + (size_t)i * ER_REC_SIZE;
    uint64_t ud, res;
    uint32_t flags;
    memcpy(&ud, rec, 8);
    memcpy(&res, rec + 8, 8);
    memcpy(&flags, rec + 16, 4);
    lean_object* e = lean_alloc_ctor(0, 0, 8 + 8 + 4 + 1);
    lean_ctor_set_uint64(e, 0, ud);
    lean_ctor_set_uint64(e, 8, res);
    lean_ctor_set_uint32(e, 16, flags);
    lean_ctor_set_uint8(e, 20, rec[20]);
    lean_array_set_core(arr, (size_t)i, e);
  }
  return lean_io_result_mk_ok(arr);
}

// uloop_take : @& LoopHandle → UInt32 → UInt32 → IO ByteArray
// Copy len bytes out of provided buffer buf_id and recycle the buffer.
LEAN_EXPORT lean_obj_res uloop_take(b_lean_obj_arg lh, uint32_t buf_id, uint32_t len,
                                    lean_obj_arg w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, len, len);
  int32_t rc = er_take(the_loop(lh), buf_id, len, lean_sarray_cptr(arr));
  if (rc < 0) {
    lean_dec(arr);
    return loop_io_err("evring: bad buffer take");
  }
  return lean_io_result_mk_ok(arr);
}

// uloop_recycle : @& LoopHandle → UInt32 → IO Unit
LEAN_EXPORT lean_obj_res uloop_recycle(b_lean_obj_arg lh, uint32_t buf_id, lean_obj_arg w) {
  (void)w;
  er_recycle(the_loop(lh), buf_id);
  return lean_io_result_mk_ok(lean_box(0));
}

// uloop_sq_space : @& LoopHandle → IO UInt32
LEAN_EXPORT lean_obj_res uloop_sq_space(b_lean_obj_arg lh, lean_obj_arg w) {
  (void)w;
  return lean_io_result_mk_ok(lean_box_uint32(er_sq_space(the_loop(lh))));
}

// uloop_buf_size : @& LoopHandle → IO UInt32
LEAN_EXPORT lean_obj_res uloop_buf_size(b_lean_obj_arg lh, lean_obj_arg w) {
  (void)w;
  return lean_io_result_mk_ok(lean_box_uint32(er_buf_size(the_loop(lh))));
}

// ── mesh on the loop ring (fold-in of the evring_mesh Lean ABI) ──────────────

// uloop_ring_fd : @& LoopHandle → IO Int32
LEAN_EXPORT lean_obj_res uloop_ring_fd(b_lean_obj_arg lh, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_ring_fd(the_loop(lh)));
}

// uloop_register_fd : @& LoopHandle → UInt32 → IO Int32  (raw fd → slot index)
LEAN_EXPORT lean_obj_res uloop_register_fd(b_lean_obj_arg lh, uint32_t raw_fd, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_register_fd(the_loop(lh), (int32_t)raw_fd));
}

// uloop_mesh_post : @& LoopHandle → UInt32 → @& ByteArray → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res uloop_mesh_post(b_lean_obj_arg lh, uint32_t target_ring,
                                         b_lean_obj_arg bytes, uint32_t channel, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_mesh_post(the_loop(lh), (int32_t)target_ring,
                             lean_sarray_cptr((lean_object*)bytes),
                             (uint32_t)lean_sarray_size((lean_object*)bytes), channel));
}

// uloop_mesh_send_fd : @& LoopHandle → UInt32 → UInt32 → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res uloop_mesh_send_fd(b_lean_obj_arg lh, uint32_t target_ring,
                                            uint32_t reg_index, uint32_t channel, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_mesh_send_fd(the_loop(lh), (int32_t)target_ring, reg_index, channel));
}

// uloop_mesh_take : UInt64 → UInt32 → IO ByteArray
// Copy `len` payload bytes out of the received slab at `ptr`, free it, return
// the fresh ByteArray. (No handle needed — the pointer owns the slab.)
LEAN_EXPORT lean_obj_res uloop_mesh_take(uint64_t ptr, uint32_t len, lean_obj_arg w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, len, len);
  er_mesh_take(ptr, len, lean_sarray_cptr(arr));
  return lean_io_result_mk_ok(arr);
}

// ── blocking client helpers (gates only) ────────────────────────────────────

// uloop_connect_local : UInt16 → IO Int32
LEAN_EXPORT lean_obj_res uloop_connect_local(uint16_t port, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_connect_local(port));
}

// uloop_local_port : UInt32 → IO Int32
LEAN_EXPORT lean_obj_res uloop_local_port(uint32_t fd, lean_obj_arg w) {
  (void)w;
  return ok_i32(er_local_port((int32_t)fd));
}

// uloop_send_all : UInt32 → @& ByteArray → IO Int64
LEAN_EXPORT lean_obj_res uloop_send_all(uint32_t fd, b_lean_obj_arg bytes, lean_obj_arg w) {
  (void)w;
  int64_t r = er_send_all((int32_t)fd, lean_sarray_cptr((lean_object*)bytes),
                          (uint32_t)lean_sarray_size((lean_object*)bytes));
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)r));
}

// uloop_recv_some : UInt32 → UInt32 → IO ByteArray  (empty = EOF)
LEAN_EXPORT lean_obj_res uloop_recv_some(uint32_t fd, uint32_t cap, lean_obj_arg w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, cap, cap);
  int64_t r = er_recv_some((int32_t)fd, lean_sarray_cptr(arr), cap);
  if (r < 0) {
    lean_dec(arr);
    return loop_io_err("evring: recv failed");
  }
  lean_sarray_set_size(arr, (size_t)r);
  return lean_io_result_mk_ok(arr);
}

// uloop_close_fd : UInt32 → IO Unit  (plain close, gates only)
LEAN_EXPORT lean_obj_res uloop_close_fd(uint32_t fd, lean_obj_arg w) {
  (void)w;
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}

#endif // URING_WITH_LEAN

// ─────────────────────────────────────────────────────────────────────────────
// (3) Standalone smoke test  (-DER_LOOP_STANDALONE)  — proves the UNIFIED ring:
//     ONE loop ring drains BOTH socket I/O (accept/recv/send echo) AND inter-
//     core MSG_RING deliveries, interleaved, both correct. This is the pure-C
//     witness of the merge before the Lean layer.
//
//     cc -std=gnu11 -DER_LOOP_STANDALONE evring_loop.c -luring -lpthread -o ertest && ./ertest
// ─────────────────────────────────────────────────────────────────────────────
#ifdef ER_LOOP_STANDALONE
#  include <assert.h>
#  include <pthread.h>
#  include <sched.h>
#  include <stdatomic.h>
#  include <stdio.h>

#  define ST_N 5000
#  define ST_CH_DATA 7
#  define ST_CH_STOP 0xFFFFFFFFu

static _Atomic int g_worker_ring_fd = -1;
static _Atomic int g_worker_port = -1;

static void st_pin(int cpu) {
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET(cpu, &s);
  pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
}

// Worker core: ONE loop ring that is simultaneously an echo server (multishot
// accept + recv → send) AND a mesh receiver (ER_K_MESH_DATA). Both kinds of
// completion flow through the SAME er_submit_wait drain.
static void* st_worker(void* arg) {
  (void)arg;
  st_pin(1);
  er_loop* l = er_loop_init(1024, 1024, 16384, 4096);
  if (!l) {
    fprintf(stderr, "worker init failed\n");
    return (void*)0;
  }
  int32_t lfd = er_listen(0, 128);
  if (lfd < 0) {
    fprintf(stderr, "worker listen failed\n");
    er_loop_cleanup(l);
    free(l);
    return (void*)0;
  }
  int32_t port = er_local_port(lfd);
  er_prep_accept(l, lfd, 1);
  atomic_store(&g_worker_ring_fd, er_ring_fd(l));
  atomic_store(&g_worker_port, port);

  long mesh_got = 0, mesh_ok = 0, echoed = 0;
  int socket_closed = 0, stop = 0;
  uint8_t tmp[16384];
  while (!stop) {
    int32_t n = er_submit_wait(l, 1);
    if (n < 0) {
      fprintf(stderr, "worker wait: %s\n", strerror(-n));
      break;
    }
    const uint8_t* evs = er_events(l);
    for (int32_t i = 0; i < n; ++i) {
      const uint8_t* r = evs + (size_t)i * ER_REC_SIZE;
      uint64_t ud;
      int64_t res;
      uint32_t flags;
      uint8_t kind;
      memcpy(&ud, r, 8);
      memcpy(&res, r + 8, 8);
      memcpy(&flags, r + 16, 4);
      kind = r[20];
      if (kind == ER_K_MESH_DATA) {
        uint32_t len = (uint32_t)res;
        er_mesh_take(ud, len, tmp);
        if (flags == ST_CH_STOP) { /* not used; STOP arrives via socket close */
        }
        uint64_t seq = 0;
        for (uint32_t k = 0; k < 8 && k < len; ++k) {
          seq |= (uint64_t)tmp[k] << (8 * k);
        }
        if (seq == (uint64_t)mesh_got) {
          mesh_ok++;
        }
        mesh_got++;
      } else if (kind == ER_K_ACCEPT) {
        if (res >= 0) {
          er_prep_recv(l, (int32_t)res, 1000 + (uint64_t)res);
        }
      } else if (kind == ER_K_RECV) {
        int32_t cfd = (int32_t)(ud - 1000);
        if (res > 0 && (flags & IORING_CQE_F_BUFFER)) {
          uint32_t blen = (uint32_t)res;
          uint32_t buf_id = flags >> 16;
          er_take(l, buf_id, blen, tmp);
          er_prep_send(l, cfd, tmp, blen, 2000 + (uint64_t)cfd);
          if (!(flags & IORING_CQE_F_MORE)) {
            er_prep_recv(l, cfd, ud);
          }
        } else {
          er_prep_close(l, cfd, 3000 + (uint64_t)cfd);
        }
      } else if (kind == ER_K_SEND) {
        echoed++;
      } else if (kind == ER_K_CLOSE) {
        socket_closed = 1;
      }
    }
    if (socket_closed && mesh_got >= ST_N) {
      stop = 1;
    }
  }
  er_loop_cleanup(l);
  free(l);
  long ok = (mesh_ok == ST_N) && (echoed >= ST_N) && socket_closed;
  return (void*)(intptr_t)ok;
}

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  st_pin(0);
  er_loop* l = er_loop_init(1024, 1024, 16384, 4096);
  if (!l) {
    fprintf(stderr, "main init failed\n");
    return 1;
  }

  pthread_t th;
  pthread_create(&th, NULL, st_worker, NULL);
  int target, port;
  while ((target = atomic_load(&g_worker_ring_fd)) < 0) {
    sched_yield();
  }
  while ((port = atomic_load(&g_worker_port)) < 0) {
    sched_yield();
  }

  int cfd = er_connect_local((uint16_t)port);
  if (cfd < 0) {
    fprintf(stderr, "connect failed: %s\n", strerror(-cfd));
    return 1;
  }

  // Interleave socket echo and mesh posts on the worker's single ring.
  long ok = 1;
  for (long i = 0; i < ST_N; ++i) {
    // mesh: post the 8-byte LE sequence via our ring to the worker's ring
    uint8_t payload[8];
    uint64_t seq = (uint64_t)i;
    for (int k = 0; k < 8; ++k) {
      payload[k] = (uint8_t)(seq >> (8 * k));
    }
    er_mesh_post(l, target, payload, 8, ST_CH_DATA);
    er_submit_wait(l, 0);
    // socket: send a message, read the echo, verify
    char msg[64];
    int mlen = snprintf(msg, sizeof(msg), "echo-%ld", i);
    er_send_all(cfd, msg, (uint32_t)mlen);
    char got[64];
    long total = 0;
    while (total < mlen) {
      int64_t rr = er_recv_some(cfd, got + total, (uint32_t)(mlen - total));
      if (rr <= 0) {
        ok = 0;
        break;
      }
      total += rr;
    }
    if (total != mlen || memcmp(msg, got, (size_t)mlen) != 0) {
      ok = 0;
    }
  }
  close(cfd);

  void* wret;
  pthread_join(th, &wret);
  er_loop_cleanup(l);
  free(l);

  if (ok && (intptr_t)wret) {
    printf("evring_loop standalone: OK — one ring: %d socket echoes + %d mesh msgs interleaved\n",
           ST_N, ST_N);
    return 0;
  }
  printf("evring_loop standalone: FAIL (client ok=%ld worker=%ld)\n", ok, (long)(intptr_t)wret);
  return 1;
}
#endif // ER_LOOP_STANDALONE
