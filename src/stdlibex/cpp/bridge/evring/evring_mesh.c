// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                          // aleph // evring_mesh — the shared-nothing MESH wire
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// The RUNTIME that realizes `Continuity.Machine.Mesh.codecEdge` as an actual
// cross-core wire. It is thin on purpose: it moves BYTES and FDS between
// core-pinned io_uring rings via IORING_OP_MSG_RING, and drains completions
// into flat records. It knows NOTHING about codecs, protocols, or types — all
// serialization/parsing is Lean's job via `Box`. Here we only:
//
//   • create ONE ring per owner thread (DEFER_TASKRUN|SINGLE_ISSUER|COOP —
//     the shared-nothing fast config; a ring is OWNED by the thread that
//     creates it, so each core creates its own),
//   • MSG_DATA a heap pointer across cores (shared address space, exclusive
//     ownership handoff — the receiver frees/returns the buffer),
//   • MSG_SEND_FD a registered fd across cores (sparse file table both ends),
//   • drain: distinguish RECEIVED messages from our own send-completions using
//     a marker bit passed into cqe->flags (IORING_MSG_RING_FLAGS_PASS).
//
// Layering matches evring_loop.c: em_* is pure C (testable standalone under
// -DEMESH_STANDALONE); emesh_* are the Lean-ABI wrappers under
// -DEVRING_WITH_LEAN. Keep the record layout in sync with Aleph/EVRing/Mesh.lean.
//
//   standalone smoke test:
//     cc -std=gnu11 -DEMESH_STANDALONE evring_mesh.c -luring -lpthread -o emtest && ./emtest

#define _GNU_SOURCE
#include <errno.h>
#include <liburing.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// ─────────────────────────────────────────────────────────────────────────────
// Constants and record layout
// ─────────────────────────────────────────────────────────────────────────────

// Marker bit OR'd into the target's cqe->flags for RECEIVED data messages (via
// IORING_MSG_RING_FLAGS_PASS, which copies sqe->file_index → cqe->flags). Sits
// above the low CQE flag bits (F_BUFFER/F_MORE/…) and below the buffer-id shift
// (bit 16), so it never collides on a mesh-only ring.
#define EM_MARK 0x4000u

// Event kinds — carried in the flat record's `kind` byte, mirrored in
// Aleph/EVRing/Mesh.lean (ctor order is the runtime tag).
enum {
  EM_K_SEND_DONE = 0, // our own send completed (only surfaced on ERROR; a = res)
  EM_K_DATA_RECV = 1, // a peer MSG_DATA arrived   (a = buffer ptr, b = len, channel)
  EM_K_FD_RECV = 2,   // a peer MSG_SEND_FD arrived (a = reg index, channel = cookie)
};

// One drained mesh event, as seen by Lean. 24 bytes, little-endian.
//   [0]      u8  kind    (EM_K_*)
//   [8..16)  u64 a
//   [16..20) u32 b       (payload len for DATA_RECV, else 0)
//   [20..24) u32 channel
#define EM_REC_SIZE 24

// The on-wire buffer header prepended to every MSG_DATA payload. The channel
// and length must reach the receiver, but the target cqe carries only the
// pointer (user_data) and len (res) — so channel travels in this header. The
// buffer is `sizeof(em_hdr) + len` bytes; ownership transfers to the receiver.
typedef struct {
  uint32_t channel;
  uint32_t len;
  // payload follows immediately
} em_hdr;

typedef struct {
  struct io_uring ring;
  int active;
  int fast;           // 1 if DEFER_TASKRUN|SINGLE_ISSUER accepted
  uint32_t nfiles;    // sparse registered-file table size
  uint32_t next_file; // next free slot for emesh_register_fd

  uint8_t* evout;     // flat drained-record buffer
  uint32_t evout_cap; // capacity in records
} em_mesh;

// ─────────────────────────────────────────────────────────────────────────────
// Send-buffer slab pool — the fast path for em_post/em_take (à la mesh_bench).
//
// A process-global fixed-slab allocator, cross-thread BY DESIGN: any core pops
// (em_post) and any core pushes (em_take), because the peer that receives a
// buffer is the one that frees it. A short spinlock guards the intrusive
// freelist; slabs are recognized by arena address range, so payloads larger
// than a slab (or a drained pool) fall back to malloc/free transparently. This
// keeps allocation O(1) off a fixed pool on the hot path instead of hitting the
// general allocator per message.
// ─────────────────────────────────────────────────────────────────────────────
#define EM_SLAB_SIZE 256
#define EM_POOL_SLABS (1u << 16) // 64k * 256 B = 16 MiB

static uint8_t* g_arena = NULL;
static uint8_t* g_arena_end = NULL;
static void* g_free_list = NULL;
static atomic_flag g_pool_lock = ATOMIC_FLAG_INIT;
static pthread_once_t g_pool_once = PTHREAD_ONCE_INIT;

static void em_pool_init(void) {
  g_arena = malloc((size_t)EM_POOL_SLABS * EM_SLAB_SIZE);
  if (!g_arena) {
    return;
  }
  g_arena_end = g_arena + (size_t)EM_POOL_SLABS * EM_SLAB_SIZE;
  void* head = NULL;
  for (uint32_t i = 0; i < EM_POOL_SLABS; ++i) {
    void* slab = g_arena + (size_t)i * EM_SLAB_SIZE;
    *(void**)slab = head; // intrusive next-pointer while free
    head = slab;
  }
  g_free_list = head;
}
static inline void em_pool_lock(void) {
  while (atomic_flag_test_and_set_explicit(&g_pool_lock, memory_order_acquire)) { /* spin */
  }
}
static inline void em_pool_unlock(void) {
  atomic_flag_clear_explicit(&g_pool_lock, memory_order_release);
}

// Allocate `need` bytes: a pooled slab if it fits and one is free, else malloc.
static void* em_buf_alloc(uint32_t need) {
  pthread_once(&g_pool_once, em_pool_init);
  if (need <= EM_SLAB_SIZE && g_arena) {
    em_pool_lock();
    void* p = g_free_list;
    if (p) {
      g_free_list = *(void**)p;
      em_pool_unlock();
      return p;
    }
    em_pool_unlock();
  }
  return malloc(need ? need : 1);
}
// Free a buffer: return a slab to the pool, or free a malloc fallback.
static void em_buf_free(void* p) {
  if ((uint8_t*)p >= g_arena && (uint8_t*)p < g_arena_end) {
    em_pool_lock();
    *(void**)p = g_free_list;
    g_free_list = p;
    em_pool_unlock();
  } else {
    free(p);
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) Pure-C core  (em_*)  — no Lean, no codec, no protocol
// ─────────────────────────────────────────────────────────────────────────────

// Pin the CALLING thread to `cpu`. Returns 0 or -errno. Must be called on the
// thread that will own the ring, BEFORE em_init.
int em_pin(int cpu) {
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET(cpu, &s);
  int rc = pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
  return rc == 0 ? 0 : -rc;
}

// Create ONE ring on the CALLING thread. entries = SQ depth; nfiles = sparse
// registered-file table (for fd send/recv); evout_cap = max records per drain.
// Tries the shared-nothing fast flags, falls back to a plain ring. Returns NULL
// on failure. MUST be called on the owner thread (fast flags bind the ring to
// its creator).
em_mesh* em_init(uint32_t entries, uint32_t nfiles, uint32_t evout_cap) {
  if (entries == 0) {
    entries = 1024;
  }
  if (nfiles == 0) {
    nfiles = 1024;
  }
  if (evout_cap == 0) {
    evout_cap = 4096;
  }

  em_mesh* m = calloc(1, sizeof(em_mesh));
  if (!m) {
    return NULL;
  }

  struct io_uring_params p;
  memset(&p, 0, sizeof(p));
  p.flags = IORING_SETUP_DEFER_TASKRUN | IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_COOP_TASKRUN |
            IORING_SETUP_CQSIZE;
  p.cq_entries = entries * 4;
  int rc = io_uring_queue_init_params(entries, &m->ring, &p);
  if (rc < 0) {
    memset(&p, 0, sizeof(p));
    rc = io_uring_queue_init(entries, &m->ring, 0);
    if (rc < 0) {
      free(m);
      return NULL;
    }
    m->fast = 0;
  } else {
    m->fast = 1;
  }
  m->active = 1;

  // sparse registered-file table: fd send/recv both need one.
  if (io_uring_register_files_sparse(&m->ring, nfiles) < 0) {
    goto fail;
  }
  m->nfiles = nfiles;
  m->next_file = 0;

  m->evout_cap = evout_cap;
  m->evout = malloc((size_t)evout_cap * EM_REC_SIZE);
  if (!m->evout) {
    goto fail;
  }
  return m;

fail:
  io_uring_queue_exit(&m->ring);
  free(m->evout);
  free(m);
  return NULL;
}

// Idempotent teardown (also the Lean finalizer).
void em_cleanup(em_mesh* m) {
  if (!m || !m->active) {
    return;
  }
  io_uring_queue_exit(&m->ring);
  free(m->evout);
  m->evout = NULL;
  m->active = 0;
}

// The ring's fd — a peer targets it with MSG_RING. Publish this so peers can
// reach this core.
int em_ring_fd(const em_mesh* m) {
  return (m && m->active) ? m->ring.ring_fd : -1;
}

int em_fast(const em_mesh* m) {
  return m ? m->fast : 0;
}

// SQE acquisition with an inline flush when the SQ is full.
static struct io_uring_sqe* em_get_sqe(em_mesh* m) {
  struct io_uring_sqe* sqe = io_uring_get_sqe(&m->ring);
  if (!sqe) {
    io_uring_submit(&m->ring);
    sqe = io_uring_get_sqe(&m->ring);
  }
  return sqe;
}

// Install a raw fd into this ring's sparse table; returns the slot index or
// -errno. Use the index for emesh_send_fd or fixed-file I/O on this ring.
int32_t em_register_fd(em_mesh* m, int raw_fd) {
  if (!m || !m->active) {
    return -EINVAL;
  }
  if (m->next_file >= m->nfiles) {
    return -ENOSPC;
  }
  uint32_t idx = m->next_file;
  int rc = io_uring_register_files_update(&m->ring, idx, &raw_fd, 1);
  if (rc < 0) {
    return rc;
  }
  m->next_file++;
  return (int32_t)idx;
}

// Enqueue a MSG_DATA send to `target_ring_fd`. The bytes are COPIED into a
// C-owned buffer NOW (Lean ByteArrays are GC-managed, must not cross threads);
// the pointer is passed by value as the target's user_data and ownership
// transfers to the receiver, which frees it via em_take. `channel` travels in
// the buffer header. Enqueue-only: nothing hits the kernel until em_submit_wait.
// Successful sends are silent (IOSQE_CQE_SKIP_SUCCESS) for throughput; a
// SEND_DONE record is emitted only on send ERROR. Returns 0 or -errno.
int32_t em_post(em_mesh* m, int target_ring_fd, const void* bytes, uint32_t len, uint32_t channel) {
  if (!m || !m->active) {
    return -EINVAL;
  }
  em_hdr* buf = em_buf_alloc((uint32_t)(sizeof(em_hdr) + len));
  if (!buf) {
    return -ENOMEM;
  }
  buf->channel = channel;
  buf->len = len;
  if (len) {
    memcpy((uint8_t*)buf + sizeof(em_hdr), bytes, len);
  }

  struct io_uring_sqe* sqe = em_get_sqe(m);
  if (!sqe) {
    em_buf_free(buf);
    return -EAGAIN;
  }
  // len → target cqe->res, (u64)buf → target cqe->user_data, EM_MARK → flags.
  io_uring_prep_msg_ring_cqe_flags(sqe, target_ring_fd, len, (uint64_t)(uintptr_t)buf, 0, EM_MARK);
  io_uring_sqe_set_data64(sqe, channel); // our completion's ud (error reporting)
  sqe->flags |= IOSQE_CQE_SKIP_SUCCESS;
  return 0;
}

// Enqueue a MSG_SEND_FD: hand the registered fd at `reg_index` (a slot in THIS
// ring's table) to the peer, which auto-allocates a slot in its own table. The
// receiver recovers the assigned index from its FD_RECV record; `channel` is
// the cookie. Enqueue-only; silent on success. Returns 0 or -errno.
int32_t em_send_fd(em_mesh* m, int target_ring_fd, uint32_t reg_index, uint32_t channel) {
  if (!m || !m->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = em_get_sqe(m);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_msg_ring_fd_alloc(sqe, target_ring_fd, (int)reg_index, (uint64_t)channel, 0);
  io_uring_sqe_set_data64(sqe, channel);
  sqe->flags |= IOSQE_CQE_SKIP_SUCCESS;
  return 0;
}

// Submit everything enqueued, wait for ≥ min_complete completions, then drain
// up to evout_cap records. Returns the record count (≥0) or -errno.
//
// Disambiguation on a mesh-only ring:
//   cqe->flags & EM_MARK  → DATA_RECV (a=user_data ptr; channel/len from header)
//   else cqe->res >= 0    → FD_RECV   (a=res index; channel=user_data cookie)
//   else (res < 0)        → SEND_DONE (a=res; our own failed send)
int32_t em_submit_wait(em_mesh* m, uint32_t min_complete) {
  if (!m || !m->active) {
    return -EINVAL;
  }
  int rc = io_uring_submit_and_wait(&m->ring, min_complete);
  if (rc < 0 && rc != -ETIME && rc != -EINTR) {
    return rc;
  }

  uint32_t n = 0, drained = 0;
  unsigned head;
  struct io_uring_cqe* cqe;
  io_uring_for_each_cqe(&m->ring, head, cqe) {
    if (n >= m->evout_cap) {
      break;
    }
    ++drained;

    uint8_t kind;
    uint64_t a = 0;
    uint32_t b = 0, channel = 0;

    if (cqe->flags & EM_MARK) {
      // received data message: user_data is the buffer pointer
      kind = EM_K_DATA_RECV;
      a = cqe->user_data;
      const em_hdr* h = (const em_hdr*)(uintptr_t)cqe->user_data;
      b = h->len;
      channel = h->channel;
    } else if (cqe->res >= 0) {
      // received fd: res is the assigned registered index, user_data the cookie
      kind = EM_K_FD_RECV;
      a = (uint64_t)(uint32_t)cqe->res;
      channel = (uint32_t)cqe->user_data;
    } else {
      // our own send failed (SKIP_SUCCESS suppresses the ok case)
      kind = EM_K_SEND_DONE;
      a = (uint64_t)(int64_t)cqe->res;
      channel = (uint32_t)cqe->user_data;
    }

    uint8_t* r = m->evout + (size_t)n * EM_REC_SIZE;
    r[0] = kind;
    r[1] = r[2] = r[3] = r[4] = r[5] = r[6] = r[7] = 0;
    memcpy(r + 8, &a, 8);
    memcpy(r + 16, &b, 4);
    memcpy(r + 20, &channel, 4);
    ++n;
  }
  io_uring_cq_advance(&m->ring, drained);
  return (int32_t)n;
}

// Submit enqueued SQEs WITHOUT waiting or draining. Lets a core push its sends
// out mid-batch (so a peer isn't left idle) while it keeps processing a drained
// batch — the key to overlapping both cores instead of ping-ponging in
// lockstep. Returns 0 or -errno.
int32_t em_flush(em_mesh* m) {
  if (!m || !m->active) {
    return -EINVAL;
  }
  int rc = io_uring_submit(&m->ring);
  return rc < 0 ? rc : 0;
}

const uint8_t* em_events(const em_mesh* m) {
  return m->evout;
}

// Copy `len` payload bytes out of the received buffer at `ptr` into `dst`, then
// FREE the buffer (ownership ends here). `ptr` is the header pointer as
// delivered in a DATA_RECV record's `a`. Returns 0.
int32_t em_take(uint64_t ptr, uint32_t len, void* dst) {
  em_hdr* buf = (em_hdr*)(uintptr_t)ptr;
  if (len) {
    memcpy(dst, (uint8_t*)buf + sizeof(em_hdr), len);
  }
  em_buf_free(buf);
  return 0;
}

uint32_t em_sq_space(const em_mesh* m) {
  return (m && m->active) ? io_uring_sq_space_left(&((em_mesh*)m)->ring) : 0;
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) Lean-ABI wrappers  (emesh_*)
// ─────────────────────────────────────────────────────────────────────────────
#ifdef EVRING_WITH_LEAN
#  include <lean/lean.h>

static lean_external_class* g_mesh_class = NULL;

static void emesh_finalize(void* p) {
  em_cleanup((em_mesh*)p);
  free(p);
}
static void emesh_foreach(void* p, b_lean_obj_arg f) {
  (void)p;
  (void)f;
}

static lean_external_class* mesh_class(void) {
  if (g_mesh_class == NULL) {
    g_mesh_class = lean_register_external_class(emesh_finalize, emesh_foreach);
  }
  return g_mesh_class;
}

static inline lean_obj_res mesh_io_err(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
static inline em_mesh* the_mesh(b_lean_obj_arg h) {
  return (em_mesh*)lean_get_external_data(h);
}
static inline lean_obj_res ok_i32(int32_t v) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)v));
}

// emesh_pin : UInt32 → IO Int32
LEAN_EXPORT lean_obj_res emesh_pin(uint32_t cpu, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_pin((int)cpu));
}

// emesh_init : UInt32 → UInt32 → UInt32 → IO MeshHandle   (owner thread only)
LEAN_EXPORT lean_obj_res emesh_init(uint32_t entries, uint32_t nfiles, uint32_t evout_cap,
                                    lean_obj_arg w) {
  (void)w;
  em_mesh* m = em_init(entries, nfiles, evout_cap);
  if (!m) {
    return mesh_io_err("mesh: init failed");
  }
  return lean_io_result_mk_ok(lean_alloc_external(mesh_class(), m));
}

// emesh_cleanup : @& MeshHandle → IO Unit
LEAN_EXPORT lean_obj_res emesh_cleanup(b_lean_obj_arg mh, lean_obj_arg w) {
  (void)w;
  em_cleanup(the_mesh(mh));
  return lean_io_result_mk_ok(lean_box(0));
}

// emesh_ring_fd : @& MeshHandle → IO Int32
LEAN_EXPORT lean_obj_res emesh_ring_fd(b_lean_obj_arg mh, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_ring_fd(the_mesh(mh)));
}

// emesh_fast : @& MeshHandle → IO UInt8
LEAN_EXPORT lean_obj_res emesh_fast(b_lean_obj_arg mh, lean_obj_arg w) {
  (void)w;
  return lean_io_result_mk_ok(lean_box(em_fast(the_mesh(mh)) ? 1 : 0));
}

// emesh_register_fd : @& MeshHandle → UInt32 → IO Int32   (raw fd → slot index)
LEAN_EXPORT lean_obj_res emesh_register_fd(b_lean_obj_arg mh, uint32_t raw_fd, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_register_fd(the_mesh(mh), (int)raw_fd));
}

// emesh_post : @& MeshHandle → Int32 → @& ByteArray → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res emesh_post(b_lean_obj_arg mh, uint32_t target_ring_fd,
                                    b_lean_obj_arg bytes, uint32_t channel, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_post(the_mesh(mh), (int)target_ring_fd, lean_sarray_cptr((lean_object*)bytes),
                        (uint32_t)lean_sarray_size((lean_object*)bytes), channel));
}

// emesh_send_fd : @& MeshHandle → Int32 → UInt32 → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res emesh_send_fd(b_lean_obj_arg mh, uint32_t target_ring_fd,
                                       uint32_t reg_index, uint32_t channel, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_send_fd(the_mesh(mh), (int)target_ring_fd, reg_index, channel));
}

// emesh_submit_wait : @& MeshHandle → UInt32 → IO (Array MeshEvent)
// MeshEvent scalar layout (declaration order): a : UInt64 @0, b : UInt32 @8,
// channel : UInt32 @12, kind : MeshKind (u8) @16. MUST match Mesh.lean.
LEAN_EXPORT lean_obj_res emesh_submit_wait(b_lean_obj_arg mh, uint32_t min_complete,
                                           lean_obj_arg w) {
  (void)w;
  em_mesh* m = the_mesh(mh);
  int32_t n = em_submit_wait(m, min_complete);
  if (n < 0) {
    return mesh_io_err("mesh: submit_and_wait failed");
  }
  lean_object* arr = lean_alloc_array((size_t)n, (size_t)n);
  const uint8_t* evs = em_events(m);
  for (int32_t i = 0; i < n; ++i) {
    const uint8_t* rec = evs + (size_t)i * EM_REC_SIZE;
    uint64_t a;
    uint32_t b, channel;
    memcpy(&a, rec + 8, 8);
    memcpy(&b, rec + 16, 4);
    memcpy(&channel, rec + 20, 4);
    lean_object* e = lean_alloc_ctor(0, 0, 8 + 4 + 4 + 1);
    lean_ctor_set_uint64(e, 0, a);
    lean_ctor_set_uint32(e, 8, b);
    lean_ctor_set_uint32(e, 12, channel);
    lean_ctor_set_uint8(e, 16, rec[0]);
    lean_array_set_core(arr, (size_t)i, e);
  }
  return lean_io_result_mk_ok(arr);
}

// emesh_take : UInt64 → UInt32 → IO ByteArray
// Copy `len` payload bytes out of the received buffer at `ptr`, free it, return
// the fresh ByteArray. (No handle needed — the pointer owns the buffer.)
LEAN_EXPORT lean_obj_res emesh_take(uint64_t ptr, uint32_t len, lean_obj_arg w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, len, len);
  em_take(ptr, len, lean_sarray_cptr(arr));
  return lean_io_result_mk_ok(arr);
}

// emesh_sq_space : @& MeshHandle → IO UInt32
LEAN_EXPORT lean_obj_res emesh_sq_space(b_lean_obj_arg mh, lean_obj_arg w) {
  (void)w;
  return lean_io_result_mk_ok(lean_box_uint32(em_sq_space(the_mesh(mh))));
}

// emesh_flush : @& MeshHandle → IO Int32
LEAN_EXPORT lean_obj_res emesh_flush(b_lean_obj_arg mh, lean_obj_arg w) {
  (void)w;
  return ok_i32(em_flush(the_mesh(mh)));
}

#endif // EVRING_WITH_LEAN

// ─────────────────────────────────────────────────────────────────────────────
// (3) Standalone smoke test  (-DEMESH_STANDALONE)  — proves the pure em_* core
//     before the Lean layer. Mirrors mesh_poc.c: data + fd handoff, 2 cores.
// ─────────────────────────────────────────────────────────────────────────────
#ifdef EMESH_STANDALONE
#  include <assert.h>
#  include <stdatomic.h>
#  include <stdio.h>
#  include <sys/socket.h>

#  define CH_DATA 7
#  define CH_STOP 0xFFFFFFFFu
#  define CH_FD 9

static const char* PAYLOAD = "hello across the em mesh";
static _Atomic int worker_fd = -1;

// core 1: owns its ring, receives K data messages + one fd, verifies, echoes count.
static void* worker(void* arg) {
  long K = (long)(intptr_t)arg;
  em_pin(1);
  em_mesh* m = em_init(1024, 1024, 4096);
  if (!m) {
    fprintf(stderr, "worker init failed\n");
    return (void*)0;
  }
  atomic_store(&worker_fd, em_ring_fd(m));

  long got = 0, fd_ok = 0;
  int stop = 0;
  char rbuf[128];
  while (!stop) {
    int32_t n = em_submit_wait(m, 1);
    if (n < 0) {
      fprintf(stderr, "worker wait: %s\n", strerror(-n));
      break;
    }
    const uint8_t* evs = em_events(m);
    for (int32_t i = 0; i < n; ++i) {
      const uint8_t* r = evs + (size_t)i * EM_REC_SIZE;
      uint8_t kind = r[0];
      uint64_t a;
      uint32_t b, ch;
      memcpy(&a, r + 8, 8);
      memcpy(&b, r + 16, 4);
      memcpy(&ch, r + 20, 4);
      if (kind == EM_K_DATA_RECV) {
        if (ch == CH_STOP) {
          stop = 1;
          continue;
        }
        uint8_t tmp[128];
        em_take(a, b, tmp);
        // verify payload: each message is the 8-byte LE seq
        uint64_t seq = 0;
        for (int k = 0; k < 8 && (uint32_t)k < b; ++k) {
          seq |= (uint64_t)tmp[k] << (8 * k);
        }
        if (seq == (uint64_t)got) {
          got++;
        }
      } else if (kind == EM_K_FD_RECV) {
        // read the migrated fd through the fixed-file table
        int idx = (int)a;
        struct io_uring_sqe* sqe = io_uring_get_sqe(&m->ring);
        io_uring_prep_read(sqe, idx, rbuf, sizeof(rbuf), 0);
        sqe->flags |= IOSQE_FIXED_FILE;
        io_uring_sqe_set_data64(sqe, 0xF00D);
        io_uring_submit(&m->ring);
        struct io_uring_cqe* c;
        io_uring_wait_cqe(&m->ring, &c);
        if (c->res > 0) {
          rbuf[c->res] = 0;
          fd_ok = (strcmp(rbuf, PAYLOAD) == 0);
        }
        io_uring_cqe_seen(&m->ring, c);
      }
    }
  }
  em_cleanup(m);
  free(m);
  return (void*)(intptr_t)((got == K) && fd_ok);
}

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  const long K = 100000;
  em_pin(0);
  em_mesh* m = em_init(1024, 1024, 4096);
  if (!m) {
    fprintf(stderr, "main init failed\n");
    return 1;
  }
  printf("(rings: %s)\n", em_fast(m) ? "DEFER_TASKRUN|SINGLE_ISSUER" : "plain");

  pthread_t th;
  pthread_create(&th, NULL, worker, (void*)(intptr_t)K);
  int target;
  while ((target = atomic_load(&worker_fd)) < 0) {
    sched_yield();
  }

  // K data messages, windowed by SQ space.
  long sent = 0;
  while (sent < K) {
    while (sent < K && em_sq_space(m) > 2) {
      uint8_t payload[8];
      uint64_t seq = (uint64_t)sent;
      for (int k = 0; k < 8; ++k) {
        payload[k] = (uint8_t)(seq >> (8 * k));
      }
      if (em_post(m, target, payload, 8, CH_DATA) < 0) {
        break;
      }
      sent++;
    }
    em_submit_wait(m, 0);
  }

  // fd handoff: fill a socketpair, register the read end, send it.
  int pfd[2];
  assert(socketpair(AF_UNIX, SOCK_STREAM, 0, pfd) == 0);
  assert(write(pfd[1], PAYLOAD, strlen(PAYLOAD)) == (ssize_t)strlen(PAYLOAD));
  int32_t idx = em_register_fd(m, pfd[0]);
  assert(idx >= 0);
  em_send_fd(m, target, (uint32_t)idx, CH_FD);
  em_submit_wait(m, 0);

  // stop
  em_post(m, target, NULL, 0, CH_STOP);
  em_submit_wait(m, 0);

  void* wret;
  pthread_join(th, &wret);
  em_cleanup(m);
  free(m);
  close(pfd[0]);
  close(pfd[1]);

  if ((intptr_t)wret) {
    printf("emesh standalone: OK — %ld data msgs + fd handoff across 2 pinned cores\n", K);
    return 0;
  }
  printf("emesh standalone: FAIL\n");
  return 1;
}
#endif // EMESH_STANDALONE
