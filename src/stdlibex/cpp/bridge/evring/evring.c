// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // aleph // evring — io_uring bridge
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Two layers, deliberately separated:
//
//   (1) PURE-C CORE  (er_*)   — plain C types, real io_uring. No Lean. This is
//       the load-bearing logic and it is testable standalone against a live ring.
//
//   (2) LEAN-ABI WRAPPERS (evring_*) — the lean_object boundary. Thin: convert
//       args, call the core, box results. RingHandle is a finalized external
//       object so a dropped ring is always cleaned up (and explicit cleanup is
//       idempotent via the `active` flag — no double-exit).
//
// The split exists so the part that can be proven in-sandbox (the ring ops) is
// not entangled with the part that can only link on-box (the Lean runtime, which
// is libc++ — decision VII). evring.c is pure C and pulls no C++ stdlib.

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <liburing.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

// ─────────────────────────────────────────────────────────────────────────────
// (1) Pure-C core
// ─────────────────────────────────────────────────────────────────────────────

typedef struct {
  struct io_uring ring;
  int active; // 1 while the ring is initialized; guards double-exit
} er_ring;

// Initialize a ring with `entries` SQ slots. Returns NULL on failure.
er_ring* er_init(uint32_t entries) {
  if (entries == 0) {
    entries = 8;
  }
  er_ring* r = (er_ring*)calloc(1, sizeof(er_ring));
  if (!r) {
    return NULL;
  }
  int rc = io_uring_queue_init(entries, &r->ring, 0);
  if (rc < 0) {
    free(r);
    return NULL;
  }
  r->active = 1;
  return r;
}

// Idempotent: safe to call explicitly AND from the finalizer.
void er_cleanup(er_ring* r) {
  if (!r) {
    return;
  }
  if (r->active) {
    io_uring_queue_exit(&r->ring);
    r->active = 0;
  }
}

// Submit `n` no-ops and reap them. Returns the number that completed with res==0.
uint32_t er_batch_nop(er_ring* r, uint32_t n) {
  if (!r || !r->active) {
    return 0;
  }
  uint32_t submitted = 0;
  for (uint32_t i = 0; i < n; ++i) {
    struct io_uring_sqe* sqe = io_uring_get_sqe(&r->ring);
    if (!sqe) {
      break;
    }
    io_uring_prep_nop(sqe);
    io_uring_sqe_set_data64(sqe, (uint64_t)i);
    ++submitted;
  }
  if (submitted == 0) {
    return 0;
  }
  int sub = io_uring_submit(&r->ring);
  if (sub < 0) {
    return 0;
  }
  uint32_t done = 0;
  for (uint32_t i = 0; i < submitted; ++i) {
    struct io_uring_cqe* cqe = NULL;
    if (io_uring_wait_cqe(&r->ring, &cqe) < 0) {
      break;
    }
    if (cqe->res == 0) {
      ++done;
    }
    io_uring_cqe_seen(&r->ring, cqe);
  }
  return done;
}

// Single completion helper: submit one prepared SQE, wait, return cqe->res.
static int64_t er_submit_one(er_ring* r) {
  int sub = io_uring_submit(&r->ring);
  if (sub < 0) {
    return sub;
  }
  struct io_uring_cqe* cqe = NULL;
  int w = io_uring_wait_cqe(&r->ring, &cqe);
  if (w < 0) {
    return w;
  }
  int64_t res = (int64_t)cqe->res;
  io_uring_cqe_seen(&r->ring, cqe);
  return res;
}

// statx via ring. Returns file size in bytes, or -errno on failure.
int64_t er_statx(er_ring* r, const char* path) {
  if (!r || !r->active) {
    return -EINVAL;
  }
  struct statx stxbuf;
  memset(&stxbuf, 0, sizeof(stxbuf));
  struct io_uring_sqe* sqe = io_uring_get_sqe(&r->ring);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_statx(sqe, AT_FDCWD, path, 0, STATX_SIZE, &stxbuf);
  int64_t res = er_submit_one(r);
  if (res < 0) {
    return res;
  }
  return (int64_t)stxbuf.stx_size;
}

// openat via ring. Returns fd (>=0) or -errno.
int32_t er_open(er_ring* r, const char* path, int32_t flags, uint32_t mode) {
  if (!r || !r->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = io_uring_get_sqe(&r->ring);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_openat(sqe, AT_FDCWD, path, (int)flags, (mode_t)mode);
  int64_t res = er_submit_one(r);
  return (int32_t)res;
}

// read via ring into buf. Returns bytes read (>=0) or -errno.
int64_t er_read(er_ring* r, int32_t fd, void* buf, uint32_t sz, int64_t off) {
  if (!r || !r->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = io_uring_get_sqe(&r->ring);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_read(sqe, (int)fd, buf, sz, (uint64_t)off);
  return er_submit_one(r);
}

// close via ring. Returns 0 or -errno.
int32_t er_close(er_ring* r, int32_t fd) {
  if (!r || !r->active) {
    return -EINVAL;
  }
  struct io_uring_sqe* sqe = io_uring_get_sqe(&r->ring);
  if (!sqe) {
    return -EAGAIN;
  }
  io_uring_prep_close(sqe, (int)fd);
  int64_t res = er_submit_one(r);
  return (int32_t)res;
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) Lean-ABI wrappers
// ─────────────────────────────────────────────────────────────────────────────
// Compiled only when the Lean runtime header is on the include path (the on-box
// `lake`/`leanc` build). The pure-C core above builds and tests without it.
#ifdef EVRING_WITH_LEAN
#  include <lean/lean.h>

// RingHandle external class — finalizer guarantees cleanup of a dropped ring.
static lean_external_class* g_ring_class = NULL;

static void er_finalize(void* p) {
  er_ring* r = (er_ring*)p;
  er_cleanup(r);
  free(r);
}
static void er_foreach(void* p, b_lean_obj_arg f) {
  (void)p;
  (void)f; // no nested Lean objects to traverse
}
static lean_external_class* ring_class(void) {
  if (g_ring_class == NULL) {
    g_ring_class = lean_register_external_class(er_finalize, er_foreach);
  }
  return g_ring_class;
}

static inline lean_obj_res io_err(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

// evring_init : UInt32 → IO RingHandle
LEAN_EXPORT lean_obj_res evring_init(uint32_t entries, lean_obj_arg w) {
  (void)w;
  er_ring* r = er_init(entries);
  if (!r) {
    return io_err("evring: io_uring_queue_init failed");
  }
  return lean_io_result_mk_ok(lean_alloc_external(ring_class(), r));
}

// evring_cleanup : @& RingHandle → IO Unit
LEAN_EXPORT lean_obj_res evring_cleanup(b_lean_obj_arg rh, lean_obj_arg w) {
  (void)w;
  er_cleanup((er_ring*)lean_get_external_data(rh));
  return lean_io_result_mk_ok(lean_box(0));
}

// evring_batch_nop : @& RingHandle → UInt32 → IO UInt32
LEAN_EXPORT lean_obj_res evring_batch_nop(b_lean_obj_arg rh, uint32_t n, lean_obj_arg w) {
  (void)w;
  uint32_t done = er_batch_nop((er_ring*)lean_get_external_data(rh), n);
  return lean_io_result_mk_ok(lean_box_uint32(done));
}

// evring_statx : @& RingHandle → @& String → IO Nat
LEAN_EXPORT lean_obj_res evring_statx(b_lean_obj_arg rh, b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int64_t sz = er_statx((er_ring*)lean_get_external_data(rh), lean_string_cstr(path));
  if (sz < 0) {
    return io_err("evring: statx failed");
  }
  return lean_io_result_mk_ok(lean_uint64_to_nat((uint64_t)sz));
}

// evring_open : @& RingHandle → @& String → Int32 → UInt32 → IO Int32
LEAN_EXPORT lean_obj_res evring_open(b_lean_obj_arg rh, b_lean_obj_arg path, uint32_t flags,
                                     uint32_t mode, lean_obj_arg w) {
  (void)w;
  int32_t fd =
      er_open((er_ring*)lean_get_external_data(rh), lean_string_cstr(path), (int32_t)flags, mode);
  if (fd < 0) {
    return io_err("evring: open failed");
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

// evring_read : @& RingHandle → Int32 → UInt32 → Int64 → IO ByteArray
LEAN_EXPORT lean_obj_res evring_read(b_lean_obj_arg rh, uint32_t fd, uint32_t sz, uint64_t off,
                                     lean_obj_arg w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, sz, sz);
  int64_t n = er_read((er_ring*)lean_get_external_data(rh), (int32_t)fd, lean_sarray_cptr(arr), sz,
                      (int64_t)off);
  if (n < 0) {
    lean_dec(arr);
    return io_err("evring: read failed");
  }
  lean_sarray_set_size(arr, (size_t)n); // shrink to bytes actually read
  return lean_io_result_mk_ok(arr);
}

// evring_close : @& RingHandle → Int32 → IO Int32
LEAN_EXPORT lean_obj_res evring_close(b_lean_obj_arg rh, uint32_t fd, lean_obj_arg w) {
  (void)w;
  int32_t res = er_close((er_ring*)lean_get_external_data(rh), (int32_t)fd);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)res));
}

#endif // EVRING_WITH_LEAN
