/*
 * straylight_tls_bio.c — async TLS via LibreSSL libssl over MEMORY BIOs.
 *
 * Decouples the TLS record-layer crypto from socket I/O. An SSL object is wired
 * to two memory BIOs instead of a socket:
 *
 *     network ciphertext ──sl_bio_feed──▶ rbio ──▶ SSL ──▶ sl_bio_read  (plaintext)
 *     plaintext ──sl_bio_write──▶ SSL ──▶ wbio ──sl_bio_pull──▶ network ciphertext
 *
 * so the caller owns the network I/O — blocking socket today, io_uring next — and
 * the SSL state machine advances purely on bytes fed in / pulled out. Userspace
 * AEAD (no NIC offload), but no new dependency: libssl/libcrypto already link.
 *
 * Also a few blocking raw-socket helpers (sl_sock_*) purely to drive/validate the
 * BIO core end-to-end before the io_uring integration replaces them.
 */
#include <lean/lean.h>
#include <netdb.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

/* ── SSL-over-memory-BIO connection (opaque Lean external object) ── */
typedef struct {
  SSL_CTX* ctx;
  SSL* ssl;  /* owns rbio/wbio after SSL_set_bio */
  BIO* rbio; /* network → SSL */
  BIO* wbio; /* SSL → network */
} sl_bio_conn;

static lean_external_class* g_bio_class = NULL;

static void bio_finalize(void* p) {
  sl_bio_conn* c = (sl_bio_conn*)p;
  if (c) {
    if (c->ssl) {
      SSL_free(c->ssl); /* frees rbio + wbio too */
    }
    if (c->ctx) {
      SSL_CTX_free(c->ctx);
    }
    free(c);
  }
}
static void bio_foreach(void* p, b_lean_obj_arg fn) {
  (void)p;
  (void)fn;
}
static void register_bio_class(void) {
  if (!g_bio_class) {
    g_bio_class = lean_register_external_class(bio_finalize, bio_foreach);
  }
}
static lean_object* mkerr(const char* m) {
  return lean_mk_io_user_error(lean_mk_string(m));
}

/* comma list "h2,http/1.1" → ALPN wire format (each proto length-prefixed) */
static int build_alpn(const char* csv, unsigned char* out, size_t cap) {
  size_t n = 0;
  const char* p = csv;
  while (*p) {
    const char* comma = strchr(p, ',');
    size_t len = comma ? (size_t)(comma - p) : strlen(p);
    if (len == 0 || len > 255 || n + 1 + len > cap) {
      return -1;
    }
    out[n++] = (unsigned char)len;
    memcpy(out + n, p, len);
    n += len;
    if (!comma) {
      break;
    }
    p = comma + 1;
  }
  return (int)n;
}

/* sl_bio_new : host → alpn → IO SslConn (client, connect-state, SNI + ALPN set) */
LEAN_EXPORT lean_object* sl_bio_new(b_lean_obj_arg host_obj, b_lean_obj_arg alpn_obj,
                                    lean_object* w) {
  (void)w;
  register_bio_class();
  sl_bio_conn* c = (sl_bio_conn*)calloc(1, sizeof(sl_bio_conn));
  if (!c) {
    return lean_io_result_mk_error(mkerr("oom"));
  }
  c->ctx = SSL_CTX_new(TLS_client_method());
  if (!c->ctx) {
    free(c);
    return lean_io_result_mk_error(mkerr("SSL_CTX_new"));
  }
  SSL_CTX_set_min_proto_version(c->ctx, TLS1_2_VERSION);
  SSL_CTX_set_verify(c->ctx, SSL_VERIFY_NONE, NULL); /* demo: mechanism test, not cert-verify */

  unsigned char wire[512];
  int wlen = build_alpn(lean_string_cstr(alpn_obj), wire, sizeof(wire));
  if (wlen > 0) {
    SSL_CTX_set_alpn_protos(c->ctx, wire, (unsigned)wlen);
  }

  c->ssl = SSL_new(c->ctx);
  c->rbio = BIO_new(BIO_s_mem());
  c->wbio = BIO_new(BIO_s_mem());
  if (!c->ssl || !c->rbio || !c->wbio) {
    bio_finalize(c);
    return lean_io_result_mk_error(mkerr("SSL_new/BIO"));
  }
  SSL_set_bio(c->ssl, c->rbio, c->wbio);
  SSL_set_connect_state(c->ssl);
  SSL_set_tlsext_host_name(c->ssl, lean_string_cstr(host_obj)); /* SNI */

  return lean_io_result_mk_ok(lean_alloc_external(g_bio_class, c));
}

static sl_bio_conn* the_conn(b_lean_obj_arg o) {
  return (sl_bio_conn*)lean_get_external_data(o);
}

/* sl_bio_feed : SslConn → ByteArray → IO Unit (received ciphertext → rbio) */
LEAN_EXPORT lean_object* sl_bio_feed(b_lean_obj_arg co, b_lean_obj_arg data, lean_object* w) {
  (void)w;
  size_t len = lean_sarray_size(data);
  if (len > 0) {
    BIO_write(the_conn(co)->rbio, lean_sarray_cptr(data), (int)len);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* sl_bio_pull : SslConn → IO ByteArray (ciphertext SSL wants to send, from wbio) */
LEAN_EXPORT lean_object* sl_bio_pull(b_lean_obj_arg co, lean_object* w) {
  (void)w;
  sl_bio_conn* c = the_conn(co);
  int pend = BIO_pending(c->wbio);
  if (pend < 0) {
    pend = 0;
  }
  lean_object* arr = lean_alloc_sarray(1, 0, (size_t)pend);
  if (pend > 0) {
    int n = BIO_read(c->wbio, lean_sarray_cptr(arr), pend);
    lean_sarray_set_size(arr, n > 0 ? (size_t)n : 0);
  }
  return lean_io_result_mk_ok(arr);
}

/* sl_bio_handshake : SslConn → IO UInt32 (0 done · 1 want-io · 2 error) */
LEAN_EXPORT lean_object* sl_bio_handshake(b_lean_obj_arg co, lean_object* w) {
  (void)w;
  SSL* ssl = the_conn(co)->ssl;
  int r = SSL_do_handshake(ssl);
  if (r == 1) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
  int e = SSL_get_error(ssl, r);
  uint32_t st = (e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE) ? 1 : 2;
  return lean_io_result_mk_ok(lean_box_uint32(st));
}

/* sl_bio_read : SslConn → maxlen → IO ByteArray (plaintext; empty if want-read)
 *
 * SSL_read into a stack scratch, then return an EXACT-sized ByteArray. The caller
 * drains (reads until 0), so this fires ≥2×/response — allocating the full `maxlen`
 * (64 KB) up front sent every call through Lean's big-object allocator to move ~100
 * bytes of plaintext. A 16 KB stack buffer (one TLS record max) + an n-sized small-
 * object alloc + memcpy keeps the recv path off the slow allocator entirely. */
LEAN_EXPORT lean_object* sl_bio_read(b_lean_obj_arg co, size_t maxlen, lean_object* w) {
  (void)w;
  unsigned char scratch[16384];
  size_t cap = maxlen < sizeof(scratch) ? maxlen : sizeof(scratch);
  int n = SSL_read(the_conn(co)->ssl, scratch, (int)cap);
  size_t sz = n > 0 ? (size_t)n : 0;
  lean_object* arr = lean_alloc_sarray(1, sz, sz);
  if (sz) {
    memcpy(lean_sarray_cptr(arr), scratch, sz);
  }
  return lean_io_result_mk_ok(arr);
}

/* sl_bio_write : SslConn → ByteArray → IO Unit (plaintext → SSL → wbio ciphertext) */
LEAN_EXPORT lean_object* sl_bio_write(b_lean_obj_arg co, b_lean_obj_arg data, lean_object* w) {
  (void)w;
  size_t len = lean_sarray_size(data);
  if (len > 0) {
    SSL_write(the_conn(co)->ssl, lean_sarray_cptr(data), (int)len);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* sl_bio_alpn : SslConn → IO String (the negotiated protocol) */
LEAN_EXPORT lean_object* sl_bio_alpn(b_lean_obj_arg co, lean_object* w) {
  (void)w;
  const unsigned char* proto = NULL;
  unsigned int len = 0;
  SSL_get0_alpn_selected(the_conn(co)->ssl, &proto, &len);
  char buf[64];
  if (len >= sizeof(buf)) {
    len = sizeof(buf) - 1;
  }
  if (proto && len) {
    memcpy(buf, proto, len);
  }
  buf[len] = 0;
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* ── blocking raw-socket helpers — drive the BIO core until io_uring replaces them ── */

/* sl_sock_connect : host → port → IO UInt32 (fd) */
LEAN_EXPORT lean_object* sl_sock_connect(b_lean_obj_arg host_obj, uint16_t port, lean_object* w) {
  (void)w;
  char ps[8];
  snprintf(ps, sizeof(ps), "%u", port);
  struct addrinfo hints;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  struct addrinfo* res = NULL;
  if (getaddrinfo(lean_string_cstr(host_obj), ps, &hints, &res) != 0 || !res) {
    return lean_io_result_mk_error(mkerr("getaddrinfo"));
  }
  int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
  if (fd < 0) {
    freeaddrinfo(res);
    return lean_io_result_mk_error(mkerr("socket"));
  }
  if (connect(fd, res->ai_addr, res->ai_addrlen) != 0) {
    close(fd);
    freeaddrinfo(res);
    return lean_io_result_mk_error(mkerr("connect"));
  }
  freeaddrinfo(res);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* sl_sock_send : fd → ByteArray → IO UInt32 (bytes written) */
LEAN_EXPORT lean_object* sl_sock_send(uint32_t fd, b_lean_obj_arg data, lean_object* w) {
  (void)w;
  size_t len = lean_sarray_size(data);
  const uint8_t* buf = lean_sarray_cptr(data);
  size_t total = 0;
  while (total < len) {
    ssize_t n = send((int)fd, buf + total, len - total, MSG_NOSIGNAL);
    if (n <= 0) {
      return lean_io_result_mk_error(mkerr("send"));
    }
    total += (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)total));
}

/* sl_sock_recv : fd → maxlen → IO ByteArray (0-length on EOF) */
LEAN_EXPORT lean_object* sl_sock_recv(uint32_t fd, size_t maxlen, lean_object* w) {
  (void)w;
  lean_object* arr = lean_alloc_sarray(1, 0, maxlen);
  ssize_t n = recv((int)fd, lean_sarray_cptr(arr), maxlen, 0);
  lean_sarray_set_size(arr, n > 0 ? (size_t)n : 0);
  return lean_io_result_mk_ok(arr);
}

/* sl_sock_close : fd → IO Unit */
LEAN_EXPORT lean_object* sl_sock_close(uint32_t fd, lean_object* w) {
  (void)w;
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}
