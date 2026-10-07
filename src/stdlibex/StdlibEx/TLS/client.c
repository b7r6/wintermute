/*
 * StdlibEx // TLS // Client — Lean @[extern] bridge to LibreSSL's libtls (statically linked)
 *
 * The high-level libtls API (not raw libssl): handshake, read, write, close.
 * Verified record-layer invariants in Continuity.Codec.Wire.TlsRecord and
 * Continuity.Machine.Codegen.Tls describe the framing this wraps; the crypto
 * core (AEAD, key schedule, X.509) is LibreSSL's, linked static for a
 * self-contained `aleph` binary with no runtime OpenSSL/LibreSSL .so dependency.
 *
 * Surface (matches StdlibEx/Tls.lean):
 *   tls_client_connect : host → port → alpn → Except String TlsConn
 *   tls_conn_write     : TlsConn → ByteArray → Except String Nat
 *   tls_conn_read      : TlsConn → Nat → Except String ByteArray
 *   tls_conn_close     : TlsConn → Unit
 *
 * Link (static):
 *   gcc ... straylight_tls.o \
 *     libtls.a libssl.a libcrypto.a libcompat.a -lpthread
 */
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <tls.h>

/* ── one-time library init (tls_init is idempotent + thread-safe in LibreSSL) ── */
static int ensure_init(void) {
  static int done = 0;
  if (!done) {
    if (tls_init() != 0) {
      return -1;
    }
    done = 1;
  }
  return 0;
}

/* ── TlsConn is an opaque Lean external object wrapping `struct tls*` ──
 * We register a finalizer so a dropped TlsConn closes + frees the context,
 * matching the linear-resource discipline used for rings/fds elsewhere. */
static lean_external_class* g_tls_class = NULL;

static void tls_finalize(void* p) {
  struct tls* ctx = (struct tls*)p;
  if (ctx) {
    tls_close(ctx); /* best-effort; ignore error on drop */
    tls_free(ctx);
  }
}
static void tls_foreach(void* p, b_lean_obj_arg fn) {
  (void)p;
  (void)fn;
}

static void register_class(void) {
  if (!g_tls_class) {
    g_tls_class = lean_register_external_class(tls_finalize, tls_foreach);
  }
}

/* helper: build `Except.error "msg"` */
static lean_object* mk_error(const char* msg) {
  return lean_mk_io_user_error(lean_mk_string(msg));
}

/* ── tls_client_connect : host port alpn → IO (Except String TlsConn) ──
 * Returns the TLS context post-handshake, or an error string. */
LEAN_EXPORT lean_object* stdlibex_tls_connect(b_lean_obj_arg host_obj, uint16_t port,
                                              b_lean_obj_arg alpn_obj, lean_object* w) {
  (void)w;
  register_class();
  if (ensure_init() != 0) {
    return lean_io_result_mk_error(mk_error("tls_init failed"));
  }

  const char* host = lean_string_cstr(host_obj);
  const char* alpn = lean_string_cstr(alpn_obj); /* "" → no ALPN */

  char port_str[16];
  snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);

  struct tls_config* cfg = tls_config_new();
  if (!cfg) {
    return lean_io_result_mk_error(mk_error("tls_config_new failed"));
  }

  if (alpn[0] != '\0') {
    tls_config_set_alpn(cfg, alpn);
  }

  /* CA bundle. libtls verifies cert + name + time by DEFAULT, but only if it
   * can load a CA bundle. Its compiled-in default (tls_default_ca_cert_file())
   * is often wrong on Linux (e.g. /usr/lib/ssl/cert.pem vs the distro's real
   * /etc/ssl/certs/ca-certificates.crt). If no CA loads, verification fails
   * OPEN on some builds — a silent security hole. So we set it explicitly,
   * trying the common locations, and HARD-FAIL if none load. */
  {
    const char* ca_candidates[] = {tls_default_ca_cert_file(),           /* build default first */
                                   "/etc/ssl/certs/ca-certificates.crt", /* Debian/Ubuntu */
                                   "/etc/pki/tls/certs/ca-bundle.crt",   /* RHEL/Fedora */
                                   "/etc/ssl/cert.pem",                  /* Alpine/BSD/macOS */
                                   "/usr/local/etc/ssl/cert.pem",        /* LibreSSL prefix */
                                   NULL};
    int ca_ok = 0;
    for (int i = 0; ca_candidates[i]; i++) {
      const char* p = ca_candidates[i];
      if (!p) {
        continue;
      }
      FILE* f = fopen(p, "r");
      if (f) {
        fclose(f);
        if (tls_config_set_ca_file(cfg, p) == 0) {
          ca_ok = 1;
          break;
        }
      }
    }
    /* Allow an explicit override via env for unusual layouts. */
    const char* env_ca = getenv("SSL_CERT_FILE");
    if (env_ca && tls_config_set_ca_file(cfg, env_ca) == 0) {
      ca_ok = 1;
    }

    if (!ca_ok) {
      tls_config_free(cfg);
      return lean_io_result_mk_error(
          mk_error("no CA bundle found — refusing to connect without cert verification "
                   "(set SSL_CERT_FILE)"));
    }
  }

  struct tls* ctx = tls_client();
  if (!ctx) {
    tls_config_free(cfg);
    return lean_io_result_mk_error(mk_error("tls_client failed"));
  }

  if (tls_configure(ctx, cfg) != 0) {
    char buf[256];
    snprintf(buf, sizeof(buf), "tls_configure: %s", tls_error(ctx));
    tls_free(ctx);
    tls_config_free(cfg);
    return lean_io_result_mk_error(mk_error(buf));
  }
  tls_config_free(cfg); /* ctx holds its own ref after configure */

  if (tls_connect(ctx, host, port_str) != 0) {
    char buf[256];
    snprintf(buf, sizeof(buf), "tls_connect: %s", tls_error(ctx));
    tls_free(ctx);
    return lean_io_result_mk_error(mk_error(buf));
  }

  /* Force the handshake now so errors surface here, not on first read. */
  if (tls_handshake(ctx) != 0) {
    char buf[256];
    snprintf(buf, sizeof(buf), "tls_handshake: %s", tls_error(ctx));
    tls_close(ctx);
    tls_free(ctx);
    return lean_io_result_mk_error(mk_error(buf));
  }

  lean_object* conn = lean_alloc_external(g_tls_class, ctx);
  return lean_io_result_mk_ok(conn);
}

/* ── tls_conn_write : TlsConn ByteArray → IO (Except String Nat) ── */
LEAN_EXPORT lean_object* stdlibex_tls_write(b_lean_obj_arg conn_obj, b_lean_obj_arg data_obj,
                                            lean_object* w) {
  (void)w;
  struct tls* ctx = (struct tls*)lean_get_external_data(conn_obj);
  size_t len = lean_sarray_size(data_obj);
  const uint8_t* buf = lean_sarray_cptr(data_obj);

  size_t total = 0;
  while (total < len) {
    ssize_t n = tls_write(ctx, buf + total, len - total);
    if (n == TLS_WANT_POLLIN || n == TLS_WANT_POLLOUT) {
      continue;
    }
    if (n < 0) {
      char b[256];
      snprintf(b, sizeof(b), "tls_write: %s", tls_error(ctx));
      return lean_io_result_mk_error(mk_error(b));
    }
    total += (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box(total)); /* Nat fits in box for small */
}

/* ── tls_conn_read : TlsConn maxlen → IO (Except String ByteArray) ── */
LEAN_EXPORT lean_object* stdlibex_tls_read(b_lean_obj_arg conn_obj, size_t maxlen, lean_object* w) {
  (void)w;
  struct tls* ctx = (struct tls*)lean_get_external_data(conn_obj);

  lean_object* arr = lean_alloc_sarray(1, 0, maxlen);
  uint8_t* dst = lean_sarray_cptr(arr);

  ssize_t n;
  do {
    n = tls_read(ctx, dst, maxlen);
  } while (n == TLS_WANT_POLLIN || n == TLS_WANT_POLLOUT);

  if (n < 0) {
    const char* err = tls_error(ctx);
    /* Many real servers close the socket without a TLS close_notify. libtls
     * (over OpenSSL) surfaces that as "unexpected eof while reading". For a
     * read loop this is just end-of-stream, not a failure — return 0 bytes.
     * A truncation attack is the tradeoff, but for HTTP/1 with Content-Length
     * or chunked framing the caller detects truncation at the protocol layer. */
    if (err && strstr(err, "unexpected eof")) {
      lean_sarray_set_size(arr, 0);
      return lean_io_result_mk_ok(arr);
    }
    char b[256];
    snprintf(b, sizeof(b), "tls_read: %s", err);
    lean_dec_ref(arr);
    return lean_io_result_mk_error(mk_error(b));
  }
  lean_sarray_set_size(arr, (size_t)n);
  return lean_io_result_mk_ok(arr);
}

/* ── tls_conn_close : TlsConn → IO Unit ── */
LEAN_EXPORT lean_object* stdlibex_tls_close(b_lean_obj_arg conn_obj, lean_object* w) {
  (void)w;
  struct tls* ctx = (struct tls*)lean_get_external_data(conn_obj);
  if (ctx) {
    tls_close(ctx);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* ── tls_conn_alpn_selected : TlsConn → IO String ──
 * The ALPN protocol the peer SELECTED during the handshake (RFC 7301): e.g.
 * "h2" or "http/1.1", or "" if none was negotiated (empty offer, or the server
 * declined). Fixed after handshake. This IS the upstream's h2-vs-h1 dispatch. */
LEAN_EXPORT lean_object* stdlibex_tls_alpn_selected(b_lean_obj_arg conn_obj, lean_object* w) {
  (void)w;
  struct tls* ctx = (struct tls*)lean_get_external_data(conn_obj);
  const char* proto = tls_conn_alpn_selected(ctx);
  return lean_io_result_mk_ok(lean_mk_string(proto ? proto : ""));
}

/* ── tls_client_connect_ca : host port alpn ca_file → IO (Except String TlsConn) ──
 * Like connect, but uses an explicit CA file (e.g. a private/self-signed root).
 * Proves the verified path: trust THIS CA, reject everything else. */
LEAN_EXPORT lean_object* stdlibex_tls_connect_ca(b_lean_obj_arg host_obj, uint16_t port,
                                                 b_lean_obj_arg alpn_obj, b_lean_obj_arg ca_obj,
                                                 lean_object* w) {
  (void)w;
  register_class();
  if (ensure_init() != 0) {
    return lean_io_result_mk_error(mk_error("tls_init failed"));
  }

  const char* host = lean_string_cstr(host_obj);
  const char* alpn = lean_string_cstr(alpn_obj);
  const char* ca = lean_string_cstr(ca_obj);
  char port_str[16];
  snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);

  struct tls_config* cfg = tls_config_new();
  if (!cfg) {
    return lean_io_result_mk_error(mk_error("tls_config_new failed"));
  }
  if (alpn[0] != '\0') {
    tls_config_set_alpn(cfg, alpn);
  }

  if (tls_config_set_ca_file(cfg, ca) != 0) {
    char b[256];
    snprintf(b, sizeof(b), "set_ca_file: %s", tls_config_error(cfg));
    tls_config_free(cfg);
    return lean_io_result_mk_error(mk_error(b));
  }

  struct tls* ctx = tls_client();
  if (!ctx) {
    tls_config_free(cfg);
    return lean_io_result_mk_error(mk_error("tls_client failed"));
  }
  if (tls_configure(ctx, cfg) != 0) {
    char b[256];
    snprintf(b, sizeof(b), "tls_configure: %s", tls_error(ctx));
    tls_free(ctx);
    tls_config_free(cfg);
    return lean_io_result_mk_error(mk_error(b));
  }
  tls_config_free(cfg);
  if (tls_connect(ctx, host, port_str) != 0) {
    char b[256];
    snprintf(b, sizeof(b), "tls_connect: %s", tls_error(ctx));
    tls_free(ctx);
    return lean_io_result_mk_error(mk_error(b));
  }
  if (tls_handshake(ctx) != 0) {
    char b[256];
    snprintf(b, sizeof(b), "tls_handshake: %s", tls_error(ctx));
    tls_close(ctx);
    tls_free(ctx);
    return lean_io_result_mk_error(mk_error(b));
  }
  return lean_io_result_mk_ok(lean_alloc_external(g_tls_class, ctx));
}
