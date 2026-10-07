/*
 * straylight_h3.c — Lean @[extern] bridge: a synchronous HTTP/3 GET over QUIC.
 *
 *   ngtcp2 (QUIC transport)  +  nghttp3 (HTTP/3)  +  GnuTLS (TLS 1.3 / QUIC crypto)
 *
 * The whole fetch is ONE blocking call from Lean's perspective:
 *
 *   straylight_h3_get : host → port → path → caFile → IO (Except String H3Response)
 *
 * Internally it owns the UDP socket, the ngtcp2 connection, the GnuTLS session,
 * the nghttp3 H3 connection, and the poll loop (send → recv → expiry timers) until
 * the response stream ends or an error/timeout occurs. This mirrors the TLS bridge's
 * shape (Lean drives, the library transports) — the verified H3/QPACK *framing* lives
 * in Continuity.Codec.Wire.Http.Http3; this is the imperative transport shell.
 *
 * Crypto callbacks (encrypt/decrypt/hp_mask/client_initial/recv_crypto_data/key
 * update) come from libngtcp2_crypto_gnutls; we supply the rest (recv_stream_data,
 * acked_stream_data_offset, get_new_connection_id, rand, handshake_completed,
 * extend_max_local_streams_bidi).
 *
 * Result is returned to Lean as a small constructor:  H3Response := { status, body }.
 *
 * Link (static or dynamic):
 *   ... -lngtcp2 -lngtcp2_crypto_gnutls -lnghttp3 -lgnutls
 */
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <gnutls/crypto.h>
#include <gnutls/gnutls.h>
#include <lean/lean.h>
#include <netdb.h>
#include <netinet/in.h>
#include <nghttp3/nghttp3.h>
#include <ngtcp2/ngtcp2.h>
#include <ngtcp2/ngtcp2_crypto.h>
#include <ngtcp2/ngtcp2_crypto_gnutls.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>


/* ─────────────────────────── helpers ─────────────────────────── */

static uint64_t timestamp_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * NGTCP2_SECONDS + (uint64_t)t.tv_nsec;
}

/* Growable byte buffer for the response body. */
typedef struct {
  uint8_t* p;
  size_t len, cap;
} buf_t;
static void buf_init(buf_t* b) {
  b->p = NULL;
  b->len = 0;
  b->cap = 0;
}
static void buf_append(buf_t* b, const uint8_t* d, size_t n) {
  if (b->len + n > b->cap) {
    size_t nc = b->cap ? b->cap * 2 : 4096;
    while (nc < b->len + n) {
      nc *= 2;
    }
    b->p = realloc(b->p, nc);
    b->cap = nc;
  }
  memcpy(b->p + b->len, d, n);
  b->len += n;
}
static void buf_free(buf_t* b) {
  free(b->p);
  b->p = NULL;
  b->len = b->cap = 0;
}

/* The whole client state for one fetch. */
typedef struct {
  int fd; /* UDP socket */
  ngtcp2_conn* conn;
  gnutls_session_t session;
  gnutls_certificate_credentials_t cred;
  nghttp3_conn* h3;
  ngtcp2_crypto_conn_ref conn_ref; /* GnuTLS → ngtcp2 conn linkage */
  int64_t stream_id;               /* request stream */

  struct sockaddr_storage local_sa, remote_sa;
  socklen_t local_salen, remote_salen;

  /* outcome */
  int status;          /* HTTP/3 :status */
  long content_length; /* from content-length header, -1 if absent */
  buf_t body;
  int done; /* response stream ended */
  int failed;
  char err[256];
} h3_client;

static void set_err(h3_client* c, const char* fmt, const char* detail) {
  snprintf(c->err, sizeof(c->err), "%s%s%s", fmt, detail ? ": " : "", detail ? detail : "");
  c->failed = 1;
}

/* ─────────────────────── ngtcp2 callbacks ─────────────────────── */

static void rand_cb(uint8_t* dest, size_t destlen, const ngtcp2_rand_ctx* rand_ctx) {
  (void)rand_ctx;
  gnutls_rnd(GNUTLS_RND_RANDOM, dest, destlen);
}

static int get_new_connection_id_cb(ngtcp2_conn* conn, ngtcp2_cid* cid, uint8_t* token,
                                    size_t cidlen, void* user) {
  (void)conn;
  (void)user;
  if (gnutls_rnd(GNUTLS_RND_RANDOM, cid->data, cidlen) != 0) {
    return NGTCP2_ERR_CALLBACK_FAILURE;
  }
  cid->datalen = cidlen;
  if (gnutls_rnd(GNUTLS_RND_RANDOM, token, NGTCP2_STATELESS_RESET_TOKENLEN) != 0) {
    return NGTCP2_ERR_CALLBACK_FAILURE;
  }
  return 0;
}

/* nghttp3 is fed by the QUIC stream-data / acked / stream-close callbacks. */
static int recv_stream_data_cb(ngtcp2_conn* conn, uint32_t flags, int64_t stream_id,
                               uint64_t offset, const uint8_t* data, size_t datalen, void* user,
                               void* stream_user) {
  (void)offset;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  int fin = (flags & NGTCP2_STREAM_DATA_FLAG_FIN) != 0;
  if (!c->h3) {
    return 0;
  }
  nghttp3_ssize n = nghttp3_conn_read_stream(c->h3, stream_id, data, datalen, fin);
  if (n < 0) {
    set_err(c, "nghttp3_conn_read_stream", nghttp3_strerror((int)n));
    return NGTCP2_ERR_CALLBACK_FAILURE;
  }
  ngtcp2_conn_extend_max_stream_offset(conn, stream_id, datalen);
  ngtcp2_conn_extend_max_offset(conn, datalen);
  return 0;
}

static int acked_stream_data_offset_cb(ngtcp2_conn* conn, int64_t stream_id, uint64_t offset,
                                       uint64_t datalen, void* user, void* stream_user) {
  (void)conn;
  (void)offset;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  if (c->h3) {
    int rv = nghttp3_conn_add_ack_offset(c->h3, stream_id, datalen);
    if (rv != 0) {
      return NGTCP2_ERR_CALLBACK_FAILURE;
    }
  }
  return 0;
}

static int stream_close_cb(ngtcp2_conn* conn, uint32_t flags, int64_t stream_id,
                           uint64_t app_error_code, void* user, void* stream_user) {
  (void)conn;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  if (!(flags & NGTCP2_STREAM_CLOSE_FLAG_APP_ERROR_CODE_SET)) {
    app_error_code = NGHTTP3_H3_NO_ERROR;
  }
  if (c->h3) {
    int rv = nghttp3_conn_close_stream(c->h3, stream_id, app_error_code);
    if (rv != 0 && rv != NGHTTP3_ERR_STREAM_NOT_FOUND) {
      return NGTCP2_ERR_CALLBACK_FAILURE;
    }
  }
  return 0;
}

static int stream_reset_cb(ngtcp2_conn* conn, int64_t stream_id, uint64_t final_size,
                           uint64_t app_error_code, void* user, void* stream_user) {
  (void)conn;
  (void)final_size;
  (void)app_error_code;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  if (c->h3) {
    nghttp3_conn_shutdown_stream_read(c->h3, stream_id);
  }
  return 0;
}

static int extend_max_local_streams_bidi_cb(ngtcp2_conn* conn, uint64_t max_streams, void* user) {
  (void)conn;
  (void)max_streams;
  (void)user;
  return 0; /* we open our single request stream eagerly below */
}

static int handshake_completed_cb(ngtcp2_conn* conn, void* user) {
  (void)conn;
  (void)user;
  return 0;
}

/* ─────────────────────── nghttp3 callbacks ─────────────────────── */

static int h3_recv_data_cb(nghttp3_conn* h3, int64_t stream_id, const uint8_t* data, size_t datalen,
                           void* user, void* stream_user) {
  (void)h3;
  (void)stream_id;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  buf_append(&c->body, data, datalen);
  if (c->content_length >= 0 && (long)c->body.len >= c->content_length) {
    c->done = 1;
  }
  return 0;
}

static int h3_recv_header_cb(nghttp3_conn* h3, int64_t stream_id, int32_t token,
                             nghttp3_rcbuf* name, nghttp3_rcbuf* value, uint8_t flags, void* user,
                             void* stream_user) {
  (void)h3;
  (void)stream_id;
  (void)flags;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  nghttp3_vec nv = nghttp3_rcbuf_get_buf(name);
  nghttp3_vec vv = nghttp3_rcbuf_get_buf(value);
  if (nv.len == 7 && memcmp(nv.base, ":status", 7) == 0) {
    char tmp[8] = {0};
    size_t n = vv.len < 7 ? vv.len : 7;
    memcpy(tmp, vv.base, n);
    c->status = atoi(tmp);
  } else if (nv.len == 14 && memcmp(nv.base, "content-length", 14) == 0) {
    char tmp[24] = {0};
    size_t n = vv.len < 23 ? vv.len : 23;
    memcpy(tmp, vv.base, n);
    c->content_length = atol(tmp);
  }
  return 0;
}

static int h3_end_stream_cb(nghttp3_conn* h3, int64_t stream_id, void* user, void* stream_user) {
  (void)h3;
  (void)stream_id;
  (void)stream_user;
  h3_client* c = (h3_client*)user;
  c->done = 1;
  return 0;
}

static int h3_stop_sending_cb(nghttp3_conn* h3, int64_t stream_id, uint64_t app_error_code,
                              void* user, void* stream_user) {
  (void)h3;
  (void)stream_id;
  (void)app_error_code;
  (void)user;
  (void)stream_user;
  return 0;
}

static int h3_reset_stream_cb(nghttp3_conn* h3, int64_t stream_id, uint64_t app_error_code,
                              void* user, void* stream_user) {
  (void)h3;
  (void)stream_id;
  (void)app_error_code;
  (void)user;
  (void)stream_user;
  return 0;
}

/* The crypto helper calls this to recover the ngtcp2_conn from the session. */
static ngtcp2_conn* get_conn_cb(ngtcp2_crypto_conn_ref* ref) {
  h3_client* c = (h3_client*)ref->user_data;
  return c->conn;
}

/* ───────────────────────── GnuTLS session ───────────────────────── */

static int setup_gnutls(h3_client* c, const char* host, const char* ca_file) {
  if (gnutls_certificate_allocate_credentials(&c->cred) != 0) {
    return -1;
  }
  if (!ca_file || !ca_file[0]) {
    ca_file = getenv("STRAYLIGHT_H3_CA");
  }
  if (ca_file && ca_file[0]) {
    if (gnutls_certificate_set_x509_trust_file(c->cred, ca_file, GNUTLS_X509_FMT_PEM) < 0) {
      return -1;
    }
  } else {
    if (gnutls_certificate_set_x509_system_trust(c->cred) < 0) {
      return -1;
    }
  }
  if (gnutls_init(&c->session, GNUTLS_CLIENT) != 0) {
    return -1;
  }
  if (ngtcp2_crypto_gnutls_configure_client_session(c->session) != 0) {
    return -1;
  }
  if (gnutls_priority_set_direct(
          c->session,
          "%DISABLE_TLS13_COMPAT_MODE:NORMAL:-VERS-ALL:+VERS-TLS1.3:-CIPHER-ALL:"
          "+AES-128-GCM:+AES-256-GCM:+CHACHA20-POLY1305:+AES-128-CCM:"
          "-GROUP-ALL:+GROUP-SECP256R1:+GROUP-X25519:+GROUP-SECP384R1:+GROUP-SECP521R1:"
          "%DISABLE_TLS13_COMPAT_MODE",
          NULL) != 0) {
    return -1;
  }
  gnutls_credentials_set(c->session, GNUTLS_CRD_CERTIFICATE, c->cred);

  /* ALPN: h3 */
  gnutls_datum_t alpn = {(unsigned char*)"h3", 2};
  gnutls_alpn_set_protocols(c->session, &alpn, 1, GNUTLS_ALPN_MANDATORY);

  /* SNI + hostname verification */
  gnutls_server_name_set(c->session, GNUTLS_NAME_DNS, host, strlen(host));
  gnutls_session_set_verify_cert(c->session, host, 0);
  return 0;
}

/* ───────────────────────── UDP send/recv ───────────────────────── */

static int write_to_socket(h3_client* c) {
  uint8_t buf[1500];
  ngtcp2_path_storage ps;
  ngtcp2_path_storage_zero(&ps);
  ngtcp2_pkt_info pi;
  for (;;) {
    ngtcp2_ssize n =
        ngtcp2_conn_write_stream(c->conn, &ps.path, &pi, buf, sizeof(buf), NULL,
                                 NGTCP2_WRITE_STREAM_FLAG_NONE, -1, NULL, 0, timestamp_ns());
    if (n < 0) {
      if (n == NGTCP2_ERR_WRITE_MORE) {
        continue;
      }
      set_err(c, "ngtcp2_conn_write_stream", ngtcp2_strerror((int)n));
      return -1;
    }
    if (n == 0) {
      return 0;
    }
    ssize_t s = sendto(c->fd, buf, (size_t)n, 0, (struct sockaddr*)&c->remote_sa, c->remote_salen);
    if (s < 0) {
      set_err(c, "sendto", strerror(errno));
      return -1;
    }
  }
}

/* Drive nghttp3 → ngtcp2: pump any pending H3 stream data into QUIC packets. */
static int write_streams(h3_client* c) {
  uint8_t buf[1500];
  ngtcp2_path_storage ps;
  ngtcp2_path_storage_zero(&ps);
  ngtcp2_pkt_info pi;
  for (;;) {
    int64_t sid = -1;
    nghttp3_vec vec[16];
    nghttp3_ssize sveccnt = 0;
    int fin = 0;
    if (c->h3) {
      sveccnt = nghttp3_conn_writev_stream(c->h3, &sid, &fin, vec, 16);
      if (sveccnt < 0) {
        set_err(c, "nghttp3_conn_writev_stream", nghttp3_strerror((int)sveccnt));
        return -1;
      }
    }
    ngtcp2_ssize ndata;
    uint32_t flags = NGTCP2_WRITE_STREAM_FLAG_MORE | (fin ? NGTCP2_WRITE_STREAM_FLAG_FIN : 0);
    ngtcp2_ssize n =
        ngtcp2_conn_writev_stream(c->conn, &ps.path, &pi, buf, sizeof(buf), &ndata, flags, sid,
                                  (const ngtcp2_vec*)vec, (size_t)sveccnt, timestamp_ns());
    if (n < 0) {
      if (n == NGTCP2_ERR_WRITE_MORE) {
        if (ndata > 0) {
          nghttp3_conn_add_write_offset(c->h3, sid, (size_t)ndata);
        }
        continue;
      }
      set_err(c, "ngtcp2_conn_writev_stream", ngtcp2_strerror((int)n));
      return -1;
    }
    if (ndata > 0) {
      nghttp3_conn_add_write_offset(c->h3, sid, (size_t)ndata);
    }
    if (n == 0) {
      return 0;
    }
    ssize_t s = sendto(c->fd, buf, (size_t)n, 0, (struct sockaddr*)&c->remote_sa, c->remote_salen);
    if (s < 0) {
      set_err(c, "sendto", strerror(errno));
      return -1;
    }
  }
}

static int read_from_socket(h3_client* c) {
  uint8_t buf[65536];
  struct sockaddr_storage from;
  socklen_t fromlen = sizeof(from);
  for (;;) {
    ssize_t n = recvfrom(c->fd, buf, sizeof(buf), 0, (struct sockaddr*)&from, &fromlen);
    if (n < 0) {
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        return 0;
      }
      set_err(c, "recvfrom", strerror(errno));
      return -1;
    }
    ngtcp2_path path = {
        {(struct sockaddr*)&c->local_sa, c->local_salen}, {(struct sockaddr*)&from, fromlen}, NULL};
    ngtcp2_pkt_info pi = {0};
    int rv = ngtcp2_conn_read_pkt(c->conn, &path, &pi, buf, (size_t)n, timestamp_ns());
    if (rv != 0) {
      set_err(c, "ngtcp2_conn_read_pkt", ngtcp2_strerror(rv));
      return -1;
    }
  }
}

/* ─────────────────────── the fetch ─────────────────────── */

static int h3_setup_streams(h3_client* c) {
  /* control + qpack streams, then the request stream */
  int64_t ctrl_id, qenc_id, qdec_id;
  if (ngtcp2_conn_open_uni_stream(c->conn, &ctrl_id, NULL) != 0) {
    return -1;
  }
  if (ngtcp2_conn_open_uni_stream(c->conn, &qenc_id, NULL) != 0) {
    return -1;
  }
  if (ngtcp2_conn_open_uni_stream(c->conn, &qdec_id, NULL) != 0) {
    return -1;
  }
  if (nghttp3_conn_bind_control_stream(c->h3, ctrl_id) != 0) {
    return -1;
  }
  if (nghttp3_conn_bind_qpack_streams(c->h3, qenc_id, qdec_id) != 0) {
    return -1;
  }
  return 0;
}

/* Returns 0 on success (status+body filled), -1 on failure (err filled). */
static int do_fetch(h3_client* c, const char* host, const char* port, const char* path) {
  /* ── resolve + UDP socket ── */
  struct addrinfo hints = {0}, *res = NULL;
  hints.ai_family = AF_INET; /* sandbox: IPv4 only */
  hints.ai_socktype = SOCK_DGRAM;
  if (getaddrinfo(host, port, &hints, &res) != 0 || !res) {
    set_err(c, "getaddrinfo", host);
    return -1;
  }
  c->fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
  if (c->fd < 0) {
    set_err(c, "socket", strerror(errno));
    freeaddrinfo(res);
    return -1;
  }
  memcpy(&c->remote_sa, res->ai_addr, res->ai_addrlen);
  c->remote_salen = res->ai_addrlen;
  if (connect(c->fd, res->ai_addr, res->ai_addrlen) != 0) {
    set_err(c, "connect", strerror(errno));
    freeaddrinfo(res);
    return -1;
  }
  freeaddrinfo(res);
  c->local_salen = sizeof(c->local_sa);
  getsockname(c->fd, (struct sockaddr*)&c->local_sa, &c->local_salen);
  /* non-blocking */
  fcntl(c->fd, F_SETFL, O_NONBLOCK);

  /* ── GnuTLS ── */
  if (setup_gnutls(c, host, NULL) != 0) {
    set_err(c, "gnutls setup", NULL);
    return -1;
  }

  /* ── ngtcp2 conn ── */
  ngtcp2_cid dcid, scid;
  uint8_t cidbuf[NGTCP2_MAX_CIDLEN];
  gnutls_rnd(GNUTLS_RND_RANDOM, cidbuf, 16);
  dcid.datalen = 16;
  memcpy(dcid.data, cidbuf, 16);
  gnutls_rnd(GNUTLS_RND_RANDOM, cidbuf, 16);
  scid.datalen = 16;
  memcpy(scid.data, cidbuf, 16);

  ngtcp2_callbacks cbs = {0};
  cbs.client_initial = ngtcp2_crypto_client_initial_cb;
  cbs.recv_crypto_data = ngtcp2_crypto_recv_crypto_data_cb;
  cbs.encrypt = ngtcp2_crypto_encrypt_cb;
  cbs.decrypt = ngtcp2_crypto_decrypt_cb;
  cbs.hp_mask = ngtcp2_crypto_hp_mask_cb;
  cbs.recv_retry = ngtcp2_crypto_recv_retry_cb;
  cbs.update_key = ngtcp2_crypto_update_key_cb;
  cbs.delete_crypto_aead_ctx = ngtcp2_crypto_delete_crypto_aead_ctx_cb;
  cbs.delete_crypto_cipher_ctx = ngtcp2_crypto_delete_crypto_cipher_ctx_cb;
  cbs.get_path_challenge_data = ngtcp2_crypto_get_path_challenge_data_cb;
  cbs.version_negotiation = ngtcp2_crypto_version_negotiation_cb;
  cbs.handshake_completed = handshake_completed_cb;
  cbs.recv_stream_data = recv_stream_data_cb;
  cbs.acked_stream_data_offset = acked_stream_data_offset_cb;
  cbs.stream_close = stream_close_cb;
  cbs.stream_reset = stream_reset_cb;
  cbs.extend_max_local_streams_bidi = extend_max_local_streams_bidi_cb;
  cbs.rand = rand_cb;
  cbs.get_new_connection_id = get_new_connection_id_cb;

  ngtcp2_settings settings;
  ngtcp2_settings_default(&settings);
  settings.initial_ts = timestamp_ns();

  ngtcp2_transport_params params;
  ngtcp2_transport_params_default(&params);
  params.initial_max_streams_uni = 100;
  params.initial_max_stream_data_bidi_local = 256 * 1024;
  params.initial_max_data = 1024 * 1024;

  ngtcp2_path conn_path = {{(struct sockaddr*)&c->local_sa, c->local_salen},
                           {(struct sockaddr*)&c->remote_sa, c->remote_salen},
                           NULL};

  int rv = ngtcp2_conn_client_new(&c->conn, &dcid, &scid, &conn_path, NGTCP2_PROTO_VER_V1, &cbs,
                                  &settings, &params, NULL, c);
  if (rv != 0) {
    set_err(c, "ngtcp2_conn_client_new", ngtcp2_strerror(rv));
    return -1;
  }

  ngtcp2_conn_set_tls_native_handle(c->conn, c->session);
  /* The crypto helper needs a conn_ref (with get_conn) on the session,
   * NOT the raw conn pointer. */
  c->conn_ref.get_conn = get_conn_cb;
  c->conn_ref.user_data = c;
  gnutls_session_set_ptr(c->session, &c->conn_ref);

  /* ── poll loop ── */
  uint64_t deadline = timestamp_ns() + 10 * NGTCP2_SECONDS;
  int req_sent = 0;
  if (write_to_socket(c) != 0) {
    return -1;
  }

  while (!c->done && !c->failed) {
    if (timestamp_ns() > deadline) {
      set_err(c, "timeout", NULL);
      return -1;
    }

    ngtcp2_tstamp expiry = ngtcp2_conn_get_expiry(c->conn);
    int timeout_ms = 100;
    if (expiry != UINT64_MAX) {
      uint64_t now = timestamp_ns();
      timeout_ms = expiry <= now ? 0 : (int)((expiry - now) / NGTCP2_MILLISECONDS) + 1;
      if (timeout_ms > 100) {
        timeout_ms = 100;
      }
    }

    struct pollfd pfd = {c->fd, POLLIN, 0};
    int pr = poll(&pfd, 1, timeout_ms);
    if (pr < 0) {
      set_err(c, "poll", strerror(errno));
      return -1;
    }
    if (pr > 0 && (pfd.revents & POLLIN)) {
      if (read_from_socket(c) != 0) {
        return -1;
      }
    }
    if (c->done) {
      break;
    }

    /* handle timers */
    rv = ngtcp2_conn_handle_expiry(c->conn, timestamp_ns());
    if (rv != 0) {
      set_err(c, "handle_expiry", ngtcp2_strerror(rv));
      return -1;
    }

    /* once handshake completes, set up H3 and send the request once */
    if (!req_sent && ngtcp2_conn_get_handshake_completed(c->conn)) {
      nghttp3_callbacks h3cbs = {0};
      h3cbs.recv_data = h3_recv_data_cb;
      h3cbs.recv_header = h3_recv_header_cb;
      h3cbs.end_stream = h3_end_stream_cb;
      h3cbs.stop_sending = h3_stop_sending_cb;
      h3cbs.reset_stream = h3_reset_stream_cb;
      nghttp3_settings h3settings;
      nghttp3_settings_default(&h3settings);
      if (nghttp3_conn_client_new(&c->h3, &h3cbs, &h3settings, NULL, c) != 0) {
        set_err(c, "nghttp3_conn_client_new", NULL);
        return -1;
      }
      if (h3_setup_streams(c) != 0) {
        set_err(c, "h3 setup streams", NULL);
        return -1;
      }

      if (ngtcp2_conn_open_bidi_stream(c->conn, &c->stream_id, NULL) != 0) {
        set_err(c, "open_bidi_stream", NULL);
        return -1;
      }
      nghttp3_nv nva[] = {
          {(uint8_t*)":method", (uint8_t*)"GET", 7, 3, NGHTTP3_NV_FLAG_NONE},
          {(uint8_t*)":scheme", (uint8_t*)"https", 7, 5, NGHTTP3_NV_FLAG_NONE},
          {(uint8_t*)":authority", (uint8_t*)host, 10, strlen(host), NGHTTP3_NV_FLAG_NONE},
          {(uint8_t*)":path", (uint8_t*)path, 5, strlen(path), NGHTTP3_NV_FLAG_NONE},
      };
      if (nghttp3_conn_submit_request(c->h3, c->stream_id, nva, 4, NULL, NULL) != 0) {
        set_err(c, "submit_request", NULL);
        return -1;
      }
      req_sent = 1;
    }

    if (write_streams(c) != 0) {
      return -1;
    }
    if (write_to_socket(c) != 0) {
      return -1;
    }
  }
  return c->failed ? -1 : 0;
}

/* ─────────────────────── Lean entry point ─────────────────────── */

static int g_gnutls_init = 0;

/* H3Response is a Lean structure { status : UInt32, body : ByteArray }.
 * We build it as a constructor with 2 fields. */
static lean_object* mk_response(int status, buf_t* body) {
  lean_object* arr = lean_alloc_sarray(1, body->len, body->len);
  if (body->len) {
    memcpy(lean_sarray_cptr(arr), body->p, body->len);
  }
  /* Make H3Response { status : Nat, body : ByteArray } — both boxed objects,
   * so the layout is unambiguous (no scalar-after-object packing to reason about).
   * status as Nat is boxed via lean_usize_to_nat. */
  lean_object* r = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(r, 0, lean_usize_to_nat((size_t)status)); /* status : Nat */
  lean_ctor_set(r, 1, arr);                               /* body : ByteArray */
  return r;
}

static lean_object* mk_error(const char* msg) {
  return lean_mk_io_user_error(lean_mk_string(msg));
}

/* straylight_h3_get : host → port → path → IO (Except String H3Response) */
LEAN_EXPORT lean_object* straylight_h3_get(b_lean_obj_arg host_obj, uint16_t port,
                                           b_lean_obj_arg path_obj, lean_object* w) {
  (void)w;
  if (!g_gnutls_init) {
    gnutls_global_init();
    g_gnutls_init = 1;
  }

  const char* host = lean_string_cstr(host_obj);
  const char* path = lean_string_cstr(path_obj);
  char port_str[16];
  snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);

  h3_client c;
  memset(&c, 0, sizeof(c));
  c.fd = -1;
  c.stream_id = -1;
  c.status = 0;
  c.content_length = -1;
  buf_init(&c.body);

  int rv = do_fetch(&c, host, port_str, path);

  lean_object* result;
  if (rv == 0) {
    result = lean_io_result_mk_ok(mk_response(c.status, &c.body));
  } else {
    result = lean_io_result_mk_error(mk_error(c.err[0] ? c.err : "h3 fetch failed"));
  }

  /* cleanup */
  if (c.h3) {
    nghttp3_conn_del(c.h3);
  }
  if (c.conn) {
    ngtcp2_conn_del(c.conn);
  }
  if (c.session) {
    gnutls_deinit(c.session);
  }
  if (c.cred) {
    gnutls_certificate_free_credentials(c.cred);
  }
  if (c.fd >= 0) {
    close(c.fd);
  }
  buf_free(&c.body);

  return result;
}

/* straylight_h3_get_ca : host → port → path → caFile → IO (Except String H3Response) */
LEAN_EXPORT lean_object* straylight_h3_get_ca(b_lean_obj_arg host_obj, uint16_t port,
                                              b_lean_obj_arg path_obj, b_lean_obj_arg ca_obj,
                                              lean_object* w) {
  (void)w;
  if (!g_gnutls_init) {
    gnutls_global_init();
    g_gnutls_init = 1;
  }

  const char* host = lean_string_cstr(host_obj);
  const char* path = lean_string_cstr(path_obj);
  const char* ca = lean_string_cstr(ca_obj);
  char port_str[16];
  snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);

  h3_client c;
  memset(&c, 0, sizeof(c));
  c.fd = -1;
  c.stream_id = -1;
  c.status = 0;
  c.content_length = -1;
  buf_init(&c.body);

  /* do_fetch hardcodes system trust; for explicit CA we set it before calling
   * by stashing on a thread-local. Simpler: replicate do_fetch's gnutls setup
   * via setup_gnutls with ca. We re-run do_fetch but pre-seed the CA by a small
   * override: set an env the setup reads. */
  setenv("STRAYLIGHT_H3_CA", ca, 1);
  int rv = do_fetch(&c, host, port_str, path);
  unsetenv("STRAYLIGHT_H3_CA");
  lean_object* result;
  if (rv == 0) {
    result = lean_io_result_mk_ok(mk_response(c.status, &c.body));
  } else {
    result = lean_io_result_mk_error(mk_error(c.err[0] ? c.err : "h3 fetch failed"));
  }
  if (c.h3) {
    nghttp3_conn_del(c.h3);
  }
  if (c.conn) {
    ngtcp2_conn_del(c.conn);
  }
  if (c.session) {
    gnutls_deinit(c.session);
  }
  if (c.cred) {
    gnutls_certificate_free_credentials(c.cred);
  }
  if (c.fd >= 0) {
    close(c.fd);
  }
  buf_free(&c.body);
  return result;
}
