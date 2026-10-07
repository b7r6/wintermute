/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // STDLIBEX // TLS // BIO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Async TLS via LibreSSL libssl over MEMORY BIOs.

    The record-layer crypto is decoupled from network I/O:
      · `feed` — push received ciphertext in
      · `pull` — get ciphertext to send out
      · `read`/`write` — plaintext I/O

    The SSL state machine advances purely on bytes moved through the BIOs, so ANY
    I/O source can drive it — blocking socket, io_uring, etc. Userspace AEAD, no
    new dependency (libssl/libcrypto already link).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.TLS.Bio

-- ══════════════════════════════════════════════════════════════════════════════
-- CONNECTION HANDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- An SSL connection over two memory BIOs (opaque; wraps `SSL*` + `SSL_CTX*`). -/
opaque SslConnPointed : NonemptyType

def SslConn : Type := SslConnPointed.type
instance : Nonempty SslConn := SslConnPointed.property

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — BIO-based TLS
-- ══════════════════════════════════════════════════════════════════════════════

/-- New client SSL over memory BIOs — SNI = `host`, ALPN offer = `alpn` (comma
    list, e.g. "h2,http/1.1"), connect-state. No socket yet: the caller pumps I/O. -/
@[extern "bio_new"]
opaque new (host : @& String) (alpn : @& String) : IO SslConn

/-- Feed received network ciphertext into the SSL input BIO. -/
@[extern "bio_feed"]
opaque feed (conn : @& SslConn) (ciphertext : @& ByteArray) : IO Unit

/-- Pull ciphertext the SSL wants to send (drains the output BIO; may be empty). -/
@[extern "bio_pull"]
opaque pull (conn : @& SslConn) : IO ByteArray

/-- Advance the handshake: `0` done · `1` want-I/O (feed/pull + retry) · `2` error. -/
@[extern "bio_handshake"]
opaque handshake (conn : @& SslConn) : IO UInt32

/-- Read decrypted plaintext (empty when the record layer wants more input). -/
@[extern "bio_read"]
opaque read (conn : @& SslConn) (maxlen : USize) : IO ByteArray

/-- Encrypt plaintext into the output BIO (then `pull` to get the ciphertext). -/
@[extern "bio_write"]
opaque write (conn : @& SslConn) (plaintext : @& ByteArray) : IO Unit

/-- The negotiated ALPN protocol (post-handshake). -/
@[extern "bio_alpn"]
opaque alpn (conn : @& SslConn) : IO String

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — blocking socket helpers (for testing, replaced by io_uring)
-- ══════════════════════════════════════════════════════════════════════════════

@[extern "sock_connect"]
opaque sockConnect (host : @& String) (port : UInt16) : IO UInt32

@[extern "sock_send"]
opaque sockSend (fd : UInt32) (data : @& ByteArray) : IO UInt32

@[extern "sock_recv"]
opaque sockRecv (fd : UInt32) (maxlen : USize) : IO ByteArray

@[extern "sock_close"]
opaque sockClose (fd : UInt32) : IO Unit

end StdlibEx.TLS.Bio
