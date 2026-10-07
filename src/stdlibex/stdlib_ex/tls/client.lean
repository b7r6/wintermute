/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // STDLIBEX // TLS // CLIENT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    High-level TLS client via LibreSSL's `libtls` API. Blocking, socket-based.

    Resource discipline: `Conn` is an opaque external object with a finalizer
    (`tls_close` + `tls_free`), so a dropped connection is always closed.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.TLS.Client

-- ══════════════════════════════════════════════════════════════════════════════
-- CONNECTION HANDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- An established TLS connection (opaque; wraps LibreSSL `struct tls*`). -/
opaque ConnPointed : NonemptyType

def Conn : Type := ConnPointed.type
instance : Nonempty Conn := ConnPointed.property

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI
-- ══════════════════════════════════════════════════════════════════════════════

/-- Connect to `host:port` over TLS, performing the handshake before returning.
    `alpn` is the ALPN protocol string (e.g. "h2", "http/1.1"); "" disables ALPN.
    Errors (DNS, handshake, cert validation) surface as `IO` exceptions. -/
@[extern "stdlibex_tls_connect"]
opaque connect (host : @& String) (port : UInt16) (alpn : @& String) : IO Conn

/-- Connect trusting an explicit CA file (e.g. a private/self-signed root). -/
@[extern "stdlibex_tls_connect_ca"]
opaque connectCA (host : @& String) (port : UInt16) (alpn : @& String) (caFile : @& String) : IO Conn

/-- Write the full buffer (loops over `tls_write`, handling WANT_POLL*). -/
@[extern "stdlibex_tls_write"]
opaque write (conn : @& Conn) (data : @& ByteArray) : IO Nat

/-- Read up to `maxlen` bytes (one `tls_read`, handling WANT_POLL*). -/
@[extern "stdlibex_tls_read"]
opaque read (conn : @& Conn) (maxlen : USize) : IO ByteArray

/-- Send close-notify. The finalizer also closes on drop, so this is optional
    but lets the peer see a clean shutdown. -/
@[extern "stdlibex_tls_close"]
opaque close (conn : @& Conn) : IO Unit

/-- The ALPN protocol the peer SELECTED during the handshake (RFC 7301). -/
@[extern "stdlibex_tls_alpn_selected"]
opaque alpnSelected (conn : @& Conn) : IO String

-- ══════════════════════════════════════════════════════════════════════════════
-- HIGH-LEVEL API
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bracket: connect, run, always close. -/
def withConn
    {resultType : Type}
    (host : String)
    (port : UInt16)
    (alpn : String)
    (action : Conn → IO resultType)
    : IO resultType := do
  let conn ← connect host port alpn
  try
    let result ← action conn
    close conn
    return result
  catch e =>
    close conn
    throw e

/-- Read until the peer closes (EOF = a zero-length read). -/
partial
def readAll (conn : Conn) (chunk : USize := 16384) : IO ByteArray := do
  let rec loop (buffer : ByteArray) : IO ByteArray := do
    let bs ← read conn chunk
    if bs.size == 0 then
      return buffer
    else loop (buffer ++ bs)
  loop ByteArray.empty

end StdlibEx.TLS.Client
