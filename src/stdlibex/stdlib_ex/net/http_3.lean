/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // STDLIBEX // NET // HTTP3
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A synchronous HTTP/3 GET over QUIC, bound to the reference transport stack:

        ngtcp2 (QUIC)  +  nghttp3 (HTTP/3)  +  GnuTLS (TLS 1.3 / QUIC crypto)

    The whole fetch — UDP socket, QUIC handshake, control + QPACK + request
    streams, the send/recv/expiry poll loop — runs inside one blocking C call,
    so Lean sees a simple synchronous API.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Net.Http3

/-- An HTTP/3 response: the `:status` pseudo-header and the body bytes. -/
structure Response where
  status : Nat
  body   : ByteArray

/-- `GET https://host:port/path` over HTTP/3, verifying the server cert against
    the system CA bundle (ALPN `h3`, hostname + time checked). Errors (DNS, QUIC
    handshake, cert validation, timeout) surface as `IO` exceptions. -/
@[extern "h3_get"]
opaque get (host : @& String) (port : UInt16) (path : @& String) : IO Response

/-- Like `get`, but trusting an explicit CA file (private / self-signed roots)
    instead of the system bundle. Verifies cert + name + time against THAT CA;
    rejects all others. -/
@[extern "h3_get_ca"]
opaque getCA (host : @& String) (port : UInt16) (path : @& String) (caFile : @& String) :
    IO Response

/-- Body as a UTF-8 string (lossy if the body isn't valid UTF-8). -/
def Response.text (response : Response) : String := String.fromUTF8! response.body

end StdlibEx.Net.Http3
