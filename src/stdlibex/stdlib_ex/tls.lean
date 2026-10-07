/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // STDLIBEX // TLS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    TLS FFI — LibreSSL bindings for secure transport.

    Structure:
      · `StdlibEx.TLS.Client` — high-level libtls API (blocking, socket-based)
      · `StdlibEx.TLS.Bio`    — async TLS via memory BIOs (for io_uring)

    Both are linked STATICALLY (libtls.a + libssl.a + libcrypto.a). No runtime
    OpenSSL/LibreSSL .so dependency.

    The C shims live at `TLS/*.c`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import stdlib_ex.tls.client
import stdlib_ex.tls.bio
