/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // LINUX // URING // CORE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    DEPRECATED: This module is superseded by StdlibEx.IOUring.

    Re-exports StdlibEx.IOUring for backward compatibility. New code should
    import StdlibEx.IOUring directly.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import stdlib_ex.io_uring.core

namespace StdlibEx.Linux.Uring

export StdlibEx.IOUring (RingHandle init cleanup batchNop statx openFile read close)
export StdlibEx.IOUring (cleanup_succeeds cleanup_idempotent batch_nop_bounded)

end StdlibEx.Linux.Uring
