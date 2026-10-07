/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // LINUX // URING // LOOP
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    DEPRECATED: This module is superseded by StdlibEx.IOUring.Loop.

    Re-exports StdlibEx.IOUring.Loop for backward compatibility. New code should
    import StdlibEx.IOUring.Loop directly.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import stdlib_ex.io_uring.loop

namespace StdlibEx.Linux.Uring.Loop

export StdlibEx.IOUring.Loop (OpKind Event LoopHandle)
export StdlibEx.IOUring.Loop (cqeFBuffer cqeFMore cqeBufferShift)
export StdlibEx.IOUring.Loop (init cleanup listen pin socket)
export StdlibEx.IOUring.Loop (prepAccept prepRecv prepSend prepClose prepConnect)
export StdlibEx.IOUring.Loop (prepTimeout prepCancelFd prepOpen prepRead)
export StdlibEx.IOUring.Loop (prepRecvFixed prepSendFixed prepCloseFixed)
export StdlibEx.IOUring.Loop (submitWait take recycle sqSpace bufSize)
export StdlibEx.IOUring.Loop (ringFd registerFd meshPost meshSendFd meshTake)
export StdlibEx.IOUring.Loop (connectLocal localPort sendAll recvSome closeFd)

end StdlibEx.Linux.Uring.Loop
