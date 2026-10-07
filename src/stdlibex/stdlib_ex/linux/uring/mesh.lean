/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // LINUX // URING // MESH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    DEPRECATED: This module is superseded by StdlibEx.IOUring.Mesh.

    Re-exports StdlibEx.IOUring.Mesh for backward compatibility. New code should
    import StdlibEx.IOUring.Mesh directly.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import stdlib_ex.io_uring.mesh

namespace StdlibEx.Linux.Uring.Mesh

export StdlibEx.IOUring.Mesh (MeshKind MeshEvent MeshHandle)
export StdlibEx.IOUring.Mesh (pin init cleanup ringFd fast registerFd)
export StdlibEx.IOUring.Mesh (post sendFd submitWait take sqSpace flush)

end StdlibEx.Linux.Uring.Mesh
