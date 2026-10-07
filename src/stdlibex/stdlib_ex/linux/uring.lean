/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // STDLIBEX // LINUX // URING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Linux io_uring FFI — raw kernel interface for async I/O.

    This module provides the AXIOMATIZED interface to io_uring. The semantics
    match the Linux kernel's io_uring(7) contract. We trust liburing and the
    kernel; the axioms state what the syscall interface promises.

    Structure:
      · `StdlibEx.Linux.Uring.Core`  — basic ring: init, cleanup, nop, statx, open, read, close
      · `StdlibEx.Linux.Uring.Loop`  — batched proactor: multishot accept/recv, buffer ring
      · `StdlibEx.Linux.Uring.Mesh`  — cross-core MSG_RING transport

    The C shims live at `Uring/*.c`.

    Higher-level abstractions (lifecycle brackets, proven state machines) live
    in `EVRing.*` and build on this raw interface.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import stdlib_ex.linux.uring.core
import stdlib_ex.linux.uring.loop
import stdlib_ex.linux.uring.mesh
