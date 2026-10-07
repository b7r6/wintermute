/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // STDLIBEX // LINUX // FANOTIFY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Linux fanotify FFI — filesystem event monitoring.

    One fd, recursive, entire mount. Zero CPU when idle. The ring can block on
    IORING_OP_READ of the fanotify fd. On wake: batch statx, diff, invalidate.

    Requires CAP_SYS_ADMIN or CAP_SYS_FANOTIFY.

    The C shim lives at `Fanotify/fanotify.c`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Linux.Fanotify

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI
-- ══════════════════════════════════════════════════════════════════════════════

/-- Initialize fanotify watching on `rootPath`. Returns the fanotify fd.
    Requires CAP_SYS_ADMIN or CAP_SYS_FANOTIFY. -/
@[extern "fanotify_init_watch"]
opaque initWatch (rootPath : @& String) : IO UInt32

/-- Read pending fanotify events. Returns count of events read.
    Returns 0 if no events ready (EAGAIN). -/
@[extern "fanotify_read_events"]
opaque readEvents (fd : UInt32) : IO UInt32

/-- Close the fanotify fd. -/
@[extern "fanotify_close"]
opaque closeWatch (fd : UInt32) : IO Unit

/-- Recursively scan a directory tree, returning (path, mtime, size) for each file. -/
@[extern "fanotify_scan_tree"]
opaque scanTree (rootPath : @& String) : IO (Array (String × Nat × Nat))

end StdlibEx.Linux.Fanotify
