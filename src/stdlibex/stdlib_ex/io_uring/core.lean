/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // IOURING // CORE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Basic io_uring operations: init, cleanup, nop, statx, open, read, close.

    This is the raw FFI layer. The C shim (`core.c`) wraps liburing with a
    two-layer design:
      · Pure-C core (ur_*) — testable standalone against a live ring
      · Lean-ABI wrappers (uring_*) — thin conversion layer

    The RingHandle is a finalized external object so a dropped ring is always
    cleaned up.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.IOUring

-- ══════════════════════════════════════════════════════════════════════════════
-- RING HANDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Opaque handle to an io_uring instance. Must be cleaned up via `cleanup`. -/
opaque RingHandlePointed : NonemptyType

def RingHandle : Type := RingHandlePointed.type
instance : Nonempty RingHandle := RingHandlePointed.property

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI
-- ══════════════════════════════════════════════════════════════════════════════

/-- Initialize an io_uring with `entries` submission queue slots.
    Returns an opaque handle that MUST be cleaned up. -/
@[extern "uring_init"]
opaque init (entries : UInt32) : IO RingHandle

/-- Clean up the ring. Idempotent (safe to call multiple times). -/
@[extern "uring_cleanup"]
opaque cleanup (ring : @& RingHandle) : IO Unit

/-- Submit `n` no-ops and reap them. Returns count that completed successfully.
    Useful for testing ring liveness. -/
@[extern "uring_batch_nop"]
opaque batchNop (ring : @& RingHandle) (count : UInt32) : IO UInt32

/-- Stat a file via io_uring. Returns file size on success. -/
@[extern "uring_statx"]
opaque statx (ring : @& RingHandle) (path : @& String) : IO Nat

/-- Open a file via io_uring. Returns fd on success, negative errno on failure. -/
@[extern "uring_open"]
opaque openFile (ring : @& RingHandle) (path : @& String) (flags : Int32) (mode : UInt32) : IO Int32

/-- Read from fd via io_uring. Returns the bytes read. -/
@[extern "uring_read"]
opaque read (ring : @& RingHandle) (fd : Int32) (size : UInt32) (offset : Int64) : IO ByteArray

/-- Close fd via io_uring. Returns 0 on success, negative errno on failure. -/
@[extern "uring_close"]
opaque close (ring : @& RingHandle) (fd : Int32) : IO Int32

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS — the io_uring contract
-- ══════════════════════════════════════════════════════════════════════════════

/-- A successfully initialized ring can be cleaned up. -/
axiom cleanup_succeeds (ring : RingHandle) : ∃ u : Unit, cleanup ring = pure u

/-- Cleanup is idempotent — calling it twice is safe. -/
axiom cleanup_idempotent (ring : RingHandle) :
    (cleanup ring >>= fun _ => cleanup ring) = cleanup ring

/-- batchNop returns at most n completions. -/
axiom batch_nop_bounded (ring : RingHandle) (count : UInt32) :
    ∀ result, batchNop ring count = pure result → result ≤ count

end StdlibEx.IOUring
