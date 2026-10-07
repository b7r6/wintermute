/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // IOURING // LOOP
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Batched io_uring proactor: multishot accept/recv, provided buffer ring,
    flat completion records. The contract per loop iteration is exactly:

        prep… (enqueue only) → submitWait (1 syscall) → Array Event (1 copy)

    Lean's user_data is a `UInt64` that travels through a C-side inflight
    table; the record's `kind` byte tells us which op completed, so decoding
    events never guesses. Buffer-ring payloads are copied out exactly once
    (`take`, which also recycles the kernel buffer).

    This is the raw FFI layer. Higher-level abstractions (lifecycle brackets,
    proven state machines) build on this.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.IOUring.Loop

-- ══════════════════════════════════════════════════════════════════════════════
-- EVENT RECORDS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Op kinds — MUST match the `ER_K_*` enum in loop.c (ctor order is the tag).
    `meshData`/`meshFd` are folded-in mesh deliveries: a peer MSG_RING landing
    on THIS ring (same ring that does socket I/O). -/
inductive OpKind where
  | nop
  | accept
  | recv
  | send
  | close
  | timeout
  | cancel
  | «open»
  | read
  | write
  | meshData
  | meshFd
  | connect
  deriving DecidableEq, Repr, Inhabited

/-- Raw CQE flag bits (liburing). -/
def cqeFBuffer : UInt32 := 1

def cqeFMore : UInt32 := 2
def cqeBufferShift : UInt32 := 16

/-- One drained completion. Constructed directly in C by `submitWait`
    (scalar layout: ud@0, res@8, flags@16, kind@20) — field order and types
    here are ABI. -/
structure Event where
  ud    : UInt64
  res   : Int64
  flags : UInt32
  kind  : OpKind
  deriving Repr, Inhabited

namespace Event

@[inline]
def ok (event : Event) : Bool := event.res ≥ 0

@[inline]
def errno (event : Event) : Int64 := if event.res < 0 then -event.res else 0

/-- Multishot chain continues after this completion. -/
@[inline]
def more (event : Event) : Bool := event.flags &&& cqeFMore ≠ 0

/-- Payload arrived in a provided buffer. -/
@[inline]
def hasBuffer (event : Event) : Bool := event.flags &&& cqeFBuffer ≠ 0

/-- Provided-buffer id (valid iff `hasBuffer`). -/
@[inline]
def bufferId (event : Event) : UInt32 := event.flags >>> cqeBufferShift

end Event

-- ══════════════════════════════════════════════════════════════════════════════
-- LOOP HANDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Opaque handle to a batched io_uring proactor. -/
opaque LoopHandlePointed : NonemptyType

def LoopHandle : Type := LoopHandlePointed.type
instance : Nonempty LoopHandle := LoopHandlePointed.property

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — lifecycle
-- ══════════════════════════════════════════════════════════════════════════════

/-- Initialize the proactor with `entries` SQ slots, `nbufs` provided buffers
    of `bufSize` bytes each, and space for `evoutCap` events per submit. -/
@[extern "uloop_init"]
opaque init (entries nbufs bufSize evoutCap : UInt32) : IO LoopHandle

/-- Clean up the proactor. -/
@[extern "uloop_cleanup"]
opaque cleanup (loop : @& LoopHandle) : IO Unit

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — socket setup
-- ══════════════════════════════════════════════════════════════════════════════

/-- Create a listening socket on `port` with `backlog`. Returns fd. -/
@[extern "uloop_listen"]
opaque listen (port : UInt16) (backlog : UInt32) : IO Int32

/-- Pin current thread to CPU `cpu`. Returns 0 on success. -/
@[extern "uloop_pin"]
opaque pin (cpu : UInt32) : IO Int32

/-- Create an unconnected TCP socket. Returns fd. -/
@[extern "uloop_socket"]
opaque socket : IO Int32

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — prep operations (enqueue only, no syscall)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Prep multishot accept on listening fd. -/
@[extern "uloop_prep_accept"]
opaque prepAccept (loop : @& LoopHandle) (fd : UInt32) (ud : UInt64) : IO Int32

/-- Prep multishot recv into provided buffer ring. -/
@[extern "uloop_prep_recv"]
opaque prepRecv (loop : @& LoopHandle) (fd : UInt32) (ud : UInt64) : IO Int32

/-- Prep send. -/
@[extern "uloop_prep_send"]
opaque prepSend (loop : @& LoopHandle) (fd : UInt32) (bytes : @& ByteArray) (ud : UInt64) : IO Int32

/-- Prep close. -/
@[extern "uloop_prep_close"]
opaque prepClose (loop : @& LoopHandle) (fd : UInt32) (ud : UInt64) : IO Int32

/-- Prep connect to localhost:port. -/
@[extern "uloop_prep_connect"]
opaque prepConnect (loop : @& LoopHandle) (fd : UInt32) (port : UInt16) (ud : UInt64) : IO Int32

/-- Prep timeout (nanoseconds). -/
@[extern "uloop_prep_timeout"]
opaque prepTimeout (loop : @& LoopHandle) (nanos : UInt64) (ud : UInt64) : IO Int32

/-- Prep cancel all ops on fd. -/
@[extern "uloop_prep_cancel_fd"]
opaque prepCancelFd (loop : @& LoopHandle) (fd : UInt32) (ud : UInt64) : IO Int32

/-- Prep open file. -/
@[extern "uloop_prep_open"]
opaque prepOpen (loop : @& LoopHandle) (path : @& String) (flags mode : UInt32) (ud : UInt64) : IO Int32

/-- Prep read from fd. -/
@[extern "uloop_prep_read"]
opaque prepRead (loop : @& LoopHandle) (fd maxLen : UInt32) (off : UInt64) (ud : UInt64) : IO Int32

-- Fixed-file ops (IOSQE_FIXED_FILE) on registered fd index
@[extern "uloop_prep_recv_fixed"]
opaque prepRecvFixed (loop : @& LoopHandle) (regIndex : UInt32) (ud : UInt64) : IO Int32

@[extern "uloop_prep_send_fixed"]
opaque prepSendFixed (loop : @& LoopHandle) (regIndex : UInt32) (bytes : @& ByteArray) (ud : UInt64) : IO Int32

@[extern "uloop_prep_close_fixed"]
opaque prepCloseFixed (loop : @& LoopHandle) (regIndex : UInt32) (ud : UInt64) : IO Int32

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — submit and reap
-- ══════════════════════════════════════════════════════════════════════════════

/-- Submit all prepped SQEs and wait for at least `minComplete` completions.
    Returns array of Event records. This is the ONE syscall per iteration. -/
@[extern "uloop_submit_wait"]
opaque submitWait (loop : @& LoopHandle) (minComplete : UInt32) : IO (Array Event)

/-- Copy out buffer-ring payload and recycle the buffer. -/
@[extern "uloop_take"]
opaque take (loop : @& LoopHandle) (bufId len : UInt32) : IO ByteArray

/-- Recycle a buffer without reading it (e.g., on error). -/
@[extern "uloop_recycle"]
opaque recycle (loop : @& LoopHandle) (bufId : UInt32) : IO Unit

/-- Available SQ slots. -/
@[extern "uloop_sq_space"]
opaque sqSpace (loop : @& LoopHandle) : IO UInt32

/-- Size of each provided buffer. -/
@[extern "uloop_buf_size"]
opaque bufSize (loop : @& LoopHandle) : IO UInt32

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — mesh (cross-core MSG_RING)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Get this loop's ring fd (for mesh registration). -/
@[extern "uloop_ring_fd"]
opaque ringFd (loop : @& LoopHandle) : IO Int32

/-- Register a raw fd for fixed-file ops. Returns the registered index. -/
@[extern "uloop_register_fd"]
opaque registerFd (loop : @& LoopHandle) (rawFd : UInt32) : IO Int32

/-- Post data to another core's ring via MSG_RING. -/
@[extern "uloop_mesh_post"]
opaque meshPost (loop : @& LoopHandle) (targetRing : UInt32) (bytes : @& ByteArray) (channel : UInt32) : IO Int32

/-- Send a registered fd to another core's ring. -/
@[extern "uloop_mesh_send_fd"]
opaque meshSendFd (loop : @& LoopHandle) (targetRing regIndex channel : UInt32) : IO Int32

/-- Copy out mesh payload. -/
@[extern "uloop_mesh_take"]
opaque meshTake (ptr : UInt64) (len : UInt32) : IO ByteArray

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI — blocking helpers (for tests/gates only, never hot path)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Blocking connect to localhost:port. -/
@[extern "uloop_connect_local"]
opaque connectLocal (port : UInt16) : IO Int32

/-- Get local port of a socket. -/
@[extern "uloop_local_port"]
opaque localPort (fd : UInt32) : IO Int32

/-- Blocking send all bytes. -/
@[extern "uloop_send_all"]
opaque sendAll (fd : UInt32) (bytes : @& ByteArray) : IO Int64

/-- Blocking recv up to cap bytes. -/
@[extern "uloop_recv_some"]
opaque recvSome (fd cap : UInt32) : IO ByteArray

/-- Blocking close. -/
@[extern "uloop_close_fd"]
opaque closeFd (fd : UInt32) : IO Unit

end StdlibEx.IOUring.Loop
