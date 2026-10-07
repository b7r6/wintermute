/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // STDLIBEX // IOURING // MESH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Shared-nothing cross-core mesh: IORING_OP_MSG_RING transport between rings
    on pinned cores. Each ring is OWNED by its creating thread.

    Shared-nothing discipline:
      · A DEFER_TASKRUN|SINGLE_ISSUER ring is OWNED by its creating thread
      · Each core creates its OWN ring after pinning
      · MSG_DATA carries a HEAP POINTER (exclusive ownership handoff)
      · Receiver frees the buffer at `take`

    This is the raw FFI layer. Higher-level abstractions build on this.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.IOUring.Mesh

-- ══════════════════════════════════════════════════════════════════════════════
-- EVENT RECORDS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Kind of mesh completion — MUST match `EM_K_*` enum in mesh.c. -/
inductive MeshKind where
  | sendDone -- our send failed (a = -errno); success is silent
  | dataRecv -- peer MSG_DATA arrived (a = buffer ptr, b = len, channel)
  | fdRecv   -- peer MSG_SEND_FD arrived (a = reg index, channel = cookie)
  deriving DecidableEq, Repr, Inhabited

/-- One drained mesh completion. Scalar layout: a@0, b@8, channel@12, kind@16. -/
structure MeshEvent where
  a       : UInt64   -- DATA_RECV: buffer pointer · FD_RECV: reg index · SEND_DONE: res
  b       : UInt32   -- DATA_RECV: payload length · else 0
  channel : UInt32   -- application channel / cookie
  kind    : MeshKind
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════════════════
-- MESH HANDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Opaque handle to a mesh ring (core-pinned, single-issuer). -/
opaque MeshHandlePointed : NonemptyType

def MeshHandle : Type := MeshHandlePointed.type
instance : Nonempty MeshHandle := MeshHandlePointed.property

-- ══════════════════════════════════════════════════════════════════════════════
-- RAW FFI
-- ══════════════════════════════════════════════════════════════════════════════

/-- Pin the CALLING thread to `cpu`. Must be called BEFORE init. -/
@[extern "umesh_pin"]
opaque pin (cpu : UInt32) : IO Int32

/-- Initialize mesh ring after pinning. -/
@[extern "umesh_init"]
opaque init (entries nfiles evoutCap : UInt32) : IO MeshHandle

/-- Clean up the mesh ring. -/
@[extern "umesh_cleanup"]
opaque cleanup (mesh : @& MeshHandle) : IO Unit

/-- Get this mesh's ring fd (for peer registration). -/
@[extern "umesh_ring_fd"]
opaque ringFd (mesh : @& MeshHandle) : IO Int32

/-- Check if fast-path features are available. -/
@[extern "umesh_fast"]
opaque fast (mesh : @& MeshHandle) : IO UInt8

/-- Register a raw fd for fixed-file ops. Returns registered index. -/
@[extern "umesh_register_fd"]
opaque registerFd (mesh : @& MeshHandle) (rawFd : UInt32) : IO Int32

/-- Post data to target ring. -/
@[extern "umesh_post"]
opaque post (mesh : @& MeshHandle) (targetRingFd : UInt32) (bytes : @& ByteArray) (channel : UInt32) : IO Int32

/-- Send a registered fd to target ring. -/
@[extern "umesh_send_fd"]
opaque sendFd (mesh : @& MeshHandle) (targetRingFd regIndex channel : UInt32) : IO Int32

/-- Submit and wait for completions. -/
@[extern "umesh_submit_wait"]
opaque submitWait (mesh : @& MeshHandle) (minComplete : UInt32) : IO (Array MeshEvent)

/-- Copy out received data and free the buffer. -/
@[extern "umesh_take"]
opaque take (ptr : UInt64) (len : UInt32) : IO ByteArray

/-- Available SQ slots. -/
@[extern "umesh_sq_space"]
opaque sqSpace (mesh : @& MeshHandle) : IO UInt32

/-- Flush pending submissions. -/
@[extern "umesh_flush"]
opaque flush (mesh : @& MeshHandle) : IO Int32

end StdlibEx.IOUring.Mesh
