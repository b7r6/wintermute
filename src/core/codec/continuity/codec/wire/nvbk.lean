/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // CONTINUITY // CODEC // WIRE // NVBK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The NVBK GPU-broker request header — the guest→host wire of the Firecracker
    gpu-broker (CUDA/NVML call brokering over vsock cid=2 port=9999). NEW SPEC,
    written here first (the corpus's §10b headline alongside the vsock CSM it rides
    on). Ported from `isospin-microvm/gpu-broker/src/vsock.rs` (`WireRequest`):

        #[repr(C, packed)]                       little-endian, 32 bytes
        le32 magic ("NVBK" = 0x4E56424B) · le32 version · le64 client_id
        le64 seq · le32 op_type · le32 payload_len      then `payload_len` bytes

    The 32-byte header `Box` is a `seq` tower of the verified per-field LE boxes mapped
    via `isoBox`, so roundtrip + consumption come free (`header_consumption`). The op
    payloads (Alloc/Free/MapMemory/…) are the data layer the generator dispatches on.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.codec.core.box

namespace Continuity.Codec.Wire.Nvbk

open Continuity.Codec.Core

/-- `WIRE_MAGIC` — `"NVBK"` little-endian. -/
def WIRE_MAGIC : UInt32 := 0x4E56424B

def WIRE_VERSION : UInt32 := 1
def DEFAULT_VSOCK_PORT : UInt32 := 9999
def MAX_PAYLOAD_SIZE : Nat := 4096

/-- The NVBK request header — fields as bit-vectors of their wire widths, in order.
    Mirrors the Rust `#[repr(C, packed)]` `WireRequest`. -/
structure wire_request where
  magic      : BitVec 32
  version    : BitVec 32
  clientId   : BitVec 64
  seq        : BitVec 64
  opType     : BitVec 32
  payloadLen : BitVec 32
  deriving DecidableEq, Repr

private
abbrev HeaderTuple := ((((BitVec 32 × BitVec 32) × BitVec 64) × BitVec 64) × BitVec 32) × BitVec 32

private
def headerTupleBox : Box HeaderTuple :=
  seq
    (seq (seq (seq (seq u32leBitVec u32leBitVec) u64leBitVec) u64leBitVec) u32leBitVec)
    u32leBitVec

private
def toHeader : HeaderTuple → wire_request
  | ⟨⟨⟨⟨⟨magic, version⟩, clientId⟩, seq⟩, opType⟩, payloadLen⟩ =>
    { magic, version, clientId, seq, opType, payloadLen }

private
def ofHeader : wire_request → HeaderTuple
  | { magic, version, clientId, seq, opType, payloadLen } =>
    ⟨⟨⟨⟨⟨magic, version⟩, clientId⟩, seq⟩, opType⟩, payloadLen⟩

/-- The verified NVBK request-header codec — roundtrip + consumption from the `seq` tower. -/
def headerBox : Box wire_request :=
  isoBox headerTupleBox toHeader ofHeader (fun _ => rfl) (fun _ => rfl)

theorem header_consumption
        (header : wire_request)
        (rest : Bytes)
        : headerBox.parse (headerBox.serialize header ++ rest) = ParseResult.ok header rest :=
  headerBox.consumption header rest

private
def sample : wire_request :=
  { magic      := WIRE_MAGIC.toBitVec,
    version    := 1,
    clientId   := 7,
    seq        := 42,
    opType     := 2,
    payloadLen := 16 }

example : headerBox.parse (headerBox.serialize sample) = ParseResult.ok sample ByteArray.empty := by
  native_decide

example : (headerBox.serialize sample).size = 32 := by native_decide

end Continuity.Codec.Wire.Nvbk
