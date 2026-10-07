/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // CONTINUITY // CODEC // WIRE // VSOCK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The virtio-vsock packet header — the 44-byte, little-endian, `__attribute__
    ((packed))` C struct every vsock packet leads with. The verified spec the
    generator (`Codec/Codegen/Vsock`) mirrors, and the wire the CSM
    (`Machine/Codegen/Vsock`) rides on.

    Ported from the hand-rolled Rust `VsockPacketHeader` (canonical Firecracker
    `.../virtio/vsock/packet.rs`), whose ten fields are, in order:

        le64 src_cid · le64 dst_cid · le32 src_port · le32 dst_port · le32 len
        le16 type    · le16 op      · le32 flags    · le32 buf_alloc · le32 fwd_cnt
        ── 8 + 8 + 4 + 4 + 4 + 2 + 2 + 4 + 4 + 4 = 44 bytes (VSOCK_PKT_HDR_SIZE) ──

    The header `Box` is assembled as a `seq` tower of the verified per-field LE
    boxes (`u64leBitVec` / `u32leBitVec` / `u16leBitVec`, `Codec/Core/Box`) and
    mapped to the named `VsockHeader` via `isoBox`. Because `seq` composes BOTH the
    roundtrip and the consumption laws, the whole header inherits them for free —
    `parse (serialize h ++ rest) = ok h rest`, proven, not asserted.

    The payload bounds checks (`len > MAX_PKT_BUF_SIZE`, descriptor-chain length)
    are the validation layer ABOVE this pure header codec — the generator carries
    the `MAX_PKT_BUF_SIZE` guard; the chain accounting is the device's data layer.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.codec.core.box

namespace Continuity.Codec.Wire.Vsock

open Continuity.Codec.Core

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // protocol constants (super::defs::uapi)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The packed header size — `VSOCK_PKT_HDR_SIZE` (Rust asserts it equals
    `size_of::<VsockPacketHeader>()`). -/
def VSOCK_PKT_HDR_SIZE : Nat := 44

/-- Largest packet payload we accept — `defs::MAX_PKT_BUF_SIZE` (64 KiB). -/
def MAX_PKT_BUF_SIZE : UInt32 := 64 * 1024

-- The `VSOCK_OP_*` operation ids (`hdr.op`).
def VSOCK_OP_REQUEST : UInt16 := 1

def VSOCK_OP_RESPONSE : UInt16 := 2
def VSOCK_OP_RST : UInt16 := 3
def VSOCK_OP_SHUTDOWN : UInt16 := 4
def VSOCK_OP_RW : UInt16 := 5
def VSOCK_OP_CREDIT_UPDATE : UInt16 := 6
def VSOCK_OP_CREDIT_REQUEST : UInt16 := 7

-- Shutdown flags (`hdr.flags` with `VSOCK_OP_SHUTDOWN`) and the stream socket type.
def VSOCK_FLAGS_SHUTDOWN_RCV : UInt32 := 1

def VSOCK_FLAGS_SHUTDOWN_SEND : UInt32 := 2
def VSOCK_TYPE_STREAM : UInt16 := 1
def VSOCK_HOST_CID : UInt64 := 2

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                  // the header
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The vsock packet header — fields as bit-vectors of their wire widths, in wire
    order. Mirrors the Rust `#[repr(C, packed)]` `VsockPacketHeader`. -/
structure vsock_header where
  srcCid   : BitVec 64
  dstCid   : BitVec 64
  srcPort  : BitVec 32
  dstPort  : BitVec 32
  len      : BitVec 32
  type     : BitVec 16
  op       : BitVec 16
  flags    : BitVec 32
  bufAlloc : BitVec 32
  fwdCnt   : BitVec 32
  deriving DecidableEq, Repr

/-- The left-nested tuple the `seq` tower produces, ten fields deep. -/
private
abbrev HeaderTuple :=
  ((((((((BitVec 64 × BitVec 64) × BitVec 32) × BitVec 32) × BitVec 32) × BitVec 16) × BitVec 16)
      × BitVec 32)
      × BitVec 32)
      × BitVec 32

/-- The fields sequenced in wire order — roundtrip and consumption come from `seq`. -/
private
def headerTupleBox : Box HeaderTuple :=
  seq
    (seq
      (seq
        (seq
          (seq
            (seq (seq (seq (seq u64leBitVec u64leBitVec) u32leBitVec) u32leBitVec) u32leBitVec)
            u16leBitVec)
          u16leBitVec)
        u32leBitVec)
      u32leBitVec)
    u32leBitVec

private
def toHeader : HeaderTuple → vsock_header
  | ⟨⟨⟨⟨⟨⟨⟨⟨⟨srcCid, dstCid⟩, srcPort⟩, dstPort⟩, len⟩, type⟩, opcode⟩, flags⟩, bufAlloc⟩, fwdCnt⟩ =>
    { srcCid, dstCid, srcPort, dstPort, len, type, op := opcode, flags, bufAlloc, fwdCnt }

private
def ofHeader : vsock_header → HeaderTuple
  | header =>
    ⟨
      ⟨
        ⟨
          ⟨
            ⟨
              ⟨⟨⟨⟨header.srcCid, header.dstCid⟩, header.srcPort⟩, header.dstPort⟩, header.len⟩,
              header.type
            ⟩,
            header.op
          ⟩,
          header.flags
        ⟩,
        header.bufAlloc
      ⟩,
      header.fwdCnt
    ⟩

/-- The verified vsock header codec: parse/serialize the 44-byte LE header, with the
    roundtrip and consumption laws inherited from the field `seq` tower. -/
def headerBox : Box vsock_header :=
  isoBox headerTupleBox toHeader ofHeader (fun _ => rfl) (fun _ => rfl)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // it round-trips, exactly
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The proven law, restated at the header level: parse undoes serialize, leaving any
    trailing payload bytes untouched (the foundation the device's chain logic sits on). -/
theorem header_consumption
        (evidence : vsock_header)
        (rest : Bytes)
        : headerBox.parse (headerBox.serialize evidence ++ rest) = ParseResult.ok evidence rest :=
  headerBox.consumption evidence rest

/-- A concrete header (the Rust `test_packet_hdr_accessors` field set: 1..10) round-
    trips through the real serialize/parse by computation, and lands on 44 bytes. -/
private
def sample : vsock_header :=
  { srcCid   := 1,
    dstCid   := 2,
    srcPort  := 3,
    dstPort  := 4,
    len      := 5,
    type     := 6,
    op       := 7,
    flags    := 8,
    bufAlloc := 9,
    fwdCnt   := 10 }

example : headerBox.parse (headerBox.serialize sample) = ParseResult.ok sample ByteArray.empty := by
  native_decide

example : (headerBox.serialize sample).size = VSOCK_PKT_HDR_SIZE := by native_decide

end Continuity.Codec.Wire.Vsock
