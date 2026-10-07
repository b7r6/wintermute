/-
  Continuity.Codec.Wire.Nix.Daemon.Framing - Nix daemon framing

  8-byte little-endian u64 length prefix, built on the generic Core.Framing
  engine.
-/

import continuity.codec.core.framing

namespace Continuity.Codec.Wire.Nix.Framing

open Continuity.Codec.Core.Framing

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- NIX DAEMON: 8-byte LE u64 length
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Encode length as 8-byte little-endian -/
def nixEncodeLength (count : Nat) : Bytes :=
  let wordValue := count.toUInt64
  [
    (wordValue &&& 0xFF).toUInt8,
    ((wordValue >>> 8) &&& 0xFF).toUInt8,
    ((wordValue >>> 16) &&& 0xFF).toUInt8,
    ((wordValue >>> 24) &&& 0xFF).toUInt8,
    ((wordValue >>> 32) &&& 0xFF).toUInt8,
    ((wordValue >>> 40) &&& 0xFF).toUInt8,
    ((wordValue >>> 48) &&& 0xFF).toUInt8,
    ((wordValue >>> 56) &&& 0xFF).toUInt8
  ].toByteArray

/-- Decode 8-byte little-endian length -/
def nixDecodeLength (bytes : Bytes) : Option (Nat × Nat) :=
  if h : bytes.size >= 8 then
    let wordValue : UInt64 :=
      bytes[0].toUInt64 ||| (bytes[1].toUInt64 <<< 8) ||| (bytes[2].toUInt64 <<< 16)
          ||| (bytes[3].toUInt64 <<< 24)
          ||| (bytes[4].toUInt64 <<< 32)
          ||| (bytes[5].toUInt64 <<< 40)
          ||| (bytes[6].toUInt64 <<< 48)
          ||| (bytes[7].toUInt64 <<< 56)
    some (wordValue.toNat, 8)
  else
    none

/-- Size of encoded nix length is always 8 -/
theorem nixEncodeLength_size (count : Nat) : (nixEncodeLength count).size = 8 := by
  simp [nixEncodeLength, List.size_toByteArray]

/-- Little-endian 8-byte roundtrip: extract bytes then reconstruct equals original -/
theorem le_u64_roundtrip
        (wordValue : UInt64)
        : ((wordValue &&& 0xFF).toUInt8).toUInt64
            ||| (((wordValue >>> 8) &&& 0xFF).toUInt8).toUInt64 <<< 8
            ||| (((wordValue >>> 16) &&& 0xFF).toUInt8).toUInt64 <<< 16
            ||| (((wordValue >>> 24) &&& 0xFF).toUInt8).toUInt64 <<< 24
            ||| (((wordValue >>> 32) &&& 0xFF).toUInt8).toUInt64 <<< 32
            ||| (((wordValue >>> 40) &&& 0xFF).toUInt8).toUInt64 <<< 40
            ||| (((wordValue >>> 48) &&& 0xFF).toUInt8).toUInt64 <<< 48
            ||| (((wordValue >>> 56) &&& 0xFF).toUInt8).toUInt64 <<< 56
            = wordValue := by bv_decide

/-- Nix daemon length codec -/
def nixLengthCodec : LengthCodec where
  fixedSize := 8
  maxPayload := 2^32  -- practical limit
  encode := nixEncodeLength
  decode := nixDecodeLength
  roundtrip := by
    intro payloadSize sizeBound
    simp only [nixDecodeLength, nixEncodeLength]
    -- Size is 8
    have hsize : ([ (payloadSize.toUInt64 &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 8) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 16) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 24) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 32) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 40) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 48) &&& 0xFF).toUInt8
                  , ((payloadSize.toUInt64 >>> 56) &&& 0xFF).toUInt8
                  ].toByteArray).size >= 8 := by simp [List.size_toByteArray]
    simp only [hsize, ↓reduceDIte, List.getElem_toByteArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    -- For payloadSize ≤ 2^32, payloadSize.toUInt64.toNat = payloadSize
    have hbound : payloadSize < 2^64 := by omega
    have htoUInt64 : payloadSize.toUInt64.toNat = payloadSize := by
      simp only [Nat.toUInt64, UInt64.toNat]
      exact Nat.mod_eq_of_lt hbound
    -- Use the LE roundtrip lemma
    have hle := le_u64_roundtrip payloadSize.toUInt64
    simp only [hle, htoUInt64]
  encode_size := nixEncodeLength_size
  decode_append := by
    intro payloadSize extra sizeBound
    -- Unfold definitions but keep nixEncodeLength for rewriting
    simp only [nixDecodeLength]
    -- Size of (encode ++ extra) >= 8
    have henc_sz : (nixEncodeLength payloadSize).size = 8 := nixEncodeLength_size payloadSize
    have hsize : (nixEncodeLength payloadSize ++ extra).size >= 8 := by
      simp only [ByteArray.size_append, henc_sz]; omega
    rw [dif_pos hsize]
    -- Bounds proofs for getElem_append_left
    have byte0Evidence : (0 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have firstEvidence : (1 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have secondEvidence : (2 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have thirdEvidence : (3 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have byte4Evidence : (4 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have byte5Evidence : (5 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have byte6Evidence : (6 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    have byte7Evidence : (7 : Nat) < (nixEncodeLength payloadSize).size := by simp only [henc_sz]; omega
    simp only [ByteArray.getElem_append_left byte0Evidence, ByteArray.getElem_append_left firstEvidence,
               ByteArray.getElem_append_left secondEvidence, ByteArray.getElem_append_left thirdEvidence,
               ByteArray.getElem_append_left byte4Evidence, ByteArray.getElem_append_left byte5Evidence,
               ByteArray.getElem_append_left byte6Evidence, ByteArray.getElem_append_left byte7Evidence]
    simp only [nixEncodeLength, List.getElem_toByteArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    -- Same reconstruction as roundtrip
    have hbound : payloadSize < 2^64 := by omega
    have htoUInt64 : payloadSize.toUInt64.toNat = payloadSize := by
      simp only [Nat.toUInt64, UInt64.toNat]
      exact Nat.mod_eq_of_lt hbound
    have hle := le_u64_roundtrip payloadSize.toUInt64
    simp only [hle, htoUInt64]

/-- Nix daemon bounded frame box -/
def nixBoundedFrame : Box (BoundedFrame nixLengthCodec) := boundedFrameBox nixLengthCodec

/-- Nix daemon frame parsing (partial - no Box guarantees for oversized frames) -/
def nixFrame.parse := parseFrame nixLengthCodec

end Continuity.Codec.Wire.Nix.Framing
