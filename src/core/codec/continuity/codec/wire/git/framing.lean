/-
  Continuity.Codec.Wire.Git.Pack.Framing - Git pkt-line framing

  4-hex-digit length prefix ("0000" = flush), capability negotiation, and
  sideband demux, built on the generic Core.Framing engine.
-/

import continuity.codec.core.framing

namespace Continuity.Codec.Wire.Git.Framing

open Continuity.Codec.Core.Framing

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- GIT PKT-LINE: 4 hex digits, "0000" = flush
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert a nibble (0-15) to hex char -/
def toHexChar (count : Nat) : UInt8 :=
  if count < 10 then (48 + count).toUInt8  -- '0'-'9'
  else (87 + count).toUInt8 -- 'a'-'f'

/-- Convert hex char to nibble, or none -/
def fromHexChar (cursor : UInt8) : Option Nat :=
  if cursor >= 48 && cursor <= 57 then some (cursor.toNat - 48)       -- '0'-'9'
  else if cursor >= 97 && cursor <= 102 then some (cursor.toNat - 87) -- 'a'-'f'
  else if cursor >= 65 && cursor <= 70 then some (cursor.toNat - 55)  -- 'A'-'F'
  else none

-- ═══════════════════════════════════════════════════════════════════════════════
-- HEX ENCODING LEMMAS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- toHexChar produces valid hex digits (0-9 or a-f) -/
theorem toHexChar_in_range
        (count : Nat)
        (evidence : count < 16)
        : (toHexChar count >= 48 && toHexChar count <= 57)
            || (toHexChar count >= 97 && toHexChar count <= 102) := by
  match count, evidence with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | count + 16, header => nomatch (Nat.not_lt.mpr (Nat.le_add_left 16 count) header)

/-- fromHexChar inverts toHexChar for nibbles -/
theorem fromHexChar_toHexChar
        (count : Nat)
        (evidence : count < 16)
        : fromHexChar (toHexChar count) = some count := by
  match count, evidence with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | count + 16, header => nomatch (Nat.not_lt.mpr (Nat.le_add_left 16 count) header)

/-- Encode length as 4 hex digits (includes the 4-byte header in length) -/
def gitEncodeLength (payloadLen : Nat) : Bytes :=
  let totalLen := payloadLen + 4 -- pkt-line length includes header
  let hexDigit0 := (totalLen / 4096) % 16
  let hexDigit1 := (totalLen / 256) % 16
  let hexDigit2 := (totalLen / 16) % 16
  let hexDigit3 := totalLen % 16
  [toHexChar hexDigit0, toHexChar hexDigit1, toHexChar hexDigit2, toHexChar hexDigit3].toByteArray

/-- Decode 4 hex digits to length -/
def gitDecodeLength (bytes : Bytes) : Option (Nat × Nat) :=
  if h : bytes.size >= 4 then
    match fromHexChar bytes[0], fromHexChar bytes[1], fromHexChar bytes[2], fromHexChar bytes[3] with
    | some digit0, some digit1, some digit2, some digit3 =>
      let totalLen := digit0 * 4096 + digit1 * 256 + digit2 * 16 + digit3
      if totalLen == 0 then some (0, 4)  -- flush packet
      else if totalLen < 4 then none      -- invalid (reserved 0001-0003)
      else some (totalLen - 4, 4)         -- payload length
    | _, _, _, _ => none
  else none

/-- Size of encoded git length is always 4 -/
theorem gitEncodeLength_size (count : Nat) : (gitEncodeLength count).size = 4 := by
  simp [gitEncodeLength, List.size_toByteArray]

private
theorem gitLengthCodec_roundtrip
        (count : Nat)
        (countEvidence : count ≤ 65516)
        : gitDecodeLength (gitEncodeLength count) = some (count, 4) := by
  simp only [gitDecodeLength, gitEncodeLength]
  have hsize :
      [
        toHexChar ((count + 4) / 4096 % 16),
        toHexChar ((count + 4) / 256 % 16),
        toHexChar ((count + 4) / 16 % 16),
        toHexChar ((count + 4) % 16)
      ].toByteArray.size
          >= 4 := by simp [List.size_toByteArray]
  simp only [hsize, ↓reduceDIte]
  have byte0Evidence : (count + 4) / 4096 % 16 < 16 := Nat.mod_lt _ (by omega)
  have firstEvidence : (count + 4) / 256 % 16 < 16 := Nat.mod_lt _ (by omega)
  have secondEvidence : (count + 4) / 16 % 16 < 16 := Nat.mod_lt _ (by omega)
  have thirdEvidence : (count + 4) % 16 < 16 := Nat.mod_lt _ (by omega)
  simp only [List.getElem_toByteArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [fromHexChar_toHexChar _ byte0Evidence, fromHexChar_toHexChar _ firstEvidence,
    fromHexChar_toHexChar _ secondEvidence, fromHexChar_toHexChar _ thirdEvidence]
  have hrecon :
      (count + 4) / 4096 % 16 * 4096 + (count + 4) / 256 % 16 * 256 + (count + 4) / 16 % 16 * 16
          + (count + 4) % 16
          = count + 4 := by
    have hbound : count + 4 < 65536 := by omega
    omega
  simp only [hrecon]
  have hne_zero : (count + 4 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  have hge_four : ¬(count + 4 < 4) := by omega
  simp only [hne_zero, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hge_four]
  simp only [Nat.add_sub_cancel]

private
theorem gitLengthCodec_decode_append
        (count : Nat)
        (extra : ByteArray)
        (countEvidence : count ≤ 65516)
        : gitDecodeLength (gitEncodeLength count ++ extra) = some (count, 4) := by
  simp only [gitDecodeLength]
  have hsize : (gitEncodeLength count ++ extra).size >= 4 := by
    simp [ByteArray.size_append, gitEncodeLength_size]
  rw [dif_pos hsize]
  have byte0Evidence : (0 : Nat) < (gitEncodeLength count).size := by simp [gitEncodeLength_size]
  have firstEvidence : (1 : Nat) < (gitEncodeLength count).size := by simp [gitEncodeLength_size]
  have secondEvidence : (2 : Nat) < (gitEncodeLength count).size := by simp [gitEncodeLength_size]
  have thirdEvidence : (3 : Nat) < (gitEncodeLength count).size := by simp [gitEncodeLength_size]
  simp only [ByteArray.getElem_append_left byte0Evidence,
    ByteArray.getElem_append_left firstEvidence, ByteArray.getElem_append_left secondEvidence,
    ByteArray.getElem_append_left thirdEvidence]
  simp only [gitEncodeLength, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hn0 : (count + 4) / 4096 % 16 < 16 := Nat.mod_lt _ (by omega)
  have hn1 : (count + 4) / 256 % 16 < 16 := Nat.mod_lt _ (by omega)
  have hn2 : (count + 4) / 16 % 16 < 16 := Nat.mod_lt _ (by omega)
  have hn3 : (count + 4) % 16 < 16 := Nat.mod_lt _ (by omega)
  rw [fromHexChar_toHexChar _ hn0, fromHexChar_toHexChar _ hn1, fromHexChar_toHexChar _ hn2,
    fromHexChar_toHexChar _ hn3]
  have hrecon :
      (count + 4) / 4096 % 16 * 4096 + (count + 4) / 256 % 16 * 256 + (count + 4) / 16 % 16 * 16
          + (count + 4) % 16
          = count + 4 := by
    have hbound : count + 4 < 65536 := by omega
    omega
  simp only [hrecon]
  have hne_zero : (count + 4 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  have hge_four : ¬(count + 4 < 4) := by omega
  simp only [hne_zero, Bool.false_eq_true, if_false]
  rw [if_neg hge_four]
  simp only [Nat.add_sub_cancel]

/-- Git pkt-line length codec -/
def gitLengthCodec : LengthCodec where
  fixedSize := 4
  maxPayload := 65516 -- 65520 - 4
  encode := gitEncodeLength
  decode := gitDecodeLength
  roundtrip := gitLengthCodec_roundtrip
  encode_size := gitEncodeLength_size
  decode_append := gitLengthCodec_decode_append

/-- Git pkt-line bounded frame box -/
def gitBoundedFrame : Box (BoundedFrame gitLengthCodec) := boundedFrameBox gitLengthCodec

/-- Git pkt-line frame parsing (partial - no Box guarantees for oversized frames) -/
def gitFrame.parse := parseFrame gitLengthCodec
-- ═══════════════════════════════════════════════════════════════════════════════
-- CAPABILITY NEGOTIATION (shared pattern)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A capability is just a string identifier -/
abbrev Capability := String

/-- Parse space-separated capabilities -/
def parseCapabilities (state : String) : List Capability := state.splitOn " " |>.filter (·!= "")

/-- Serialize capabilities as space-separated -/
def serializeCapabilities (caps : List Capability) : String := String.intercalate " " caps

-- ═══════════════════════════════════════════════════════════════════════════════
-- SIDEBAND DEMULTIPLEXING (Git uses this)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sideband channel -/
inductive SidebandChannel where
  | packData -- channel 1: pack data
  | progress -- channel 2: progress messages
  | error    -- channel 3: error messages
  deriving Repr, DecidableEq

/-- Parse sideband channel from first byte -/
def parseSidebandChannel (rightValue : UInt8) : Option SidebandChannel :=
  match rightValue.toNat with
  | 1 => some .packData
  | 2 => some .progress
  | 3 => some .error
  | _ => none

/-- Demux a sideband frame -/
def demuxSideband (function : Frame) : Option (SidebandChannel × Bytes) :=
  if h : function.payload.size > 0 then
    match parseSidebandChannel function.payload[0] with
    | some character => some (character, function.payload.extract 1 function.payload.size)
    | none           => none
  else
    none

end Continuity.Codec.Wire.Git.Framing
