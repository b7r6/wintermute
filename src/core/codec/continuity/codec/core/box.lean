/-
  Continuity.Codec.Core - Verified Box Implementations

  This module contains Box definitions with COMPLETE proofs.
  No `sorry`, no `axiom`, no `partial`.

  The goal: real load-bearing proofs that guarantee roundtrip correctness.
-/

import Std.Tactic.BVDecide

namespace Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- BYTES (same as Basic, but we'll use ByteArray directly for lemma access)
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev Bytes := ByteArray

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSE RESULT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse result: either failure or (value, remaining bytes) -/
inductive ParseResult (Value : Type) where
  | ok : Value → Bytes → ParseResult Value
  | fail : ParseResult Value
  deriving DecidableEq

namespace ParseResult

def map
    {Value ResultValue : Type}
    (function : Value → ResultValue)
    : ParseResult Value → ParseResult ResultValue
  | ok value rest => ok (function value) rest
  | fail          => fail

def bind
    {Value ResultValue : Type}
    (result : ParseResult Value)
    (function : Value → Bytes → ParseResult ResultValue)
    : ParseResult ResultValue :=
  match result with
  | ok value rest => function value rest
  | fail          => fail

-- Lemmas about ParseResult
@[simp]
theorem map_ok
        {Value ResultValue : Type}
        (function : Value → ResultValue)
        (leftValue : Value)
        (rest : Bytes)
        : map function (ok leftValue rest) = ok (function leftValue) rest :=
  rfl

@[simp]
theorem map_fail
        {Value ResultValue : Type}
        (function : Value → ResultValue)
        : map function (fail : ParseResult Value) = fail :=
  rfl

@[simp]
theorem bind_ok
        {Value ResultValue : Type}
        (leftValue : Value)
        (rest : Bytes)
        (function : Value → Bytes → ParseResult ResultValue)
        : bind (ok leftValue rest) function = function leftValue rest :=
  rfl

@[simp]
theorem bind_fail
        {Value ResultValue : Type}
        (function : Value → Bytes → ParseResult ResultValue)
        : bind (fail : ParseResult Value) function = fail :=
  rfl

end ParseResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX - The verified codec structure
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A Box is a verified bidirectional codec.

Key properties:
- `roundtrip`: parsing what you serialized gives back the original value
- `consumption`: parsing consumes exactly the serialized bytes, leaving extra untouched
-/
structure Box (Value : Type) where
  parse       : Bytes → ParseResult Value
  serialize   : Value → Bytes
  roundtrip   : ∀ a, parse (serialize a) = ParseResult.ok a ByteArray.empty
  consumption : ∀ a extra, parse (serialize a ++ extra) = ParseResult.ok a extra
  --- TODO[b7r6]: !! exhaustion proof not complete !!
  --- missing the CONVERSE / tightness law:
  ---   tight : ∀ bs a rest, parse bs = .ok a rest → bs = serialize a ++ rest
  --- `consumption` only constrains parse on the serialize-image; `tight` is what
  --- rules out attacker bytes outside that image (anti-smuggling). Add as a field
  --- here, then discharge it in every Box instance + combinator below.

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNIT BOX - The trivial case (zero bytes)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The unit box: encodes Unit as zero bytes -/
def unit : Box Unit where
  parse bs := .ok () bs
  serialize _ := ByteArray.empty
  roundtrip := by
    intro unitValue
    -- parse (serialize ()) = parse ByteArray.empty = .ok () ByteArray.empty
    rfl
  consumption := by
    intro unitValue extra
    -- parse (serialize () ++ extra) = parse (ByteArray.empty ++ extra) = parse extra = .ok () extra
    simp [ByteArray.empty_append]

-- ═══════════════════════════════════════════════════════════════════════════════
-- U8 BOX - Single byte
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse a single byte -/
def parseU8 (bytes : Bytes) : ParseResult UInt8 :=
  if h : bytes.size > 0 then .ok bytes[0] (bytes.extract 1 bytes.size) else .fail

/-- Serialize a single byte -/
def serializeU8 (value : UInt8) : Bytes := [value].toByteArray

-- Key lemma: size of a singleton ByteArray
theorem singleton_size (value : UInt8) : [value].toByteArray.size = 1 := by
  simp [List.size_toByteArray]

-- Key lemma: getting element 0 of singleton
theorem singleton_getElem (value : UInt8) : [value].toByteArray[0]'(by simp) = value := by simp

-- Key lemma: extracting from position 1 of a size-1 array gives empty
theorem singleton_extract_tail
        (value : UInt8)
        : [value].toByteArray.extract 1 [value].toByteArray.size = ByteArray.empty := by simp

/-- Single byte box with verified roundtrip -/
def u8 : Box UInt8 where
  parse := parseU8
  serialize := serializeU8
  roundtrip := by
    intro value
    simp only [parseU8, serializeU8]
    -- Need to show: if h : [v].toByteArray.size > 0 then ...
    have hsize : [value].toByteArray.size > 0 := by simp
    simp only [hsize, ↓reduceDIte]
    -- Show equality by showing both components match
    have hval : [value].toByteArray[0]'hsize = value := by simp
    have hrest :
        [value].toByteArray.extract 1 [value].toByteArray.size = ByteArray.empty := by
      simp
    simp only [hval, hrest]
  consumption := by
    intro value extra
    simp only [parseU8, serializeU8]
    -- Size of [v].toByteArray ++ extra > 0
    have hsize : ([value].toByteArray ++ extra).size > 0 := by
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons, List.length_nil]
      omega
    simp only [hsize, ↓reduceDIte]
    -- Show value component: ([v].toByteArray ++ extra)[0] = v
    have hval : ([value].toByteArray ++ extra)[0]'hsize = value := by
      have index0InBounds : (0 : Nat) < [value].toByteArray.size := by simp
      rw [ByteArray.getElem_append_left index0InBounds]
      simp
    -- Show remaining component: extract 1 (size) = extra
    have hrest :
        ([value].toByteArray ++ extra).extract 1 ([value].toByteArray ++ extra).size = extra := by
      simp only [ByteArray.size_append]
      -- extract 1 (1 + extra.size) from ([v].toByteArray ++ extra)
      -- [v].toByteArray has size 1, so extract from position 1 gives us the second part
      rw [ByteArray.extract_append_eq_right (by simp : 1 = [value].toByteArray.size)]
      simp
    simp only [hval, hrest]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SEQUENCE COMBINATOR
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Sequence two boxes: parse A then B, serialize A then B.
If both A and B have verified roundtrip, so does (A, B).
-/
def seq {Value ResultValue : Type} (boxA : Box Value) (boxB : Box ResultValue) : Box (Value × ResultValue) where
  --- TODO[b7r6]: !! exhaustion proof not complete !!
  --- when `tight` is added to Box, compose it here: boxA.tight then boxB.tight on
  --- the residual. The bind splits bs = serA a ++ (serB b ++ rest) — needs both.
  parse bs :=
    boxA.parse bs |>.bind fun leftValue rest =>
      boxB.parse rest |>.map fun rightValue => (leftValue, rightValue)
  serialize ab := boxA.serialize ab.1 ++ boxB.serialize ab.2
  roundtrip := by
    intro ⟨firstValue, secondValue⟩
    simp only [ParseResult.bind, ParseResult.map]
    -- parse (serA a ++ serB b)
    -- = parseA (serA a ++ serB b) >>= ...
    -- By consumption of A: parseA (serA a ++ serB b) = ok a (serB b)
    rw [boxA.consumption firstValue (boxB.serialize secondValue)]
    -- Simplify the match
    simp only []
    -- Now: parseB (serB b) = ok b empty
    rw [boxB.roundtrip secondValue]
  consumption := by
    intro ⟨firstValue, secondValue⟩ extra
    simp only [ParseResult.bind, ParseResult.map]
    -- parse ((serA a ++ serB b) ++ extra)
    -- = parseA ((serA a ++ serB b) ++ extra) >>= ...
    -- Rewrite: (serA a ++ serB b) ++ extra = serA a ++ (serB b ++ extra)
    rw [ByteArray.append_assoc]
    -- By consumption of A: parseA (serA a ++ (serB b ++ extra)) = ok a (serB b ++ extra)
    rw [boxA.consumption firstValue (boxB.serialize secondValue ++ extra)]
    -- Simplify the match
    simp only []
    -- By consumption of B: parseB (serB b ++ extra) = ok b extra
    rw [boxB.consumption secondValue extra]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ISO COMBINATOR (mapping through isomorphism)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Map a box through an isomorphism.
Given Box Value and bijection f : Value ↔ ResultValue, get Box ResultValue.
-/
def isoBox
    {Value ResultValue : Type}
    (box : Box Value)
    (function : Value → ResultValue)
    (secondFunction : ResultValue → Value)
    (forwardComposition : ∀ b, function (secondFunction b) = b)
    (_reverseComposition : ∀ leftValue, secondFunction (function leftValue) = leftValue)
    : Box ResultValue where
  --- TODO[b7r6]: !! exhaustion proof not complete !!
  --- transport `tight` across the iso: parse = box.parse |>.map f preserves the
  --- residual, so box.tight + `_gf` (g (f a) = a) should give it directly.
  parse bs := box.parse bs |>.map function
  serialize b := box.serialize (secondFunction b)
  roundtrip := by
    intro targetValue
    show
      ParseResult.map function (box.parse (box.serialize (secondFunction targetValue)))
          = ParseResult.ok targetValue ByteArray.empty
    have evidence := box.roundtrip (secondFunction targetValue)
    simp only [evidence, ParseResult.map, forwardComposition]
  consumption := by
    intro targetValue extra
    show
      ParseResult.map function (box.parse (box.serialize (secondFunction targetValue) ++ extra))
          = ParseResult.ok targetValue extra
    have evidence := box.consumption (secondFunction targetValue) extra
    simp only [evidence, ParseResult.map, forwardComposition]

-- ═══════════════════════════════════════════════════════════════════════════════
-- U64LE BOX - 64-bit little-endian using BitVec
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract byte i (0-indexed from LSB) from a 64-bit value using setWidth and shift -/
def extractByte
    (value : BitVec 64)
    (index : Nat)
    (_upperBound : index < 8 := by omega)
    : BitVec 8 :=
  (value >>> (index * 8)).setWidth 8

/-- Combine 8 bytes into a 64-bit value (little-endian) -/
def combineBytes (byte0 byte1 byte2 byte3 byte4 byte5 byte6 byte7 : BitVec 8) : BitVec 64 :=

  -- Little-endian: byte0 is LSB, byte7 is MSB
  -- We build from MSB to LSB using append
  let shiftedByte7 : BitVec 64 := byte7.setWidth 64 <<< 56
  let shiftedByte6 : BitVec 64 := byte6.setWidth 64 <<< 48
  let shiftedByte5 : BitVec 64 := byte5.setWidth 64 <<< 40
  let shiftedByte4 : BitVec 64 := byte4.setWidth 64 <<< 32
  let shiftedByte3 : BitVec 64 := byte3.setWidth 64 <<< 24
  let shiftedByte2 : BitVec 64 := byte2.setWidth 64 <<< 16
  let shiftedByte1 : BitVec 64 := byte1.setWidth 64 <<< 8
  let shiftedByte0 : BitVec 64 := byte0.setWidth 64
  shiftedByte7 ||| shiftedByte6 ||| shiftedByte5 ||| shiftedByte4 ||| shiftedByte3 ||| shiftedByte2
      ||| shiftedByte1
      ||| shiftedByte0

/-- Parse 8 bytes as little-endian u64 -/
def parseU64le (bytes : Bytes) : ParseResult (BitVec 64) :=
  if h : bytes.size ≥ 8 then
    have index0InBounds : 0 < bytes.size := by omega
    have index1InBounds : 1 < bytes.size := by omega
    have index2InBounds : 2 < bytes.size := by omega
    have index3InBounds : 3 < bytes.size := by omega
    have index4InBounds : 4 < bytes.size := by omega
    have index5InBounds : 5 < bytes.size := by omega
    have index6InBounds : 6 < bytes.size := by omega
    have index7InBounds : 7 < bytes.size := by omega
    let byte0 : BitVec 8 := BitVec.ofNat 8 (bytes[0]).toNat
    let byte1 : BitVec 8 := BitVec.ofNat 8 (bytes[1]).toNat
    let byte2 : BitVec 8 := BitVec.ofNat 8 (bytes[2]).toNat
    let byte3 : BitVec 8 := BitVec.ofNat 8 (bytes[3]).toNat
    let byte4 : BitVec 8 := BitVec.ofNat 8 (bytes[4]).toNat
    let byte5 : BitVec 8 := BitVec.ofNat 8 (bytes[5]).toNat
    let byte6 : BitVec 8 := BitVec.ofNat 8 (bytes[6]).toNat
    let byte7 : BitVec 8 := BitVec.ofNat 8 (bytes[7]).toNat
    .ok (combineBytes byte0 byte1 byte2 byte3 byte4 byte5 byte6 byte7) (bytes.extract 8 bytes.size)
  else
    .fail

/-- Serialize u64 as 8 bytes little-endian -/
def serializeU64le (value : BitVec 64) : Bytes :=
  let byte0 := (extractByte value 0).toNat.toUInt8
  let byte1 := (extractByte value 1).toNat.toUInt8
  let byte2 := (extractByte value 2).toNat.toUInt8
  let byte3 := (extractByte value 3).toNat.toUInt8
  let byte4 := (extractByte value 4).toNat.toUInt8
  let byte5 := (extractByte value 5).toNat.toUInt8
  let byte6 := (extractByte value 6).toNat.toUInt8
  let byte7 := (extractByte value 7).toNat.toUInt8
  [byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7].toByteArray

-- Key lemma: extractByte extracts the correct byte
theorem extractByte_toNat
        (value : BitVec 64)
        (index : Nat)
        (upperBound : index < 8)
        : (extractByte value index upperBound).toNat = (value.toNat >>> (index * 8)) % 256 := by
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

-- Key lemma: size of serialized u64
theorem serializeU64le_size (value : BitVec 64) : (serializeU64le value).size = 8 := by
  simp [serializeU64le, List.size_toByteArray]

-- Helper: List of 8 elements has length 8
theorem list8_length
        {Value : Type}
        (leftValue rightValue cursor decoder element function secondFunction evidence : Value)
        : [leftValue, rightValue, cursor, decoder, element, function, secondFunction, evidence].length
            = 8 :=
  rfl

-- The key inverse: extracting every byte of `v` then recombining reconstructs `v`.
-- `bv_decide` discharges the whole little-endian shuffle; the round-trip rides entirely
-- on this one lemma (no per-byte `combineBytes_extractByte_i` family is needed).
theorem extractBytes_combineBytes
        (value : BitVec 64)
        : combineBytes
          (extractByte value 0)
          (extractByte value 1)
          (extractByte value 2)
          (extractByte value 3)
          (extractByte value 4)
          (extractByte value 5)
          (extractByte value 6)
          (extractByte value 7)
            = value := by
  simp only [extractByte, combineBytes]

  -- Simplify the remaining goal.
  bv_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- U64LE BOX (complete with proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Helper: UInt8 ↔ BitVec 8 roundtrip
theorem uint8_IsLt (value : UInt8) : value.toNat < 256 := by
  unfold UInt8.toNat

  -- Close the remaining goal.
  exact value.toBitVec.isLt

theorem bitvec8_IsLt (rightValue : BitVec 8) : rightValue.toNat < 256 := rightValue.isLt

-- Key: BitVec.ofNat 8 (x.toNat) where x : UInt8 preserves the value
theorem ofNat8_uint8_toNat (value : UInt8) : (BitVec.ofNat 8 value.toNat).toNat = value.toNat := by
  simp only [BitVec.toNat_ofNat]

  -- Close the remaining goal.
  exact Nat.mod_eq_of_lt (uint8_IsLt value)

-- Key: extractByte then toUInt8 then back to BitVec = extractByte
theorem extractByte_uint8_roundtrip
        (value : BitVec 64)
        (index : Nat)
        (upperBound : index < 8)
        : BitVec.ofNat 8 ((extractByte value index upperBound).toNat.toUInt8.toNat)
            = extractByte value index upperBound := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hlt : (extractByte value index upperBound).toNat < 256 := bitvec8_IsLt _
  -- toUInt8.toNat of a value < 256 is identity
  have index1InBounds : (extractByte value index upperBound).toNat.toUInt8.toNat = (extractByte value index upperBound).toNat := by
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [index1InBounds]
  exact Nat.mod_eq_of_lt hlt

-- The big theorem: parsing serialized bytes reconstructs the original value
theorem parseU64le_serializeU64le
        (value : BitVec 64)
        : parseU64le (serializeU64le value) = ParseResult.ok value ByteArray.empty := by
  have hsize : (serializeU64le value).size ≥ 8 := by simp [serializeU64le_size]
  have hextract : (serializeU64le value).extract 8 (serializeU64le value).size = ByteArray.empty := by
    simp [serializeU64le_size]
  simp only [parseU64le, hsize, ↓reduceDIte, hextract]
  congr 1
  simp only [serializeU64le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte_uint8_roundtrip]
  exact extractBytes_combineBytes value

-- Consumption: parsing serialized bytes ++ extra leaves extra
theorem parseU64le_serializeU64le_append
        (value : BitVec 64)
        (extra : Bytes)
        : parseU64le (serializeU64le value ++ extra) = ParseResult.ok value extra := by
  have hsize : (serializeU64le value ++ extra).size ≥ 8 := by
    simp [ByteArray.size_append, serializeU64le_size]
  have hextract : (serializeU64le value ++ extra).extract 8 (serializeU64le value ++ extra).size = extra := by
    have nextIndexEvidence : (serializeU64le value ++ extra).size = (serializeU64le value).size + extra.size := by
      simp [ByteArray.size_append]
    rw [nextIndexEvidence, ByteArray.extract_append_eq_right (serializeU64le_size value).symm rfl]
  simp only [parseU64le, hsize, ↓reduceDIte, hextract]
  congr 1
  -- Strip the `++ extra` with `serializeU64le` folded (bounds pre-supplied), THEN unfold
  -- and reduce — keeps the byte list out of the whnf.
  have bytesEvidence : ∀ i : Nat, i < 8 → i < (serializeU64le value).size := fun _ inputBound => by
    rwa [serializeU64le_size]
  simp only [ByteArray.getElem_append_left (bytesEvidence 0 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 1 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 2 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 3 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 4 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 5 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 6 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 7 (by omega))]
  simp only [serializeU64le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte_uint8_roundtrip]
  exact extractBytes_combineBytes value

/-- The verified u64le box -/
def u64leBitVec : Box (BitVec 64) where
  parse := parseU64le
  serialize := serializeU64le
  roundtrip := parseU64le_serializeU64le
  consumption := parseU64le_serializeU64le_append

-- ═══════════════════════════════════════════════════════════════════════════════
-- U32LE BOX (32-bit little-endian, for Protobuf fixed32)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract byte i from a 32-bit value (little-endian) -/
def extractByte32 (value : BitVec 32) (index : Nat) (_ : index < 4 := by omega) : BitVec 8 :=
  (value >>> (index * 8)).setWidth 8

/-- Combine 4 bytes into a 32-bit value (little-endian) -/
def combineBytes32 (byte0 byte1 byte2 byte3 : BitVec 8) : BitVec 32 :=
  byte0.setWidth 32 ||| (byte1.setWidth 32 <<< 8) ||| (byte2.setWidth 32 <<< 16)
      ||| (byte3.setWidth 32 <<< 24)

/-- Serialize a 32-bit value to 4 bytes -/
def serializeU32le (value : BitVec 32) : Bytes :=
  let byte0 : UInt8 := (extractByte32 value 0).toNat.toUInt8
  let byte1 : UInt8 := (extractByte32 value 1).toNat.toUInt8
  let byte2 : UInt8 := (extractByte32 value 2).toNat.toUInt8
  let byte3 : UInt8 := (extractByte32 value 3).toNat.toUInt8
  [byte0, byte1, byte2, byte3].toByteArray

/-- Parse 4 bytes as a 32-bit value -/
def parseU32le (bytes : Bytes) : ParseResult (BitVec 32) :=
  if h : bytes.size ≥ 4 then
    let byte0 := BitVec.ofNat 8 bytes[0].toNat
    let byte1 := BitVec.ofNat 8 bytes[1].toNat
    let byte2 := BitVec.ofNat 8 bytes[2].toNat
    let byte3 := BitVec.ofNat 8 bytes[3].toNat
    .ok (combineBytes32 byte0 byte1 byte2 byte3) (bytes.extract 4 bytes.size)
  else
    .fail

@[simp]
theorem serializeU32le_size (value : BitVec 32) : (serializeU32le value).size = 4 := by
  simp [serializeU32le, List.size_toByteArray]

-- The key inverse: extract every byte then recombine reconstructs `v` (bv_decide).
theorem extractBytes32_combineBytes
        (value : BitVec 32)
        : combineBytes32
          (extractByte32 value 0)
          (extractByte32 value 1)
          (extractByte32 value 2)
          (extractByte32 value 3)
            = value := by
  simp only [extractByte32, combineBytes32]

  -- Simplify the remaining goal.
  bv_decide

-- UInt8 roundtrip for 32-bit
theorem extractByte32_uint8_roundtrip
        (value : BitVec 32)
        (index : Nat)
        (upperBound : index < 4)
        : BitVec.ofNat 8 ((extractByte32 value index upperBound).toNat.toUInt8.toNat)
            = extractByte32 value index upperBound := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hlt : (extractByte32 value index upperBound).toNat < 256 := bitvec8_IsLt _
  have index1InBounds : (extractByte32 value index upperBound).toNat.toUInt8.toNat = (extractByte32 value index upperBound).toNat := by
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [index1InBounds]
  exact Nat.mod_eq_of_lt hlt

-- Main roundtrip theorem
theorem parseU32le_serializeU32le
        (value : BitVec 32)
        : parseU32le (serializeU32le value) = ParseResult.ok value ByteArray.empty := by
  have hsize : (serializeU32le value).size ≥ 4 := by simp [serializeU32le_size]
  have hextract : (serializeU32le value).extract 4 (serializeU32le value).size = ByteArray.empty := by
    simp [serializeU32le_size]
  simp only [parseU32le, hsize, ↓reduceDIte, hextract]
  congr 1
  simp only [serializeU32le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte32_uint8_roundtrip]
  exact extractBytes32_combineBytes value

-- Consumption theorem
theorem parseU32le_serializeU32le_append
        (value : BitVec 32)
        (extra : Bytes)
        : parseU32le (serializeU32le value ++ extra) = ParseResult.ok value extra := by
  have hsize : (serializeU32le value ++ extra).size ≥ 4 := by
    simp [ByteArray.size_append, serializeU32le_size]
  have hextract : (serializeU32le value ++ extra).extract 4 (serializeU32le value ++ extra).size = extra := by
    have nextIndexEvidence : (serializeU32le value ++ extra).size = (serializeU32le value).size + extra.size := by
      simp [ByteArray.size_append]
    rw [nextIndexEvidence, ByteArray.extract_append_eq_right (serializeU32le_size value).symm rfl]
  simp only [parseU32le, hsize, ↓reduceDIte, hextract]
  congr 1
  have bytesEvidence : ∀ i : Nat, i < 4 → i < (serializeU32le value).size := fun _ inputBound => by
    rwa [serializeU32le_size]
  simp only [ByteArray.getElem_append_left (bytesEvidence 0 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 1 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 2 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 3 (by omega))]
  simp only [serializeU32le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte32_uint8_roundtrip]
  exact extractBytes32_combineBytes value

/-- The verified u32le box -/
def u32leBitVec : Box (BitVec 32) where
  parse := parseU32le
  serialize := serializeU32le
  roundtrip := parseU32le_serializeU32le
  consumption := parseU32le_serializeU32le_append

-- ═══════════════════════════════════════════════════════════════════════════════
-- U16LE BOX (16-bit little-endian — vsock `type`/`op`, and many wire u16 fields)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract byte i from a 16-bit value (little-endian) -/
def extractByte16 (value : BitVec 16) (index : Nat) (_ : index < 2 := by omega) : BitVec 8 :=
  (value >>> (index * 8)).setWidth 8

/-- Combine 2 bytes into a 16-bit value (little-endian) -/
def combineBytes16 (byte0 byte1 : BitVec 8) : BitVec 16 :=
  byte0.setWidth 16 ||| (byte1.setWidth 16 <<< 8)

/-- Serialize a 16-bit value to 2 bytes -/
def serializeU16le (value : BitVec 16) : Bytes :=
  let byte0 : UInt8 := (extractByte16 value 0).toNat.toUInt8
  let byte1 : UInt8 := (extractByte16 value 1).toNat.toUInt8
  [byte0, byte1].toByteArray

/-- Parse 2 bytes as a 16-bit value -/
def parseU16le (bytes : Bytes) : ParseResult (BitVec 16) :=
  if h : bytes.size ≥ 2 then
    let byte0 := BitVec.ofNat 8 bytes[0].toNat
    let byte1 := BitVec.ofNat 8 bytes[1].toNat
    .ok (combineBytes16 byte0 byte1) (bytes.extract 2 bytes.size)
  else
    .fail

@[simp]
theorem serializeU16le_size (value : BitVec 16) : (serializeU16le value).size = 2 := by
  simp [serializeU16le, List.size_toByteArray]

-- The key inverse: extract every byte then recombine reconstructs `v` (bv_decide).
theorem extractBytes16_combineBytes
        (value : BitVec 16)
        : combineBytes16 (extractByte16 value 0) (extractByte16 value 1) = value := by
  simp only [extractByte16, combineBytes16]

  -- Simplify the remaining goal.
  bv_decide

-- UInt8 roundtrip for 16-bit
theorem extractByte16_uint8_roundtrip
        (value : BitVec 16)
        (index : Nat)
        (upperBound : index < 2)
        : BitVec.ofNat 8 ((extractByte16 value index upperBound).toNat.toUInt8.toNat)
            = extractByte16 value index upperBound := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hlt : (extractByte16 value index upperBound).toNat < 256 := bitvec8_IsLt _
  have index1InBounds : (extractByte16 value index upperBound).toNat.toUInt8.toNat = (extractByte16 value index upperBound).toNat := by
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [index1InBounds]
  exact Nat.mod_eq_of_lt hlt

-- Main roundtrip theorem
theorem parseU16le_serializeU16le
        (value : BitVec 16)
        : parseU16le (serializeU16le value) = ParseResult.ok value ByteArray.empty := by
  have hsize : (serializeU16le value).size ≥ 2 := by simp [serializeU16le_size]
  have hextract : (serializeU16le value).extract 2 (serializeU16le value).size = ByteArray.empty := by
    simp [serializeU16le_size]
  simp only [parseU16le, hsize, ↓reduceDIte, hextract]
  congr 1
  simp only [serializeU16le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte16_uint8_roundtrip]
  exact extractBytes16_combineBytes value

-- Consumption theorem
theorem parseU16le_serializeU16le_append
        (value : BitVec 16)
        (extra : Bytes)
        : parseU16le (serializeU16le value ++ extra) = ParseResult.ok value extra := by
  have hsize : (serializeU16le value ++ extra).size ≥ 2 := by
    simp [ByteArray.size_append, serializeU16le_size]
  have hextract : (serializeU16le value ++ extra).extract 2 (serializeU16le value ++ extra).size = extra := by
    have nextIndexEvidence : (serializeU16le value ++ extra).size = (serializeU16le value).size + extra.size := by
      simp [ByteArray.size_append]
    rw [nextIndexEvidence, ByteArray.extract_append_eq_right (serializeU16le_size value).symm rfl]
  simp only [parseU16le, hsize, ↓reduceDIte, hextract]
  congr 1
  have bytesEvidence : ∀ i : Nat, i < 2 → i < (serializeU16le value).size := fun _ inputBound => by
    rwa [serializeU16le_size]
  simp only [ByteArray.getElem_append_left (bytesEvidence 0 (by omega)),
    ByteArray.getElem_append_left (bytesEvidence 1 (by omega))]
  simp only [serializeU16le, List.getElem_toByteArray, List.getElem_cons_zero,
    List.getElem_cons_succ, extractByte16_uint8_roundtrip]
  exact extractBytes16_combineBytes value

/-- The verified u16le box -/
def u16leBitVec : Box (BitVec 16) where
  parse := parseU16le
  serialize := serializeU16le
  roundtrip := parseU16le_serializeU16le
  consumption := parseU16le_serializeU16le_append

-- ═══════════════════════════════════════════════════════════════════════════════
-- DERIVED BOXES (built from primitives)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two bytes (u8, u8) -/
def u8pair : Box (UInt8 × UInt8) := seq u8 u8

/-- Three bytes -/
def u8triple : Box ((UInt8 × UInt8) × UInt8) := seq u8pair u8

/-- Four bytes -/
def u8quad : Box (((UInt8 × UInt8) × UInt8) × UInt8) := seq u8triple u8

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXAMPLE: Using isoBox to create a wrapped type
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A wrapper type for demonstration -/
structure wrapped_byte where
  val : UInt8
  deriving DecidableEq

/-- Box for WrappedByte -/
def wrappedByte : Box wrapped_byte :=
  isoBox u8 wrapped_byte.mk wrapped_byte.val (fun _ => rfl) (fun ⟨_⟩ => rfl)

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATISTICS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Verification Status

### Fully Verified Boxes (0 sorry):

| Box/Combinator | Roundtrip | Consumption | Status |
|----------------|-----------|-------------|--------|
| unit           | ✓ proven  | ✓ proven    | DONE   |
| u8             | ✓ proven  | ✓ proven    | DONE   |
| u32leBitVec    | ✓ proven  | ✓ proven    | DONE   |
| u64leBitVec    | ✓ proven  | ✓ proven    | DONE   |
| seq            | ✓ proven  | ✓ proven    | DONE   |
| isoBox         | ✓ proven  | ✓ proven    | DONE   |

### BitVec Lemmas (bv_decide, 0 sorry):

| Lemma | What's Proven |
|-------|---------------|
| extractBytes_combineBytes | combine(extractByte(v, 0..7)) = v |
| extractBytes32_combineBytes | combine32(extractByte32(v, 0..3)) = v |
| parseU64le_serializeU64le | parse(serialize(v)) = ok v empty |
| parseU32le_serializeU32le | parse(serialize(v)) = ok v empty |

### Derived (compositionally verified):

| Box | Built From |
|-----|------------|
| u8pair | seq u8 u8 |
| u8triple | seq u8pair u8 |
| u8quad | seq u8triple u8 |
| wrappedByte | isoBox u8 |
| u64le (UInt64) | isoBox u64leBitVec (via Basic.lean) |
| u32le (UInt32) | isoBox u32leBitVec (via Basic.lean) |
| bool64 | isoBox u64leBitVec (via Basic.lean) |

**Total: 6 primitive boxes, all round-trips machine-checked, 0 sorry.**
**Compositionally: infinite verified boxes constructible**
-/

end Continuity.Codec.Core
