/-
  Continuity.Codec.Core.Framing - generic length-prefixed frame engine

  Frame / LengthCodec / BoundedFrame and the verified boundedFrameBox, plus
  multi-frame parsing. Protocol-agnostic; concrete length codecs (Git pkt-line,
  Nix daemon) live in their Wire families.
-/

import continuity.codec.core.basic
import Std.Tactic.BVDecide

namespace Continuity.Codec.Core.Framing

open Continuity.Codec.Core

-- GENERIC FRAME
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A frame is length + payload. The length encoding varies by protocol. -/
@[ext]
structure Frame where
  payload : Bytes
  deriving Repr, DecidableEq

/-- Flush/terminator frame (empty payload, special encoding) -/
def Frame.flush : Frame := ⟨Bytes.empty⟩

def Frame.isFlush (function : Frame) : Bool := function.payload.size == 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- LENGTH ENCODING STRATEGIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- How to encode/decode the length prefix -/
structure LengthCodec where
  /-- Size of the length field in bytes (0 for variable-length) -/
  fixedSize : Nat
  /-- Maximum payload size (for bounds checking) -/
  maxPayload : Nat
  /-- Encode a length to bytes -/
  encode : Nat → Bytes
  /-- Decode length from bytes, returns (length, bytes consumed) or none -/
  decode : Bytes → Option (Nat × Nat)
  /-- Proof: decode (encode n) = some (n, fixedSize) for valid n -/
  roundtrip : ∀ n, n ≤ maxPayload → decode (encode n) = some (n, fixedSize)
  /-- Proof: encoded length has exactly fixedSize bytes -/
  encode_size : ∀ n, (encode n).size = fixedSize
  /-- Proof: decode works correctly with appended extra bytes -/
  decode_append : ∀ n extra, n ≤ maxPayload → decode (encode n ++ extra) = some (n, fixedSize)

/-- A frame bounded by a codec's maxPayload -/
structure BoundedFrame (codec : LengthCodec) where
  frame : Frame
  bound : frame.payload.size ≤ codec.maxPayload

/-- Create bounded frame from frame with proof -/
def Frame.bounded
    (codec : LengthCodec)
    (function : Frame)
    (evidence : function.payload.size ≤ codec.maxPayload)
    : BoundedFrame codec :=
  ⟨function, evidence⟩

/-- Bounded flush frame -/
def BoundedFrame.flush (codec : LengthCodec) : BoundedFrame codec :=
  ⟨Frame.flush, by simp only [Frame.flush, Bytes.empty, ByteArray.size_empty]; omega⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERIC FRAME BOX
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse a frame using the given length codec (partial - may fail for large payloads) -/
def parseFrame (codec : LengthCodec) (bytes : Bytes) : ParseResult Frame :=
  match codec.decode bytes with
  | none => .fail
  | some (len, headerSize) =>
    if len == 0 then
      .ok Frame.flush (bytes.extract headerSize bytes.size)
    else if _h : bytes.size >= headerSize + len then
      let payload := bytes.extract headerSize (headerSize + len)
      let rest := bytes.extract (headerSize + len) bytes.size
      .ok ⟨payload⟩ rest
    else
      .fail

/-- Serialize a frame using the given length codec -/
def serializeFrame (codec : LengthCodec) (function : Frame) : Bytes :=
  if function.isFlush then
    codec.encode 0
  else
    codec.encode function.payload.size ++ function.payload

/-- Parse a bounded frame -/
def parseBoundedFrame (codec : LengthCodec) (bytes : Bytes) : ParseResult (BoundedFrame codec) :=
  match codec.decode bytes with
  | none => .fail
  | some (len, headerSize) =>
    if hlen : len == 0 then
      .ok (BoundedFrame.flush codec) (bytes.extract headerSize bytes.size)
    else if hbound : len ≤ codec.maxPayload then
      if h : bytes.size >= headerSize + len then
        let payload := bytes.extract headerSize (headerSize + len)
        let rest := bytes.extract (headerSize + len) bytes.size
        -- Need to prove payload.size ≤ maxPayload
        have hpayload_size : payload.size = len := by
          rw [ByteArray.size_extract]
          have hle : headerSize + len ≤ bytes.size := h
          rw [Nat.min_eq_left hle]
          omega
        .ok ⟨⟨payload⟩, by simp only [hpayload_size]; exact hbound⟩ rest
      else
        .fail
    else
      .fail -- Reject frames that exceed maxPayload

/-- Serialize a bounded frame -/
def serializeBoundedFrame (codec : LengthCodec) (bufferEvidence : BoundedFrame codec) : Bytes :=
  serializeFrame codec bufferEvidence.frame

/-- ByteArray.extract from 0 to size is identity -/
theorem ByteArray.extract_full (bytes : ByteArray) : bytes.extract 0 bytes.size = bytes := by
  apply ByteArray.ext

  -- Simplify the remaining goal.
  simp

/-- ByteArray.extract of empty range gives empty -/
theorem ByteArray.extract_empty
        (bytes : ByteArray)
        (index : Nat)
        (_indexBound : index ≤ bytes.size)
        : bytes.extract index index = ByteArray.empty := by
  apply ByteArray.ext

  -- Simplify the remaining goal.
  simp

/-- Extract starting from 0 is self when end >= size -/
theorem ByteArray.extract_eq_self_of_ge
        (bytes : ByteArray)
        (element : Nat)
        (evidence : element >= bytes.size)
        : bytes.extract 0 element = bytes := by
  apply ByteArray.ext
  unfold ByteArray.extract ByteArray.copySlice
  simp only [Nat.sub_zero, ByteArray.empty, Nat.zero_add, Nat.sub_zero]
  have hempty : (ByteArray.emptyWithCapacity 0).data = #[] := rfl
  rw [hempty]
  have firstEvidence : (#[] : Array UInt8).extract 0 0 = #[] := rfl
  have secondEvidence : (#[] : Array UInt8).extract (min element bytes.data.size) = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    simp only [Array.size_extract, Array.size_empty, Nat.min_zero, Nat.zero_sub]
  rw [firstEvidence, secondEvidence]
  simp only [Array.empty_append, Array.append_empty]
  have hdata : bytes.size = bytes.data.size := rfl
  have sizeBound : element >= bytes.data.size := by rw [← hdata]; exact evidence
  have hextr : bytes.data.extract 0 element = bytes.data.extract 0 bytes.data.size := by
    rw [Array.ext_iff]
    constructor
    · simp only [Array.size_extract, Nat.min_eq_right sizeBound, Nat.min_self, Nat.sub_zero]
    · intro index hi1 hi2
      simp only [Array.getElem_extract]
  rw [hextr, Array.extract_size]

/-- Extract first a.size bytes from (a ++ b) gives a -/
theorem ByteArray.extract_append_left
        (leftValue rightValue : ByteArray)
        : (leftValue ++ rightValue).extract 0 leftValue.size = leftValue := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [Array.ext_iff]
  have hle : leftValue.data.size ≤ leftValue.data.size + rightValue.data.size :=
    Nat.le_add_right _ _
  constructor
  · simp only [Array.size_extract, Array.size_append]
    exact Nat.min_eq_left hle
  · intro index hi1 hi2
    simp only [Array.getElem_extract, Nat.zero_add]
    exact Array.getElem_append_left hi2

/-- Extract from (a ++ b) when range is entirely within a equals extract from a -/
theorem ByteArray.extract_append_left_of_le
        (leftValue rightValue : ByteArray)
        (index nextIndex : Nat)
        (nextIndexEvidence : nextIndex ≤ leftValue.size)
        : (leftValue ++ rightValue).extract index nextIndex = leftValue.extract index nextIndex := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [Array.ext_iff]
  have leftSizeBound : nextIndex ≤ leftValue.data.size := nextIndexEvidence
  have hle : leftValue.data.size ≤ leftValue.data.size + rightValue.data.size :=
    Nat.le_add_right _ _
  have hjab : nextIndex ≤ leftValue.data.size + rightValue.data.size :=
    Nat.le_trans leftSizeBound hle
  constructor
  · simp only [Array.size_extract, Array.size_append]
    have firstEvidence : min nextIndex (leftValue.data.size + rightValue.data.size) = nextIndex :=
      Nat.min_eq_left hjab
    have secondEvidence : min nextIndex leftValue.data.size = nextIndex :=
      Nat.min_eq_left leftSizeBound
    omega
  · intro offset hk1 hk2
    simp only [Array.getElem_extract]
    have hik_lt : index + offset < leftValue.data.size := by
      have hk_bound : offset < nextIndex - index := by
        simp only [Array.size_extract, Array.size_append] at hk1
        have firstEvidence : min nextIndex (leftValue.data.size + rightValue.data.size) = nextIndex :=
          Nat.min_eq_left hjab
        omega
      have : index + offset < nextIndex := by omega
      omega
    rw [Array.getElem_append_left (by exact hik_lt)]

private
theorem boundedFrameRoundtrip
        (codec : LengthCodec)
        (bufferEvidence : BoundedFrame codec)
        : parseBoundedFrame codec (serializeBoundedFrame codec bufferEvidence)
            = .ok bufferEvidence ByteArray.empty := by
  unfold parseBoundedFrame serializeBoundedFrame serializeFrame
  cases hflush : bufferEvidence.frame.isFlush
  case false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hpayload := bufferEvidence.bound
    have hdec :=
      codec.decode_append bufferEvidence.frame.payload.size bufferEvidence.frame.payload hpayload
    simp only [hdec]
    have hne : bufferEvidence.frame.payload.size ≠ 0 := by
      simp only [Frame.isFlush] at hflush
      intro heq
      simp only [heq, beq_self_eq_true] at hflush
      exact Bool.noConfusion hflush
    have hne_beq : (bufferEvidence.frame.payload.size == 0) = false := beq_eq_false_iff_ne.mpr hne
    simp only [hne_beq]
    simp only [hpayload, dite_true]
    have hencsize := codec.encode_size bufferEvidence.frame.payload.size
    have hge :
        (codec.encode bufferEvidence.frame.payload.size ++ bufferEvidence.frame.payload).size
            >= codec.fixedSize + bufferEvidence.frame.payload.size := by
      simp only [ByteArray.size_append, hencsize]; exact Nat.le_refl _
    simp only [hge, dite_true]
    cases bufferEvidence with
    | mk frame bound =>
      simp only [Frame.isFlush] at hflush
      simp only [Bool.false_eq_true, dite_false]
      have hpay :
          (codec.encode frame.payload.size ++ frame.payload).extract
            codec.fixedSize
            (codec.fixedSize + frame.payload.size)
              = frame.payload := by
        rw [ByteArray.extract_append_eq_right hencsize.symm]
        simp only [hencsize]
      simp only [hpay]
      congr 1
      simp only [ByteArray.extract_eq_empty_iff, ByteArray.size_append, hencsize]; omega
  case true =>
    simp only [↓reduceIte]
    have hdec := codec.roundtrip 0 (by omega : 0 ≤ codec.maxPayload)
    simp only [hdec, beq_self_eq_true, dite_true]
    have hsize := codec.encode_size 0
    congr 1
    · simp only [Frame.isFlush, beq_iff_eq, ByteArray.size_eq_zero_iff] at hflush
      cases bufferEvidence with
      | mk frame bound =>
        simp only at hflush
        simp only [BoundedFrame.flush, Frame.flush, Bytes.empty]
        congr 1
        exact Frame.ext hflush.symm
    · simp only [ByteArray.extract_eq_empty_iff, hsize]
      omega

private
theorem extractFramedPayload
        (codec : LengthCodec)
        (payload extra : Bytes)
        : ((codec.encode payload.size ++ payload) ++ extra).extract
          codec.fixedSize
          (codec.fixedSize + payload.size)
            = payload := by
  have encodedSize := codec.encode_size payload.size
  have stop : codec.fixedSize + payload.size ≤ (codec.encode payload.size ++ payload).size := by
    simp only [ByteArray.size_append, encodedSize]
    exact Nat.le_refl _
  rw [ByteArray.extract_append_left_of_le _ extra _ _ stop]
  rw [ByteArray.extract_append_eq_right encodedSize.symm]
  simp only [encodedSize]

private
theorem extractFramedRest
        (codec : LengthCodec)
        (payload extra : Bytes)
        : ((codec.encode payload.size ++ payload) ++ extra).extract
          (codec.fixedSize + payload.size)
          ((codec.encode payload.size ++ payload) ++ extra).size
            = extra := by
  have encodedSize := codec.encode_size payload.size
  have frameSize : codec.fixedSize + payload.size = (codec.encode payload.size ++ payload).size := by
    simp only [ByteArray.size_append, encodedSize]
  have totalSize :
      ((codec.encode payload.size ++ payload) ++ extra).size
          = (codec.encode payload.size ++ payload).size + extra.size := by
    simp only [ByteArray.size_append]
  rw [ByteArray.extract_append_eq_right frameSize totalSize]

private
theorem boundedFrameConsumption
        (codec : LengthCodec)
        (bufferEvidence : BoundedFrame codec)
        (extra : Bytes)
        : parseBoundedFrame codec (serializeBoundedFrame codec bufferEvidence ++ extra)
            = .ok bufferEvidence extra := by
  simp only [parseBoundedFrame, serializeBoundedFrame, serializeFrame]
  by_cases hflush : bufferEvidence.frame.isFlush
  · simp only [hflush, ↓reduceIte]
    have hdec := codec.decode_append 0 extra (by omega)
    simp only [hdec]
    simp only [beq_self_eq_true, dite_true]
    congr 1
    · simp only [Frame.isFlush, beq_iff_eq, ByteArray.size_eq_zero_iff] at hflush
      cases bufferEvidence with
      | mk frame bound =>
        simp only at hflush
        simp only [BoundedFrame.flush, Frame.flush, Bytes.empty]
        congr 1
        exact Frame.ext hflush.symm
    · have hencsize := codec.encode_size 0
      have upperBound : codec.fixedSize = (codec.encode 0).size := hencsize.symm
      have nextIndexEvidence : (codec.encode 0 ++ extra).size = (codec.encode 0).size + extra.size := by
        simp only [ByteArray.size_append]
      rw [ByteArray.extract_append_eq_right upperBound nextIndexEvidence]
  · simp only [if_neg hflush]
    have hpayload := bufferEvidence.bound
    have hencsize := codec.encode_size bufferEvidence.frame.payload.size
    have hep_size :
        (codec.encode bufferEvidence.frame.payload.size ++ bufferEvidence.frame.payload).size
            = codec.fixedSize + bufferEvidence.frame.payload.size := by
      simp only [ByteArray.size_append, hencsize]
    simp only [ByteArray.append_assoc]
    have hdec :=
      codec.decode_append
        bufferEvidence.frame.payload.size
        (bufferEvidence.frame.payload ++ extra)
        hpayload
    rw [hdec]
    simp only []
    have hne : bufferEvidence.frame.payload.size ≠ 0 := by
      simp only [Frame.isFlush, beq_iff_eq, ByteArray.size_eq_zero_iff] at hflush
      intro heq
      exact hflush (ByteArray.size_eq_zero_iff.mp heq)
    have hne_eq_true : ¬((bufferEvidence.frame.payload.size == 0) = true) := by
      intro sizeZero
      rw [beq_iff_eq] at sizeZero
      exact hne sizeZero
    rw [dif_neg hne_eq_true]
    rw [dif_pos hpayload]
    have hge :
        (codec.encode bufferEvidence.frame.payload.size ++ (bufferEvidence.frame.payload ++ extra)).size
            >= codec.fixedSize + bufferEvidence.frame.payload.size := by
      simp only [ByteArray.size_append, hencsize]; omega
    rw [dif_pos hge]
    simp only [ByteArray.append_assoc.symm]
    congr 1
    · cases bufferEvidence with
      | mk frame bound => simp only [extractFramedPayload]
    · exact extractFramedRest codec bufferEvidence.frame.payload extra

/-- Bounded frame box for a given length codec. -/
def boundedFrameBox (codec : LengthCodec) : Box (BoundedFrame codec) where
  parse := parseBoundedFrame codec
  serialize := serializeBoundedFrame codec
  roundtrip := boundedFrameRoundtrip codec
  consumption := boundedFrameConsumption codec

-- ═══════════════════════════════════════════════════════════════════════════════
-- MULTI-FRAME PARSING (parse until flush)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse frames until flush packet, returns (frames, remaining bytes) -/
partial
def parseUntilFlush
    (codec : LengthCodec)
    (bytes : Bytes)
    (framesRev : List Frame)
    : Option (List Frame × Bytes) :=
  match parseFrame codec bytes with
  | .fail => none
  | .ok frame rest =>
    if frame.isFlush then
      some (framesRev.reverse, rest)
    else
      parseUntilFlush codec rest (frame :: framesRev)

/-- Serialize frames with trailing flush -/
def serializeWithFlush (codec : LengthCodec) (frames : List Frame) : Bytes :=
  let serialized := frames.map (serializeFrame codec)
  let body := serialized.foldl (· ++ ·) Bytes.empty
  body ++ serializeFrame codec Frame.flush

end Continuity.Codec.Core.Framing
