import continuity.codec.core.box
import continuity.codec.core.basic
import Std.Tactic.BVDecide

open Continuity.Codec.Core
open Continuity.Codec.Core
namespace Continuity.Codec.Core.Varint

theorem nat_shr7_lt (count : Nat) (evidence : count ≥ 128) : count >>> 7 < count := by omega

theorem uint64_shr7_lt
        (value : UInt64)
        (evidence : ¬value < 128)
        : (value >>> 7).toNat < value.toNat := by
  rw [UInt64.toNat_shiftRight]; simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact nat_shr7_lt value.toNat (by simp only [UInt64.not_lt] at evidence; exact evidence)

def svc (value : UInt64) (outputPrefix : ByteArray) : ByteArray :=
  if _h : value < 128 then
    outputPrefix.push value.toUInt8
  else
    svc (value >>> 7) (outputPrefix.push ((value &&& (0x7F : UInt64)) ||| (0x80 : UInt64)).toUInt8)
  termination_by value.toNat
  decreasing_by exact uint64_shr7_lt value _h

def serializeVarint (value : UInt64) : ByteArray := svc value ByteArray.empty

private
theorem push_eq_append
        (bytes : ByteArray)
        (byte : UInt8)
        : bytes.push byte = bytes ++ { data := #[byte] } := by apply ByteArray.ext; simp

theorem svc_acc
        (value : UInt64)
        (outputPrefix : ByteArray)
        : svc value outputPrefix = outputPrefix ++ svc value ByteArray.empty := by
  rw [svc.eq_1 value outputPrefix, svc.eq_1 value ByteArray.empty]; by_cases is_single_byte : value < 128
  · simp only [is_single_byte, ↓reduceDIte, push_eq_append, ByteArray.empty_append]
  · simp only [is_single_byte, ↓reduceDIte]
    rw [svc_acc (value>>>7) (outputPrefix.push _), svc_acc (value>>>7) (ByteArray.empty.push _)]
    rw [push_eq_append outputPrefix, push_eq_append ByteArray.empty]
    simp [ByteArray.append_assoc, ByteArray.empty_append]

termination_by value.toNat
decreasing_by all_goals { rw [UInt64.toNat_shiftRight]; simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; exact nat_shr7_lt _ (by simp only [UInt64.not_lt] at is_single_byte; exact is_single_byte) }

def pvt
    (bytes : ByteArray)
    (decodedValue : UInt64)
    (shift : UInt64)
    (fuel : Nat)
    : ParseResult UInt64 :=
  match fuel with
  | 0 => .fail
  | fuel' + 1 =>
    if h : bytes.size > 0 then
      let byte : UInt8 := bytes[0]'(by omega)
      let nextValue : UInt64 := decodedValue ||| ((byte.toUInt64 &&& 0x7F) <<< shift)
      if byte &&& (0x80 : UInt8) == (0 : UInt8) then
        .ok nextValue (bytes.extract 1 bytes.size)
      else
        pvt (bytes.extract 1 bytes.size) nextValue (shift + 7) fuel'
    else
      .fail

def parseVarint (bytes : ByteArray) : ParseResult UInt64 := pvt bytes 0 0 10

set_option maxRecDepth 8192 in
theorem varint_append
        (decodedValue value shift : UInt64)
        (sizeEvidence : shift < 57)
        : (decodedValue ||| ((value &&& 0x7F) <<< shift)) ||| ((value >>> 7) <<< (shift + 7))
            = decodedValue ||| (value <<< shift) := by
  apply UInt64.eq_of_toBitVec_eq; simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_decide

theorem continuation_bit_clear
        (value : UInt64)
        (evidence : value < 128)
        : (value.toUInt8 &&& (0x80 : UInt8) == (0 : UInt8)) = true := by
  simp only [beq_iff_eq]; apply UInt8.eq_of_toBitVec_eq; simp only [UInt8.toBitVec_and, UInt8.toBitVec_ofNat, UInt64.toBitVec_toUInt8]; bv_decide

theorem continuation_bit_set
        (value : UInt64)
        (evidence : ¬value < 128)
        : (((value &&& 0x7F) ||| 0x80).toUInt8 &&& (0x80 : UInt8) == (0 : UInt8)) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro h_eq; have := congrArg UInt8.toBitVec h_eq
  simp only [UInt8.toBitVec_ofNat] at this; revert this; bv_decide

theorem low_seven_bits_roundtrip
        (value : UInt64)
        (evidence : value < 128)
        : (value.toUInt8.toUInt64 &&& (0x7F : UInt64)) = value := by
  apply UInt64.eq_of_toBitVec_eq; simp only [UInt64.toBitVec_and, UInt64.toBitVec_ofNat, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]; bv_decide

theorem shift_by_seven
        (value : UInt64)
        : (((value &&& 0x7F) ||| 0x80).toUInt8.toUInt64 &&& (0x7F : UInt64)) = (value &&& 0x7F) := by
  apply UInt64.eq_of_toBitVec_eq; simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_ofNat, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]; bv_decide

private
def mkB (byte : UInt8) : ByteArray := ⟨#[byte]⟩

private
theorem mksz (byte : UInt8) : (mkB byte).size = 1 := by simp [mkB, ByteArray.size]

private
theorem mkp (byte : UInt8) (result : ByteArray) : (mkB byte ++ result).size > 0 := by
  have := mksz byte; have := @ByteArray.size_append (mkB byte) result; omega

private
theorem mkg
        (byte : UInt8)
        (result : ByteArray)
        : (mkB byte ++ result)[0]'(mkp byte result) = byte := by
  rw [ByteArray.getElem_append_left (hlt := by rw [mksz]; omega)]; rfl

private
theorem mkt
        (byte : UInt8)
        (result : ByteArray)
        : (mkB byte ++ result).extract 1 (mkB byte ++ result).size = result := by
  exact
    ByteArray.extract_append_eq_right
      (mksz byte)
      (by have := @ByteArray.size_append (mkB byte) result; have := mksz byte; omega)

private
theorem svc_lt
        (value : UInt64)
        (evidence : value < 128)
        : svc value ByteArray.empty = mkB value.toUInt8 := by
  rw [svc.eq_1]; simp only [evidence, ↓reduceDIte, push_eq_append, ByteArray.empty_append, mkB]

private
theorem svc_ge
        (value : UInt64)
        (evidence : ¬value < 128)
        : svc value ByteArray.empty
            = mkB ((value &&& 0x7F) ||| 0x80).toUInt8 ++ svc (value >>> 7) ByteArray.empty := by
  rw [svc.eq_1]
  simp only [evidence, ↓reduceDIte]
  rw [svc_acc, push_eq_append, ByteArray.empty_append]
  rfl

private
theorem add_seven_toNat
        (state : UInt64)
        (evidence : state < 57)
        : (state + 7).toNat = state.toNat + 7 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat]; simp only [Nat.reducePow, Nat.reduceMod]; have : state.toNat < 57 := evidence; omega

private
theorem pow2_7 : (2:Nat) ^ 7 = 128 := by decide

private
theorem bslt
        (value state : UInt64)
        (hge : ¬value < 128)
        (bytesEvidence : value.toNat < 2^(64-state.toNat))
        : state < 57 := by
  simp only [UInt64.not_lt] at hge
  rcases Nat.lt_or_ge state.toNat 57 with shiftBound | shiftBound
  · exact shiftBound
  · exfalso; have : 2^(64-state.toNat) ≤ 2^7 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (2:Nat)^7 = 128 := pow2_7; have : 2^(64-state.toNat) ≤ 128 := by omega
    have : value.toNat ≥ 128 := hge; omega

private
theorem brec
        (value state : UInt64)
        (hge : ¬value < 128)
        (bytesEvidence : value.toNat < 2^(64-state.toNat))
        : (value >>> 7).toNat < 2 ^ (64 - (state + 7).toNat) := by
  have sizeEvidence := bslt value state hge bytesEvidence
  rw [add_seven_toNat state sizeEvidence, UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show 64-(state.toNat+7) = 57-state.toNat from by have : state.toNat < 57 := sizeEvidence; omega]
  rw [
    show 64-state.toNat = 7+(57-state.toNat) from by have : state.toNat < 57 := sizeEvidence; omega,
    Nat.pow_add,
    pow2_7
  ] at bytesEvidence
  have := Nat.div_lt_of_lt_mul bytesEvidence; omega

-- Invariant: shift.toNat + 7*fuel ≥ 64 AND fuel ≥ 1.
theorem pvt_svc
        (value : UInt64)
        (tail : ByteArray)
        (decodedValue shift : UInt64)
        (fuel : Nat)
        (hfuel : fuel ≥ 1)
        (hinv : shift.toNat + 7 * fuel ≥ 64)
        (hbound : value.toNat < 2^(64-shift.toNat))
        : pvt (svc value ByteArray.empty ++ tail) decodedValue shift fuel
            = ParseResult.ok (decodedValue ||| (value <<< shift)) tail := by
  by_cases is_single_byte : value < 128
  · rw [svc_lt value is_single_byte]; cases fuel with
    | zero => omega
    | succ remaining_fuel =>
      unfold pvt
      simp only [mkp, ↓reduceDIte, mkg, continuation_bit_clear value is_single_byte, ↓reduceIte,
        mkt, low_seven_bits_roundtrip value is_single_byte]
  · have sizeEvidence := bslt value shift is_single_byte hbound
    rw [svc_ge value is_single_byte, ByteArray.append_assoc]; cases fuel with
    | zero => omega
    | succ remaining_fuel =>
      unfold pvt
      simp only [mkp, ↓reduceDIte, mkg, continuation_bit_set value is_single_byte,
        Bool.false_eq_true, ↓reduceIte, mkt, shift_by_seven]
      have countEvidence : remaining_fuel ≥ 1 := by have : shift.toNat < 57 := sizeEvidence; omega
      have hinv_rec : (shift+7).toNat + 7 * remaining_fuel ≥ 64 := by
        rw [add_seven_toNat shift sizeEvidence]
        have : shift.toNat < 57 := sizeEvidence
        omega
      rw [pvt_svc (value>>>7) tail _ (shift+7) remaining_fuel countEvidence hinv_rec
        (brec value shift is_single_byte hbound)]
      congr 1
      exact varint_append decodedValue value shift sizeEvidence
  termination_by value.toNat
  decreasing_by exact uint64_shr7_lt value is_single_byte

theorem roundtrip
        (value : UInt64)
        : parseVarint (serializeVarint value) = ParseResult.ok value ByteArray.empty := by
  have :=
    pvt_svc
      value
      ByteArray.empty
      0
      0
      10
      (by omega)
      (by simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)
      (by
        simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero]; exact UInt64.toNat_lt value)
  simp at this; exact this

theorem consumption
        (value : UInt64)
        (extra : ByteArray)
        : parseVarint (serializeVarint value ++ extra) = ParseResult.ok value extra := by
  have :=
    pvt_svc
      value
      extra
      0
      0
      10
      (by omega)
      (by simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)
      (by
        simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero]; exact UInt64.toNat_lt value)
  simp at this; exact this

def varint : Box UInt64 where
  parse := parseVarint; serialize := serializeVarint; roundtrip v := roundtrip v; consumption v extra := consumption v extra

end Continuity.Codec.Core.Varint
