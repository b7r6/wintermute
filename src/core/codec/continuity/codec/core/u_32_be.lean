import continuity.codec.core.box
import continuity.codec.core.basic
import continuity.codec.core.bytes
import continuity.codec.core.varint
import continuity.codec.core.proto

open Continuity.Codec.Core
open Continuity.Codec.Core
open Continuity.Codec.Core.Varint

namespace Continuity.Codec.Core.U32BE

-- u32be: same proof structure as u32le, reversed byte order
def serializeU32be (value : BitVec 32) : Bytes :=
  [
    (extractByte32 value 3).toNat.toUInt8,
    (extractByte32 value 2).toNat.toUInt8,
    (extractByte32 value 1).toNat.toUInt8,
    (extractByte32 value 0).toNat.toUInt8
  ].toByteArray

def parseU32be (bytes : Bytes) : ParseResult (BitVec 32) :=
  if h : bytes.size >= 4 then
    .ok
      (combineBytes32
        (BitVec.ofNat 8 bytes[3].toNat)
        (BitVec.ofNat 8 bytes[2].toNat)
        (BitVec.ofNat 8 bytes[1].toNat)
        (BitVec.ofNat 8 bytes[0].toNat))
      (bytes.extract 4 bytes.size)
  else
    .fail

@[simp]
theorem serializeU32be_size (value : BitVec 32) : (serializeU32be value).size = 4 := by
  simp [serializeU32be, List.size_toByteArray]

theorem serializeU32be_getElem
        (value : BitVec 32)
        (index : Nat)
        (upperBound : index < 4)
        : (serializeU32be value)[index]'(by simp; exact upperBound)
            = (extractByte32 value (3 - index) (by omega)).toNat.toUInt8 := by
  simp only [serializeU32be]; match index with | 0 => simp | 1 => simp | 2 => simp | 3 => simp

@[simp]
theorem be_bv0
        (value : BitVec 32)
        (evidence : 0 < (serializeU32be value).size := by simp)
        : BitVec.ofNat 8 (serializeU32be value)[0].toNat = extractByte32 value 3 (by omega) := by
  rw [serializeU32be_getElem (upperBound := by omega)]; exact extractByte32_uint8_roundtrip value 3 (by omega)

@[simp]
theorem be_bv1
        (value : BitVec 32)
        (evidence : 1 < (serializeU32be value).size := by simp)
        : BitVec.ofNat 8 (serializeU32be value)[1].toNat = extractByte32 value 2 (by omega) := by
  rw [serializeU32be_getElem (upperBound := by omega)]; exact extractByte32_uint8_roundtrip value 2 (by omega)

@[simp]
theorem be_bv2
        (value : BitVec 32)
        (evidence : 2 < (serializeU32be value).size := by simp)
        : BitVec.ofNat 8 (serializeU32be value)[2].toNat = extractByte32 value 1 (by omega) := by
  rw [serializeU32be_getElem (upperBound := by omega)]; exact extractByte32_uint8_roundtrip value 1 (by omega)

@[simp]
theorem be_bv3
        (value : BitVec 32)
        (evidence : 3 < (serializeU32be value).size := by simp)
        : BitVec.ofNat 8 (serializeU32be value)[3].toNat = extractByte32 value 0 (by omega) := by
  rw [serializeU32be_getElem (upperBound := by omega)]; exact extractByte32_uint8_roundtrip value 0 (by omega)

theorem parseU32be_roundtrip
        (value : BitVec 32)
        : parseU32be (serializeU32be value) = ParseResult.ok value ByteArray.empty := by
  simp only [parseU32be, show (serializeU32be value).size >= 4 from by simp, ↓reduceDIte,
    show (serializeU32be value).extract 4 (serializeU32be value).size = ByteArray.empty from by simp]
  congr 1; simp only [be_bv3, be_bv2, be_bv1, be_bv0]; exact extractBytes32_combineBytes value

theorem parseU32be_consumption
        (value : BitVec 32)
        (extra : Bytes)
        : parseU32be (serializeU32be value ++ extra) = ParseResult.ok value extra := by
  simp only [parseU32be, show (serializeU32be value ++ extra).size >= 4 from by simp [ByteArray.size_append], ↓reduceDIte,
    show (serializeU32be value ++ extra).extract 4 (serializeU32be value ++ extra).size = extra from
      ByteArray.extract_append_eq_right (serializeU32be_size value) (by simp [ByteArray.size_append])]
  congr 1
  rw [ByteArray.getElem_append_left (hlt := by simp),
    ByteArray.getElem_append_left (hlt := by simp), ByteArray.getElem_append_left (hlt := by simp),
    ByteArray.getElem_append_left (hlt := by simp)]
  simp only [be_bv3, be_bv2, be_bv1, be_bv0]; exact extractBytes32_combineBytes value

def u32beBitVec : Box (BitVec 32) where
  parse := parseU32be; serialize := serializeU32be
  roundtrip := parseU32be_roundtrip; consumption := parseU32be_consumption

end Continuity.Codec.Core.U32BE
