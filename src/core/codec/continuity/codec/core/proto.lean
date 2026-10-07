import continuity.codec.core.box
import continuity.codec.core.basic
import continuity.codec.core.bytes
import continuity.codec.core.varint

open Continuity.Codec.Core
open Continuity.Codec.Core
open Continuity.Codec.Core.Varint

namespace Continuity.Codec.Core.Proto
open Continuity.Codec.Core.Bytes

private
theorem size_u64_rt
        (count : Nat)
        (evidence : count < 2^64)
        : (UInt64.ofNat count).toNat = count := by simp [UInt64.ofNat, UInt64.toNat]; omega

structure proto_bytes where
  data  : ByteArray
  bound : data.size < 2^64

def protoBytes : Box proto_bytes where
  parse bs :=
    match varint.parse bs with
    | .ok len rest =>
      match takeN len.toNat rest with
      | .ok data rest2 => if h : data.size < 2 ^ 64 then .ok ⟨data, h⟩ rest2 else .fail
      | .fail => .fail
    | .fail => .fail

  -- Encode the payload bytes.
  serialize pb := varint.serialize pb.data.size.toUInt64 ++ pb.data

  -- Prove the codec roundtrip.
  roundtrip pb := by
    rw [varint.consumption]
    dsimp only []
    rw [size_u64_rt pb.data.size pb.bound, takeN_of_size_eq pb.data pb.data.size rfl]
    dsimp only []
    simp only [pb.bound, ↓reduceDIte]

  -- Prove exact input consumption.
  consumption pb extra := by
    rw [ByteArray.append_assoc, varint.consumption]
    dsimp only []
    rw [size_u64_rt pb.data.size pb.bound, takeN_append_of_size_eq pb.data extra pb.data.size rfl]
    dsimp only []
    simp only [pb.bound, ↓reduceDIte]

end Continuity.Codec.Core.Proto
