import continuity.codec.core.box
import continuity.codec.core.basic

open Continuity.Codec.Core
open Continuity.Codec.Core

namespace Continuity.Codec.Core.Bytes

--- TODO[b7r6]: !! exhaustion proof not complete !!
--- takeN is the length-driven consumption primitive; the converse (parse bs = ok a rest
--- → bs = a ++ rest) must be proven here first — fixedBytes/lenPrefixed inherit from it.
def takeN (count : Nat) (bytes : Bytes) : ParseResult Bytes :=
  if _ : bytes.size ≥ count then
    .ok (bytes.extract 0 count) (bytes.extract count bytes.size)
  else
    .fail

theorem takeN_of_size_eq
        (data : ByteArray)
        (count : Nat)
        (evidence : data.size = count)
        : takeN count data = ParseResult.ok data ByteArray.empty := by
  subst evidence; unfold takeN; simp only [Nat.le_refl, ↓reduceDIte]
  congr 1; exact ByteArray.extract_zero_size; simp

theorem takeN_append_of_size_eq
        (data extra : ByteArray)
        (count : Nat)
        (evidence : data.size = count)
        : takeN count (data ++ extra) = ParseResult.ok data extra := by
  subst evidence; unfold takeN; simp only [ByteArray.size_append, Nat.le_add_right, ↓reduceDIte]
  congr 1; exact ByteArray.extract_append_eq_left rfl
  exact ByteArray.extract_append_eq_right rfl rfl

structure fixed_bytes (count : Nat) where
  data    : ByteArray
  size_eq : data.size = count

--- TODO[b7r6]: !! exhaustion proof not complete !!
def fixedBytes (count : Nat) : Box (fixed_bytes count) where
  parse bs :=
    match takeN count bs with
    | .ok data rest => if h : data.size = count then .ok ⟨data, h⟩ rest else .fail
    | .fail         => .fail
  serialize fb := fb.data
  roundtrip fb := by
    rw [takeN_of_size_eq fb.data count fb.size_eq]
    simp only [fb.size_eq, ↓reduceDIte]
  consumption fb extra := by
    rw [takeN_append_of_size_eq fb.data extra count fb.size_eq]
    simp only [fb.size_eq, ↓reduceDIte]

-- lenPrefixed
structure len_prefixed where
  data  : ByteArray
  bound : data.size < 2^64

private
theorem size_u64_roundtrip
        (count : Nat)
        (evidence : count < 2^64)
        : (UInt64.ofNat count).toNat = count := by simp [UInt64.ofNat, UInt64.toNat]; omega

--- TODO[b7r6]: !! exhaustion proof not complete !!
--- the dangerous one: length is attacker-controlled. The converse must show a parsed
--- `data` of declared size cannot under/over-read — i.e. a forged length can't leave a
--- consumable tail. This is where frame-smuggling would live; prove `tight` carefully.
def lenPrefixed : Box len_prefixed where
  parse bs :=
    match u64le.parse bs with
    | .ok len rest =>
      match takeN len.toNat rest with
      | .ok data rest2 => if h : data.size < 2 ^ 64 then .ok ⟨data, h⟩ rest2 else .fail
      | .fail          => .fail
    | .fail => .fail
  serialize lp := u64le.serialize lp.data.size.toUInt64 ++ lp.data
  roundtrip lp := by
    rw [u64le.consumption]; simp only []
    rw [size_u64_roundtrip lp.data.size lp.bound]
    rw [takeN_of_size_eq lp.data lp.data.size rfl]
    simp only [lp.bound, ↓reduceDIte]
  consumption lp extra := by
    rw [ByteArray.append_assoc, u64le.consumption]; simp only []
    rw [size_u64_roundtrip lp.data.size lp.bound]
    rw [takeN_append_of_size_eq lp.data extra lp.data.size rfl]
    simp only [lp.bound, ↓reduceDIte]

def bytes32 : Box (fixed_bytes 32) := fixedBytes 32
def bytes20 : Box (fixed_bytes 20) := fixedBytes 20
def bytes64 : Box (fixed_bytes 64) := fixedBytes 64

end Continuity.Codec.Core.Bytes
