import continuity.codec.core.guards
import continuity.codec.core.limits

open Continuity.Codec.Core
open Continuity.Codec.Core
open Continuity.Codec.Core.Guards
open Continuity.Codec.Core.Limits

namespace Continuity.Codec.Wire.Nix.Padded
open Continuity.Codec.Core.Bytes

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // continuity // codec // nix padded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Nix wire protocol: length-prefixed strings with 8-byte aligned zero padding.
--
-- The padding gap (skipN → expectPad) is closed here.
-- The size limit (dead constant → bounded) is enforced here.
-- Both are built on Guards.lean so they're right once.
-- ──────────────────────────────────────────────────────────────────────────────

def padSize (payloadLength : Nat) : Nat :=
  if payloadLength % 8 == 0 then 0 else 8 - payloadLength % 8

def zeroPad (payloadLength : Nat) : ByteArray := mkPad 0 payloadLength

theorem zeroPad_size (payloadLength : Nat) : (zeroPad payloadLength).size = payloadLength :=
  mkPad_size 0 payloadLength

-- ─── padSize lemma ────────────────────────────────────────────────────────────

theorem padSize_le_7 (payloadLength : Nat) : padSize payloadLength ≤ 7 := by
  unfold padSize
  have : payloadLength % 8 < 8 := Nat.mod_lt payloadLength (by omega)
  by_cases is_aligned : payloadLength % 8 = 0
  · simp [is_aligned]
  · have : (payloadLength % 8 == 0) = false := by simp [BEq.beq]; exact is_aligned
    simp [this]; omega

-- ─── zero-padding proofs by cases over {0..7} ─────────────────────────────────

theorem checkPad_zero_zeroPad_padSize
        (payloadLength : Nat)
        : checkPad (· == 0) (padSize payloadLength) (zeroPad (padSize payloadLength)) = true := by
  have byte7Evidence := padSize_le_7 payloadLength
  have :
      padSize payloadLength = 0
          ∨ padSize payloadLength = 1
          ∨ padSize payloadLength = 2
          ∨ padSize payloadLength = 3
          ∨ padSize payloadLength = 4
          ∨ padSize payloadLength = 5
          ∨ padSize payloadLength = 6
          ∨ padSize payloadLength = 7 := by omega
  rcases this with
    padEq0 | padEq1 | padEq2 | padEq3 | padEq4 | padEq5 | padEq6 | padEq7
    <;> simp [*] <;> native_decide

theorem checkPad_zero_zeroPad_append_padSize
        (payloadLength : Nat)
        (extra : ByteArray)
        : checkPad (· == 0) (padSize payloadLength) (zeroPad (padSize payloadLength) ++ extra)
            = true := by
  have byte7Evidence := padSize_le_7 payloadLength
  have hcases :
      padSize payloadLength = 0
          ∨ padSize payloadLength = 1
          ∨ padSize payloadLength = 2
          ∨ padSize payloadLength = 3
          ∨ padSize payloadLength = 4
          ∨ padSize payloadLength = 5
          ∨ padSize payloadLength = 6
          ∨ padSize payloadLength = 7 := by omega
  unfold checkPad
  rcases hcases with
    padEq0 | padEq1 | padEq2 | padEq3 | padEq4 | padEq5 | padEq6 | padEq7
    <;> simp only [*]
    <;> rw [ByteArray.extract_append_eq_left (zeroPad_size _).symm] <;> native_decide

-- ─── NixString ────────────────────────────────────────────────────────────────

private
theorem size_u64_rt
        (payloadLength : Nat)
        (evidence : payloadLength < 2^64)
        : (UInt64.ofNat payloadLength).toNat = payloadLength := by
  simp [UInt64.ofNat, UInt64.toNat]; omega

structure NixString where
  data  : ByteArray
  bound : data.size < 2^64

/-- Nix wire string: u64le length ++ data ++ zero padding to 8-byte boundary.
    Padding bytes are VERIFIED to be zero (expectPad from Guards).
    This is the fixed version — skipN consumed without checking. -/
def nixString : Box NixString where
  parse bs :=
    match u64le.parse bs with
    | .ok len rest =>
      let payloadLength := len.toNat
      match takeN payloadLength rest with
      | .ok data rest2 =>
        match expectPad (· == 0) (padSize payloadLength) rest2 with
        | .ok () rest3 => if h : data.size < 2 ^ 64 then .ok ⟨data, h⟩ rest3 else .fail
        | .fail        => .fail
      | .fail => .fail
    | .fail => .fail
  serialize ns := u64le.serialize ns.data.size.toUInt64 ++ ns.data ++ zeroPad (padSize ns.data.size)
  roundtrip ns := by
    simp only
    rw [ByteArray.append_assoc, u64le.consumption]; simp only []
    rw [size_u64_rt ns.data.size ns.bound]
    rw [takeN_append_of_size_eq ns.data (zeroPad (padSize ns.data.size)) ns.data.size rfl]
    dsimp only []
    rw [expectPad_of_size_eq
      (· == 0)
      (zeroPad (padSize ns.data.size))
      (padSize ns.data.size)
      (zeroPad_size _)
      (checkPad_zero_zeroPad_padSize _)]
    dsimp only []
    simp [ns.bound]
  consumption ns extra := by
    simp only
    rw [ByteArray.append_assoc, ByteArray.append_assoc, u64le.consumption]; simp only []
    rw [size_u64_rt ns.data.size ns.bound]
    rw [takeN_append_of_size_eq ns.data (zeroPad (padSize ns.data.size) ++ extra) ns.data.size rfl]
    dsimp only []
    rw [expectPad_append_of_size_eq
      (· == 0)
      (zeroPad (padSize ns.data.size))
      extra
      (padSize ns.data.size)
      (zeroPad_size _)
      (checkPad_zero_zeroPad_append_padSize _ _)]
    dsimp only []
    simp [ns.bound]

end Continuity.Codec.Wire.Nix.Padded
