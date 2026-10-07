import continuity.codec.core.box
import continuity.codec.core.basic
import continuity.codec.core.bytes

open Continuity.Codec.Core
open Continuity.Codec.Core

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // continuity // codec // guards
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Three combinators that belong in the core:
--
--   expectPad   — consume n bytes, verify a predicate, reject if violated
--   bounded     — wrap a Box with a size ceiling, reject oversized inputs
--   exhaustion  — connect bounded to a resource budget (the missing theorem)
--
-- Get these right once. Then it won't be a little wrong everywhere.
-- ──────────────────────────────────────────────────────────────────────────────

namespace Continuity.Codec.Core.Guards
open Continuity.Codec.Core.Bytes

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1. EXPECT PAD — generalized padding validation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check that the first n bytes of bs satisfy a predicate -/
def checkPad (parser : UInt8 → Bool) (count : Nat) (bytes : ByteArray) : Bool :=
  bytes.extract 0 count |>.data.all parser

/-- Consume n bytes, verify each satisfies predicate p. Reject on violation.
    This is the general form. expectZeros is expectPad (· == 0).
    expectFF is expectPad (· == 0xFF). The predicate is the parameter. -/
def expectPad (parser : UInt8 → Bool) (count : Nat) (bytes : ByteArray) : ParseResult Unit :=
  if _ : bytes.size ≥ count then
    if checkPad parser count bytes then .ok () (bytes.extract count bytes.size) else .fail
  else
    .fail

/-- Construct padding from a fixed byte value -/
def mkPad (value : UInt8) (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count value)

theorem mkPad_size (value : UInt8) (count : Nat) : (mkPad value count).size = count := by
  simp [mkPad, ByteArray.size]

-- ─── expectPad lemmas ─────────────────────────────────────────────────────────

theorem expectPad_of_size_eq
        (parser : UInt8 → Bool)
        (pad : ByteArray)
        (count : Nat)
        (h_size : pad.size = count)
        (h_check : checkPad parser count pad = true)
        : expectPad parser count pad = ParseResult.ok () ByteArray.empty := by
  subst h_size
  simp only [expectPad, Nat.le_refl, ↓reduceDIte, h_check, ite_true]
  congr 1; simp

theorem expectPad_append_of_size_eq
        (parser : UInt8 → Bool)
        (pad extra : ByteArray)
        (count : Nat)
        (h_size : pad.size = count)
        (h_check : checkPad parser count (pad ++ extra) = true)
        : expectPad parser count (pad ++ extra) = ParseResult.ok () extra := by
  subst h_size
  simp only [expectPad, ByteArray.size_append, Nat.le_add_right, ↓reduceDIte, h_check, ite_true]
  congr 1; exact ByteArray.extract_append_eq_right rfl rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2. BOUNDED — size-limited Box
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A value whose serialization is within a size bound.
    The proof obligation `size_ok` is part of the type — you can't construct
    a Bounded without proving the size fits. -/
structure Bounded (Value : Type) (box : Box Value) (maxBytes : Nat) where
  val     : Value
  size_ok : (box.serialize val).size ≤ maxBytes

/-- Wrap a Box with a size ceiling. Rejects oversized inputs at parse time.
    serialize never exceeds maxBytes by construction (size_ok in the type). -/
def bounded
    {Value : Type}
    (box : Box Value)
    (maxBytes : Nat)
    : Box (Bounded Value box maxBytes) where
  parse bs :=
    match box.parse bs with
    | .ok value rest =>
      if h : (box.serialize value).size ≤ maxBytes then .ok ⟨value, h⟩ rest else .fail
    | .fail => .fail
  serialize b := box.serialize b.val
  roundtrip b := by
    rw [box.roundtrip b.val]
    simp only [b.size_ok, ↓reduceDIte]
  consumption b extra := by
    rw [box.consumption b.val extra]
    simp only [b.size_ok, ↓reduceDIte]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3. EXHAUSTION — resource budget theorems
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A bounded value's serialization never exceeds the bound.
    This is the bridge between the type system and resource accounting. -/
theorem bounded_serialize_le
        {Value : Type}
        (box : Box Value)
        (maxBytes : Nat)
        (rightValue : Bounded Value box maxBytes)
        : (box.serialize rightValue.val).size ≤ maxBytes :=
  rightValue.size_ok

/-- For a list of bounded values, total serialization ≤ count × bound.
    This is the theorem that prevents resource exhaustion:
    if each item fits in maxBytes and you have n items,
    the total is at most n × maxBytes. -/
theorem bounded_list_total
        {Value : Type}
        (box : Box Value)
        (maxBytes : Nat)
        (bytes : List (Bounded Value box maxBytes))
        : (bytes.map (fun boundedValue => (box.serialize boundedValue.val).size)).sum
            ≤ bytes.length * maxBytes := by
  induction bytes with
  | nil => simp
  | cons bounded_value rest induction_hypothesis =>
    simp only [List.map, List.sum_cons, List.length_cons, Nat.succ_mul]
    rw [Nat.add_comm]
    exact Nat.add_le_add induction_hypothesis bounded_value.size_ok

/-- Corollary: if a bounded list fits in a memory budget, parsing is safe.
    Given a budget M and a bound maxBytes, at most M / maxBytes items
    can be parsed before the budget is exhausted. -/
theorem bounded_list_fits_budget
        {Value : Type}
        (box : Box Value)
        (maxBytes : Nat)
        (budget : Nat)
        (bytes : List (Bounded Value box maxBytes))
        (h_count : bytes.length ≤ budget / maxBytes)
        (_h_pos : maxBytes > 0)
        : (bytes.map (fun boundedValue => (box.serialize boundedValue.val).size)).sum ≤ budget := by
  have firstEvidence := bounded_list_total box maxBytes bytes
  have secondEvidence : bytes.length * maxBytes ≤ (budget / maxBytes) * maxBytes :=
    Nat.mul_le_mul_right maxBytes h_count
  have thirdEvidence : (budget / maxBytes) * maxBytes ≤ budget :=
    Nat.div_mul_le_self budget maxBytes
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4. SPECIALIZATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- expectZeros: reject non-zero padding bytes -/
abbrev expectZeros (count : Nat) (bytes : ByteArray) : ParseResult Unit :=
  expectPad (· == 0) count bytes

/-- expectFF: reject non-0xFF padding bytes -/
abbrev expectFF (count : Nat) (bytes : ByteArray) : ParseResult Unit :=
  expectPad (· == 0xFF) count bytes

/-- Bounded length-prefixed string with a size ceiling -/
def boundedString (maxBytes : Nat) : Box (Bounded len_prefixed lenPrefixed maxBytes) :=
  bounded lenPrefixed maxBytes

end Continuity.Codec.Core.Guards
