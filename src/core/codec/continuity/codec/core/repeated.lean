import continuity.codec.core.box
import continuity.codec.core.basic

open Continuity.Codec.Core
open Continuity.Codec.Core

namespace Continuity.Codec.Core.Repeated

def serializeList {Value : Type} (box : Box Value) : List Value → ByteArray
  | []            => ByteArray.empty
  | item :: items => box.serialize item ++ serializeList box items

def parseList {Value : Type} (box : Box Value) : Nat → Bytes → List Value → ParseResult (List Value)
  | 0, rest, itemsRev => ParseResult.ok itemsRev.reverse rest
  | count+1, bytes, itemsRev =>
    match box.parse bytes with
    | ParseResult.ok value rest => parseList box count rest (value :: itemsRev)
    | ParseResult.fail          => ParseResult.fail

-- Core lemma: n explicit, length hypothesis
theorem parseList_core
        {Value : Type}
        (box : Box Value)
        (values : List Value)
        (count : Nat)
        (countEvidence : values.length = count)
        (tail : ByteArray)
        (itemsRev : List Value)
        : parseList box count (serializeList box values ++ tail) itemsRev
            = ParseResult.ok (itemsRev.reverse ++ values) tail := by

  -- Split the remaining proof cases.
  subst countEvidence; induction values generalizing tail itemsRev with
  | nil => simp [parseList, serializeList, ByteArray.empty_append, List.append_nil]
  | cons item remaining_items induction_hypothesis =>
    simp only [parseList, serializeList, ByteArray.append_assoc, List.length_cons]
    rw [box.consumption]
    exact induction_hypothesis tail (item :: itemsRev) |>.trans
      (by simp [List.reverse_cons, List.append_assoc])

-- Roundtrip and consumption for parseRepeated
def parseRepeated
    {Value : Type}
    (count : Nat)
    (box : Box Value)
    (bytes : Bytes)
    : ParseResult { xs : List Value // xs.length = count } :=
  match parseList box count bytes [] with
  | ParseResult.ok items rest =>
    if h : items.length = count then ParseResult.ok ⟨items, h⟩ rest else ParseResult.fail
  | ParseResult.fail => ParseResult.fail

-- These take hlen : xs.length = n and use subst to avoid the motive issue
theorem parseRepeated_roundtrip
        {Value : Type}
        (count : Nat)
        (box : Box Value)
        (values : List Value)
        (hlen : values.length = count)
        : parseRepeated count box (serializeList box values)
            = ParseResult.ok ⟨values, hlen⟩ ByteArray.empty := by
  subst hlen -- now n = xs.length everywhere

  -- Expose the remaining proof obligation.
  unfold parseRepeated

  -- Simplify the remaining goal.
  rw [show serializeList box values = serializeList box values ++ ByteArray.empty from (ByteArray.append_empty).symm]

  -- Simplify the remaining goal.
  rw [parseList_core box values values.length rfl ByteArray.empty []]

  -- Simplify the remaining goal.
  simp

theorem parseRepeated_consumption
        {Value : Type}
        (count : Nat)
        (box : Box Value)
        (values : List Value)
        (hlen : values.length = count)
        (extra : ByteArray)
        : parseRepeated count box (serializeList box values ++ extra)
            = ParseResult.ok ⟨values, hlen⟩ extra := by
  subst hlen

  -- Expose the remaining proof obligation.
  unfold parseRepeated

  -- Simplify the remaining goal.
  rw [parseList_core box values values.length rfl extra []]

  -- Simplify the remaining goal.
  simp

def repeatedN
    {Value : Type}
    (count : Nat)
    (box : Box Value)
    : Box { xs : List Value // xs.length = count } where
  parse := parseRepeated count box
  serialize xs := serializeList box xs.val
  roundtrip := fun ⟨xs, hlen⟩ => parseRepeated_roundtrip count box xs hlen
  consumption := fun ⟨xs, hlen⟩ extra => parseRepeated_consumption count box xs hlen extra

end Continuity.Codec.Core.Repeated
