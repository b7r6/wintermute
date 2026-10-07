/-
  Cornell - Verified Binary Format DSL

  "Cornell boxes... the man made these things. Boxes with things inside them."

  A box is a bidirectional codec with machine-checked round-trip correctness.

  This module re-exports verified boxes from Continuity.Codec.Core.
  All boxes have complete proofs - no sorry, no axiom, no partial.
-/

import continuity.codec.core.box
import continuity.codec.core.native

namespace Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- RE-EXPORTS FROM PROOFS
-- All of these have complete, machine-checked proofs.
-- ═══════════════════════════════════════════════════════════════════════════════

-- Core types

-- Verified primitive boxes

-- Verified combinators

-- ═══════════════════════════════════════════════════════════════════════════════
-- BYTES UTILITIES (convenience functions)
-- ═══════════════════════════════════════════════════════════════════════════════

instance : Repr Bytes where
  reprPrec bs _ :=
    let hex :=
      bs.toList.map fun byte =>
        let highNibble := byte.toNat / 16
        let lowNibble := byte.toNat % 16
        let toHex :=
          fun nibble => if nibble < 10 then Char.ofNat (48 + nibble) else Char.ofNat (87 + nibble)
        s!"{toHex highNibble}{toHex lowNibble}"
    Std.Format.text s!"⟨{String.intercalate " " hex}⟩"

def Bytes.empty : Bytes := ByteArray.empty

def Bytes.length (bytes : Bytes) : Nat := bytes.size

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSERESULT UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

open Continuity.Codec.Core in
instance {Value : Type} [Repr Value] : Repr (ParseResult Value) where
  reprPrec
    | .ok value _, count =>
      Repr.addAppParen ("ParseResult.ok " ++ reprArg value ++ " <bytes>") count
    | .fail, _ => "ParseResult.fail"

open Continuity.Codec.Core in
def ParseResult.isOk {Value : Type} : ParseResult Value → Bool
  | .ok _ _ => true
  | .fail   => false

open Continuity.Codec.Core in
def ParseResult.toOption {Value : Type} : ParseResult Value → Option (Value × Bytes)
  | .ok value rest => some (value, rest)
  | .fail          => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- UINTXX BOXES (via isoBox from BitVec)
-- These use the verified BitVec boxes and convert via isomorphism
-- ═══════════════════════════════════════════════════════════════════════════════

open Continuity.Codec.Core in
/-- Little-endian u64 (verified via isoBox from u64leBitVec) -/
def u64le : Box UInt64 :=
  isoBox u64leBitVec UInt64.ofBitVec UInt64.toBitVec (fun _ => rfl) (fun _ => rfl)

open Continuity.Codec.Core in
/-- Little-endian u32 (verified via isoBox from u32leBitVec) -/
def u32le : Box UInt32 :=
  isoBox u32leBitVec UInt32.ofBitVec UInt32.toBitVec (fun _ => rfl) (fun _ => rfl)

open Continuity.Codec.Core in
/-- Boolean as u64 (Nix style): 0 = false, nonzero = true

    Note: This is a lossy encoding (many u64 values map to true).
    The roundtrip property still holds: parse(serialize(b)) = b
-/
def bool64 : Box Bool where
  parse bs := (u64le.parse bs).map (· != 0)
  serialize b := u64le.serialize (if b then 1 else 0)
  roundtrip b := by
    simp only [u64le, isoBox, ParseResult.map]
    cases b
    · -- false case: serialize gives 0, parse gives 0, (0 != 0) = false
      rw [u64leBitVec.roundtrip]; rfl
    · -- true case: serialize gives 1, parse gives 1, (1 != 0) = true
      rw [u64leBitVec.roundtrip]; rfl
  consumption b extra := by
    simp only [u64le, isoBox, ParseResult.map]
    cases b
    · rw [u64leBitVec.consumption]; rfl
    · rw [u64leBitVec.consumption]; rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVENIENCE COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

open Continuity.Codec.Core in
/-- Map a box through an isomorphism (alias for isoBox) -/
def isoMap
    {Value ResultValue : Type}
    (box : Box Value)
    (function : Value → ResultValue)
    (secondFunction : ResultValue → Value)
    (iso_fg : ∀ b, function (secondFunction b) = b)
    (iso_gf : ∀ a, secondFunction (function a) = a)
    : Box ResultValue :=
  isoBox box function secondFunction iso_fg iso_gf

end Continuity.Codec.Core
