import continuity.codec.core.box
import continuity.codec.core.scanner

open Continuity.Codec.Core
open Continuity.Codec.Core.Scanner
namespace Continuity.Codec.Core.Delimited

def DelimFree (decoder : UInt8) (cursor : ByteArray) : Prop :=
  ∀ i : Nat, (evidence : i < cursor.size) → cursor[i] ≠ decoder

def fbf (decoder : UInt8) (bytes : ByteArray) (state : Nat) : Option Nat :=
  if h : state < bytes.size then
    if bytes[state] == decoder then some state else fbf decoder bytes (state + 1)
  else
    none
  termination_by bytes.size - state

private
theorem neq_subst
        {bytes : ByteArray}
        {decoder : UInt8}
        {index nextIndex : Nat}
        {upperBound : index < bytes.size}
        {nextIndexEvidence : nextIndex < bytes.size}
        (heq : nextIndex = index)
        (evidence : bytes[index] ≠ decoder)
        : bytes[nextIndex] ≠ decoder :=
  heq ▸ evidence

private
theorem eq_subst
        {bytes : ByteArray}
        {decoder : UInt8}
        {index nextIndex : Nat}
        {upperBound : index < bytes.size}
        {nextIndexEvidence : nextIndex < bytes.size}
        (heq : nextIndex = index)
        (evidence : bytes[index] = decoder)
        : bytes[nextIndex] = decoder :=
  heq ▸ evidence

theorem fbf_skip
        (decoder : UInt8)
        (bytes : ByteArray)
        (state count : Nat)
        (bytesEvidence : state + count < bytes.size)
        (functionEvidence : ∀ k, k < count → (keyEvidence : state + k < bytes.size) → bytes[state + k] ≠ decoder)
        (upperEvidence : bytes[state + count]'bytesEvidence = decoder)
        : fbf decoder bytes state = some (state + count) := by
  induction count generalizing state with
  | zero =>
    unfold fbf; simp only [Nat.add_zero] at bytesEvidence upperEvidence; simp [bytesEvidence, upperEvidence]
  | succ remaining_length induction_hypothesis =>
    have sizeEvidence : state < bytes.size := by omega
    have hne : bytes[state]'sizeEvidence ≠ decoder := functionEvidence 0 (by omega) sizeEvidence
    unfold fbf
    simp only [sizeEvidence, ↓reduceDIte,
      show (bytes[state] == decoder) = false from beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true,
      ↓reduceIte]
    suffices recursiveResult : fbf decoder bytes (state+1) = some ((state+1) + remaining_length) by
      rwa [show (state+1)+remaining_length = state+(remaining_length+1) from by omega] at recursiveResult
    exact
      induction_hypothesis
        (state + 1)
        (by omega)
        (fun kdx indexBound hkb =>
          neq_subst
            (show (state + 1) + kdx = state + (kdx + 1) from by omega)
            (functionEvidence (kdx + 1) (by omega) (by omega)))
        (eq_subst
          (show (state+1)+remaining_length = state+(remaining_length+1) from by omega)
          upperEvidence)

private
theorem sza
        {leftValue rightValue : ByteArray}
        : (leftValue ++ rightValue).size = leftValue.size + rightValue.size :=
  ByteArray.size_append

private
theorem sz1 {decoder : UInt8} : (⟨#[decoder]⟩ : ByteArray).size = 1 := by simp [ByteArray.size]

def ser (decoder : UInt8) (data : ByteArray) : ByteArray := data ++ ⟨#[decoder]⟩

def par (decoder : UInt8) (bytes : ByteArray) : ParseResult ByteArray :=
  match fbf decoder bytes 0 with
  | some idx => .ok (bytes.extract 0 idx) (bytes.extract (idx + 1) bytes.size)
  | none     => .fail

theorem roundtrip
        (decoder : UInt8)
        (data : ByteArray)
        (hfree : DelimFree decoder data)
        : par decoder (ser decoder data) = ParseResult.ok data ByteArray.empty := by
  simp only [par, ser]
  have hfind : fbf decoder (data ++ ⟨#[decoder]⟩) 0 = some data.size := by
    have :=
      fbf_skip
        decoder
        (data ++ ⟨#[decoder]⟩)
        0
        data.size
        (by rw [sza, sz1]; omega)
        (fun kdx indexBound hkb => by
          simp only [Nat.zero_add] at hkb ⊢
          rw [ByteArray.getElem_append_left (hlt := by omega)]
          exact hfree kdx indexBound)
        (by
          simp only [Nat.zero_add]
          rw [ByteArray.getElem_append_right (hle := Nat.le_refl _)]
          simp only [Nat.sub_self]; rfl)
    simpa using this
  rw [hfind]; dsimp only []; congr 1
  · exact ByteArray.extract_append_eq_left rfl
  · simp [sz1]

set_option maxHeartbeats 800000 in
theorem consumption
        (decoder : UInt8)
        (data extra : ByteArray)
        (hfree : DelimFree decoder data)
        : par decoder (ser decoder data ++ extra) = ParseResult.ok data extra := by
  simp only [par, ser, ByteArray.append_assoc]
  have hfind : fbf decoder (data ++ (⟨#[decoder]⟩ ++ extra)) 0 = some data.size := by
    have :=
      fbf_skip
        decoder
        (data ++ (⟨#[decoder]⟩ ++ extra))
        0
        data.size
        (by rw [sza, sza, sz1]; omega)
        (fun kdx indexBound hkb => by
          simp only [Nat.zero_add] at hkb ⊢
          rw [ByteArray.getElem_append_left (hlt := by omega)]
          exact hfree kdx indexBound)
        (by
          simp only [Nat.zero_add]
          rw [ByteArray.getElem_append_right (hle := Nat.le_refl _)]
          simp only [Nat.sub_self]
          rw [ByteArray.getElem_append_left (hlt := by rw [sz1]; omega)]; rfl)
    simpa using this
  rw [hfind]; dsimp only []; congr 1
  · exact ByteArray.extract_append_eq_left rfl
  · rw [
      show data.size + 1 = data.size + (⟨#[decoder]⟩ : ByteArray).size from by rw [sz1],
      ← ByteArray.append_assoc,
      show data.size + (⟨#[decoder]⟩ : ByteArray).size = (data ++ ⟨#[decoder]⟩).size from by rw [sza]
    ]
    exact ByteArray.extract_append_eq_right rfl (by rw [sza])

end Continuity.Codec.Core.Delimited
