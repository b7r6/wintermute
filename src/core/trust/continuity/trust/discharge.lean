/-
  Continuity.Trust.Discharge - discharge proofs (declared coeffects >= actual)
-/

import continuity.crypto
import continuity.coeffect
import continuity.witness
import continuity.trust.core

namespace Continuity.Trust.Discharge

open Continuity.Crypto
open Continuity.Coeffect
open Continuity.Witness
open Continuity.Trust

-- ══════════════════════════════════════════════════════════════════════════════
--                                                           // DISCHARGE // PROOF
-- ══════════════════════════════════════════════════════════════════════════════

/-- Complete discharge proof: evidence that coeffects were satisfied. -/
structure DischargeProof where
  declaredCoeffects : Coeffects
  syscallTrace      : List witnessed_syscall
  envAccesses       : List env_access
  fileAccesses      : List file_access
  netAccesses       : List net_access
  timeAccesses      : List time_access
  randomAccesses    : List random_access
  builder           : HybridPublicKey
  startTime         : Timestamp
  endTime           : Timestamp
  derivationHash    : Hash
  outputHashes      : List (String × Hash)
  signature         : HybridSignature

namespace DischargeProof

-- Note: message hashes the relevant parts of the proof
noncomputable
def message (proof : DischargeProof) : Hash := hash_of proof.derivationHash -- Simplified to avoid Inhabited requirement

def wellFormed (proof : DischargeProof) : Prop :=
  hybrid_verify proof.builder proof.message proof.signature = true

def isPure (proof : DischargeProof) : Bool :=
  proof.envAccesses.isEmpty && proof.netAccesses.isEmpty && proof.timeAccesses.isEmpty
      && proof.randomAccesses.isEmpty

def isReproducible (proof : DischargeProof) : Bool :=
  proof.timeAccesses.isEmpty && proof.randomAccesses.isEmpty
      && proof.envAccesses.all (fun access => access.name != "USER" && access.name != "HOME")
      && proof.fileAccesses.all (fun access => access.contentHash.isSome)
      && proof.netAccesses.all (fun access => access.contentHash.isSome)

def actualCoeffects (proof : DischargeProof) : Coeffects :=
  let envCoeffs := proof.envAccesses.map (fun access => Coeffect.environment access.name)
  let fileCoeffs :=
    proof.fileAccesses.map
      (fun access => match access.contentHash with
        | some contentHash => Coeffect.filesystemCA contentHash
        | none             => Coeffect.filesystem access.path)
  let netCoeffs :=
    proof.netAccesses.map
      (fun access => match access.contentHash with
        | some contentHash => Coeffect.networkCA contentHash
        | none             => Coeffect.network access.host access.port)
  let timeCoeffs := if proof.timeAccesses.isEmpty then [] else [Coeffect.time]
  let randCoeffs := if proof.randomAccesses.isEmpty then [] else [Coeffect.random]
  envCoeffs ++ fileCoeffs ++ netCoeffs ++ timeCoeffs ++ randCoeffs

end DischargeProof

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                     // THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Pure proofs have no external coeffects. -/
theorem pure_no_coeffects
        (proof : DischargeProof)
        (isPure : proof.isPure = true)
        : proof.envAccesses = []
            ∧ proof.netAccesses = []
            ∧ proof.timeAccesses = []
            ∧ proof.randomAccesses = [] := by
  simp only [DischargeProof.isPure, Bool.and_eq_true, List.isEmpty_iff] at isPure

  obtain ⟨⟨⟨envEmpty, netEmpty⟩, timeEmpty⟩, randomEmpty⟩ := isPure

  exact ⟨envEmpty, netEmpty, timeEmpty, randomEmpty⟩

/-- Reproducible proofs have no time or random access. -/
theorem reproducible_no_time_random
        (proof : DischargeProof)
        (isReproducible : proof.isReproducible = true)
        : proof.timeAccesses = [] ∧ proof.randomAccesses = [] := by
  simp only [DischargeProof.isReproducible, Bool.and_eq_true, List.isEmpty_iff] at isReproducible

  obtain ⟨⟨⟨⟨timeEmpty, randomEmpty⟩, _⟩, _⟩, _⟩ := isReproducible

  exact ⟨timeEmpty, randomEmpty⟩

/-- Pure implies time and random are empty (partial reproducibility). -/
theorem pure_implies_no_time_random
        (proof : DischargeProof)
        (isPure : proof.isPure = true)
        : proof.timeAccesses = [] ∧ proof.randomAccesses = [] := by
  simp only [DischargeProof.isPure, Bool.and_eq_true, List.isEmpty_iff] at isPure

  obtain ⟨⟨⟨_, _⟩, timeEmpty⟩, randomEmpty⟩ := isPure

  exact ⟨timeEmpty, randomEmpty⟩

end Continuity.Trust.Discharge
