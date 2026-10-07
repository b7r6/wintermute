/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // CONTINUITY // TRUST
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


                         Trust Model and Vouch Chains


                                                       straylight.software · 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

No CA. No global root. Just a graph of attestations (vouches) from roots
you explicitly trust. Trust flows through vouch chains.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.crypto
import continuity.trust.authority

namespace Continuity.Trust

open Continuity.Crypto
open Continuity.Trust.Authority

-- ══════════════════════════════════════════════════════════════════════════════
--                                                            // TRUST // DISTANCE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Distance from the rfl nexus. Each axiom crossed is a step from certainty. -/
inductive TrustDistance where
  | kernel    -- 0: rfl, Lean's type theory
  | crypto    -- 1: + SHA256, ed25519, ML-DSA, SLH-DSA
  | os        -- 2: + namespaces, syscalls
  | toolchain -- 3: + compilers
  | consensus -- 4: + human agreement
  deriving DecidableEq, Repr, Inhabited

namespace TrustDistance

def rank : TrustDistance → Nat
  | kernel    => 0
  | crypto    => 1
  | .os       => 2
  | toolchain => 3
  | consensus => 4

theorem rank_injective : ∀ a b, rank a = rank b → a = b := by
  intro leftDistance rightDistance ranksEqual

  cases leftDistance <;> cases rightDistance
    <;> first | rfl | (simp only [rank] at ranksEqual; omega)

end TrustDistance

instance : LE TrustDistance where
  le a b := TrustDistance.rank a ≤ TrustDistance.rank b

instance : DecidableRel (·≤ ·: TrustDistance → TrustDistance → Prop) := fun left right =>
  inferInstanceAs (Decidable (TrustDistance.rank left ≤ TrustDistance.rank right))

theorem trust_distance_total : ∀ a b : TrustDistance, a ≤ b ∨ b ≤ a := by
  intro leftDistance rightDistance

  unfold LE.le instLETrustDistance

  simp only [TrustDistance.rank]

  omega

theorem trust_distance_trans : ∀ a b c : TrustDistance, a ≤ b → b ≤ c → a ≤ c := by
  intro firstDistance secondDistance thirdDistance hab hbc

  unfold LE.le instLETrustDistance at *

  simp only [TrustDistance.rank] at *

  omega

def is_safety_critical (distance : TrustDistance) : Bool := decide (distance ≤ TrustDistance.crypto)

-- ══════════════════════════════════════════════════════════════════════════════
--                                                         // RECOGNITION // LEVEL
-- ══════════════════════════════════════════════════════════════════════════════

/-- How much do we trust this key? -/
inductive RecognitionLevel where
  | unrecognized -- No trust path
  | proofBound (proof : String) -- Proved something external
  | vouched (depth : Nat) -- Vouched by someone trusted
  | direct -- Directly trusted (root)
  deriving DecidableEq, Repr, Inhabited

namespace RecognitionLevel

def rank : RecognitionLevel → Nat
  | unrecognized => 0
  | proofBound _ => 1
  | vouched _    => 2
  | direct       => 3

end RecognitionLevel

instance : LE RecognitionLevel where
  le a b := RecognitionLevel.rank a ≤ RecognitionLevel.rank b

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                    // TIMESTAMP
-- ══════════════════════════════════════════════════════════════════════════════

abbrev Timestamp := Nat

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                      // VOUCHES
-- ══════════════════════════════════════════════════════════════════════════════

/-- A vouch: one identity vouches for another with bounded scope. -/
structure vouch where
  voucher   : HybridPublicKey
  vouchee   : HybridPublicKey
  scope     : Authority
  expires   : Timestamp
  signature : HybridSignature

/-- A revocation: cancels a previous vouch. -/
structure revocation where
  revoker   : HybridPublicKey
  revoked   : HybridPublicKey
  timestamp : Timestamp
  signature : HybridSignature

-- ══════════════════════════════════════════════════════════════════════════════
--                                                               // TRUST // STATE
-- ══════════════════════════════════════════════════════════════════════════════

/-- The complete recognition graph. Your local view of trust. -/
structure TrustState where
  direct      : List HybridPublicKey
  vouches     : List vouch
  revocations : List revocation

namespace TrustState

/-- Count vouches (simple metric) -/
def vouch_count (trustState : TrustState) : Nat := trustState.vouches.length

/-- Count direct trusts -/
def direct_count (trustState : TrustState) : Nat := trustState.direct.length

/-- Is a key directly trusted? -/
noncomputable
def is_direct (trustState : TrustState) (publicKey : HybridPublicKey) : Bool :=
  trustState.direct.any (· == publicKey)

/-- Check if a vouch has been revoked. -/
noncomputable
def is_revoked (trustState : TrustState) (voucher : vouch) : Bool :=
  trustState.revocations.any fun revocation =>
    revocation.revoker == voucher.voucher && revocation.revoked == voucher.vouchee
        && revocation.timestamp > 0

/-- Find vouch chain from root to target.
    Returns some [] for direct trust, some [v1, v2, ...] for vouch chain, none for no path.
    Note: Uses fuel parameter to ensure termination in potentially cyclic trust graphs.
    In practice, vouch chains should be DAGs. -/
noncomputable
def find_vouch_chain
    (trustState : TrustState)
    (target : HybridPublicKey)
    (fuel : Nat := 100)
    : Option (List vouch) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if trustState.direct.any (· == target) then
      some []
    else
      let validVouches :=
        trustState.vouches.filter fun voucher =>
          !trustState.is_revoked voucher && voucher.vouchee == target
      validVouches.findSome? fun voucher =>
        (find_vouch_chain trustState voucher.voucher fuel').map (voucher :: ·)

/-- Compute authority bound from vouch chain.
    Authority NARROWS through delegation: chain_authority = all ⊓ v1.scope ⊓ v2.scope ⊓ ... -/
def chain_authority (chain : List vouch) : Authority :=
  chain.foldl (fun authority item => min authority item.scope) Authority.all

/-- Get authority for a pubkey.
    Direct trust → Authority.all, no path → Authority.none, vouch chain → bounded by chain. -/
noncomputable
def authority_of
    (trustState : TrustState)
    (publicKey : HybridPublicKey)
    (now : Timestamp)
    : Authority :=
  if trustState.direct.any (· == publicKey) then
    Authority.all
  else
    match trustState.find_vouch_chain publicKey with
    | none => Authority.none
    | some chain =>
      let validChain := chain.filter (fun voucher => voucher.expires > now)
      if validChain.length != chain.length then
        Authority.none  -- Some vouch expired
      else
        chain_authority chain

/-- Get recognition level for a pubkey. -/
noncomputable
def recognition_of (trustState : TrustState) (publicKey : HybridPublicKey) : RecognitionLevel :=
  if trustState.direct.any (· == publicKey) then
    .direct
  else
    match trustState.find_vouch_chain publicKey with
    | none       => .unrecognized
    | some chain => .vouched chain.length

/-- Simple recognition level based on direct trust (legacy) -/
noncomputable
def recognition (trustState : TrustState) (publicKey : HybridPublicKey) : RecognitionLevel :=
  if trustState.is_direct publicKey then .direct else .unrecognized

end TrustState

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                     // THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Empty trust state has no direct trusts. -/
theorem empty_no_direct : TrustState.direct_count ⟨[], [], []⟩ = 0 := rfl

/-- Adding to direct increases count. -/
theorem add_direct_increases
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        : TrustState.direct_count { trustState with direct := publicKey :: trustState.direct }
            = trustState.direct_count + 1 := by
  simp only [TrustState.direct_count, List.length_cons]

/-- Trust distance is reflexive. -/
theorem trust_distance_refl : ∀ a : TrustDistance, a ≤ a := by
  intro distance

  unfold LE.le instLETrustDistance

  exact Nat.le_refl _

/-- Vouch chain length is non-negative. -/
theorem vouch_chain_nonneg (chain : List vouch) : 0 ≤ chain.length := Nat.zero_le _

/-- Unrecognized is minimum recognition. -/
theorem unrecognized_min : ∀ r : RecognitionLevel, .unrecognized ≤ r := by
  intro recognition

  simp only [LE.le, RecognitionLevel.rank]

  exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
--                                                      // VOUCH CHAIN // THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A single vouch step can only reduce authority via meet. -/
theorem vouch_step_reduces_authority
        (authority : Authority)
        (item : vouch)
        : min authority item.scope ≤ authority := by
  exact authority_meet_le_left authority item.scope

/-- Helper: foldl with meet is monotone in its initial value. -/
theorem foldl_meet_monotone
        (init₁ init₂ : Authority)
        (chain : List vouch)
        (initialLe : init₁ ≤ init₂)
        : chain.foldl (fun authority item => min authority item.scope) init₁
            ≤ chain.foldl (fun authority item => min authority item.scope) init₂ := by
  induction chain generalizing init₁ init₂ with
  | nil => exact initialLe
  | cons voucher chain' inductionProof =>
    simp only [List.foldl_cons]
    apply inductionProof
    simp only [LE.le, Authority.subset, Min.min, Authority.meet] at initialLe ⊢
    simp only [List.mem_filter]
    intro capability ⟨initialMembership, scopeMembership⟩
    exact ⟨initialLe capability initialMembership, scopeMembership⟩

/-- Chain authority is monotonically decreasing: adding a vouch can only reduce authority. -/
theorem chain_authority_monotone
        (chain : List vouch)
        (voucher : vouch)
        : TrustState.chain_authority (voucher :: chain) ≤ TrustState.chain_authority chain := by
  simp only [TrustState.chain_authority, List.foldl_cons]

  apply foldl_meet_monotone

  exact authority_meet_le_left _ _

/-- When directly trusted, find_vouch_chain returns empty list. -/
theorem find_vouch_chain_direct
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        (h_direct : trustState.direct.any (·== publicKey) = true)
        (fuel : Nat)
        (h_fuel : fuel > 0)
        : trustState.find_vouch_chain publicKey fuel = some [] := by
  match fuel with
  | 0 => omega
  | remainingFuel + 1 =>
    unfold TrustState.find_vouch_chain
    simp only [h_direct, ↓reduceIte]

/-- chain_authority of empty list is Authority.all -/
theorem chain_authority_nil : TrustState.chain_authority [] = Authority.all := by
  unfold TrustState.chain_authority

  simp only [List.foldl_nil]

/-- Authority through vouch chains is bounded by the meet of all vouches. -/
-- Helper lemma for filter length preservation
private
theorem filter_length_of_all_valid
        (chain : List vouch)
        (now : Timestamp)
        (h_valid : ∀ v ∈ chain, v.expires > now)
        : (chain.filter (fun voucher => voucher.expires > now)).length = chain.length := by
  induction chain with
  | nil => simp
  | cons headVouch tailVouches inductionProof =>
    simp only [List.filter, List.length_cons]
    have h_hd : decide (headVouch.expires > now) = true := by
      simp only [decide_eq_true_eq]
      exact h_valid headVouch List.mem_cons_self
    simp only [h_hd, List.length_cons]
    have tailLengthEquality :=
      inductionProof fun voucher membership =>
        h_valid voucher (List.mem_cons_of_mem headVouch membership)
    omega

theorem authority_bound_preservation
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        (chain : List vouch)
        (now : Timestamp)
        (h_chain : trustState.find_vouch_chain publicKey = some chain)
        (h_valid : ∀ v ∈ chain, v.expires > now)
        : trustState.authority_of publicKey now ≤ TrustState.chain_authority chain := by
  unfold TrustState.authority_of
  by_cases h_direct : trustState.direct.any (·== publicKey)
  case pos =>
    -- Direct trust: authority_of returns Authority.all
    -- and find_vouch_chain returns some [], so chain = []
    simp only [h_direct]
    have h_chain_nil := find_vouch_chain_direct trustState publicKey h_direct 100 (by omega)
    rw [h_chain_nil] at h_chain
    injection h_chain with chainEquation
    rw [← chainEquation]
    rw [chain_authority_nil]
    -- Authority.all ≤ Authority.all is reflexive by Authority.subset definition
    simp only [LE.le, Authority.subset]
    intro capability membership
    exact membership
  case neg =>
    simp only [Bool.not_eq_true] at h_direct
    simp only [h_direct]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_chain]
    simp only
    -- Now we need to prove that when chain is valid, result ≤ chain_authority
    have h_filter := filter_length_of_all_valid chain now h_valid
    have h_len_eq :
        ((chain.filter fun voucher => decide (voucher.expires > now)).length != chain.length)
            = false := by simp [h_filter]
    rw [h_len_eq]
    simp only [Bool.false_eq_true, ite_false]
    -- Now both sides are chain_authority chain, so ≤ is reflexive
    simp only [LE.le, Authority.subset]
    intro capability membership
    exact membership

/-- Direct trust gives full authority. -/
theorem direct_trust_max
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        (now : Timestamp)
        (h_direct : publicKey ∈ trustState.direct)
        : trustState.authority_of publicKey now = Authority.all := by
  simp only [TrustState.authority_of]
  have h_contains : trustState.direct.any (·== publicKey) = true := by
    simp only [List.any_eq_true]
    exact ⟨publicKey, h_direct, beq_self_eq_true publicKey⟩
  simp only [h_contains, ite_true]

/-- Unrecognized keys have no authority. -/
theorem unrecognized_no_authority
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        (now : Timestamp)
        (h_unrec : trustState.recognition_of publicKey = .unrecognized)
        : trustState.authority_of publicKey now = Authority.none := by
  simp only [TrustState.recognition_of] at h_unrec
  simp only [TrustState.authority_of]
  by_cases h_direct : trustState.direct.any (· == publicKey)
  case pos =>
    -- Direct trust means recognition is .direct, contradicting h_unrec
    simp only [h_direct, ite_true] at h_unrec
    -- h_unrec : RecognitionLevel.direct = RecognitionLevel.unrecognized
    cases h_unrec
  case neg =>
    simp only [Bool.not_eq_true] at h_direct
    simp only [h_direct] at h_unrec ⊢
    simp only [Bool.false_eq_true, ite_false] at h_unrec ⊢
    match h_chain : trustState.find_vouch_chain publicKey with
    | none => rfl
    | some chain =>
      -- If chain found, recognition is .vouched, not .unrecognized
      simp only [h_chain] at h_unrec
      -- h_unrec : RecognitionLevel.vouched chain.length = RecognitionLevel.unrecognized
      cases h_unrec

/-- Direct trust gives maximum recognition level. -/
theorem direct_max_recognition
        (trustState : TrustState)
        (publicKey : HybridPublicKey)
        (h_direct : publicKey ∈ trustState.direct)
        : trustState.recognition_of publicKey = .direct := by
  simp only [TrustState.recognition_of]
  have h_contains : trustState.direct.any (·== publicKey) = true := by
    simp only [List.any_eq_true]
    exact ⟨publicKey, h_direct, beq_self_eq_true publicKey⟩
  simp only [h_contains, ite_true]

/-- is_revoked is monotone (adding revocations only increases it). -/
theorem is_revoked_monotone
        : ∀ (trustState : TrustState) (newRevocation : revocation) (voucher : vouch),
            trustState.is_revoked voucher = true
                → { trustState with revocations := newRevocation :: trustState.revocations }.is_revoked
                  voucher
                    = true := by
  intro trustState newRevocation vouchedItem h_revoked

  simp only [TrustState.is_revoked] at h_revoked ⊢

  simp only [List.any_eq_true] at h_revoked ⊢

  obtain ⟨matchedRevocation, matchedMembership, matchedFields⟩ := h_revoked

  exact ⟨matchedRevocation, List.mem_cons_of_mem newRevocation matchedMembership, matchedFields⟩

/-- Revocation only removes trust paths, never adds them. -/
theorem revocation_preserves_valid_vouches
        (trustState : TrustState)
        (newRevocation : revocation)
        (voucher : vouch)
        (h_not_revoked' : { trustState with revocations := newRevocation :: trustState.revocations }.is_revoked
          voucher
            = false)
        : trustState.is_revoked voucher = false := by
  cases h_eq : trustState.is_revoked voucher with
  | false => rfl
  | true =>
    have h_still_revoked := is_revoked_monotone trustState newRevocation voucher h_eq
    rw [h_still_revoked] at h_not_revoked'
    exact absurd h_not_revoked'.symm Bool.false_ne_true

end Continuity.Trust
