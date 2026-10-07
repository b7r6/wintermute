/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // CONTINUITY // COEFFECT // GRADED
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SPIKE — coeffect grades on Mathlib `Finset`.

    The tensor (⊗) of coeffect demands is SET UNION; the pure demand is ∅;
    sub-effecting (weakening) is ⊆. `Finset` already gives us a `DistribLattice`,
    so the monoid/lattice laws that `Coeffect.Core` proves BY HAND collapse to
    Mathlib one-liners — and we gain the two things `List ++` could never give:

      · commutativity + idempotence (a demand is a SET, not a sequence), and
      · the sub-effecting ORDER ⊆, which is what makes reproducibility ANTITONE,
        `hermetic ⟹ reproducible` a lift of a pointwise fact, and the
        environment-satisfies-demand check DECIDABLE (predict-failure-before-run).

    This module is parallel to `Coeffect.Core` and does not touch it — it exists
    to evaluate the migration before committing. See [[build-roadmap]].

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.coeffect.core
import continuity.data.finset

open Continuity.Data
--
--

namespace Continuity.Coeffect.Graded

open Continuity.Coeffect (Coeffect)

/-- A coeffect demand is a *set* of requirements. Tensor (⊗) is `∪`, the pure
    demand is `∅`, sub-effecting (weakening) is `⊆`. -/
abbrev Coeffects := Finset Coeffect

-- ══════════════════════════════════════════════════════════════════════════════
--  THE MONOID / LATTICE LAWS ARE NOW FREE  (cf. Coeffect.Core: tensor_assoc, …)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tensor_assoc
        (resource stateValue valueT : Coeffects)
        : (resource ∪ stateValue) ∪ valueT = resource ∪ (stateValue ∪ valueT) :=
  Finset.union_assoc resource stateValue valueT

theorem tensor_pure_left (resource : Coeffects) : (∅ : Coeffects) ∪ resource = resource :=
  Finset.empty_union resource

theorem tensor_pure_right (resource : Coeffects) : resource ∪ (∅ : Coeffects) = resource :=
  Finset.union_empty resource

/-- NEW — impossible under `List ++`, free under `Finset ∪`: order doesn't matter. -/
theorem tensor_comm
        (resource stateValue : Coeffects)
        : resource ∪ stateValue = stateValue ∪ resource :=
  Finset.union_comm resource stateValue

/-- NEW — demanding the same thing twice is demanding it once. -/
theorem tensor_idem (resource : Coeffects) : resource ∪ resource = resource :=
  Finset.union_idempotent resource

-- ══════════════════════════════════════════════════════════════════════════════
--  REPRODUCIBILITY  — a predicate over the demand set
-- ══════════════════════════════════════════════════════════════════════════════

/-- Which single coeffects are reproducible (deterministic / content-addressed).
    Same classification as `Coeffect.Core.Coeffects.isReproducible`. -/
def Reproducible : Coeffect → Bool
  | .pure           => true
  | .filesystemCA _ => true
  | .networkCA _    => true
  | .auth _         => true
  | .gpu _          => true
  | .sandbox _      => true
  | _               => false

/-- A demand is reproducible iff every coeffect in it is. -/
def isReproducible (resource : Coeffects) : Prop := ∀ c ∈ resource, Reproducible c

instance (resource : Coeffects) : Decidable (isReproducible resource) := by
  unfold isReproducible; infer_instance

/-- `tensor_reproducible` (Core) — now one lemma: union of reproducible demands is
    reproducible, because membership in `r ∪ s` splits. -/
theorem tensor_reproducible
        {resource stateValue : Coeffects}
        (relationHypothesis : isReproducible resource)
        (hypotheses : isReproducible stateValue)
        : isReproducible (resource ∪ stateValue) := by
  simp only [isReproducible, Finset.forall_mem_union]

  exact ⟨relationHypothesis, hypotheses⟩

/-- THE PAYOFF the order unlocks: reproducibility is ANTITONE in `⊆`. A *smaller*
    demand inherits reproducibility — there is no `List ++` analogue of this. -/
theorem reproducible_antitone
        {resource stateValue : Coeffects}
        (hypothesis : resource ⊆ stateValue)
        (hypotheses : isReproducible stateValue)
        : isReproducible resource := by
  intro coeffect coeffectMem
  exact hypotheses coeffect (hypothesis coeffectMem)

-- ══════════════════════════════════════════════════════════════════════════════
--  HERMETICITY  ⟹  REPRODUCIBILITY  — a lift of a pointwise implication
-- ══════════════════════════════════════════════════════════════════════════════

/-- Hermetic single coeffects: content-addressed or sandboxed only — strictly
    fewer than `Reproducible` (excludes `auth`/`gpu`). -/
def Hermetic : Coeffect → Bool
  | .pure           => true
  | .filesystemCA _ => true
  | .networkCA _    => true
  | .sandbox _      => true
  | _               => false

/-- Pointwise: hermetic ⟹ reproducible (auth/gpu witness the strict inclusion). -/
theorem hermetic_le_reproducible (valueC : Coeffect) : Hermetic valueC → Reproducible valueC := by
  cases valueC <;> simp [Hermetic, Reproducible]

/-- A demand is hermetic iff every coeffect in it is. -/
def isHermetic (resource : Coeffects) : Prop := ∀ c ∈ resource, Hermetic c

/-- Headline (cf. gist `hermetic_implies_reproducible`): a hermetic build is
    reproducible — the pointwise fact lifted over the demand set. -/
theorem hermetic_implies_reproducible
        {resource : Coeffects}
        (hypothesis : isHermetic resource)
        : isReproducible resource := by
  intro coeffect coeffectMem

  exact hermetic_le_reproducible coeffect (hypothesis coeffect coeffectMem)

-- ══════════════════════════════════════════════════════════════════════════════
--  IMPURITY GRADE  — a free monoid hom (Coeffects, ∪, ∅) → (ℕ, ⊔, 0)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Impurity level of a single coeffect: 0 pure … 3 nondeterministic. -/
def impurity : Coeffect → ℕ
  | .pure           => 0
  | .filesystemCA _ => 1
  | .networkCA _    => 1
  | .sandbox _      => 1
  | .auth _         => 1
  | .gpu _          => 1
  | .filesystem _   => 2
  | .network _ _    => 2
  | .environment _  => 2
  | .identity       => 2
  | .time           => 3
  | .random         => 3

/-- A build's impurity is the WORST coeffect it demands (the join). -/
def maxImpurity (resource : Coeffects) : ℕ := resource.sup impurity

/-- `minPurity`-as-hom, dualized: combining demands takes the max impurity — a free
    monoid homomorphism via `Finset.sup_union`, replacing Core's hand-rolled fold. -/
theorem maxImpurity_tensor
        (resource stateValue : Coeffects)
        : maxImpurity (resource ∪ stateValue) = maxImpurity resource ⊔ maxImpurity stateValue := by
  simp only [maxImpurity, Finset.sup_union]

/-- The pure demand is maximally pure. -/
theorem maxImpurity_pure : maxImpurity (∅ : Coeffects) = 0 := by simp [maxImpurity]

-- ══════════════════════════════════════════════════════════════════════════════
--  PREDICT-FAILURE-BEFORE-RUN  — the demand check is DECIDABLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- The environment `supply` satisfies a build's `demand` iff `demand ⊆ supply`. -/
def satisfiedBy (demand supply : Coeffects) : Prop := demand ⊆ supply

/-- The check is decidable AND computable: it `decide`s at elaboration, so an
    under-provisioned build is a *type* error, not a runtime failure. -/
instance (demand supply : Coeffects) : Decidable (satisfiedBy demand supply) :=
  inferInstanceAs (Decidable (demand ⊆ supply))

/-- Satisfaction is monotone: a richer environment still satisfies the demand. -/
theorem satisfiedBy_mono
        {demand supply supply' : Coeffects}
        (hypothesis : satisfiedBy demand supply)
        (hsup : supply ⊆ supply')
        : satisfiedBy demand supply' :=
  Finset.Subset.trans hypothesis hsup

-- ══════════════════════════════════════════════════════════════════════════════
--  IT COMPUTES  — these `decide` at elaboration. Impossible while `Hash` was opaque;
--  the last one exercises the now-computable `DecidableEq` *through* a `Hash` payload.
-- ══════════════════════════════════════════════════════════════════════════════

example : satisfiedBy ({.pure} : Coeffects) {.pure, .time} := by decide

example : ¬satisfiedBy ({.time} : Coeffects) {.pure} := by decide

example :
    satisfiedBy ({.filesystemCA ⟨⟨#[1, 2, 3]⟩⟩} : Coeffects) {.filesystemCA ⟨⟨#[1, 2, 3]⟩⟩, .pure} := by
  decide

example : ¬satisfiedBy ({.filesystemCA ⟨⟨#[1, 2, 3]⟩⟩} : Coeffects) {.filesystemCA ⟨⟨#[9, 9, 9]⟩⟩} := by
  decide

end Continuity.Coeffect.Graded
