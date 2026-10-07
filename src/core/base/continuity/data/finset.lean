import Batteries.Data.List.Perm
set_option autoImplicit false
namespace Continuity.Data

structure Finset (α : Type) [DecidableEq α] where
  val   : List α
  nodup : val.Nodup

namespace Finset
variable {α : Type} [DecidableEq α]

protected
def empty : Finset α := ⟨[], List.nodup_nil⟩

instance : EmptyCollection (Finset α) := ⟨Finset.empty⟩
instance : Membership α (Finset α) := ⟨fun collection element => element ∈ collection.val⟩

instance inst_dec_mem (elementA : α) (setValue : Finset α) : Decidable (elementA ∈ setValue) :=
  inferInstanceAs (Decidable (elementA ∈ setValue.val))

@[simp]
theorem not_mem_empty (elementA : α) : elementA ∉ (∅ : Finset α) := by
  intro emptyMem
  exact (List.not_mem_nil) emptyMem

@[simp]
theorem mem_empty_iff (elementA : α) : elementA ∈ (∅ : Finset α) ↔ False :=
  ⟨fun membership => not_mem_empty elementA membership, False.elim⟩

def insert (elementA : α) (setValue : Finset α) : Finset α :=
  if h : elementA ∈ setValue.val then
    setValue
  else
    ⟨elementA :: setValue.val, List.nodup_cons.mpr ⟨h, setValue.nodup⟩⟩

def union (setOne setTwo : Finset α) : Finset α :=
  setTwo.val.foldl (fun result item => result.insert item) setOne

instance : Union (Finset α) := ⟨union⟩

def erase (setValue : Finset α) (elementA : α) : Finset α :=
  ⟨setValue.val.erase elementA, setValue.nodup.erase elementA⟩

@[simp]
theorem mem_erase
        {elementA elementB : α}
        {setValue : Finset α}
        : elementA ∈ setValue.erase elementB ↔ elementA ≠ elementB ∧ elementA ∈ setValue :=
  setValue.nodup.mem_erase_iff

def image {β : Type} [DecidableEq β] (function : α → β) (setValue : Finset α) : Finset β :=
  setValue.val.foldl (fun result item => result.insert (function item)) ∅

def card (setValue : Finset α) : Nat := setValue.val.length

/-
  Finset extensionality. We back `Finset` by a `List` with a `Nodup` proof rather than
  by `Quotient (Perm)` (Mathlib's `Multiset` route) to stay Mathlib-free and keep the
  representation computable for the build tool's hot path. The cost of that choice is a
  single irreducible assumption: two `Nodup` lists with the same members denote the same
  finite set. The honest content splits cleanly:

    • `nodup_same_mem_perm` (THEOREM, from Batteries): same members ⟹ the lists are a
      permutation of each other. Order is the only thing that can differ.
    • `perm_nodup_eq` (AXIOM): a permutation of `Nodup` lists yields *equal* `Finset`s.
      This is exactly the quotient-by-`Perm` identification that `Multiset` makes
      definitional; here we assert it. It is consistent (it holds in the `Multiset`
      model) and is the sole axiom this vendored library adds.
-/
theorem nodup_same_mem_perm
        {listOne listTwo : List α}
        (hypothesisOne : listOne.Nodup)
        (hypothesisTwo : listTwo.Nodup)
        (membershipHypothesis : ∀ a, a ∈ listOne ↔ a ∈ listTwo)
        : listOne.Perm listTwo :=
  (List.perm_ext_iff_of_nodup hypothesisOne hypothesisTwo).mpr membershipHypothesis

axiom perm_nodup_eq {listOne listTwo : List α} (predicateHypothesis : listOne.Perm listTwo) (hypothesisOne : listOne.Nodup) (hypothesisTwo : listTwo.Nodup) : listOne = listTwo

theorem nodup_ext
        {listOne listTwo : List α}
        (hypothesisOne : listOne.Nodup)
        (hypothesisTwo : listTwo.Nodup)
        (membershipHypothesis : ∀ a, a ∈ listOne ↔ a ∈ listTwo)
        : listOne = listTwo :=
  perm_nodup_eq
    (nodup_same_mem_perm hypothesisOne hypothesisTwo membershipHypothesis)
    hypothesisOne
    hypothesisTwo

theorem ext
        {setOne setTwo : Finset α}
        (hypothesis : ∀ a, a ∈ setOne ↔ a ∈ setTwo)
        : setOne = setTwo := by
  cases setOne; cases setTwo; simp only [Finset.mk.injEq]; exact nodup_ext ‹_› ‹_› hypothesis

@[simp]
theorem mem_insert_iff
        {elementA elementB : α}
        {setValue : Finset α}
        : elementA ∈ setValue.insert elementB ↔ elementA = elementB ∨ elementA ∈ setValue := by
  unfold insert; split
  · next existingMember =>
      exact
        ⟨
          fun memberProof => Or.inr memberProof,
          fun | .inl equalityProof => equalityProof ▸ existingMember | .inr memberProof => memberProof
        ⟩
  · next => exact List.mem_cons

@[simp]
theorem mem_insert_self
        (elementA : α)
        (setValue : Finset α)
        : elementA ∈ setValue.insert elementA :=
  mem_insert_iff.mpr (Or.inl rfl)

@[simp]
theorem erase_insert
        {elementA : α}
        {setValue : Finset α}
        (hypothesis : elementA ∉ setValue)
        : (setValue.insert elementA).erase elementA = setValue := by
  apply ext
  intro candidate
  rw [mem_erase, mem_insert_iff]
  constructor
  · rintro ⟨candidateNe, candidateMem⟩; exact candidateMem.resolve_left candidateNe
  · intro candidateMem
    exact ⟨fun equality => hypothesis (equality ▸ candidateMem), Or.inr candidateMem⟩

theorem mem_foldl_insert_of_mem
        {elementA : α}
        {result : Finset α}
        {elements : List α}
        (hypothesis : elementA ∈ result)
        : elementA ∈ elements.foldl (fun result item => result.insert item) result := by
  induction elements generalizing result with
  | nil => exact hypothesis
  | cons _ _ inductionHypothesis =>
    exact inductionHypothesis (mem_insert_iff.mpr (Or.inr hypothesis))

theorem mem_foldl_insert_of_elem
        {elementA : α}
        {result : Finset α}
        {elements : List α}
        (hypothesis : elementA ∈ elements)
        : elementA ∈ elements.foldl (fun result item => result.insert item) result := by
  induction elements generalizing result with
  | nil => nomatch hypothesis
  | cons head tail inductionHypothesis =>
    simp only [List.foldl]
    cases List.mem_cons.mp hypothesis with
    | inl headEq => exact headEq ▸ mem_foldl_insert_of_mem (mem_insert_iff.mpr (Or.inl rfl))
    | inr tailMem => exact inductionHypothesis tailMem

theorem mem_foldl_insert_iff
        {elementA : α}
        {result : Finset α}
        {elements : List α}
        : elementA ∈ elements.foldl (fun result item => result.insert item) result
            ↔ elementA ∈ result ∨ elementA ∈ elements := by
  constructor
  · intro membership; induction elements generalizing result with
    | nil => exact Or.inl membership
    | cons head tail inductionHypothesis =>
      simp only [List.foldl] at membership
      cases inductionHypothesis membership with
      | inl resultMem => cases mem_insert_iff.mp resultMem with
        | inl headEq => exact Or.inr (List.mem_cons.mpr (Or.inl headEq))
        | inr priorResultMem => exact Or.inl priorResultMem
      | inr tailMem => exact Or.inr (List.mem_cons.mpr (Or.inr tailMem))
  · intro membership; cases membership with
    | inl resultMem => exact mem_foldl_insert_of_mem resultMem
    | inr listMem => exact mem_foldl_insert_of_elem listMem

theorem mem_union_left
        {elementA : α}
        {setOne : Finset α}
        (setTwo : Finset α)
        (hypothesis : elementA ∈ setOne)
        : elementA ∈ setOne ∪ setTwo :=
  mem_foldl_insert_of_mem hypothesis

theorem mem_union_right
        {elementA : α}
        (setOne : Finset α)
        {setTwo : Finset α}
        (hypothesis : elementA ∈ setTwo)
        : elementA ∈ setOne ∪ setTwo :=
  mem_foldl_insert_of_elem hypothesis

@[simp]
theorem union_empty (setValue : Finset α) : setValue ∪ ∅ = setValue := rfl

@[simp]
theorem empty_union (setValue : Finset α) : ∅ ∪ setValue = setValue :=
  ext fun element =>
    ⟨
      fun membership => (mem_foldl_insert_iff.mp membership).elim (nomatch ·) id,
      fun membership => mem_foldl_insert_of_elem membership
    ⟩

theorem union_comm (setOne setTwo : Finset α) : setOne ∪ setTwo = setTwo ∪ setOne :=
  ext fun element =>
    ⟨
      fun membership => match mem_foldl_insert_iff.mp membership with
        | .inl membership => mem_foldl_insert_of_elem membership
        | .inr membership => mem_foldl_insert_of_mem membership,
      fun membership => match mem_foldl_insert_iff.mp membership with
        | .inl membership => mem_foldl_insert_of_elem membership
        | .inr membership => mem_foldl_insert_of_mem membership
    ⟩

theorem union_assoc
        (setOne setTwo setThree : Finset α)
        : setOne ∪ setTwo ∪ setThree = setOne ∪ (setTwo ∪ setThree) :=
  ext fun element =>
    ⟨
      fun membership => match mem_foldl_insert_iff.mp membership with
        | .inl membership =>
          match mem_foldl_insert_iff.mp membership with
          | .inl nestedMembership => mem_foldl_insert_of_mem nestedMembership
          | .inr nestedMembership =>
            mem_foldl_insert_of_elem (mem_foldl_insert_of_mem nestedMembership)
        | .inr membership => mem_foldl_insert_of_elem (mem_foldl_insert_of_elem membership),
      fun membership => match mem_foldl_insert_iff.mp membership with
        | .inl membership => mem_foldl_insert_of_mem (mem_foldl_insert_of_mem membership)
        | .inr membership =>
          match mem_foldl_insert_iff.mp membership with
          | .inl nestedMembership =>
            mem_foldl_insert_of_mem (mem_foldl_insert_of_elem nestedMembership)
          | .inr nestedMembership => mem_foldl_insert_of_elem nestedMembership
    ⟩

instance : LE (Finset α) := ⟨fun left right => ∀ ⦃element⦄, element ∈ left → element ∈ right⟩

-- ═══ Subset (⊆) ═══

protected
def Subset (setOne setTwo : Finset α) : Prop := ∀ ⦃elementA⦄, elementA ∈ setOne → elementA ∈ setTwo

instance : HasSubset (Finset α) := ⟨Finset.Subset⟩

instance dec_subset (setOne setTwo : Finset α) : Decidable (setOne ⊆ setTwo) :=
  decidable_of_iff
    (∀ element ∈ setOne.val, element ∈ setTwo.val)
    ⟨
      fun subsetProof _ membership => subsetProof _ membership,
      fun subsetProof _ membership => subsetProof membership
    ⟩

theorem Subset.refl (setValue : Finset α) : setValue ⊆ setValue := fun _ membership => membership

theorem Subset.trans
        {setOne setTwo setThree : Finset α}
        (hypothesisOne : setOne ⊆ setTwo)
        (hypothesisTwo : setTwo ⊆ setThree)
        : setOne ⊆ setThree := fun _ membership => hypothesisTwo (hypothesisOne membership)

theorem ext_iff {setOne setTwo : Finset α} : setOne = setTwo ↔ (∀ a, a ∈ setOne ↔ a ∈ setTwo) :=
  ⟨fun equality => equality ▸ fun _ => Iff.rfl, ext⟩

theorem subset_antisymm
        {setOne setTwo : Finset α}
        (hypothesisOne : setOne ⊆ setTwo)
        (hypothesisTwo : setTwo ⊆ setOne)
        : setOne = setTwo :=
  ext fun element =>
    ⟨fun membership => hypothesisOne membership, fun membership => hypothesisTwo membership⟩

instance decEq : DecidableEq (Finset α) := fun left right =>
  if h : left ⊆ right ∧ right ⊆ left then
    isTrue (subset_antisymm h.1 h.2)
  else
    isFalse fun equality => h ⟨equality ▸ Subset.refl left, equality ▸ Subset.refl left⟩

theorem forall_mem_union
        {setOne setTwo : Finset α}
        {predicate : α → Prop}
        : (∀ a ∈ setOne ∪ setTwo, predicate a)
            ↔ (∀ a ∈ setOne, predicate a) ∧ (∀ a ∈ setTwo, predicate a) := by
  constructor
  · intro unionProperty
    exact
      ⟨
        fun element membership => unionProperty element (mem_union_left setTwo membership),
        fun element membership => unionProperty element (mem_union_right setOne membership)
      ⟩
  · intro ⟨leftProperty, rightProperty⟩ element elementMem
    cases mem_foldl_insert_iff.mp elementMem with
    | inl leftMem => exact leftProperty element leftMem
    | inr rightMem => exact rightProperty element rightMem

@[simp]
theorem union_idempotent (setValue : Finset α) : setValue ∪ setValue = setValue :=
  ext fun element =>
    ⟨
      fun membership => (mem_foldl_insert_iff.mp membership).elim id id,
      fun membership => mem_union_left setValue membership
    ⟩

-- ═══ Intersection ═══

def inter (setOne setTwo : Finset α) : Finset α :=
  ⟨setOne.val.filter (fun element => decide (element ∈ setTwo.val)), setOne.nodup.filter _⟩

instance : Inter (Finset α) := ⟨inter⟩

@[simp]
theorem mem_inter
        {elementA : α}
        {setOne setTwo : Finset α}
        : elementA ∈ setOne ∩ setTwo ↔ elementA ∈ setOne ∧ elementA ∈ setTwo := by
  show elementA ∈ (setOne.val.filter (fun element => decide (element ∈ setTwo.val))) ↔
    (elementA ∈ setOne.val ∧ elementA ∈ setTwo.val)

  rw [List.mem_filter]

  constructor

  · rintro ⟨memberOfFirst, memberOfSecond⟩
    exact ⟨memberOfFirst, of_decide_eq_true memberOfSecond⟩

  · rintro ⟨memberOfFirst, memberOfSecond⟩
    exact ⟨memberOfFirst, decide_eq_true memberOfSecond⟩

-- ═══ sup: fold a function into a max-semilattice with explicit bottom ═══

def supWith {β : Type} [Max β] (setValue : Finset α) (function : α → β) (init : β) : β :=
  setValue.val.foldl (fun result item => Max.max result (function item)) init

end Finset

-- ═══ Mathlib-compat notation: ⊔ (Sup) and ℕ ═══

class Sup (α : Type) where
  sup : α → α → α

infixl:68 " ⊔ " => Sup.sup
instance {α : Type} [Max α] : Sup α := ⟨Max.max⟩

notation "ℕ" => Nat

namespace Finset
variable {α : Type} [DecidableEq α]

/-- `sup` over a Sup-with-bottom: the Graded.lean entry point. Uses 0 as ⊥ for Nat. -/
def sup {β : Type} [Sup β] [OfNat β 0] (setValue : Finset α) (function : α → β) : β :=
  setValue.val.foldl (fun result item => Sup.sup result (function item)) (0 : β)

-- ═══ Set literal support: {x}, {x, y, z} ═══

instance : Singleton α (Finset α) := ⟨fun element => ⟨[element], by simp⟩⟩

instance : Insert α (Finset α) := ⟨Finset.insert⟩

-- Typeclass-form simp lemmas (head = Insert.insert, kept explicit so they fire)
@[simp]
theorem mem_insertC
        {elementA elementB : α}
        {setValue : Finset α}
        : @Membership.mem α (Finset α) _ (Insert.insert elementB setValue) elementA
            ↔ elementA = elementB ∨ elementA ∈ setValue :=
  mem_insert_iff

@[simp]
theorem erase_insertC
        {elementA : α}
        {setValue : Finset α}
        (hypothesis : elementA ∉ setValue)
        : (Insert.insert elementA setValue : Finset α).erase elementA = setValue :=
  erase_insert hypothesis

@[simp]
theorem mem_singleton
        {elementA elementB : α}
        : elementA ∈ ({elementB} : Finset α) ↔ elementA = elementB := by
  show elementA ∈ [elementB] ↔ elementA = elementB

  simp

/-- Build a Finset from a List by folding insert. -/
def _root_.List.toFinset (listValue : List α) : Finset α := listValue.foldr Finset.insert ∅

@[simp]
theorem _root_.List.toFinset_cons
        (elementA : α)
        (listValue : List α)
        : (elementA :: listValue).toFinset = insert elementA listValue.toFinset :=
  rfl

@[simp]
theorem _root_.List.toFinset_nil : ([] : List α).toFinset = ∅ := rfl

@[simp]
theorem singleton_union
        (elementA : α)
        (setValue : Finset α)
        : ({elementA} : Finset α) ∪ setValue = insert elementA setValue := by
  apply ext
  intro candidate
  show candidate ∈ ({elementA} : Finset α) ∪ setValue ↔ candidate ∈ setValue.insert elementA
  rw [mem_insert_iff]
  constructor
  · intro unionMem
    exact
      (mem_foldl_insert_iff.mp unionMem).elim
        (fun membership => Or.inl (mem_singleton.mp membership))
        Or.inr
  · intro insertMem
    exact
      insertMem.elim
        (fun equality => mem_union_left setValue (mem_singleton.mpr equality))
        (fun membership => mem_union_right {elementA} membership)

end Finset

-- ═══ sup_union for Nat (the impurity homomorphism) ═══

namespace Finset
variable {α : Type} [DecidableEq α]

private
theorem natFoldlMax_init
        (listValue : List Nat)
        (elementA elementB : Nat)
        : listValue.foldl Nat.max (Nat.max elementA elementB)
            = Nat.max elementA (listValue.foldl Nat.max elementB) := by
  induction listValue generalizing elementA elementB with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    simp only [List.foldl]
    rw [show (elementA.max elementB).max head = elementA.max (elementB.max head) from Nat.max_assoc elementA elementB head]
    exact inductionHypothesis elementA (elementB.max head)

private
theorem leFoldlMax (listValue : List Nat) (init : Nat) : init ≤ listValue.foldl Nat.max init := by
  induction listValue generalizing init with
  | nil => exact Nat.le_refl _
  | cons head tail inductionHypothesis =>
    simp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left init head) (inductionHypothesis _)

private
theorem memLeFoldlMax
        (listValue : List Nat)
        (init elementA : Nat)
        (hypothesis : elementA ∈ listValue)
        : elementA ≤ listValue.foldl Nat.max init := by
  induction listValue generalizing init with
  | nil => nomatch hypothesis
  | cons head tail inductionHypothesis =>
    simp only [List.foldl]
    cases List.mem_cons.mp hypothesis with
    | inl headEq =>
      subst headEq
      exact Nat.le_trans (Nat.le_max_right init elementA) (leFoldlMax tail _)
    | inr tailMem => exact inductionHypothesis _ tailMem

private
theorem foldlMaxLe
        (listValue : List Nat)
        (init elementB : Nat)
        (hinit : init ≤ elementB)
        (hmem : ∀ a ∈ listValue, a ≤ elementB)
        : listValue.foldl Nat.max init ≤ elementB := by
  induction listValue generalizing init with
  | nil => exact hinit
  | cons head tail inductionHypothesis =>
    simp only [List.foldl]
    exact
      inductionHypothesis
        (Nat.max init head)
        (Nat.max_le.mpr ⟨hinit, hmem head (List.mem_cons_self ..)⟩)
        (fun element membership => hmem element (List.mem_cons.mpr (Or.inr membership)))

private
theorem foldlSupEqMap
        (listValue : List α)
        (function : α → Nat)
        (init : Nat)
        : listValue.foldl (fun result item => Nat.max result (function item)) init
            = (listValue.map function).foldl Nat.max init := by
  induction listValue generalizing init with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    simp only [List.foldl, List.map]
    exact inductionHypothesis (Nat.max init (function head))

/-- sup expressed as foldl max over the mapped list. -/
private
theorem sup_eq_foldl
        (setValue : Finset α)
        (function : α → Nat)
        : setValue.sup function = (setValue.val.map function).foldl Nat.max 0 := by
  show setValue.val.foldl (fun result item => Nat.max result (function item)) 0 = _

  exact foldlSupEqMap setValue.val function 0

/-- a ∈ s → f a ≤ s.sup f -/
theorem le_sup
        {setValue : Finset α}
        {function : α → Nat}
        {elementA : α}
        (hypothesis : elementA ∈ setValue)
        : function elementA ≤ setValue.sup function := by
  rw [sup_eq_foldl]

  exact
    memLeFoldlMax
      (setValue.val.map function)
      0
      (function elementA)
      (List.mem_map.mpr ⟨elementA, hypothesis, rfl⟩)

/-- s.sup f ≤ b if every member's image is ≤ b -/
theorem sup_le
        {setValue : Finset α}
        {function : α → Nat}
        {elementB : Nat}
        (hypothesis : ∀ a ∈ setValue, function a ≤ elementB)
        : setValue.sup function ≤ elementB := by
  rw [sup_eq_foldl]

  refine foldlMaxLe (setValue.val.map function) 0 elementB (Nat.zero_le elementB) ?_

  intro image imageMem

  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp imageMem

  exact hypothesis source sourceMem

/-- sup over the empty set is 0. -/
@[simp]
theorem sup_empty (function : α → Nat) : (∅ : Finset α).sup function = 0 := rfl

/-- The impurity sup is a monoid homomorphism: distributes over union.
    Proven by antisymmetry using le_sup / sup_le and mem_union. -/
@[simp]
theorem sup_union
        (setOne setTwo : Finset α)
        (function : α → Nat)
        : (setOne ∪ setTwo).sup function = setOne.sup function ⊔ setTwo.sup function := by
  show (setOne ∪ setTwo).sup function = Nat.max (setOne.sup function) (setTwo.sup function)
  apply Nat.le_antisymm
  · apply sup_le
    intro element elementMem
    cases mem_foldl_insert_iff.mp elementMem with
    | inl leftMem => exact Nat.le_trans (le_sup leftMem) (Nat.le_max_left _ _)
    | inr rightMem => exact Nat.le_trans (le_sup rightMem) (Nat.le_max_right _ _)
  · apply Nat.max_le.mpr
    refine
      ⟨
        sup_le fun element membership => le_sup (mem_union_left setTwo membership),
        sup_le fun element membership => le_sup (mem_union_right setOne membership)
      ⟩

end Finset

namespace GradedMonoid

class gone {ι : Type} [Zero ι] (carrier : ι → Type) where
  one : carrier 0

class gmul {ι : Type} [Add ι] (carrier : ι → Type) where
  mul : {index indexJ : ι} → carrier index → carrier indexJ → carrier (index + indexJ)

end GradedMonoid

structure galois_connection {α β : Type} [LE α] [LE β] (listValue : α → β) (elementU : β → α) : Prop where
  le_iff_le : ∀ (elementA : α) (elementB : β), listValue elementA ≤ elementB ↔ elementA ≤ elementU elementB

end Continuity.Data
