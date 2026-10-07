/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               // CONTINUITY // AUTHORITY

                      Capability Lattice and Security Levels

                                                straylight.software · 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "With great power comes great responsibility."
    "With no power comes no responsibility."
                                        — capability-based security

Authority forms a MEET-SEMILATTICE. The meet (⊓) is intersection.
Security forms a JOIN-SEMILATTICE. The join (⊔) is minimum.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Trust.Authority

-- ══════════════════════════════════════════════════════════════════════════════
--                                          // SECURITY LEVEL  // JOIN-SEMILATTICE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Security level of cryptographic operations. Higher = better. -/
inductive SecurityLevel where
  | plain     -- Unauthenticated
  | classical -- Classical crypto (ed25519)
  | quantum   -- Post-quantum (hybrid)
  deriving DecidableEq, Repr

namespace SecurityLevel

def rank : SecurityLevel → Nat
  | plain     => 0
  | classical => 1
  | quantum   => 2

theorem rank_injective
        : ∀ leftLevel rightLevel, rank leftLevel = rank rightLevel → leftLevel = rightLevel := by
  intro leftLevel rightLevel ranksEqual

  cases leftLevel <;> cases rightLevel <;> first | rfl | (simp only [rank] at ranksEqual; omega)

/-- Join (⊔): the MINIMUM security level (weakest link). -/
def join (left right : SecurityLevel) : SecurityLevel :=
  if rank left ≤ rank right then left else right

end SecurityLevel

instance : LE SecurityLevel where
  le a b := SecurityLevel.rank a ≤ SecurityLevel.rank b

instance : Max SecurityLevel where
  max := SecurityLevel.join

theorem security_join_comm : ∀ a b : SecurityLevel, max a b = max b a := by
  intro leftLevel rightLevel
  simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]
  cases leftLevel <;> cases rightLevel <;> simp

theorem security_join_assoc : ∀ a b c : SecurityLevel, max (max a b) c = max a (max b c) := by
  intro firstLevel secondLevel thirdLevel
  simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]
  cases firstLevel <;> cases secondLevel <;> cases thirdLevel <;> simp

theorem security_join_idem : ∀ a : SecurityLevel, max a a = a := by
  intro level
  simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]
  cases level <;> simp

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                 // CAPABILITIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Individual capabilities: what you're allowed to do. -/
inductive Capability where
  | shell (user : String)
  | exec (user : String) (command : String)
  | gitUploadPack (repos : List String)
  | gitReceivePack (repos : List String)
  | portForward (ports : List (String × Nat))
  | sftp (paths : List String)
  | build (targets : List String) -- Can build these targets
  | attest (scopes : List String) -- Can sign attestations for these
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════════════════════════
--                                                // AUTHORITY // MEET-SEMILATTICE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Authority: a set of capabilities. -/
structure Authority where
  capabilities : List Capability
  deriving DecidableEq, Repr

namespace Authority

def none : Authority := ⟨[]⟩

def all : Authority :=
  ⟨
    [
      .shell "root",
      .exec "root" "*",
      .gitUploadPack ["*"],
      .gitReceivePack ["*"],
      .portForward [],
      .sftp ["*"],
      .build ["*"],
      .attest ["*"]
    ]
  ⟩

def has (authority : Authority) (capability : Capability) : Bool :=
  authority.capabilities.contains capability

/-- Meet (⊓): intersection of capabilities. -/
def meet (left right : Authority) : Authority :=
  ⟨left.capabilities.filter (right.capabilities.contains ·)⟩

/-- Join (⊔): union of capabilities. -/
def join (left right : Authority) : Authority :=
  ⟨
    left.capabilities
        ++ right.capabilities.filter (fun capability => !left.capabilities.contains capability)
  ⟩

def subset (left right : Authority) : Prop :=
  ∀ capability ∈ left.capabilities, capability ∈ right.capabilities

/-- Extensionality for Authority. -/
theorem ext
        {left right : Authority}
        (capabilitiesEqual : left.capabilities = right.capabilities)
        : left = right := by
  cases left
  cases right
  simp only [Authority.mk.injEq]
  exact capabilitiesEqual

end Authority

instance : Min Authority where
  min := Authority.meet

instance : Max Authority where
  max := Authority.join

instance : LE Authority where
  le := Authority.subset

instance : DecidableRel (·≤ ·: Authority → Authority → Prop) := fun left right =>
  inferInstanceAs (Decidable (∀ capability ∈ left.capabilities, capability ∈ right.capabilities))

-- ══════════════════════════════════════════════════════════════════════════════
--                                                          // LATTICE // THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Set equivalence for Authority: same elements (possibly different order). -/
def Authority.set_equiv (left right : Authority) : Prop :=
  ∀ capability, capability ∈ left.capabilities ↔ capability ∈ right.capabilities

/-- Meet is commutative up to set equivalence: a ⊓ b ≈ b ⊓ a -/
theorem authority_meet_comm_equiv : ∀ a b : Authority, (min a b).set_equiv (min b a) := by
  intro leftAuthority rightAuthority capability
  simp only [Min.min, Authority.meet, List.mem_filter, List.contains_eq_any_beq, List.any_eq_true]
  constructor
  · intro ⟨hca, hcb⟩
    obtain ⟨witness, witnessInRight, capabilityEq⟩ := hcb
    simp only [beq_iff_eq] at capabilityEq
    subst capabilityEq
    exact ⟨witnessInRight, ⟨capability, hca, beq_self_eq_true capability⟩⟩
  · intro ⟨hcb, hca⟩
    obtain ⟨witness, witnessInLeft, capabilityEq⟩ := hca
    simp only [beq_iff_eq] at capabilityEq
    subst capabilityEq
    exact ⟨witnessInLeft, ⟨capability, hcb, beq_self_eq_true capability⟩⟩

/-- Meet is associative up to set equivalence: (a ⊓ b) ⊓ c ≈ a ⊓ (b ⊓ c) -/
theorem authority_meet_assoc_equiv
        : ∀ a b c : Authority, (min (min a b) c).set_equiv (min a (min b c)) := by
  intro firstAuthority secondAuthority thirdAuthority capability
  simp only [Min.min, Authority.meet, List.mem_filter, List.contains_eq_any_beq, List.any_eq_true]
  constructor
  · intro ⟨⟨hca, hcb⟩, hcc⟩
    obtain ⟨secondWitness, witnessInSecond, capabilityEqSecond⟩ := hcb
    simp only [beq_iff_eq] at capabilityEqSecond; subst capabilityEqSecond
    obtain ⟨thirdWitness, witnessInThird, capabilityEqThird⟩ := hcc
    simp only [beq_iff_eq] at capabilityEqThird; subst capabilityEqThird
    constructor
    · exact hca
    · exact
        ⟨
          capability,
          ⟨witnessInSecond, ⟨capability, witnessInThird, beq_self_eq_true capability⟩⟩,
          beq_self_eq_true capability
        ⟩
  · intro ⟨hca, hbc⟩
    obtain ⟨witness, witnessInMeet, capabilityEq⟩ := hbc
    simp only [beq_iff_eq] at capabilityEq; subst capabilityEq
    obtain ⟨secondMembership, hcc⟩ := witnessInMeet
    obtain ⟨thirdWitness, witnessInThird, capabilityEqThird⟩ := hcc
    simp only [beq_iff_eq] at capabilityEqThird; subst capabilityEqThird
    constructor
    · exact ⟨hca, ⟨capability, secondMembership, beq_self_eq_true capability⟩⟩
    · exact ⟨capability, witnessInThird, beq_self_eq_true capability⟩

/-- Meet is idempotent up to set equivalence: a ⊓ a ≈ a -/
theorem authority_meet_idem_equiv : ∀ a : Authority, (min a a).set_equiv a := by
  intro authority capability

  simp only [Min.min, Authority.meet, List.mem_filter, List.contains_eq_any_beq, List.any_eq_true]

  constructor

  · intro ⟨hca, _⟩; exact hca

  · intro hca; exact ⟨hca, ⟨capability, hca, beq_self_eq_true capability⟩⟩

/-- Backward compatibility: meet is commutative up to ≤ -/
theorem authority_meet_comm : ∀ a b : Authority, min a b ≤ min b a ∧ min b a ≤ min a b := by
  intro leftAuthority rightAuthority

  have equivalence := authority_meet_comm_equiv leftAuthority rightAuthority

  constructor

  · intro capability membership; exact (equivalence capability).mp membership

  · intro capability membership; exact (equivalence capability).mpr membership

theorem authority_meet_assoc
        : ∀ a b c : Authority, min (min a b) c ≤ min a (min b c) ∧ min a (min b c) ≤ min (min a b) c := by
  intro firstAuthority secondAuthority thirdAuthority

  have equivalence := authority_meet_assoc_equiv firstAuthority secondAuthority thirdAuthority

  constructor

  · intro capability membership; exact (equivalence capability).mp membership

  · intro capability membership; exact (equivalence capability).mpr membership

theorem authority_meet_idem : ∀ a : Authority, min a a ≤ a ∧ a ≤ min a a := by
  intro authority

  have equivalence := authority_meet_idem_equiv authority

  constructor

  · intro capability membership; exact (equivalence capability).mp membership

  · intro capability membership; exact (equivalence capability).mpr membership

theorem authority_meet_le_left : ∀ a b : Authority, min a b ≤ a := by
  intro leftAuthority rightAuthority
  simp only [Min.min, Authority.meet, LE.le, Authority.subset]
  intro capability membership
  simp only [List.mem_filter] at membership
  exact membership.1

theorem authority_meet_le_right : ∀ a b : Authority, min a b ≤ b := by
  intro leftAuthority rightAuthority
  simp only [Min.min, Authority.meet, LE.le, Authority.subset]
  intro capability membership
  simp only [List.mem_filter] at membership
  obtain ⟨_, hcb⟩ := membership
  simp only [List.contains_eq_any_beq, List.any_eq_true] at hcb
  obtain ⟨witness, witnessInRight, capabilityEq⟩ := hcb
  simp only [beq_iff_eq] at capabilityEq
  rw [capabilityEq]; exact witnessInRight

theorem authority_meet_glb : ∀ a b c : Authority, c ≤ a → c ≤ b → c ≤ min a b := by
  intro leftAuthority rightAuthority lowerBound hca hcb

  simp only [LE.le, Authority.subset, Min.min, Authority.meet] at *

  intro cap hcap

  simp only [List.mem_filter, List.contains_eq_any_beq, List.any_eq_true]

  constructor

  · exact hca cap hcap

  · exact ⟨cap, hcb cap hcap, by simp only [beq_self_eq_true]⟩

end Continuity.Trust.Authority
