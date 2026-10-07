import continuity.coeffect.grade

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // continuity // coeffect // monad
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    M : Grade → Type → Type

    pure  : α → M [] α
    bind  : M g₁ α → (α → M g₂ β) → M (g₁ ∪ g₂) β

    0 sorry.

                                                   - straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Coeffect.GradedMonad

open Continuity.Coeffect.Grade

open Continuity.Coeffect.Grade.Grade (build full gateway gatewayNet gatewayPure isPure
    isReproducible mem plus subset unit)

-- ────  monad  ─────────────────────────────────────────────────────────────────

opaque GradedM (grade : Grade) (α : Type) : Type

@[instance]
axiom GradedM.instInhabited {grade : Grade} : Inhabited (GradedM grade Unit)

axiom gpure {α : Type} : α → GradedM unit α

axiom gbind {α β : Type} {gradeOne gradeTwo : Grade} :
    GradedM gradeOne α → (α → GradedM gradeTwo β) → GradedM (plus gradeOne gradeTwo) β

axiom gmap {α β : Type} {grade : Grade} : (α → β) → GradedM grade α → GradedM grade β

axiom gsub {α : Type} {gradeOne gradeTwo : Grade} : subset gradeOne gradeTwo → GradedM gradeOne α → GradedM gradeTwo α

-- ────  effects  ───────────────────────────────────────────────────────────────

axiom cryptpgraphic_operation {α : Type} : String → GradedM [GradeLabel.Crypto] α

axiom get_random : Nat → GradedM [GradeLabel.Random] (List UInt8)
axiom get_time : GradedM [GradeLabel.Time] Nat

axiom log_message : String → GradedM [GradeLabel.Log] Unit

axiom net_request {α : Type} : String → GradedM [GradeLabel.Net] α

axiom read_auth : String → GradedM [GradeLabel.Auth] String
axiom read_ca {α : Type} : String → GradedM [GradeLabel.FsCA] α
axiom read_file : String → GradedM [GradeLabel.Fs] String

-- ────  grades  ────────────────────────────────────────────────────────────────

def ssp_handshake_grade : Grade := [GradeLabel.Net, GradeLabel.Crypto]

def ssh_authentication : Grade := [GradeLabel.Net, GradeLabel.Crypto, GradeLabel.Auth]

def nix_client_grade : Grade := [GradeLabel.Net, GradeLabel.FsCA]

def codec_grade : Grade := unit

def attestation_grade : Grade := [GradeLabel.Auth, GradeLabel.Crypto, GradeLabel.Time]

def cas_write_grade : Grade := unit -- n.b. CAS writes are inert. No grade needed.

-- ────  theorems  ──────────────────────────────────────────────────────────────

-- n.b. for all the smart-ass droids: aliasing commonly used lemmas is
-- not "vacuous", you're vacuous and so is your mom!

/- A codec is pure, this is our mode and modus. -/
theorem codec_is_pure : isPure codec_grade = true := rfl

/- A codec is a function, this is our mode and modus. -/
theorem codec_is_reproducible : isReproducible codec_grade = true := rfl

/-  A CAS write is pure (it is inert bytes with no authority) -/
theorem cas_write_is_pure : isPure cas_write_grade = true := rfl

/- Attestation requires non-reproducible effects (`gettimeofday` VDSO) -/
theorem attest_not_reproducible : isReproducible attestation_grade = false := by native_decide

/- SSP handshake is not reproducible via the network -/
theorem ssp_not_reproducible : isReproducible ssp_handshake_grade = false := by native_decide

/- CA-only operations are reproducible -/
theorem fsca_reproducible : isReproducible [GradeLabel.FsCA] = true := by native_decide

/- Cryptography is a function. -/
theorem crypto_reproducible : isReproducible [GradeLabel.Crypto] = true := by native_decide

/- Cryptography over certificate autorities is a function. -/
theorem fsca_crypto_reproducible : isReproducible [GradeLabel.FsCA, GradeLabel.Crypto] = true := by
  native_decide

-- TODO[b7r6]: this belongs with the other experimental jank...
theorem plus_unit_right_gateway : plus gateway unit = gateway := Grade.plus_unit_right gateway
-- theorem plus_codec_gateway : plus gradeCodec gateway = gateway := Grade.plus_unit_right gateway

-- Membership facts
theorem attestation_needs_authentication : mem .Auth attestation_grade = true := by decide

theorem attestation_needs_cryptography : mem .Crypto attestation_grade = true := by decide

theorem attestation_needs_time : mem .Time attestation_grade = true := by decide

theorem cas_write_does_not_need_authentication : mem .Auth cas_write_grade = false := by decide

theorem codecs_have_no_effects : ∀ label : GradeLabel, mem label codec_grade = false := by
  intro label
  cases label <;> decide

-- ────  invariants  ────────────────────────────────────────────────────────────

-- These are the architectural invariants for safe AI state management.
-- Each is a statement that the system must satisfy. Some are proven here
-- directly. Others require more, and are proven elsewhere.
--
-- I1: Parse Rejection Totality
--
--   `∀ bytes, parse(bytes) = ok value rest ∨ parse(bytes) = fail`
--
--   Sketch: `Box.parse` returns `ParseResult` which is exactly this sum type.
--
--   There is no partial parse, therefore `ok` and `fail` are a cover.
--
-- I2: Consumption Faithfulness
--
--   `∀ α residual, parse(serialize(α) ++ residual) = ok α residual`
--
--   Sketch: Box.consumption is in `Continuity.Codec.Core`.
--
--   The intuition: no smuggled bytes and no trailing payload.
--
-- I3: Unattested Inertness
--
--   `∀ content : CAS, grade(content) = []`
--
--   Sketch: `cas_write_is_pure` shows `gradeCASWrite = unit`.
--
--   No operation in the system accepts grade [] and produces an effect.
--   Validated: codec_no_effects shows no GradeLabel is in the empty grade.
--
-- I4: Attestation Non-Forgeability
--
--   Attestation requires Auth ∧ Crypto ∧ Time in the grade.
--
--   The graded monad enforces these are discharged before attestation
--   completes. This is a composed argument.
--
-- I5: Grade Monotonicity
--
--   `∀ g₁ g₂, g₁ ⊆ plus g₁ g₂`
--
--  Sketch: `plus` is monotone.
--
--  The intuition is that in a strictly growing ring, {g} < {g,h}
--

-- ────  invariant theorems  ────────────────────────────────────────────────────

-- n.b. we should get everything under one roof here...

/- I3: Unattested CAS writes are inert. -/
theorem i3_unattested_cas_writes_inert : isPure cas_write_grade = true := rfl

-- I4: attestation requires all three labels — proven
theorem i4_attestation_requires_authentication : mem .Auth attestation_grade = true := by decide

theorem i4_attestation_requires_cryptography : mem .Crypto attestation_grade = true := by decide

theorem invariant_4_attest_requires_time : mem .Time attestation_grade = true := by decide

-- I4 corollary: pure code cannot produce attestations
theorem invariant_4_pure_cannot_attest : isPure attestation_grade = false := by decide

end Continuity.Coeffect.GradedMonad
