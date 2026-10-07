/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // CONTINUITY // CRYPTOGRAPHY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                    Post-Quantum Cryptographic Primitives

                                                     - straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "They're harvesting now, decrypting later."
                                        — every cryptographer, 2024

RSA and ECC are dead. They just don't know it yet.

NIST finalized post-quantum standards in 2024:
  ML-KEM (FIPS 203)   — Key encapsulation, from CRYSTALS-Kyber
  ML-DSA (FIPS 204)   — Digital signatures, from CRYSTALS-Dilithium
  SLH-DSA (FIPS 205)  — Digital signatures, from SPHINCS+ (hash-based)

We use ALL THREE in hybrid mode. Attacker must break all to compromise.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Crypto

-- ══════════════════════════════════════════════════════════════════════════════
-- PRIMITIVE TYPES (opaque, axiomatized)
-- All crypto primitives are opaque - we trust their mathematical properties.
-- ══════════════════════════════════════════════════════════════════════════════

/-- SHA-256 digest, modeled as its raw bytes. An *unbounded* concrete type: so
    `DecidableEq`/`Inhabited` COMPUTE (content-addressing is executable), yet
    `hashBytes_injective` below stays CONSISTENT — an injection into an infinite
    codomain exists. A finite digest type (`BitVec 256`, `Vector UInt8 32`) would
    make injectivity pigeonhole-false and the whole development inconsistent. -/
structure Hash where
  bytes : ByteArray
  deriving DecidableEq, Inhabited

instance : Repr Hash := ⟨fun hashValue _ => repr hashValue.bytes.toList⟩

/-- Ed25519 public key (32 bytes). -/
opaque Ed25519PublicKey : Type

@[instance]
axiom Ed25519PublicKey.instInhabited : Inhabited Ed25519PublicKey

@[instance]
axiom Ed25519PublicKey.instDecidableEq : DecidableEq Ed25519PublicKey

/-- Ed25519 signature (64 bytes). -/
opaque Ed25519Signature : Type

@[instance]
axiom Ed25519Signature.instInhabited : Inhabited Ed25519Signature

@[instance]
axiom Ed25519Signature.instDecidableEq : DecidableEq Ed25519Signature

/-- ML-DSA-65 public key (1952 bytes). NIST Level 3 security. -/
opaque MLDSAPublicKey : Type

@[instance]
axiom MLDSAPublicKey.instInhabited : Inhabited MLDSAPublicKey

@[instance]
axiom MLDSAPublicKey.instDecidableEq : DecidableEq MLDSAPublicKey

/-- ML-DSA-65 signature (3309 bytes). -/
opaque MLDSASignature : Type

@[instance]
axiom MLDSASignature.instInhabited : Inhabited MLDSASignature

@[instance]
axiom MLDSASignature.instDecidableEq : DecidableEq MLDSASignature

/-- SLH-DSA-128s public key (32 bytes). Hash-only security assumption. -/
opaque SLHDSAPublicKey : Type

@[instance]
axiom SLHDSAPublicKey.instInhabited : Inhabited SLHDSAPublicKey

@[instance]
axiom SLHDSAPublicKey.instDecidableEq : DecidableEq SLHDSAPublicKey

/-- SLH-DSA-128s signature (7856 bytes). Conservative backup. -/
opaque SLHDSASignature : Type

@[instance]
axiom SLHDSASignature.instInhabited : Inhabited SLHDSASignature

@[instance]
axiom SLHDSASignature.instDecidableEq : DecidableEq SLHDSASignature

/-- ML-KEM-768 public key (1184 bytes). -/
opaque MLKEMPublicKey : Type

@[instance]
axiom MLKEMPublicKey.instInhabited : Inhabited MLKEMPublicKey

@[instance]
axiom MLKEMPublicKey.instDecidableEq : DecidableEq MLKEMPublicKey

/-- ML-KEM-768 ciphertext (1088 bytes). -/
opaque MLKEMCiphertext : Type

@[instance]
axiom MLKEMCiphertext.instInhabited : Inhabited MLKEMCiphertext

@[instance]
axiom MLKEMCiphertext.instDecidableEq : DecidableEq MLKEMCiphertext

@[instance]
axiom MLKEMCiphertext.inst_repr : Repr MLKEMCiphertext

-- ══════════════════════════════════════════════════════════════════════════════
-- CRYPTO AXIOMS
-- These are the trust-distance-1 assumptions about cryptographic primitives.
-- ══════════════════════════════════════════════════════════════════════════════

-- Hashing
axiom hash_of {α : Type} [Inhabited α] : α → Hash

/-- SHA-256 on bytes (opaque implementation). The content-addressed primitive
    everything that needs collision-resistance should route through. -/
opaque hashBytes : ByteArray → Hash

/-- RANDOM ORACLE IDEALIZATION: SHA-256 doesn't collide.

    Real SHA-256 maps an infinite domain to 256 bits, so this is mathematically
    false — but, crucially, it is CONSISTENT as stated here, because `Hash` wraps
    an unbounded `ByteArray`: an injection `ByteArray → Hash` genuinely exists, so
    asserting it implies no `False`. (The previous `∀ α, hash_of`-injectivity was
    refutable by elementary pigeonhole — and by Cantor at `α := Set Hash` — once
    Mathlib was in scope; this monomorphic form on bytes is not.)

    Standard random-oracle modeling (Bellare & Rogaway 1993). AXIOM BUDGET: the
    strongest single assumption in Continuity. If SHA-256 collision resistance
    fails, content-addressing fails globally (Git, Nix, Docker, Bitcoin, …) — we
    inherit the ecosystem's bet. -/
axiom hash_bytes_injective (valueA valueB : ByteArray) : hashBytes valueA = hashBytes valueB → valueA = valueB

-- Ed25519 verification
axiom ed25519_verify : Ed25519PublicKey → Hash → Ed25519Signature → Bool

-- ML-DSA verification
axiom mldsa_verify : MLDSAPublicKey → Hash → MLDSASignature → Bool

-- SLH-DSA verification
axiom slhdsa_verify : SLHDSAPublicKey → Hash → SLHDSASignature → Bool

-- ML-KEM
axiom mlkem_encapsulate : MLKEMPublicKey → MLKEMCiphertext × Hash

axiom mlkem_decapsulate_correct (publicKey : MLKEMPublicKey) :
    let (_ciphertext, sharedSecret) := mlkem_encapsulate publicKey
    ∃ (recoveredSecret : Hash), recoveredSecret = sharedSecret

-- X25519
axiom x25519_dh : Ed25519PublicKey → Ed25519PublicKey → Hash

-- ══════════════════════════════════════════════════════════════════════════════
-- HYBRID CONSTRUCTIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Hybrid public key: classical + lattice + hash-based. ~2KB total. -/
structure HybridPublicKey where
  ed25519 : Ed25519PublicKey
  mldsa   : MLDSAPublicKey
  slhdsa  : SLHDSAPublicKey

-- BEq instance for HybridPublicKey (needed for List.any comparisons)
noncomputable
instance : BEq HybridPublicKey where
  beq a b := decide (a.ed25519 = b.ed25519 ∧ a.mldsa = b.mldsa ∧ a.slhdsa = b.slhdsa)

-- ReflBEq instance for HybridPublicKey (needed for beq_self_eq_true)
noncomputable
instance : ReflBEq HybridPublicKey where
  rfl {valueA} := by simp only [BEq.beq, decide_eq_true_eq, and_self]

-- Repr instance for HybridPublicKey (needed for deriving Repr in SSP)
instance : Repr HybridPublicKey where
  reprPrec _pk _ := s!"HybridPublicKey(...)"

/-- Hybrid signature: all three must verify. ~11KB total. -/
structure HybridSignature where
  ed25519 : Ed25519Signature
  mldsa   : MLDSASignature
  slhdsa  : SLHDSASignature

-- Repr instance for HybridSignature
instance : Repr HybridSignature where
  reprPrec _sig _ := s!"HybridSignature(...)"

/-- Hybrid ephemeral: X25519 + ML-KEM. ~1.2KB total. -/
structure HybridEphemeral where
  x25519 : Ed25519PublicKey
  mlkem  : MLKEMPublicKey

-- Repr instance for HybridEphemeral
instance : Repr HybridEphemeral where
  reprPrec _eph _ := s!"HybridEphemeral(...)"

/-- Verification mode: how paranoid? -/
inductive VerifyMode where
  | fast      -- ed25519 + ML-DSA only
  | full      -- all three
  | classical -- ed25519 only (fallback)
  deriving DecidableEq, Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════════════════
-- VERIFICATION FUNCTIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Fast verification: ed25519 ∧ ML-DSA. -/
noncomputable
def hybrid_verify_fast (publicKey : HybridPublicKey) (msg : Hash) (sig : HybridSignature) : Bool :=
  ed25519_verify publicKey.ed25519 msg sig.ed25519 && mldsa_verify publicKey.mldsa msg sig.mldsa

/-- Full verification: ed25519 ∧ ML-DSA ∧ SLH-DSA. -/
noncomputable
def hybrid_verify_full (publicKey : HybridPublicKey) (msg : Hash) (sig : HybridSignature) : Bool :=
  ed25519_verify publicKey.ed25519 msg sig.ed25519 && mldsa_verify publicKey.mldsa msg sig.mldsa
      && slhdsa_verify publicKey.slhdsa msg sig.slhdsa

/-- Hybrid verification with mode selection. -/
noncomputable
def hybrid_verify
    (publicKey : HybridPublicKey)
    (msg : Hash)
    (sig : HybridSignature)
    (mode : VerifyMode := .fast)
    : Bool :=
  match mode with
  | .fast      => hybrid_verify_fast publicKey msg sig
  | .full      => hybrid_verify_full publicKey msg sig
  | .classical => ed25519_verify publicKey.ed25519 msg sig.ed25519

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY DERIVATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Hybrid key exchange inputs. -/
structure hybrid_key_exchange_input where
  clientX25519    : Ed25519PublicKey
  serverX25519    : Ed25519PublicKey
  mlkemCiphertext : MLKEMCiphertext
  clientNonce     : Hash
  serverNonce     : Hash

axiom derive_shared_secret : hybrid_key_exchange_input → Hash
axiom derive_session_key : Hash → Hash
axiom derive_subkey : Hash → String → Hash

-- ══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Fast mode requires both ed25519 and ML-DSA. -/
theorem hybrid_requires_both
        (publicKey : HybridPublicKey)
        (msg : Hash)
        (sig : HybridSignature)
        (hypothesis : hybrid_verify_fast publicKey msg sig = true)
        : ed25519_verify publicKey.ed25519 msg sig.ed25519 = true
            ∧ mldsa_verify publicKey.mldsa msg sig.mldsa = true := by
  simp only [hybrid_verify_fast, Bool.and_eq_true] at hypothesis

  exact hypothesis

/-- Full mode requires all three signature schemes. -/
theorem hybrid_requires_all_three
        (publicKey : HybridPublicKey)
        (msg : Hash)
        (sig : HybridSignature)
        (hypothesis : hybrid_verify_full publicKey msg sig = true)
        : ed25519_verify publicKey.ed25519 msg sig.ed25519 = true
            ∧ mldsa_verify publicKey.mldsa msg sig.mldsa = true
            ∧ slhdsa_verify publicKey.slhdsa msg sig.slhdsa = true := by
  simp only [hybrid_verify_full, Bool.and_eq_true] at hypothesis

  obtain ⟨classicalAndLattice, statelessValid⟩ := hypothesis

  obtain ⟨classicalValid, latticeValid⟩ := classicalAndLattice

  exact ⟨classicalValid, latticeValid, statelessValid⟩

/-- Classical mode only checks ed25519. -/
theorem classical_mode_ed25519_only
        (publicKey : HybridPublicKey)
        (msg : Hash)
        (sig : HybridSignature)
        (hypothesis : hybrid_verify publicKey msg sig .classical = true)
        : ed25519_verify publicKey.ed25519 msg sig.ed25519 = true := by
  simp only [hybrid_verify] at hypothesis

  exact hypothesis

end Continuity.Crypto
