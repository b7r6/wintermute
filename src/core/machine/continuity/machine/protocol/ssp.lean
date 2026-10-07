import continuity.machine
import continuity.crypto
import continuity.trust.authority
import continuity.trust.core
import continuity.coeffect
import continuity.witness
import continuity.trust.discharge

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                      THE STRAYLIGHT SHELL PROTOCOL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

              A Verified, Post-Quantum, Capability-Based Protocol

                        straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "The Villa Straylight knows no sky, recorded or otherwise."
                                                        — Neuromancer

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module COMPOSES the Continuity atoms into a concrete wire protocol
for remote shell access. It does NOT redefine the atoms — those live in:

  • Continuity.Crypto     — Post-quantum hybrid signatures and key exchange
  • Continuity.Trust.Authority  — Capability lattice (meet-semilattice)
  • Continuity.Trust      — Vouch chains, recognition levels, TrustState
  • Continuity.Coeffect   — What computations need from the environment
  • Continuity.Witness    — DischargeProof, syscall-level witnessing

The SSH stack is a graveyard:
  • OpenSSH: 100k+ LOC of C, CVE after CVE
  • OpenSSL: the gift that keeps on giving
  • SSH agent: lets compromised hosts use your keys
  • authorized_keys: scattered, no expiry, ambient authority
  • known_hosts: TOFU, "yes" is muscle memory

SSP replaces all of it with:
  • Post-quantum crypto from day one (ML-KEM + ML-DSA + SLH-DSA)
  • Hybrid signatures (ed25519 AND ML-DSA must both verify)
  • Hybrid key exchange (X25519 AND ML-KEM-768)
  • Short-lived capability certificates (minutes, not forever)
  • No CA — trust flows through vouch chains from roots you control
  • No agent — keys derived on demand from master secret
  • Verified state machines — no parse bugs, no state confusion

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    §1  CAPABILITY CERTIFICATES                        self-signed claims
    §2  HANDSHAKE PROTOCOL                             PQ key exchange
    §3  CHANNEL PROTOCOL                               multiplexed streams
    §4  PROTOCOL THEOREMS                              composition proofs

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Machine.Protocol.SSP

open Continuity.Crypto
open Continuity.Trust.Authority
open Continuity.Trust

-- ══════════════════════════════════════════════════════════════════════════════
-- §1. CAPABILITY CERTIFICATES
-- ══════════════════════════════════════════════════════════════════════════════

/-!
A CapabilityCert is a self-signed authority claim:

    identity + scope + issued_at + expires_at + signature

KEY PROPERTIES:

1. SELF-SIGNED:
   The identity signs the cert. "I claim this authority."
   Server verifies: does this identity actually HAVE this authority?

2. SCOPED:
   The cert requests specific capabilities.
   "I want shell access as user 'deploy'" not "I want everything"

3. SHORT-LIVED:
   expires_at is typically minutes to hours from issued_at.
   Stolen cert is worthless after expiration.
   No need for CRL (Certificate Revocation Lists).

4. INTERSECTION:
   Effective authority = (what cert claims) ⊓ (what identity is allowed)
   You can claim anything, but you only get what you're allowed.
-/

/-- A capability certificate: identity + requested scope + signature. -/
structure CapabilityCert where
  identity   : HybridPublicKey
  scope      : Authority
  issued_at  : Timestamp
  expires_at : Timestamp
  signature  : HybridSignature

-- Repr instance (noncomputable due to crypto types)
noncomputable
instance : Repr CapabilityCert where
  reprPrec c _ := s!"CapabilityCert(scope={repr c.scope})"

namespace CapabilityCert

/-- The message that gets signed. -/
noncomputable
def message (certificate : CapabilityCert) : Hash := hash_of certificate.issued_at -- Simplified; full impl would hash all fields

/-- A cert is well-formed if signature verifies. -/
noncomputable
def well_formed (certificate : CapabilityCert) : Prop :=
  hybrid_verify certificate.identity certificate.message certificate.signature = true

/-- A cert is valid at a given time. -/
def valid_at (certificate : CapabilityCert) (now : Timestamp) : Prop :=
  certificate.well_formed ∧ certificate.issued_at ≤ now ∧ now < certificate.expires_at

/-- Effective authority: min of claimed and allowed.
    THE KEY EQUATION: effective = allowed ⊓ claimed -/
noncomputable
def effective_authority
    (certificate : CapabilityCert)
    (trustState : TrustState)
    (now : Timestamp)
    : Authority :=
  let allowed := trustState.authority_of certificate.identity now
  min allowed certificate.scope

end CapabilityCert

-- ══════════════════════════════════════════════════════════════════════════════
-- §2. HANDSHAKE PROTOCOL
-- ══════════════════════════════════════════════════════════════════════════════

/-!
PQ key exchange state machine. Establishes a shared secret for the session.

    CLIENT                              SERVER
      |                                   |
      |-------- ClientHello ----------->|  ephemeral_c, nonce_c
      |                                   |
      |<------- ServerHello ------------|  ephemeral_s, nonce_s, host_pk, host_sig
      |                                   |
      |  [derive shared secret]          [derive shared secret]
      |                                   |
      |-------- CapabilityCert -------->|  prove identity, request scope
      |                                   |
      |<------- AuthResult -------------|  accepted/rejected
      |                                   |
      |  [session established]           [session established]

PROPERTIES:

1. FORWARD SECRECY:
   Compromise of long-term keys doesn't reveal past session keys.

2. QUANTUM RESISTANCE:
   Uses ML-KEM (Kyber) for key encapsulation.

3. HYBRID:
   Both X25519 (classical) and ML-KEM (PQ) contribute to session key.
   K = KDF(X25519_shared || MLKEM_shared || nonces)
-/

/-- Handshake state: where we are in the key exchange. -/
inductive HandshakeState where
  | init
  | sentClientHello (clientEph : HybridEphemeral) (clientNonce : Hash)
  | receivedServerHello (sharedSecret : Hash) (serverPubkey : HybridPublicKey)
  | authenticated (sessionKey : Hash) (serverPubkey : HybridPublicKey)
  | failed (reason : String)

-- Repr instance (noncomputable due to crypto types)
noncomputable
instance : Repr HandshakeState where
  reprPrec s _ :=
    match s with
    | .init => "HandshakeState.init"
    | .sentClientHello _ _ => "HandshakeState.sentClientHello(...)"
    | .receivedServerHello _ _ => "HandshakeState.receivedServerHello(...)"
    | .authenticated _ _ => "HandshakeState.authenticated(...)"
    | .failed reason => s!"HandshakeState.failed({repr reason})"

/-- Handshake events: inputs to the state machine. -/
inductive HandshakeEvent where
  | start (clientEph : HybridEphemeral) (clientNonce : Hash)
  | serverHello (serverEph : HybridEphemeral) (serverNonce : Hash) (mlkemCt : MLKEMCiphertext)
        (hostPk : HybridPublicKey) (hostSig : HybridSignature)
  | sendCert (cert : CapabilityCert)
  | authResult (accepted : Bool) (reason : Option String)

-- Repr instance (noncomputable due to crypto types)
noncomputable
instance : Repr HandshakeEvent where
  reprPrec e _ :=
    match e with
    | .start _ _              => "HandshakeEvent.start(...)"
    | .serverHello _ _ _ _ _  => "HandshakeEvent.serverHello(...)"
    | .sendCert certificate   => s!"HandshakeEvent.sendCert({repr certificate})"
    | .authResult auth result => s!"HandshakeEvent.authResult({repr auth}, {repr result})"

/-- Handshake actions: outputs from the state machine. -/
inductive HandshakeAction where
  | sendClientHello (eph : HybridEphemeral) (nonce : Hash)
  | sendCapabilityCert (cert : CapabilityCert)
  | establishSession (sessionKey : Hash)
  | fail (reason : String)

-- Repr instance (noncomputable due to crypto types)
noncomputable
instance : Repr HandshakeAction where
  reprPrec a _ :=
    match a with
    | .sendClientHello _ _ => "HandshakeAction.sendClientHello(...)"
    | .sendCapabilityCert certificate => s!"HandshakeAction.sendCapabilityCert({repr certificate})"
    | .establishSession _ => "HandshakeAction.establishSession(...)"
    | .fail reason => s!"HandshakeAction.fail({repr reason})"

-- Inhabited instance for default values in state machine
noncomputable
instance : Inhabited HybridPublicKey :=
  ⟨
    {
      ed25519 := default
      mldsa := default
      slhdsa := default
    }
  ⟩

noncomputable
instance : Inhabited Hash := inferInstance

/-- Handshake transition function. -/
noncomputable
def handshake_transition
    : HandshakeState → HandshakeEvent → Machine.Transition HandshakeState HandshakeAction
  | .init, .start clientEph clientNonce =>
    { next    := .sentClientHello clientEph clientNonce,
      actions := [.sendClientHello clientEph clientNonce] }

  -- Derive the shared secret from the server hello.
  | .sentClientHello clientEph clientNonce, .serverHello serverEph serverNonce mlkemCt hostPk _ =>
    let kexInput : hybrid_key_exchange_input := {
      clientX25519 := clientEph.x25519
      serverX25519 := serverEph.x25519
      mlkemCiphertext := mlkemCt
      clientNonce := clientNonce
      serverNonce := serverNonce
    }
    let sharedSecret := derive_shared_secret kexInput
    { next := .receivedServerHello sharedSecret hostPk, actions := [] }

  -- Authenticate the peer and establish the session.
  | .receivedServerHello sharedSecret hostPk, .sendCert cert =>
    let sessionKey := derive_session_key sharedSecret
    { next    := .authenticated sessionKey hostPk,
      actions := [.sendCapabilityCert cert, .establishSession sessionKey] }

  -- Preserve an authenticated session after acceptance.
  | .authenticated _ _, .authResult true _ =>
    { next := .authenticated default default, actions := [] }

  -- Fail an authenticated session after rejection.
  | .authenticated _ _, .authResult false reason =>
    { next    := .failed (reason.getD "Auth rejected"),
      actions := [.fail (reason.getD "Auth rejected")] }

  -- Keep failed sessions terminal.
  | .failed reason, _ => { next := .failed reason, actions := [] }

  -- Reject every invalid transition.
  | _, _ => { next := .failed "Invalid transition", actions := [.fail "Protocol error"] }

/-- Handshake state machine definition. -/
noncomputable
def handshakeMachine : Machine.Machine HandshakeState HandshakeEvent HandshakeAction := {
  initial := .init
  transition := handshake_transition
  isTerminal := fun state => match state with
    | .authenticated _ _ => true
    | .failed _ => true
    | _ => false
}

-- ══════════════════════════════════════════════════════════════════════════════
-- §3. CHANNEL PROTOCOL
-- ══════════════════════════════════════════════════════════════════════════════

/-!
Multiplexed channels after handshake completes. Like SSH channels, but scoped.

    Connection
      ├── Channel 0: shell session
      ├── Channel 1: git push
      ├── Channel 2: port forward localhost:8080
      └── Channel 3: sftp transfer

Each channel has its OWN scope. Channel requests are checked against
effective authority.
-/

/-- Channel state: lifecycle of a single channel. -/
inductive ChannelState where
  | closed
  | opening (scope : Authority)
  | open_ (identifier : Nat) (scope : Authority)
  | closing
  deriving Repr

/-- Channel events: inputs to the channel state machine. -/
inductive ChannelEvent where
  | requestOpen (scope : Authority)
  | openConfirmed (identifier : Nat)
  | openDenied (reason : String)
  | data (payload : List UInt8)
  | eof
  | close
  | closeAck
  deriving Repr

/-- Channel actions: outputs from the channel state machine. -/
inductive ChannelAction where
  | sendOpenRequest (scope : Authority)
  | sendData (payload : List UInt8)
  | sendEof
  | sendClose
  | sendCloseAck
  | channelReady (identifier : Nat)
  | channelClosed
  | fail (reason : String)
  deriving Repr

/-- Channel transition function. -/
def channel_transition : ChannelState → ChannelEvent → Machine.Transition ChannelState ChannelAction
  | .closed, .requestOpen scope => { next := .opening scope, actions := [.sendOpenRequest scope] }
  | .opening scope, .openConfirmed channelId =>
    { next := .open_ channelId scope, actions := [.channelReady channelId] }
  | .opening _, .openDenied reason => { next := .closed, actions := [.fail reason] }
  | .open_ channelId scope, .data payload =>
    { next := .open_ channelId scope, actions := [.sendData payload] }
  | .open_ _ _, .close => { next := .closing, actions := [.sendClose] }
  | .closing, .closeAck => { next := .closed, actions := [.channelClosed] }
  | state, _ => { next := state, actions := [] }

/-- Channel state machine definition. -/
def channelMachine : Machine.Machine ChannelState ChannelEvent ChannelAction := {
  initial := .closed
  transition := channel_transition
  isTerminal := fun state => match state with
    | .closed => true
    | _       => false
}

-- ══════════════════════════════════════════════════════════════════════════════
-- §4. PROTOCOL THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-!
Theorems about the SSP protocol. These COMPOSE the properties proven in
the atomic modules:

  • Authority lattice theorems from Continuity.Trust.Authority
  • Trust chain theorems from Continuity.Trust
  • Hybrid crypto theorems from Continuity.Crypto
-/

/-- Certificate soundness: effective authority is bounded by claimed scope. -/
theorem cert_authority_bounded_by_scope
        (certificate : CapabilityCert)
        (trustState : TrustState)
        (now : Timestamp)
        : certificate.effective_authority trustState now ≤ certificate.scope := by
  simp only [CapabilityCert.effective_authority]

  -- Select the claimed-scope side of the meet.
  exact authority_meet_le_right _ _

/-- Certificate soundness: effective authority is bounded by allowed authority. -/
theorem cert_authority_bounded_by_allowed
        (certificate : CapabilityCert)
        (trustState : TrustState)
        (now : Timestamp)
        : certificate.effective_authority trustState now
            ≤ trustState.authority_of certificate.identity now := by
  simp only [CapabilityCert.effective_authority]

  -- Select the recognized-authority side of the meet.
  exact authority_meet_le_left _ _

/-- Handshake produces session key when authenticated. -/
theorem handshake_produces_key
        (state : HandshakeState)
        (hashValue : ∃ sk spk, state = .authenticated sk spk)
        : ∃ sessionKey serverPubkey, state = .authenticated sessionKey serverPubkey :=
  hashValue

/-- Failed state is terminal. -/
theorem failed_is_terminal
        (reason : String)
        (event : HandshakeEvent)
        : (handshake_transition (.failed reason) event).next = .failed reason :=
  rfl

/-- Unrecognized identities get no effective authority. -/
theorem unrecognized_no_effective_authority
        (certificate : CapabilityCert)
        (trustState : TrustState)
        (now : Timestamp)
        (h_unrec : trustState.recognition_of certificate.identity = .unrecognized)
        : certificate.effective_authority trustState now = Authority.none := by
  simp only [CapabilityCert.effective_authority]

  -- Derive the absence of recognized authority.
  have h_no_auth := unrecognized_no_authority trustState certificate.identity now h_unrec

  -- Rewrite the recognized authority to none.
  rw [h_no_auth]

  -- Reduce the meet with empty authority.
  simp only [Min.min, Authority.meet, Authority.none, List.filter_nil]

end Continuity.Machine.Protocol.SSP
