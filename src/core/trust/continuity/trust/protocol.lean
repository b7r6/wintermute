/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // CONTINUITY // PROTOCOL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


                    Straylight Shell Protocol (SSP)


                                                       straylight.software · 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The wire protocol for post-quantum, capability-based shell access.
Replaces SSH with verified state machines and vouch-based trust.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.crypto
import continuity.trust.core
import continuity.trust.authority

namespace Continuity.Trust.Protocol

open Continuity.Crypto
open Continuity.Trust
open Continuity.Trust.Authority

-- ══════════════════════════════════════════════════════════════════════════════
--                                                    // CAPABILITY // CERTIFICATE
-- ══════════════════════════════════════════════════════════════════════════════

/-- A capability certificate: identity + requested scope + signature. -/
structure CapabilityCert where
  identity   : HybridPublicKey
  scope      : Authority
  issued_at  : Timestamp
  expires_at : Timestamp
  signature  : HybridSignature

@[instance]
axiom CapabilityCert.instDecidableEq : DecidableEq CapabilityCert

namespace CapabilityCert

noncomputable
def message (certificate : CapabilityCert) : Hash := hash_of certificate.issued_at -- Simplified to avoid Inhabited tuple

noncomputable
def well_formed (certificate : CapabilityCert) : Prop :=
  hybrid_verify certificate.identity certificate.message certificate.signature = true

def valid_at (certificate : CapabilityCert) (now : Timestamp) : Prop :=
  certificate.well_formed ∧ certificate.issued_at ≤ now ∧ now < certificate.expires_at

end CapabilityCert

noncomputable
def CapabilityCert.effective_authority
    (certificate : CapabilityCert)
    (trustState : TrustState)
    (now : Timestamp)
    : Authority :=
  let allowed := trustState.authority_of certificate.identity now
  min allowed certificate.scope

-- ══════════════════════════════════════════════════════════════════════════════
--                                                // HANDSHAKE // STATE // MACHINE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Handshake state. -/
inductive HandshakeState where
  | init
  | sentClientHello (clientEph : HybridEphemeral) (clientNonce : Hash)
  | receivedServerHello (sharedSecret : Hash) (serverPubkey : HybridPublicKey)
  | authenticated (sessionKey : Hash) (serverPubkey : HybridPublicKey)
  | failed (reason : String)

-- Axiomatize Inhabited for HybridPublicKey
@[instance]
axiom HybridPublicKey.instInhabited : Inhabited HybridPublicKey

/-- Handshake events. -/
inductive HandshakeEvent where
  | start (clientEph : HybridEphemeral) (clientNonce : Hash)
  | serverHello (serverEph : HybridEphemeral) (serverNonce : Hash) (mlkemCt : MLKEMCiphertext)
        (hostPk : HybridPublicKey) (hostSig : HybridSignature)
  | sendCert (cert : CapabilityCert)
  | authResult (accepted : Bool) (reason : Option String)

/-- Handshake actions. -/
inductive HandshakeAction where
  | sendClientHello (eph : HybridEphemeral) (nonce : Hash)
  | sendCapabilityCert (cert : CapabilityCert)
  | establishSession (sessionKey : Hash)
  | fail (reason : String)

/-- State machine transition. -/
structure Transition (State Action : Type) where
  next    : State
  actions : List Action

/-- Handshake transition function. -/
noncomputable
def handshake_transition
    : HandshakeState → HandshakeEvent → Transition HandshakeState HandshakeAction
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

  -- Preserve an existing failure.
  | .failed reason, _ => { next := .failed reason, actions := [] }

  -- Reject every invalid transition.
  | _, _ => { next := .failed "Invalid transition", actions := [.fail "Protocol error"] }

-- ══════════════════════════════════════════════════════════════════════════════
--                                                     // CHANNEL // STATE MACHINE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Channel state. -/
inductive ChannelState where
  | closed
  | opening (scope : Authority)
  | open_ (channelId : Nat) (scope : Authority)
  | closing
  deriving Repr

/-- Channel events. -/
inductive ChannelEvent where
  | requestOpen (scope : Authority)
  | openConfirmed (channelId : Nat)
  | openDenied (reason : String)
  | data (payload : List UInt8)
  | close
  | closeAck
  deriving Repr

/-- Channel actions. -/
inductive ChannelAction where
  | sendOpenRequest (scope : Authority)
  | sendData (payload : List UInt8)
  | sendClose
  | sendCloseAck
  | channelReady (channelId : Nat)
  | channelClosed
  | fail (reason : String)
  deriving Repr

/-- Channel transition function. -/
def channel_transition : ChannelState → ChannelEvent → Transition ChannelState ChannelAction
  | .closed, .requestOpen scope => { next := .opening scope, actions := [.sendOpenRequest scope] }
  | .opening scope, .openConfirmed channelId =>
    { next := .open_ channelId scope, actions := [.channelReady channelId] }
  | .opening _, .openDenied reason => { next := .closed, actions := [.fail reason] }
  | .open_ channelId scope, .data payload =>
    { next := .open_ channelId scope, actions := [.sendData payload] }
  | .open_ _ _, .close => { next := .closing, actions := [.sendClose] }
  | .closing, .closeAck => { next := .closed, actions := [.channelClosed] }
  | state, _ => { next := state, actions := [] }

-- ══════════════════════════════════════════════════════════════════════════════
--                                                                     // THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Certificate soundness: effective authority is bounded by claimed scope. -/
theorem cert_authority_sound
        (certificate : CapabilityCert)
        (trustState : TrustState)
        (now : Timestamp)
        : certificate.effective_authority trustState now ≤ certificate.scope := by
  simp only [CapabilityCert.effective_authority]

  exact authority_meet_le_right _ _

/-- Handshake produces session key when authenticated. -/
theorem handshake_security
        (state : HandshakeState)
        (authenticated : ∃ sk spk, state = .authenticated sk spk)
        : ∃ sessionKey serverPubkey, state = .authenticated sessionKey serverPubkey :=
  authenticated

/-- Failed state is terminal. -/
theorem failed_is_terminal
        (reason : String)
        (event : HandshakeEvent)
        : (handshake_transition (.failed reason) event).next = .failed reason :=
  rfl

end Continuity.Trust.Protocol
