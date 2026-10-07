/-
  Continuity.Machine.Protocol.NixHandshake - Nix daemon handshake / op / stderr machines

  Concrete state machines for the Nix daemon protocol, built on the generic
  Continuity.Machine engine. Extracted from the former Codec.StateMachine
  so the engine stays protocol-agnostic.
-/

import continuity.machine

namespace Continuity.Machine.Protocol.NixHandshake

open Continuity.Machine

-- ══════════════════════════════════════════════════════════════════════════════
-- HANDSHAKE PROTOCOL TYPES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Protocol version (major.minor packed into u64) -/
structure ProtocolVersion where
  value : UInt64
  deriving Repr, DecidableEq

namespace ProtocolVersion
def make (major minor : Nat) : ProtocolVersion := ⟨((major.toUInt64 <<< 8) ||| minor.toUInt64)⟩

def major (version : ProtocolVersion) : Nat := (version.value >>> 8).toNat
def minor (version : ProtocolVersion) : Nat := (version.value &&& 0xFF).toNat

def supports (version : ProtocolVersion) (minMinor : Nat) : Bool := version.minor >= minMinor

def current : ProtocolVersion := make 1 38
def minimum : ProtocolVersion := make 1 10
end ProtocolVersion

/-- Feature flags -/
inductive Feature where
  | reapiV2
  | casSha256
  | streamingNar
  | signedNarinfo
  deriving Repr, DecidableEq, Hashable

/-- REAPI configuration -/
structure ReapiConfig where
  instanceName   : String
  digestFunction : Nat    -- 0 = SHA256
  deriving Repr, DecidableEq

/-- Trust level -/
inductive TrustLevel where
  | unknown
  | trusted
  | untrusted
  deriving Repr, DecidableEq

/-- Handshake configuration (server settings) -/
structure handshake_config where
  serverVersion  : ProtocolVersion
  serverFeatures : List Feature
  reapiConfig    : Option ReapiConfig
  daemonVersion  : String
  trustLevel     : TrustLevel
  deriving Repr

def handshake_config.default : handshake_config :=
  {
    serverVersion := ProtocolVersion.current
    serverFeatures := [.reapiV2, .casSha256, .streamingNar]
    reapiConfig := some { instanceName := "main", digestFunction := 0 }
    daemonVersion := "nix-serve-cas 0.1.0"
    trustLevel := .trusted
  }

-- ══════════════════════════════════════════════════════════════════════════════
-- SERVER HANDSHAKE STATE MACHINE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Server handshake states -/
inductive ServerState where
  | init (config : handshake_config)
  | versioned (config : handshake_config) (negotiated : ProtocolVersion)
  | features (config : handshake_config) (negotiated : ProtocolVersion) (active : List Feature)
  | upgrading (config : handshake_config) (negotiated : ProtocolVersion) (active : List Feature)
  | nixReady (version : ProtocolVersion)
  | reapiReady (config : ReapiConfig)
  | failed (reason : String)
  deriving Repr

/-- Server events (inputs) -/
inductive server_event where
  | clientHello (clientVersion : ProtocolVersion)
  | clientLegacy -- obsolete fields received
  | clientFeatures (features : List Feature)
  | clientUpgradeResponse (accept : Bool)
  deriving Repr

/-- Server actions (outputs) -/
inductive server_action where
  | sendServerHello (version : ProtocolVersion)
  | sendDaemonVersion (version : String)
  | sendTrustLevel (level : TrustLevel)
  | sendFeatures (features : List Feature)
  | sendUpgradeOffer
  | sendReapiConfig (config : ReapiConfig)
  | ready
  | fail (reason : String)
  deriving Repr, DecidableEq

/-- Compute feature intersection -/
def featureIntersection (leftFeatures rightFeatures : List Feature) : List Feature :=
  leftFeatures.filter (rightFeatures.contains ·)

/-- Check if REAPI upgrade should be offered -/
def shouldOfferUpgrade (config : handshake_config) (active : List Feature) : Bool :=
  active.contains .reapiV2 && config.reapiConfig.isSome

def transitionClientHello
    (config : handshake_config)
    (clientVersion : ProtocolVersion)
    : Transition ServerState server_action :=
  let negotiated :=
    if clientVersion.value < config.serverVersion.value then clientVersion else config.serverVersion
  { next := .versioned config negotiated, actions := [.sendServerHello config.serverVersion] }

private
def transitionLegacy
    (config : handshake_config)
    (negotiated : ProtocolVersion)
    : Transition ServerState server_action :=
  let metadata :=
    (if negotiated.supports 33 then [.sendDaemonVersion config.daemonVersion] else [])
        ++ (if negotiated.supports 35 then [.sendTrustLevel config.trustLevel] else [])
  if negotiated.supports 38 then
    { next := .versioned config negotiated, actions := metadata }
  else
    { next := .nixReady negotiated, actions := metadata ++ [.ready] }

private
def transitionFeatures
    (config : handshake_config)
    (negotiated : ProtocolVersion)
    (clientFeatures : List Feature)
    : Transition ServerState server_action :=
  let active := featureIntersection config.serverFeatures clientFeatures
  if shouldOfferUpgrade config active then
    { next    := .upgrading config negotiated active,
      actions := [.sendFeatures config.serverFeatures, .sendUpgradeOffer] }
  else
    { next := .nixReady negotiated, actions := [.sendFeatures config.serverFeatures, .ready] }

private
def transitionUpgrade
    (config : handshake_config)
    (negotiated : ProtocolVersion)
    (accept : Bool)
    : Transition ServerState server_action :=
  if !accept then
    { next := .nixReady negotiated, actions := [.ready] }
  else
    match config.reapiConfig with
    | some reapiConfig =>
      { next := .reapiReady reapiConfig, actions := [.sendReapiConfig reapiConfig, .ready] }
    | none => { next := .failed "REAPI config missing", actions := [.fail "REAPI config missing"] }

/-- Server handshake transition function -/
def serverTransition : ServerState → server_event → Transition ServerState server_action

  -- INIT: receive client hello → VERSIONED
  | .init config, .clientHello clientVersion => transitionClientHello config clientVersion

  -- VERSIONED: receive legacy fields → check version for next state
  | .versioned config negotiated, .clientLegacy => transitionLegacy config negotiated

  -- VERSIONED: receive features → FEATURES or UPGRADING
  | .versioned config negotiated, .clientFeatures clientFeatures =>
    transitionFeatures config negotiated clientFeatures

  -- UPGRADING: receive upgrade response
  | .upgrading config negotiated _active, .clientUpgradeResponse accept =>
    transitionUpgrade config negotiated accept

  -- Terminal states: no transitions
  | .nixReady _, _ =>
    { next := .failed "Already in terminal state", actions := [.fail "Already terminal"] }
  | .reapiReady _, _ =>
    { next := .failed "Already in terminal state", actions := [.fail "Already terminal"] }
  | .failed reason, _ => { next := .failed reason, actions := [] }

  -- Invalid transitions
  | _state, event =>
    { next    := .failed s!"Invalid event {repr event} in state",
      actions := [.fail "Invalid transition"] }

/-- Server handshake state machine -/
def serverHandshake
    (config : handshake_config)
    : Machine ServerState server_event server_action := {
  initial := .init config
  transition := serverTransition
  isTerminal := fun state => match state with
    | .nixReady _   => true
    | .reapiReady _ => true
    | .failed _     => true
    | _             => false
}

-- ══════════════════════════════════════════════════════════════════════════════
-- CLIENT HANDSHAKE STATE MACHINE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Client handshake states -/
inductive client_state where
  | init (clientVersion : ProtocolVersion) (clientFeatures : List Feature)
  | sentHello (clientVersion : ProtocolVersion) (clientFeatures : List Feature)
  | versioned (negotiated : ProtocolVersion) (clientFeatures : List Feature)
  | awaitingUpgrade (negotiated : ProtocolVersion)
  | nixReady (version : ProtocolVersion)
  | reapiReady (config : ReapiConfig)
  | failed (reason : String)
  deriving Repr

/-- Client events (inputs from server) -/
inductive client_event where
  | serverHello (version : ProtocolVersion)
  | serverDaemonVersion (version : String)
  | serverTrustLevel (level : TrustLevel)
  | serverFeatures (features : List Feature)
  | upgradeOffer
  | reapiConfig (config : ReapiConfig)
  deriving Repr

/-- Client actions (outputs to server) -/
inductive client_action where
  | sendClientHello (version : ProtocolVersion)
  | sendLegacyFields
  | sendFeatures (features : List Feature)
  | sendUpgradeResponse (accept : Bool)
  | ready
  | fail (reason : String)
  deriving Repr

/-- Client handshake transition function -/
def clientTransition : client_state → client_event → Transition client_state client_action

  -- INIT → SENT_HELLO (automatic on start, not event-driven)
  -- This would be triggered by "start" event

  -- SENT_HELLO: receive server hello → VERSIONED
  | .sentHello clientVer clientFeatures, .serverHello serverVer =>
    let negotiated := if clientVer.value < serverVer.value then clientVer else serverVer
    { next := .versioned negotiated clientFeatures, actions := [.sendLegacyFields] }

  -- VERSIONED: receive daemon version (ignore, wait for more)
  | .versioned negotiated features, .serverDaemonVersion _ =>
    { next := .versioned negotiated features, actions := [] }

  -- VERSIONED: receive trust level (ignore, wait for more)
  | .versioned negotiated features, .serverTrustLevel _ =>
    { next := .versioned negotiated features, actions := [] }

  -- VERSIONED: receive server features → send ours, maybe await upgrade
  | .versioned negotiated clientFeatures, .serverFeatures serverFeatures =>
    let active := featureIntersection clientFeatures serverFeatures
    if active.contains .reapiV2 then
      { next := .awaitingUpgrade negotiated, actions := [.sendFeatures clientFeatures] }
    else
      { next := .nixReady negotiated, actions := [.sendFeatures clientFeatures, .ready] }

  -- AWAITING_UPGRADE: receive upgrade offer → accept
  | .awaitingUpgrade negotiated, .upgradeOffer =>
    {
      next := .awaitingUpgrade negotiated, -- Still waiting for config
      actions := [.sendUpgradeResponse true]
    }

  -- AWAITING_UPGRADE: receive REAPI config → ready
  | .awaitingUpgrade _, .reapiConfig config => { next := .reapiReady config, actions := [.ready] }

  -- Terminal states
  | .nixReady _, _    => { next := .failed "Already terminal", actions := [] }
  | .reapiReady _, _  => { next := .failed "Already terminal", actions := [] }
  | .failed reason, _ => { next := .failed reason, actions := [] }

  -- Invalid
  | _, _ => { next := .failed "Invalid transition", actions := [.fail "Invalid transition"] }

/-- Client handshake state machine -/
def clientHandshake
    (clientVersion : ProtocolVersion)
    (features : List Feature)
    : Machine client_state client_event client_action := {
  initial := .init clientVersion features
  transition := clientTransition
  isTerminal := fun state => match state with
    | .nixReady _   => true
    | .reapiReady _ => true
    | .failed _     => true
    | _             => false
}

-- ══════════════════════════════════════════════════════════════════════════════
-- PROPERTIES AND PROOFS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Server handshake is deterministic by construction (transition is a function) -/
theorem server_deterministic
        (config : handshake_config)
        (state : ServerState)
        (event : server_event)
        : (serverHandshake config).transition state event
            = (serverHandshake config).transition state event :=
  rfl

/-- Terminal states stay terminal: any event from a terminal state leads to a terminal state -/
theorem server_terminal_stays_terminal
        (config : handshake_config)
        (state : ServerState)
        (event : server_event)
        : (serverHandshake config).isTerminal state = true
            → (serverHandshake config).isTerminal
              ((serverHandshake config).transition state event).next
                = true := by
  intro terminalHypothesis
  simp [serverHandshake] at terminalHypothesis ⊢
  match state with
  | .nixReady _ => simp [serverTransition]
  | .reapiReady _ => simp [serverTransition]
  | .failed _ => simp [serverTransition]
  | .init _ => simp at terminalHypothesis
  | .versioned _ _ => simp at terminalHypothesis
  | .features _ _ _ => simp at terminalHypothesis
  | .upgrading _ _ _ => simp at terminalHypothesis

-- ══════════════════════════════════════════════════════════════════════════════
-- TEST TRACES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Example: successful Nix handshake (no REAPI) -/
def exampleNixHandshake : List server_event :=
  [
    .clientHello (ProtocolVersion.make 1 35), -- Old client, no features
    .clientLegacy
  ]

/-- Example: successful REAPI upgrade -/
def exampleReapiHandshake : List server_event :=
  [
    .clientHello ProtocolVersion.current,
    .clientFeatures [.reapiV2, .casSha256],
    .clientUpgradeResponse true
  ]

-- ══════════════════════════════════════════════════════════════════════════════
-- NIX DAEMON OPERATION STATE MACHINE
-- Models the request/response cycle after handshake completes
-- ══════════════════════════════════════════════════════════════════════════════

/-- Worker operation codes (subset - full list in Nix.lean) -/
inductive WorkerOp where
  | isValidPath
  | queryPathInfo
  | queryReferrers
  | addToStore
  | buildPaths
  | ensurePath
  | addTempRoot
  | queryMissing
  | narFromPath
  | addToStoreNar
  | setOptions
  | other (code : UInt64)
  deriving Repr, DecidableEq

/-- Daemon operation states -/
inductive daemon_op_state where
  /-- Waiting for client to send an operation -/
  | awaitingOp (version : ProtocolVersion)
  /-- Received operation, processing it -/
  | processing (version : ProtocolVersion) (operation : WorkerOp)
  /-- Sending stderr messages (logs, progress) -/
  | sendingStderr (version : ProtocolVersion) (operation : WorkerOp)
  /-- Sending final result -/
  | sendingResult (version : ProtocolVersion) (operation : WorkerOp)
  /-- Operation complete, ready for next -/
  | opComplete (version : ProtocolVersion)
  /-- Error occurred -/
  | opFailed (version : ProtocolVersion) (reason : String)
  deriving Repr

/-- Daemon operation events -/
inductive daemon_op_event where
  /-- Client sends an operation request -/
  | clientOp (operation : WorkerOp) (payload : Unit) -- payload is operation-specific
  /-- Processing completed (internal) -/
  | processComplete (success : Bool)
  /-- Stderr message sent -/
  | stderrSent
  /-- All stderr done, send result -/
  | stderrComplete
  /-- Result sent -/
  | resultSent
  /-- Client disconnected -/
  | clientDisconnect
  deriving Repr

/-- Daemon operation actions -/
inductive daemon_op_action where
  /-- Begin processing the operation -/
  | beginProcess (operation : WorkerOp)
  /-- Send stderr message to client -/
  | sendStderr (msg : String)
  /-- Send STDERR_LAST marker -/
  | sendStderrLast
  /-- Send operation result -/
  | sendResult (success : Bool)
  /-- Send error -/
  | sendError (reason : String)
  /-- Operation complete, ready for next -/
  | ready
  deriving Repr

/-- Daemon operation transition function -/
def daemonOpTransition
    : daemon_op_state → daemon_op_event → Transition daemon_op_state daemon_op_action
  -- AWAITING_OP: receive operation
  | .awaitingOp ver, .clientOp operation _ =>
    { next := .processing ver operation, actions := [.beginProcess operation] }

  -- PROCESSING: operation completed
  | .processing ver operation, .processComplete success =>
    if success then
      { next := .sendingStderr ver operation, actions := [] }
    else
      { next := .opFailed ver "Operation failed", actions := [.sendError "Operation failed"] }

  -- SENDING_STDERR: more stderr to send
  | .sendingStderr ver operation, .stderrSent =>
    { next := .sendingStderr ver operation, actions := [] }

  -- SENDING_STDERR: all stderr done
  | .sendingStderr ver operation, .stderrComplete =>
    { next := .sendingResult ver operation, actions := [.sendStderrLast] }

  -- SENDING_RESULT: result sent
  | .sendingResult ver _, .resultSent => { next := .opComplete ver, actions := [.ready] }

  -- OP_COMPLETE: ready for next operation
  | .opComplete ver, .clientOp operation _ =>
    { next := .processing ver operation, actions := [.beginProcess operation] }

  -- Client disconnect from any state
  | _, .clientDisconnect =>
    { next := .opFailed ProtocolVersion.current "Client disconnected", actions := [] }

  -- Failed state absorbs all
  | .opFailed ver reason, _ => { next := .opFailed ver reason, actions := [] }

  -- Invalid transitions
  | currentState, _ =>
    { next    := .opFailed ProtocolVersion.current "Invalid daemon op transition",
      actions := [.sendError "Protocol error"] }

/-- Daemon operation state machine -/
def daemonOps
    (version : ProtocolVersion)
    : Machine daemon_op_state daemon_op_event daemon_op_action :=
  {
    initial := .awaitingOp version
    transition := daemonOpTransition
    isTerminal := fun state => match state with
      | .opFailed _ _ => true
      | _ => false  -- Normal ops loop forever
  }

-- ══════════════════════════════════════════════════════════════════════════════
-- STDERR FRAMING STATE MACHINE
-- Models the stderr message protocol within an operation
-- ══════════════════════════════════════════════════════════════════════════════

/-- Stderr message types (wire codes) -/
inductive StderrType where
  | next          -- 0x6f6c6d67: more output
  | read          -- 0x64617461: request input
  | write         -- 0x64617416: write output
  | last          -- 0x616c7473: complete
  | error         -- 0x63787470: error
  | startActivity -- 0x53545254: activity start (>= 1.20)
  | stopActivity  -- 0x53544F50: activity stop (>= 1.20)
  | result        -- 0x52534C54: activity result (>= 1.20)
  deriving Repr, DecidableEq

/-- Stderr framing states -/
inductive stderr_state where
  | idle
  | streaming (pending : Nat) -- Number of messages to send
  | waitingInput              -- Waiting for client input (STDERR_READ)
  | complete
  | errored (reason : String)
  deriving Repr

/-- Stderr framing events -/
inductive stderr_event where
  | beginResponse (messageCount : Nat)
  | sendMessage (typ : StderrType) (data : Unit)
  | messageSent
  | requestInput (bytes : Nat)
  | inputReceived
  | finalize
  | error (reason : String)
  deriving Repr

/-- Stderr framing actions -/
inductive stderr_action where
  | emitStderrNext (data : Unit)
  | emitStderrRead (bytes : Nat)
  | emitStderrWrite (data : Unit)
  | emitStderrLast
  | emitStderrError (reason : String)
  | emitStartActivity (identifier : Nat) (typ : Nat)
  | emitStopActivity (identifier : Nat)
  | emitResult (identifier : Nat)
  deriving Repr

/-- Stderr framing transition function -/
def stderrTransition : stderr_state → stderr_event → Transition stderr_state stderr_action
  -- IDLE: begin response
  | .idle, .beginResponse remaining =>
    if remaining > 0 then
      { next := .streaming remaining, actions := [] }
    else
      { next := .complete, actions := [.emitStderrLast] }

  -- STREAMING: send a message
  | .streaming remaining, .sendMessage typ _ =>
    match typ with
    | .next  => { next := .streaming remaining, actions := [.emitStderrNext ()] }
    | .read  => { next := .waitingInput, actions := [.emitStderrRead 0] }
    | .last  => { next := .complete, actions := [.emitStderrLast] }
    | .error => { next := .errored "Error sent", actions := [.emitStderrError "Error"] }
    | _      => { next := .streaming remaining, actions := [] }

  -- STREAMING: message sent, decrement counter
  | .streaming remaining, .messageSent =>
    if remaining > 1 then
      { next := .streaming (remaining - 1), actions := [] }
    else
      { next := .complete, actions := [.emitStderrLast] }

  -- WAITING_INPUT: received input
  | .waitingInput, .inputReceived => { next := .streaming 0, actions := [] } -- Resume streaming

  -- STREAMING/IDLE: finalize
  | .streaming _, .finalize => { next := .complete, actions := [.emitStderrLast] }
  | .idle, .finalize        => { next := .complete, actions := [.emitStderrLast] }

  -- Error from any state
  | _, .error reason => { next := .errored reason, actions := [.emitStderrError reason] }

  -- Terminal states
  | .complete, _       => { next := .complete, actions := [] }
  | .errored result, _ => { next := .errored result, actions := [] }

  -- Invalid
  | _, _ => { next := .errored "Invalid stderr transition", actions := [] }

/-- Stderr framing state machine -/
def stderrFraming : Machine stderr_state stderr_event stderr_action := {
  initial := .idle
  transition := stderrTransition
  isTerminal := fun state => match state with
    | .complete  => true
    | .errored _ => true
    | _          => false
}

-- ══════════════════════════════════════════════════════════════════════════════
-- COMPOSED DAEMON STATE MACHINE
-- Handshake → Operations (using sequential combinator)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Combined daemon event type -/
abbrev DaemonEvent := seq_event server_event daemon_op_event

/-- Combined daemon action type -/
abbrev DaemonAction := either server_action daemon_op_action

/-- Full daemon state machine: handshake then operations -/
def daemonMachine
    (config : handshake_config)
    : Machine (seq_state ServerState daemon_op_state) DaemonEvent DaemonAction :=
  (serverHandshake config).sequential (daemonOps config.serverVersion)

/-- Example: full daemon trace (handshake + one operation) -/
def exampleDaemonTrace : List DaemonEvent :=
  [
    .ev1 (.clientHello ProtocolVersion.current),
    .ev1 (.clientFeatures [.reapiV2]),
    .ev1 (.clientUpgradeResponse true),
    .handoff,
    .ev2 (.clientOp .isValidPath ()),
    .ev2 (.processComplete true),
    .ev2 .stderrComplete,
    .ev2 .resultSent
  ]

end Continuity.Machine.Protocol.NixHandshake
