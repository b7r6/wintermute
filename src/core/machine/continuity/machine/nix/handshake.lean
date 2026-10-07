/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                            // CONTINUITY // MACHINE // NIX // HANDSHAKE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The boss — the Nix daemon server handshake on the arrow toolkit. The data-rich
    one: version negotiation (min of client/server), feature intersection, and
    conditional action lists keyed on the negotiated version. Seven states.

    The lesson of the rung: the EXISTING hand-rolled `serverTransition` (written
    against the old `Machine` engine) drops into the arrow category for free — one
    trivial adapter, logic reused verbatim. And the toolkit lets us prove the
    correctness properties that were never stated before, exactly where the
    data-richness lives:

      · negotiated_is_offered  — the server never invents a version; it picks one a
                                 party actually offered (no version injection).
      · feature_no_confusion   — an activated feature was offered by BOTH sides (no
                                 feature-confusion / silent downgrade).
      · terminal_absorbing     — a completed handshake stays completed.

    Determinism is free (the transition is a function). Five rungs of toolkit, and
    the boss is a short fight.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.machine.abstract
import continuity.machine.protocol.nix_handshake

namespace Continuity.Machine.Nix

open Continuity.Machine
open Continuity.Machine.abstract_machine
open Continuity.Machine.Protocol.NixHandshake

/-- Adapt the existing `Transition`-returning `serverTransition` to the arrow's
    pair-returning `step`. The negotiation logic is reused verbatim. -/
def serverStep (state : ServerState) (event : server_event) : ServerState × List server_action :=
  let transition := serverTransition state event
  (transition.next, transition.actions)

/-- The Nix daemon server handshake, as a first-class machine in the arrow category. -/
def nixHandshake (config : handshake_config) : abstract_machine server_event server_action where
  State := ServerState
  initial := .init config
  step := serverStep
  done := fun state => match state with
    | .nixReady _ | .reapiReady _ | .failed _ => true
    | _ => false

-- ══════════════════════════════════════════════════════════════════════════════
--  DATA-RICH CORRECTNESS  — the properties only this machine could have
-- ══════════════════════════════════════════════════════════════════════════════

/-- The server announces its own version first, before negotiating. -/
theorem hello_announces_version
        (config : handshake_config)
        (clientVersion : ProtocolVersion)
        : (serverStep (.init config) (.clientHello clientVersion)).2
            = [.sendServerHello config.serverVersion] :=
  rfl

/-- NO VERSION INJECTION: the negotiated version is one a party actually offered —
    never a value the server invented. -/
theorem negotiated_is_offered
        (config : handshake_config)
        (clientVersion : ProtocolVersion)
        : (serverStep (.init config) (.clientHello clientVersion)).1
            = .versioned config clientVersion
            ∨ (serverStep (.init config) (.clientHello clientVersion)).1
                = .versioned config config.serverVersion := by
  simp only [serverStep, serverTransition, transitionClientHello]

  -- Split on the version negotiation result.
  split

  -- Record the client-offered version.
  · exact Or.inl rfl

  -- Record the server-offered version.
  · exact Or.inr rfl

/-- NO FEATURE CONFUSION: every active feature was offered by BOTH the server (`a`)
    and the client (`b`). The server can't silently enable something the client
    never asked for — the anti-downgrade guarantee. -/
theorem feature_no_confusion
        (leftFeature rightFeature : List Feature)
        (feature : Feature)
        (hypothesis : feature ∈ featureIntersection leftFeature rightFeature)
        : feature ∈ leftFeature ∧ rightFeature.contains feature = true := by
  unfold featureIntersection at hypothesis

  -- Expose both membership conditions.
  exact List.mem_filter.mp hypothesis

/-- A completed handshake stays completed: terminal states are absorbing. -/
theorem terminal_absorbing
        (config : handshake_config)
        (state : ServerState)
        (event : server_event)
        (hypothesis : (nixHandshake config).done state = true)
        : (nixHandshake config).done (serverStep state event).1 = true := by
  match state with
  | .nixReady _ => simp [nixHandshake, serverStep, serverTransition]
  | .reapiReady _ => simp [nixHandshake, serverStep, serverTransition]
  | .failed _ => simp [nixHandshake, serverStep, serverTransition]
  | .init _ => simp [nixHandshake] at hypothesis
  | .versioned _ _ => simp [nixHandshake] at hypothesis
  | .features _ _ _ => simp [nixHandshake] at hypothesis
  | .upgrading _ _ _ => simp [nixHandshake] at hypothesis

-- ══════════════════════════════════════════════════════════════════════════════
--  THE BOSS RUNS  — a full REAPI-upgrade handshake, end to end
-- ══════════════════════════════════════════════════════════════════════════════

/-- Client hello (1.38) → features [reapiV2, casSha256] → accept upgrade: the server
    negotiates, intersects features, offers and confirms the REAPI upgrade. -/
example :
    outputs
      (nixHandshake .default)
      [
        .clientHello ProtocolVersion.current,
        .clientFeatures [.reapiV2, .casSha256],
        .clientUpgradeResponse true
      ]
        = [
          .sendServerHello ProtocolVersion.current,
          .sendFeatures [.reapiV2, .casSha256, .streamingNar],
          .sendUpgradeOffer,
          .sendReapiConfig { instanceName := "main", digestFunction := 0 },
          .ready
        ] := by native_decide

/-- It's a first-class arrow value like every other machine. -/
example (config : handshake_config) (events : List server_event) :
    outputs (idMachine ⋙ nixHandshake config) events = outputs (nixHandshake config) events :=
  id_compose (nixHandshake config) events

end Continuity.Machine.Nix
