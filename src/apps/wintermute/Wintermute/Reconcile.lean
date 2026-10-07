/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // WINTERMUTE // RECONCILE // CORE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The reconciler as a `Continuity.Machine.abstract_machine Event Command` —
    the entire hot-reload control loop is this pure Mealy step; the IO shell
    only ferries events in and commands out.

    Semantics (Kubernetes-style level triggering, generation-fenced):

      desired g t   the control plane observed generation `g` wanting theme
                    `t`. Stale generations (g ≤ applied) are REJECTED — the
                    fence that makes concurrent writers safe. Fresh no-ops
                    (t already applied) advance the fence silently. Fresh
                    changes emit `broadcast` (live channels) + `persist`
                    (durable token rewrite).
      tick          anti-entropy heartbeat: re-broadcast the applied theme so
                    a client that missed a live update (respawned terminal,
                    restarted shell) converges anyway. Never mutates state.

    THE THEOREMS

      gen_monotone          the applied generation never decreases
      tick_fixed            heartbeats never change state
      desired_idempotent    replaying an observation emits nothing
      desired_converges     a fresh observation is applied, immediately
      step_preserves        ANY predicate holding on all input themes holds on
                            every emitted command — instantiated with the hue
                            lock, this is "no transition can corrupt the ramp"
      run_preserves         the same, over whole event streams, by induction
                            through `feedThrough`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.machine.abstract
import Wintermute.Theme

namespace Wintermute

open Continuity.Machine

-- ═══════════════════════════════════════════════════════════════════════════════
--  EVENTS / COMMANDS / STATE
-- ═══════════════════════════════════════════════════════════════════════════════

inductive Event where
  /-- The control plane observed generation `gen` desiring `theme`. -/
  | desired (gen : Nat) (theme : ThemeVector)
  /-- Anti-entropy heartbeat. -/
  | tick
  deriving Repr, BEq, DecidableEq

inductive Command where
  /-- Push to every live channel (hyprctl, terminals, editors, portal). -/
  | broadcast (gen : Nat) (theme : ThemeVector)
  /-- Durably rewrite the token files (atomic temp+rename). -/
  | persist (gen : Nat) (theme : ThemeVector)
  deriving Repr, BEq, DecidableEq

def Command.theme : Command → ThemeVector
  | .broadcast _ t => t
  | .persist _ t => t

def Command.gen : Command → Nat
  | .broadcast g _ => g
  | .persist g _ => g

structure ReconState where
  gen     : Nat := 0
  applied : Option ThemeVector := none
  deriving Repr, BEq, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
--  THE STEP
-- ═══════════════════════════════════════════════════════════════════════════════

def stepFn (s : ReconState) : Event → ReconState × List Command
  | .desired g t =>
    if g ≤ s.gen then (s, [])
    else if s.applied = some t then ({ gen := g, applied := s.applied }, [])
    else ({ gen := g, applied := some t }, [.broadcast g t, .persist g t])
  | .tick =>
    match s.applied with
    | none => (s, [])
    | some t => (s, [.broadcast s.gen t])

/-- The reconciler machine. Composable with the whole `abstract_machine`
    calculus — `reconciler ⋙ arr render` is the daemon's actual pipeline. -/
def reconciler : abstract_machine Event Command where
  State := ReconState
  initial := {}
  step := stepFn

-- ═══════════════════════════════════════════════════════════════════════════════
--  SINGLE-STEP THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generation monotonicity: no event can move the fence backwards. -/
theorem gen_monotone
        (s : ReconState)
        (e : Event)
        : s.gen ≤ (stepFn s e).1.gen := by

  cases e with
  | desired g t =>
    by_cases h1 : g ≤ s.gen
    · simp [stepFn, h1]
    · by_cases h2 : s.applied = some t <;> simp [stepFn, h1, h2] <;> omega
  | tick =>
    cases h : s.applied <;> simp [stepFn, h]

/-- Heartbeats are read-only: `tick` never changes state. -/
theorem tick_fixed
        (s : ReconState)
        : (stepFn s .tick).1 = s := by

  cases h : s.applied <;> simp [stepFn, h]

/-- Anti-entropy soundness: a heartbeat broadcasts EXACTLY the applied theme
    at the applied generation — never an invented one. -/
theorem tick_broadcasts_applied
        (s : ReconState)
        (t : ThemeVector)
        (h : s.applied = some t)
        : (stepFn s .tick).2 = [.broadcast s.gen t] := by

  simp [stepFn, h]

/-- Idempotence: replaying the same observation emits nothing — the second
    application of any `desired` is a silent no-op. Level-triggered semantics
    with edge-triggered cost. -/
theorem desired_idempotent
        (s : ReconState)
        (g : Nat)
        (t : ThemeVector)
        : (stepFn (stepFn s (.desired g t)).1 (.desired g t)).2 = [] := by

  by_cases h1 : g ≤ s.gen
  · simp [stepFn, h1]
  · by_cases h2 : s.applied = some t <;> simp [stepFn, h1, h2]

/-- Convergence: a fresh observation is applied in ONE step — after
    `desired g t` with `g` past the fence, the machine's applied theme is `t`. -/
theorem desired_converges
        (s : ReconState)
        (g : Nat)
        (t : ThemeVector)
        (hfresh : s.gen < g)
        : (stepFn s (.desired g t)).1.applied = some t := by

  have h1 : ¬ g ≤ s.gen := by omega
  by_cases h2 : s.applied = some t <;> simp [stepFn, h1, h2]

/-- Fence advancement: a fresh observation moves the fence to exactly `g`. -/
theorem desired_advances
        (s : ReconState)
        (g : Nat)
        (t : ThemeVector)
        (hfresh : s.gen < g)
        : (stepFn s (.desired g t)).1.gen = g := by

  have h1 : ¬ g ≤ s.gen := by omega
  by_cases h2 : s.applied = some t <;> simp [stepFn, h1, h2]

-- ═══════════════════════════════════════════════════════════════════════════════
--  PRESERVATION  — the hue lock (or ANY invariant) survives every transition
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A predicate on themes holds of a state when it holds of the applied theme
    (vacuously of the empty state). -/
def StateOk (P : ThemeVector → Prop) (s : ReconState) : Prop :=
  ∀ u, s.applied = some u → P u

/-- An event is `P`-good when any theme it carries satisfies `P`. -/
def EventOk (P : ThemeVector → Prop) : Event → Prop
  | .desired _ t => P t
  | .tick => True

/-- ONE step preserves any theme invariant: if the state and the event are
    `P`-good, the next state is `P`-good and every emitted command carries a
    `P`-good theme. Instantiate `P` with "hue-locked ramp" and this is the
    transition half of the hue-lock story (`palette_ramp_luminance_only` is
    the color half): the daemon can only ever paint themes it was given. -/
theorem step_preserves
        (P : ThemeVector → Prop)
        (s : ReconState)
        (e : Event)
        (hs : StateOk P s)
        (he : EventOk P e)
        : StateOk P (stepFn s e).1 ∧ ∀ c ∈ (stepFn s e).2, P c.theme := by

  cases e with
  | desired g t =>
    have ht : P t := he
    by_cases h1 : g ≤ s.gen
    · constructor
      · simpa [stepFn, h1] using hs
      · intro c hc
        simp [stepFn, h1] at hc
    · by_cases h2 : s.applied = some t
      · constructor
        · intro u hu
          simp [stepFn, h1, h2] at hu
          exact hu ▸ ht
        · intro c hc
          simp [stepFn, h1, h2] at hc
      · constructor
        · intro u hu
          simp [stepFn, h1, h2] at hu
          exact hu ▸ ht
        · intro c hc
          simp [stepFn, h1, h2] at hc
          rcases hc with rfl | rfl <;> simpa [Command.theme] using ht
  | tick =>
    cases h : s.applied with
    | none =>
      constructor
      · simpa [stepFn, h] using hs
      · intro c hc
        simp [stepFn, h] at hc
    | some t =>
      constructor
      · rw [tick_fixed]
        exact hs
      · intro c hc
        rw [tick_broadcasts_applied s t h] at hc
        simp at hc
        subst hc
        simpa [Command.theme] using hs t h

/-- Stream preservation, by induction through `feedThrough`: over ANY event
    history whose desired themes all satisfy `P`, every command the reconciler
    ever emits satisfies `P`. -/
theorem run_preserves
        (P : ThemeVector → Prop)
        (s : ReconState)
        (events : List Event)
        (hs : StateOk P s)
        (he : ∀ e ∈ events, EventOk P e)
        : StateOk P (abstract_machine.feedThrough reconciler s events).1
            ∧ ∀ c ∈ (abstract_machine.feedThrough reconciler s events).2, P c.theme := by

  induction events generalizing s with
  | nil => exact ⟨hs, by intro c hc; cases hc⟩
  | cons e es ih =>
    have heHead : EventOk P e := he e (List.mem_cons_self ..)
    have heTail : ∀ e' ∈ es, EventOk P e' := fun e' h' => he e' (List.mem_cons_of_mem e h')
    have hstep := step_preserves P s e hs heHead
    have hrest := ih (stepFn s e).1 hstep.1 heTail
    refine ⟨hrest.1, ?_⟩
    intro c hc
    rw [abstract_machine.feedThrough_cons] at hc
    rcases List.mem_append.mp hc with h | h
    · exact hstep.2 c h
    · exact hrest.2 c h

-- ═══════════════════════════════════════════════════════════════════════════════
--  IT RUNS  — the semantics, checked by computation
-- ═══════════════════════════════════════════════════════════════════════════════

private def razorgirl : ThemeVector := { luminance := .dark .carbon, register := 1000 }

-- A fresh desire broadcasts + persists once; replay is silent; heartbeat
-- re-broadcasts the applied theme.
example :
    abstract_machine.outputs reconciler
      [.desired 1 razorgirl, .desired 1 razorgirl, .tick]
      = [.broadcast 1 razorgirl, .persist 1 razorgirl, .broadcast 1 razorgirl] := by
  native_decide

-- Stale generations are fenced out even with a different theme.
example :
    abstract_machine.outputs reconciler
      [.desired 5 razorgirl, .desired 3 { razorgirl with heroHue := 0 }]
      = [.broadcast 5 razorgirl, .persist 5 razorgirl] := by
  native_decide

end Wintermute
