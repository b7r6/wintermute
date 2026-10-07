/-
  Continuity.Machine - Verified State Machine DSL

  Models protocol state machines with machine-checked properties:
  - Determinism: each (state, event) pair has exactly one transition
  - Safety: only valid transitions are expressible
  - Progress: terminal states are explicitly marked
  - Completeness: all states handle all relevant events

  ## Design

  A state machine is defined by:
  1. State type (finite, enumerable)
  2. Event type (inputs that trigger transitions)
  3. Action type (outputs produced by transitions)
  4. Transition function: State → Event → (State × List Action)

  ## Properties We Prove

  - **Determinism**: transition is a function (not a relation)
  - **Type Safety**: invalid (state, event) pairs are compile errors
  - **Reachability**: all non-initial states are reachable (optional)
  - **Termination**: terminal states produce no further transitions (optional)
-/

namespace Continuity.Machine

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE STATE MACHINE TYPES
-- ══════════════════════════════════════════════════════════════════════════════

/-- A transition produces a new state and a list of actions -/
structure Transition (State Action : Type) where
  next    : State
  actions : List Action
  deriving Repr

/-- Action state machine definition -/
structure Machine (State Event Action : Type) where
  /-- Initial state -/
  initial : State
  /-- Transition function (total - must handle all state/event pairs) -/
  transition : State → Event → Transition State Action
  /-- Terminal states (no further transitions expected) -/
  isTerminal : State → Bool

/-- Step a machine: apply event to current state -/
def Machine.step
    {State Event Action : Type}
    (machine : Machine State Event Action)
    (state : State)
    (event : Event)
    : State × List Action :=
  let transition := machine.transition state event
  (transition.next, transition.actions)

/-- Run a sequence of events -/
def Machine.run
    {State Event Action : Type}
    (machine : Machine State Event Action)
    (events : List Event)
    : State × List Action :=
  events.foldl
    (fun (state, actions) event =>
      let (nextState, newActions) := machine.step state event
      (nextState, actions ++ newActions))
    (machine.initial, [])

-- ══════════════════════════════════════════════════════════════════════════════
-- PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Action transition sequence is valid if it ends in a terminal state -/
def Machine.validTrace
    {State Event Action : Type}
    (machine : Machine State Event Action)
    (events : List Event)
    : Bool :=
  machine.isTerminal (machine.run events).1

/-- Two machines are equivalent if they produce the same outputs for all inputs -/
def Machine.equiv
    {State Event Action : Type}
    [DecidableEq State]
    [DecidableEq Action]
    (leftMachine rightMachine : Machine State Event Action)
    (events : List Event)
    : Prop :=
  leftMachine.run events = rightMachine.run events

-- ══════════════════════════════════════════════════════════════════════════════
-- STATE MACHINE COMBINATORS
-- These enable compositional construction of complex state machines
-- ══════════════════════════════════════════════════════════════════════════════

/--
Product: Run two machines in parallel on their respective events.
State is the product of states, events are tagged (Left/Right).
-/
inductive either (Input Output : Type) where
  | left : Input → either Input Output
  | right : Output → either Input Output
  deriving Repr, DecidableEq

def Machine.product
    {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type}
    (leftMachine : Machine LeftState LeftEvent LeftAction)
    (rightMachine : Machine RightState RightEvent RightAction)
    : Machine (LeftState × RightState) (either LeftEvent RightEvent) (either LeftAction RightAction) where
  initial := (leftMachine.initial, rightMachine.initial)
  transition := fun (state1, state2) event => match event with
    | .left leftEvent =>
      let leftTransition := leftMachine.transition state1 leftEvent
      { next := (leftTransition.next, state2), actions := leftTransition.actions.map .left }
    | .right rightEvent =>
      let rightTransition := rightMachine.transition state2 rightEvent
      { next := (state1, rightTransition.next), actions := rightTransition.actions.map .right }
  isTerminal := fun (state1, state2) =>
    leftMachine.isTerminal state1 && rightMachine.isTerminal state2

/--
Sum: Choose between two machines based on initial event.
Once started, stays in that branch.
-/
inductive sum_state (LeftState RightState : Type) where
  | uninit
  | inLeft : LeftState → sum_state LeftState RightState
  | inRight : RightState → sum_state LeftState RightState
  deriving Repr

def Machine.sum {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type} (leftMachine : Machine LeftState LeftEvent LeftAction) (rightMachine : Machine RightState RightEvent RightAction)
    : Machine (sum_state LeftState RightState) (either LeftEvent RightEvent) (either LeftAction RightAction) where
  initial := .uninit
  transition := fun state event =>
    match state, event with
    | .uninit, .left leftEvent =>
      let transition := leftMachine.transition leftMachine.initial leftEvent
      { next := .inLeft transition.next, actions := transition.actions.map .left }
    | .uninit, .right rightEvent =>
      let transition := rightMachine.transition rightMachine.initial rightEvent
      { next := .inRight transition.next, actions := transition.actions.map .right }
    | .inLeft leftState, .left leftEvent =>
      let transition := leftMachine.transition leftState leftEvent
      { next := .inLeft transition.next, actions := transition.actions.map .left }
    | .inRight rightState, .right rightEvent =>
      let transition := rightMachine.transition rightState rightEvent
      { next := .inRight transition.next, actions := transition.actions.map .right }
    | .inLeft leftState, .right _ =>
      { next := .inLeft leftState, actions := [] }  -- Ignore wrong-branch event
    | .inRight rightState, .left _ =>
      { next := .inRight rightState, actions := [] }
  isTerminal := fun state =>
    match state with
    | .uninit => false
    | .inLeft leftState => leftMachine.isTerminal leftState
    | .inRight rightState => rightMachine.isTerminal rightState

/--
Sequential: Run leftMachine until terminal, then switch to rightMachine.
A "handoff" event triggers the transition from leftMachine's terminal state to rightMachine's initial.
-/
inductive seq_state (LeftState RightState : Type) where
  | phase1 : LeftState → seq_state LeftState RightState
  | phase2 : RightState → seq_state LeftState RightState
  deriving Repr

inductive seq_event (LeftEvent RightEvent : Type) where
  | ev1 : LeftEvent → seq_event LeftEvent RightEvent
  | handoff : seq_event LeftEvent RightEvent
  | ev2 : RightEvent → seq_event LeftEvent RightEvent
  deriving Repr

def Machine.sequential {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type} (leftMachine : Machine LeftState LeftEvent LeftAction) (rightMachine : Machine RightState RightEvent RightAction)
    : Machine (seq_state LeftState RightState) (seq_event LeftEvent RightEvent) (either LeftAction RightAction) where
  initial := .phase1 leftMachine.initial
  transition := fun state event =>
    match state, event with
    | .phase1 leftState, .ev1 leftEvent =>
      let transition := leftMachine.transition leftState leftEvent
      { next := .phase1 transition.next, actions := transition.actions.map .left }
    | .phase1 leftState, .handoff =>
      if leftMachine.isTerminal leftState then
        { next := .phase2 rightMachine.initial, actions := [] }
      else
        { next := .phase1 leftState, actions := [] }  -- Not ready to handoff
    | .phase1 leftState, .ev2 _ =>
      { next := .phase1 leftState, actions := [] }  -- Ignore phase2 events
    | .phase2 rightState, .ev2 rightEvent =>
      let transition := rightMachine.transition rightState rightEvent
      { next := .phase2 transition.next, actions := transition.actions.map .right }
    | .phase2 rightState, _ =>
      { next := .phase2 rightState, actions := [] }  -- Ignore phase1/handoff events
  isTerminal := fun state =>
    match state with
    | .phase1 _ => false
    | .phase2 rightState => rightMachine.isTerminal rightState

/--
Lift: Transform a machine's state, events, and actions through functions.
Useful for embedding a machine into a larger context.
-/
def Machine.lift
    {State Event Action State' Event' Action' : Type}
    (machine : Machine State Event Action)
    (mapState : State → State')
    (nextMapState : State' → State)
    (mapEvent : Event' → Event)
    (mapAction : Action → Action')
    (initS' : State')
    (termS' : State' → Bool)
    : Machine State' Event' Action' where
  initial := initS'
  transition := fun liftedState liftedEvent =>
    let transition := machine.transition (nextMapState liftedState) (mapEvent liftedEvent)
    { next := mapState transition.next, actions := transition.actions.map mapAction }
  isTerminal := termS'

/--
Map actions: Transform actions without changing state or events.
-/
def Machine.mapActions
    {State Event Action Action' : Type}
    (machine : Machine State Event Action)
    (transform : Action → Action')
    : Machine State Event Action' where
  initial := machine.initial
  transition := fun state event =>
    let transition := machine.transition state event
    { next := transition.next, actions := transition.actions.map transform }
  isTerminal := machine.isTerminal

/--
Filter actions: Only emit actions that satisfy a predicate.
-/
def Machine.filterActions
    {State Event Action : Type}
    (machine : Machine State Event Action)
    (predicate : Action → Bool)
    : Machine State Event Action where
  initial := machine.initial
  transition := fun state event =>
    let transition := machine.transition state event
    { next := transition.next, actions := transition.actions.filter predicate }
  isTerminal := machine.isTerminal

/--
Extend state: Add extra state that doesn't affect transitions.
Useful for attaching metadata (counters, timestamps, etc.)
-/
def Machine.extendState
    {State Event Action Extra : Type}
    (machine : Machine State Event Action)
    (init : Extra)
    : Machine (State × Extra) Event Action where
  initial := (machine.initial, init)
  transition := fun (state, extraState) event =>
    let transition := machine.transition state event
    { next := (transition.next, extraState), actions := transition.actions }
  isTerminal := fun (state, _) => machine.isTerminal state

/--
Modify extended state based on transitions.
-/
def Machine.withState
    {State Event Action Extra : Type}
    (machine : Machine State Event Action)
    (init : Extra)
    (update : State → Event → Extra → Extra)
    : Machine (State × Extra) Event Action where
  initial := (machine.initial, init)
  transition := fun (state, extraState) event =>
    let transition := machine.transition state event
    { next := (transition.next, update state event extraState), actions := transition.actions }
  isTerminal := fun (state, _) => machine.isTerminal state

-- ══════════════════════════════════════════════════════════════════════════════
-- COMBINATOR PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Product factors: left event only modifies left component -/
theorem product_left_preserves_right
        {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type}
        (leftMachine : Machine LeftState LeftEvent LeftAction)
        (rightMachine : Machine RightState RightEvent RightAction)
        (leftState : LeftState)
        (rightState : RightState)
        (leftEvent : LeftEvent)
        : ((leftMachine.product rightMachine).transition (leftState, rightState) (.left leftEvent)).next
            = ((leftMachine.transition leftState leftEvent).next, rightState) := by
  simp [Machine.product]

/-- Product factors: right event only modifies right component -/
theorem product_right_preserves_left
        {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type}
        (leftMachine : Machine LeftState LeftEvent LeftAction)
        (rightMachine : Machine RightState RightEvent RightAction)
        (leftState : LeftState)
        (rightState : RightState)
        (rightEvent : RightEvent)
        : ((leftMachine.product rightMachine).transition (leftState, rightState) (.right rightEvent)).next
            = (leftState, (rightMachine.transition rightState rightEvent).next) := by
  simp [Machine.product]

/-- Sequential handoff only occurs at terminal states -/
theorem sequential_handoff_requires_terminal
        {LeftState RightState LeftEvent RightEvent LeftAction RightAction : Type}
        (leftMachine : Machine LeftState LeftEvent LeftAction)
        (rightMachine : Machine RightState RightEvent RightAction)
        (leftState : LeftState)
        : ((leftMachine.sequential rightMachine).transition (.phase1 leftState) .handoff).next
            = .phase2 rightMachine.initial
            → leftMachine.isTerminal leftState = true := by
  simp [Machine.sequential]

  -- Introduce the claimed handoff equation.
  intro handoffEquation

  -- Split on whether the first phase is terminal.
  by_cases isTerminal : leftMachine.isTerminal leftState

  -- Discharge the terminal branch directly.
  · exact isTerminal

  -- Refute a handoff from a nonterminal state.
  · simp [isTerminal] at handoffEquation

/-- MapActions preserves state transitions exactly -/
theorem mapActions_preserves_next
        {State Event Action Action' : Type}
        (machine : Machine State Event Action)
        (transform : Action → Action')
        (state : State)
        (event : Event)
        : ((machine.mapActions transform).transition state event).next
            = (machine.transition state event).next := by simp [Machine.mapActions]

end Continuity.Machine
