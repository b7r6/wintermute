/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // CONTINUITY // MACHINE // ABSTRACT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The arrow/category of machines — so protocol machines are COMPOSED from
    verified combinators, not hand-rolled.

    `AbstractMachine Input Output` is a Mealy stream transducer: it consumes inputs `Input`
    (io_uring completions / market ticks / parsed events) and, per input, emits a
    list of outputs `Output` (submissions / orders / actions), threading hidden state.
    This is the Haskell `Mealy`/`machines` Arrow — but here the Category and Arrow
    laws are THEOREMS, not folklore.

    The whole thing rests on one homomorphism: a machine's behaviour is the stream
    function `outputs : List Input → List Output`, and composition of machines IS
    composition of those functions —

        outputs (m ⋙ n)  =  outputs n ∘ outputs m            (outputs_compose)

    Every law (identity, associativity, the arr laws) falls straight out of it.

    Mirrors libevring-cpp `evring/machine/abstract_machine.h` (which conformance-
    tests its C++ against this). See [[build-roadmap]].

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Machine

/-- A Mealy stream transducer `Input → Output` with existentially-hidden state.
    `step s i = (s', os)` : consume one input, advance state, emit a list of outputs. -/
structure abstract_machine (Input Output : Type) where
  State   : Type
  initial : State
  step    : State → Input → State × List Output
  done    : State → Bool := fun _ => false

namespace abstract_machine

variable {Input Intermediate Output Result : Type}

-- ══════════════════════════════════════════════════════════════════════════════
--  FEED-THROUGH / RUN  — driving a machine over an input list
-- ══════════════════════════════════════════════════════════════════════════════

/-- Drive `n` over `inputs` from `s`, threading state and concatenating the
    per-input output lists. (Lean's `feedThrough`; the C++ `feed_through`.) -/
def feedThrough
    (rightMachine : abstract_machine Input Output)
    : rightMachine.State → List Input → rightMachine.State × List Output
  | state, [] => (state, [])
  | state, instruction :: instructions =>
    let stepResult := rightMachine.step state instruction
    let remainingResult := feedThrough rightMachine stepResult.1 instructions
    (remainingResult.1, stepResult.2 ++ remainingResult.2)

/-- Run from the initial state. -/
def run
    (machine : abstract_machine Input Output)
    (inputs : List Input)
    : machine.State × List Output :=
  feedThrough machine machine.initial inputs

/-- The observable behaviour: the output stream produced for an input stream. -/
def outputs (machine : abstract_machine Input Output) (inputs : List Input) : List Output :=
  (run machine inputs).2

/-- Behavioural equivalence: same outputs for every input stream — the equivalence
    the C++ `equivalent_on` harness checks. The Category/Arrow laws hold up to `≋`. -/
def behEquiv (machine rightMachine : abstract_machine Input Output) : Prop :=
  ∀ inputs, outputs machine inputs = outputs rightMachine inputs

@[inherit_doc] scoped infix:50 " ≋ " => behEquiv

theorem behEquiv_refl (machine : abstract_machine Input Output) : machine ≋ machine := fun _ => rfl

theorem behEquiv_symm
        {machine rightMachine : abstract_machine Input Output}
        (equivalenceProof : machine ≋ rightMachine)
        : rightMachine ≋ machine := fun inputs => (equivalenceProof inputs).symm

theorem behEquiv_trans
        {machine rightMachine predicate : abstract_machine Input Output}
        (leftProof : machine ≋ rightMachine)
        (rightProof : rightMachine ≋ predicate)
        : machine ≋ predicate := fun inputs => (leftProof inputs).trans (rightProof inputs)

-- ══════════════════════════════════════════════════════════════════════════════
--  COMBINATORS  (the C++ identity / arr / compose / lmap / rmap / accumulate / filter)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Identity: pass each input straight through. -/
def idMachine : abstract_machine Input Input where
  State := Unit
  initial := ()
  step := fun _ input => ((), [input])

/-- Lift a pure function to a stateless machine. -/
def arr (transform : Input → Output) : abstract_machine Input Output where
  State := Unit
  initial := ()
  step := fun _ input => ((), [transform input])

/-- Sequential composition: feed `m`'s outputs through `n`. -/
def compose
    (machine : abstract_machine Input Intermediate)
    (rightMachine : abstract_machine Intermediate Output)
    : abstract_machine Input Output where
  State := machine.State × rightMachine.State
  initial := (machine.initial, rightMachine.initial)
  step := fun state input =>
    let leftResult := machine.step state.1 input
    let rightResult := feedThrough rightMachine state.2 leftResult.2
    ((leftResult.1, rightResult.1), rightResult.2)
  done := fun state => machine.done state.1 && rightMachine.done state.2

/-- Category composition (`>>>` in Haskell; `⋙` here since `>>>` is `HShiftRight`). -/
scoped infixr:80 " ⋙ " => compose

/-- Pre-process inputs (contravariant). -/
def lmap
    (transform : Input → Intermediate)
    (machine : abstract_machine Intermediate Output)
    : abstract_machine Input Output where
  State := machine.State
  initial := machine.initial
  step := fun state input => machine.step state (transform input)
  done := machine.done

/-- Post-process outputs (covariant). -/
def rmap
    (transform : Output → Result)
    (machine : abstract_machine Input Output)
    : abstract_machine Input Result where
  State := machine.State
  initial := machine.initial
  step :=
    fun state input =>
      let stepResult := machine.step state input;
      (stepResult.1, stepResult.2.map transform)
  done := machine.done

/-- Stateful fold: emit the running accumulator after each input. -/
def accumulate
    {State : Type}
    (transform : State → Input → State)
    (init : State)
    : abstract_machine Input State where
  State := State
  initial := init
  step :=
    fun state input =>
      let nextState := transform state input;
      (nextState, [nextState])

/-- Keep only outputs satisfying a predicate. -/
def filter
    (predicate : Output → Bool)
    (machine : abstract_machine Input Output)
    : abstract_machine Input Output where
  State := machine.State
  initial := machine.initial
  step :=
    fun state input =>
      let stepResult := machine.step state input;
      (stepResult.1, stepResult.2.filter predicate)
  done := machine.done

-- ══════════════════════════════════════════════════════════════════════════════
--  REDUCTION LEMMAS  — reduce `feedThrough`/projections WITHOUT unfolding machine
--  heads, so induction hypotheses (stated over folded machines) still match.
-- ══════════════════════════════════════════════════════════════════════════════

@[simp]
theorem feedThrough_nil
        (rightMachine : abstract_machine Input Output)
        (state : rightMachine.State)
        : feedThrough rightMachine state [] = (state, []) :=
  rfl

@[simp]
theorem feedThrough_cons
        (rightMachine : abstract_machine Input Output)
        (state : rightMachine.State)
        (input : Input)
        (inputs : List Input)
        : feedThrough rightMachine state (input :: inputs)
            = (
              (feedThrough rightMachine (rightMachine.step state input).1 inputs).1,
              (rightMachine.step state input).2
                  ++ (feedThrough rightMachine (rightMachine.step state input).1 inputs).2
            ) :=
  rfl

@[simp]
theorem idMachine_step
        (state : Unit)
        (input : Input)
        : (idMachine : abstract_machine Input Input).step state input = ((), [input]) :=
  rfl

@[simp]
theorem arr_step
        (transform : Input → Output)
        (state : Unit)
        (input : Input)
        : (arr transform).step state input = ((), [transform input]) :=
  rfl

@[simp]
theorem compose_initial
        (machine : abstract_machine Input Intermediate)
        (rightMachine : abstract_machine Intermediate Output)
        : (machine ⋙ rightMachine).initial = (machine.initial, rightMachine.initial) :=
  rfl

@[simp]
theorem compose_step
        (machine : abstract_machine Input Intermediate)
        (rightMachine : abstract_machine Intermediate Output)
        (state : machine.State × rightMachine.State)
        (input : Input)
        : (machine ⋙ rightMachine).step state input
            = (
              (
                (machine.step state.1 input).1,
                (feedThrough rightMachine state.2 (machine.step state.1 input).2).1
              ),
              (feedThrough rightMachine state.2 (machine.step state.1 input).2).2
            ) :=
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
--  THE KEY LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- `feedThrough` distributes over `++`: drive `a`, then drive `b` from the resulting
    state, concatenating outputs. (The C++ names this as what associativity rests on.) -/
theorem feedThrough_append
        (rightMachine : abstract_machine Input Output)
        (state : rightMachine.State)
        (value otherValue : List Input)
        : feedThrough rightMachine state (value ++ otherValue)
            = (
              (feedThrough rightMachine (feedThrough rightMachine state value).1 otherValue).1,
              (feedThrough rightMachine state value).2
                  ++ (feedThrough rightMachine (feedThrough rightMachine state value).1 otherValue).2
            ) := by
  induction value generalizing state with
  | nil => simp
  | cons input remainingInputs inductionHypothesis => simp [inductionHypothesis, List.append_assoc]

/-- Outputs of `arr f` = `map f`. -/
theorem outputs_arr
        (transform : Input → Output)
        (inputs : List Input)
        : outputs (arr transform) inputs = inputs.map transform := by
  simp only [outputs, run]
  generalize (arr transform).initial = state
  induction inputs generalizing state with
  | nil => rfl
  | cons input remainingInputs inductionHypothesis => simp [inductionHypothesis]

/-- Outputs of `idMachine` = the inputs unchanged. -/
theorem outputs_id
        (inputs : List Input)
        : outputs (idMachine : abstract_machine Input Input) inputs = inputs := by
  simp only [outputs, run]
  generalize (idMachine : abstract_machine Input Input).initial = state
  induction inputs generalizing state with
  | nil => rfl
  | cons input remainingInputs inductionHypothesis => simp [inductionHypothesis]

/-- Generalized over states: a composite's output is `n` driven over `m`'s output. -/
private
theorem feedThrough_compose_snd
        (machine : abstract_machine Input Intermediate)
        (rightMachine : abstract_machine Intermediate Output)
        (leftState : machine.State)
        (rightState : rightMachine.State)
        (inputs : List Input)
        : (feedThrough (machine ⋙ rightMachine) (leftState, rightState) inputs).2
            = (feedThrough rightMachine rightState (feedThrough machine leftState inputs).2).2 := by
  induction inputs generalizing leftState rightState with
  | nil => rfl
  | cons input remainingInputs inductionHypothesis => simp [feedThrough_append, inductionHypothesis]

/-- THE HOMOMORPHISM: composing machines composes their stream functions.
    Every Category/Arrow law below is a corollary. -/
theorem outputs_compose
        (machine : abstract_machine Input Intermediate)
        (rightMachine : abstract_machine Intermediate Output)
        (inputs : List Input)
        : outputs (machine ⋙ rightMachine) inputs = outputs rightMachine (outputs machine inputs) := by
  simp only [outputs, run, compose_initial]

  -- Reduce composition to the feed-through invariant.
  exact feedThrough_compose_snd machine rightMachine machine.initial rightMachine.initial inputs

-- ══════════════════════════════════════════════════════════════════════════════
--  THE LAWS  — proven once; every composed machine inherits them
-- ══════════════════════════════════════════════════════════════════════════════

/-- Category — left identity. -/
theorem id_compose (machine : abstract_machine Input Output) : idMachine ⋙ machine ≋ machine := by
  intro inputs; rw [outputs_compose, outputs_id]

/-- Category — right identity. -/
theorem compose_id (machine : abstract_machine Input Output) : machine ⋙ idMachine ≋ machine := by
  intro inputs; rw [outputs_compose, outputs_id]

/-- Category — associativity. -/
theorem compose_assoc
        (machine : abstract_machine Input Intermediate)
        (rightMachine : abstract_machine Intermediate Result)
        (predicate : abstract_machine Result Output)
        : (machine ⋙ rightMachine) ⋙ predicate ≋ machine ⋙ (rightMachine ⋙ predicate) := by
  intro inputs; simp only [outputs_compose]

/-- Arrow — `arr id` is the identity machine. -/
theorem arr_id : arr (fun input : Input => input) ≋ (idMachine : abstract_machine Input Input) := by
  intro inputs; simp [outputs_arr, outputs_id]

/-- Arrow — `arr` is a functor: `arr (g ∘ f) = arr f ⋙ arr g`. -/
theorem arr_compose
        (transform : Input → Intermediate)
        (nextTransform : Intermediate → Output)
        : arr (nextTransform ∘ transform) ≋ arr transform ⋙ arr nextTransform := by
  intro inputs; simp [outputs_compose, outputs_arr, List.map_map]

-- ══════════════════════════════════════════════════════════════════════════════
--  IT RUNS  — a 3-stage pipeline assembled from combinators, evaluated by computation
-- ══════════════════════════════════════════════════════════════════════════════

/-- parse · accumulate-sum · format, built entirely by composition. -/
private
def demo : abstract_machine String Nat := arr String.length ⋙ accumulate (· + ·) 0 ⋙ arr (· * 2)

example : outputs demo ["a", "bb", "ccc"] = [2, 6, 12] := by native_decide

/-- The law is real on a concrete instance. -/
example : outputs (idMachine ⋙ demo) ["x", "yy"] = outputs demo ["x", "yy"] := id_compose demo _

end abstract_machine
end Continuity.Machine
