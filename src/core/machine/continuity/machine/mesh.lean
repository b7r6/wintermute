/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // CONTINUITY // MACHINE // MESH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The distributed interpretation of the machine arrow.

    A composition `m ⋙ n : AbstractMachine Input Output` runs on one core. To SHARD it —
    `m` on core A, `n` on core B — the intermediate values (the `IntermediateType` on the
    `⋙`) must cross the core boundary. The mesh carries them as bytes: on core
    A a `Box IntermediateType` SERIALIZES each `IntermediateType`, a thin MSG_RING transport moves the bytes
    (a pointer, in the shared address space), and on core B the same `Box IntermediateType`
    PARSES them back. The composition edge becomes a wire.

    The question is whether the wire is FAITHFUL: does the sharded machine
    compute the same thing as the local one? For a lossless codec — any `Box`,
    whose `roundtrip` law says `parse (serialize a) = a` — the answer is yes,
    unconditionally. That is `mesh_faithful` below:

        m ⋙[box] n   ≋   m ⋙ n

    for ANY machines `m`, `n` and ANY `Box` on the edge type. This is the
    generality claim, proven: the mesh is a transparent distributed interpreter
    of the whole arrow category, not a bespoke protocol. It composes the codec
    `roundtrip` with the machine `outputs_compose` homomorphism — nothing more.

    The runtime (aleph) realizes `codecEdge` as: serialize on the source core,
    MSG_RING the bytes to the target core's ring, parse there. This file proves
    that realization changes nothing observable.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/
import continuity.machine.abstract
import continuity.codec.core.box

namespace Continuity.Machine.Mesh

open Continuity.Machine
open Continuity.Machine.abstract_machine
open Continuity.Codec.Core (Box ParseResult)

variable {Input Output Intermediate Result : Type}

/-- The value a codec recovers from its own serialization. By `roundtrip` this
    is the identity, but stated as a total function so it can drive a machine. -/
def thru (box : Box Input) (value : Input) : Input :=
  match box.parse (box.serialize value) with
  | .ok action _ => action
  | .fail        => value

/-- A `Box` is lossless: serialize-then-parse is the identity on values. -/
@[simp]
theorem thru_eq (box : Box Input) (value : Input) : thru box value = value := by
  simp [thru, box.roundtrip]

/-- The composition edge as value machine: each value that crosses is serialized by
    the box and parsed back — exactly what the mesh transport does on the wire.
    (`arr` is the stateless lift; the codec round-trip is the "wire".) -/
def codecEdge (box : Box Input) : abstract_machine Input Input := arr (thru box)

/-- The wire is observationally empty: it emits each value it receives,
    unchanged (the codec is lossless). -/
@[simp]
theorem codecEdge_outputs
        (box : Box Input)
        (inputs : List Input)
        : outputs (codecEdge box) inputs = inputs := by
  have roundtripIdentity : thru box = id := funext (thru_eq box)

  -- Rewrite the wire round-trip to the identity.
  simp [codecEdge, outputs_arr, roundtripIdentity]

/-- The codec edge is behaviourally the identity machine. -/
theorem codecEdge_id (box : Box Input) : codecEdge box ≋ idMachine := by
  intro inputs
  simp [codecEdge_outputs, outputs_id]

/-- Distributed composition: `m` and `n` with the intermediate `Output` values
    crossing a codec-serialized channel. `m` may run on one core and `n` on
    another; `box` is the wire format for the edge. -/
def dcompose
    (box : Box Output)
    (leftMachine : abstract_machine Input Output)
    (rightMachine : abstract_machine Output Intermediate)
    : abstract_machine Input Intermediate :=
  leftMachine ⋙ codecEdge box ⋙ rightMachine

@[inherit_doc] scoped notation:80 leftMachine " ⋙[" box "] " rightMachine => dcompose box leftMachine rightMachine

-- ══════════════════════════════════════════════════════════════════════════════
--  THE GENERALITY THEOREM — sharding a composition changes nothing observable
-- ══════════════════════════════════════════════════════════════════════════════

/-- **The mesh is faithful.** For any machines `leftMachine`, `rightMachine` and any lossless codec
    `box` on the edge type, running `leftMachine` and `rightMachine` on separate cores with the
    intermediate values serialized across the wire is behaviourally identical
    to running `leftMachine ⋙ rightMachine` locally. The distributed interpreter is transparent. -/
theorem mesh_faithful
        (box : Box Output)
        (leftMachine : abstract_machine Input Output)
        (rightMachine : abstract_machine Output Intermediate)
        : dcompose box leftMachine rightMachine ≋ (leftMachine ⋙ rightMachine) := by
  intro inputs

  -- Erase the lossless codec edge from the composition.
  simp only [dcompose, outputs_compose, codecEdge_outputs]

/-- Corollary: the sharded machine delivers exactly the local outputs, for
    every input stream. -/
theorem mesh_outputs
        (box : Box Output)
        (leftMachine : abstract_machine Input Output)
        (rightMachine : abstract_machine Output Intermediate)
        (inputs : List Input)
        : outputs (dcompose box leftMachine rightMachine) inputs
            = outputs (leftMachine ⋙ rightMachine) inputs :=
  mesh_faithful box leftMachine rightMachine inputs

-- ══════════════════════════════════════════════════════════════════════════════
--  IT GENERALIZES — associativity across three cores, still faithful
-- ══════════════════════════════════════════════════════════════════════════════

/-- A three-stage pipeline sharded across three cores (two wires) is faithful to
    the local `leftMachine ⋙ p ⋙ q`. Generality isn't limited to a single edge: every `⋙`
    in a pipeline may become a mesh wire, and the whole stays transparent. -/
theorem mesh_faithful₃
        (leftBox : Box Output)
        (rightBox : Box Intermediate)
        (leftMachine : abstract_machine Input Output)
        (pipeline : abstract_machine Output Intermediate)
        (rightPipeline : abstract_machine Intermediate Result)
        : dcompose leftBox leftMachine (dcompose rightBox pipeline rightPipeline)
            ≋ (leftMachine ⋙ pipeline ⋙ rightPipeline) := by
  intro inputs

  -- Erase both lossless codec edges from the composition.
  simp only [dcompose, outputs_compose, codecEdge_outputs]

/-- The placement is irrelevant to the result: two different codecs on the same
    edge give the same behaviour (both are lossless), so the choice of wire
    format is a performance decision, never a correctness one. -/
theorem mesh_codec_irrelevant
        (intermediateValue intermediateValue' : Box Output)
        (leftMachine : abstract_machine Input Output)
        (rightMachine : abstract_machine Output Intermediate)
        : dcompose intermediateValue leftMachine rightMachine
            ≋ dcompose intermediateValue' leftMachine rightMachine := fun inputs => by
  simp only [dcompose, outputs_compose, codecEdge_outputs]

-- ══════════════════════════════════════════════════════════════════════════════
--  THE PIPELINE — compose an arbitrary chain of machines over cores
-- ══════════════════════════════════════════════════════════════════════════════

/-- A core identifier (placement metadata; correctness never depends on it). -/
abbrev CoreId := Nat

/-- A placed, codec-wired pipeline of machines: a heterogeneous chain where each
    stage pins a machine to a core and serializes its output across a codec edge
    to the next stage. The type indices track the pipeline's overall input `Input`
    and output `Output`; the intermediate types are existentially threaded through the
    chain. This is the declarative description of a distributed computation — the
    thing the mesh runtime executes, one stage per core. -/
inductive Pipeline : Type → Type → Type 1 where
  /-- The final stage: a machine on a core, no outgoing wire. -/
  | last {Input Output : Type} (core : CoreId) (leftMachine : abstract_machine Input Output) :
            Pipeline Input Output
  /-- A stage: machine `leftMachine : Input → Intermediate` on `core`, its output serialized by `edge`
      and handed to the rest of the pipeline. -/
  | stage {Input Intermediate Output : Type} (core : CoreId)
        (leftMachine : abstract_machine Input Intermediate) (edge : Box Intermediate)
        (rest : Pipeline Intermediate Output) : Pipeline Input Output

namespace Pipeline

variable {Input Output : Type}

/-- The LOCAL semantics: fold the stage machines with `⋙`, forgetting placement
    and edges. This is what the pipeline *means* — the single-core reference. -/
def collapse : {Input Output : Type} → Pipeline Input Output → abstract_machine Input Output
  | _, _, .last _ machine         => machine
  | _, _, .stage _ machine _ rest => machine ⋙ collapse rest

/-- The DISTRIBUTED realization: every stage boundary becomes a codec wire —
    exactly what the mesh runs, one machine per core with `codecEdge` between. -/
def route : {Input Output : Type} → Pipeline Input Output → abstract_machine Input Output
  | _, _, .last _ machine            => machine
  | _, _, .stage _ machine edge rest => machine ⋙ codecEdge edge ⋙ route rest

/-- The number of stages (= cores the pipeline occupies). -/
def length : {Input Output : Type} → Pipeline Input Output → Nat
  | _, _, .last _ _         => 1
  | _, _, .stage _ _ _ rest => 1 + length rest

/-- The list of cores the pipeline is placed on, in stage order. -/
def cores : {Input Output : Type} → Pipeline Input Output → List CoreId
  | _, _, .last core _         => [core]
  | _, _, .stage core _ _ rest => core :: cores rest

-- ══════════════════════════════════════════════════════════════════════════════
--  THE PIPELINE GENERALITY THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- **A whole pipeline is faithful.** Routing a placed chain of machines across
    cores — serializing EVERY edge with its codec — is behaviourally identical to
    collapsing it to a single-core composition. For any chain of any length, any
    placement, any codecs. This is `mesh_faithful` lifted to the whole
    distributed program: the mesh executes the pipeline and computes exactly what
    the local fold would. -/
theorem faithful
        : {Input Output : Type} → (pipeline : Pipeline Input Output) → route pipeline ≋ collapse pipeline
  | _, _, .last _ machine => behEquiv_refl machine
  | _, _, .stage _ machine _ rest =>
    fun inputs => by
      simp only [route, collapse, outputs_compose, codecEdge_outputs]

      exact faithful rest (outputs machine inputs)

/-- Corollary: the sharded pipeline delivers exactly the local outputs, for every
    input stream — the operational guarantee the runtime inherits for free. -/
theorem route_outputs
        (pipeline : Pipeline Input Output)
        (inputs : List Input)
        : outputs (route pipeline) inputs = outputs (collapse pipeline) inputs :=
  faithful pipeline inputs

end Pipeline

end Continuity.Machine.Mesh
