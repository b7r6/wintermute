/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // MACHINE // SIGIL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Ladder rung 2 — SIGIL, the LLM token-stream decoder, ported from cornell's
    hand-rolled machine. New axis: SAFETY / reset-on-ambiguity.

    SIGIL tracks a semantic mode (text / think / toolCall / codeBlock). The
    discipline: malformed input is NEVER best-effort recovered — it RESETS the
    decoder to its unique ground state. For agentic systems, trusting a corrupted
    reasoning stream is worse than starting fresh.

    cornell proves the reset facts about the pure `resetDecodeState` function. This
    rung lifts them to the RUNNING machine and adds the one that matters:

        post_reset_independent — after a reset, all future behaviour is identical
        regardless of the (possibly corrupted) pre-reset state.

    i.e. corrupted upstream context provably cannot leak past a reset. The byte
    layer plugs in as a `Box`-shaped decoder via `lmap` (`sigilBytes`).

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.machine.abstract

namespace Continuity.Machine.Sigil

open Continuity.Machine
open Continuity.Machine.abstract_machine

/-- Semantic parse modes (cornell `ParseMode`). -/
inductive ParseMode where
  | text
  | think
  | toolCall
  | codeBlock
  deriving DecidableEq, Repr, Inhabited

/-- Why a reset fired (cornell `AmbiguityReason`, the structural subset). -/
inductive AmbiguityReason where
  | unmatchedModeEnd (mode : ParseMode)
  | nestedModeStart (attempted current : ParseMode)
  | reservedOpcode (code : UInt8)
  deriving DecidableEq, Repr

/-- Decoder input: a decoded wire symbol. The raw byte→symbol step is a separate
    codec (`decodeByte` below), plugged in by `lmap`. -/
inductive Sym where
  | tok (tokenId : Nat)
  | modeStart (mode : ParseMode)
  | modeEnd (mode : ParseMode)
  | reserved (code : UInt8)
  | streamEnd
  deriving DecidableEq, Repr

/-- Decoder output events. -/
inductive sigil_event where
  | token (tokenId : Nat)
  | entered (mode : ParseMode)
  | exited (mode : ParseMode)
  | wasReset (reason : AmbiguityReason)
  | streamEnded
  deriving DecidableEq, Repr

/-- Decode state (cornell `DecodeState`, minus the byte leftover that lives in the
    codec layer): the current mode plus accumulated tokens. -/
structure DecodeState where
  mode   : ParseMode := .text
  buffer : List Nat := []
  deriving DecidableEq, Repr

/-- The unique ground state — the only start, and the target of every reset. -/
def initDecodeState : DecodeState := {}

/-- One decode step. Valid mode transitions advance; everything malformed RESETS to
    ground and emits a `wasReset`. (Total transition; the reset is the benign default
    for the ambiguous cases.) -/
def sigilStep (state : DecodeState) : Sym → DecodeState × List sigil_event
  | .tok channelId => ({ state with buffer := channelId :: state.buffer }, [.token channelId])
  | .modeStart machine =>
    match state.mode with
    | .text => ({ state with mode := machine }, [.entered machine])
    | cur   => (initDecodeState, [.wasReset (.nestedModeStart machine cur)])
  | .modeEnd machine =>
    if state.mode = machine then
      ({ state with mode := .text }, [.exited machine])
    else
      (initDecodeState, [.wasReset (.unmatchedModeEnd machine)])
  | .reserved opcode => (initDecodeState, [.wasReset (.reservedOpcode opcode)])
  | .streamEnd => (state, [.streamEnded])

/-- SIGIL as a first-class machine in the arrow category. -/
def sigil : abstract_machine Sym sigil_event where
  State := DecodeState
  initial := initDecodeState
  step := sigilStep

-- ══════════════════════════════════════════════════════════════════════════════
--  RESET SAFETY  — cornell's facts, on the running machine
-- ══════════════════════════════════════════════════════════════════════════════

/-- A reserved opcode resets to ground in ANY state (cornell `reset_is_ground`). -/
theorem reset_is_ground
        (state : DecodeState)
        (chunk : UInt8)
        : (sigilStep state (.reserved chunk)).1 = initDecodeState :=
  rfl

/-- Reset erases the mode (cornell `reset_erases_mode`). -/
theorem reset_erases_mode
        (state : DecodeState)
        (chunk : UInt8)
        : (sigilStep state (.reserved chunk)).1.mode = .text :=
  rfl

/-- Reset erases the buffer (cornell `reset_erases_buffer`). -/
theorem reset_erases_buffer
        (state : DecodeState)
        (chunk : UInt8)
        : (sigilStep state (.reserved chunk)).1.buffer = [] :=
  rfl

/-- NO LEAKAGE (per-step): the post-reset state is independent of the pre-reset
    state — two different (possibly one corrupted) states reset identically. -/
theorem no_leakage
        (leftState rightState : DecodeState)
        (chunk : UInt8)
        : (sigilStep leftState (.reserved chunk)).1 = (sigilStep rightState (.reserved chunk)).1 :=
  rfl

/-- Reset is idempotent (cornell `reset_idempotent`). -/
theorem reset_idempotent
        (state : DecodeState)
        (chunk chunk' : UInt8)
        : (sigilStep (sigilStep state (.reserved chunk)).1 (.reserved chunk')).1
            = (sigilStep state (.reserved chunk)).1 :=
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
--  THE RUNG'S CONTRIBUTION  — no-leakage on the RUNNING machine (trace level)
-- ══════════════════════════════════════════════════════════════════════════════

/-- POST-RESET INDEPENDENCE: after a reset, the entire future output stream is
    identical regardless of the pre-reset state. Corrupted upstream context cannot
    influence anything decoded after a reset — the security guarantee SIGIL exists
    for, now a theorem about the machine, not just the reset function. -/
theorem post_reset_independent
        (leftState rightState : DecodeState)
        (chunk : UInt8)
        (rest : List Sym)
        : feedThrough sigil (sigilStep leftState (.reserved chunk)).1 rest
            = feedThrough sigil (sigilStep rightState (.reserved chunk)).1 rest := by
  simp only [reset_is_ground]

/-- And decoding after a reset is exactly a FRESH decode (cornell `post_reset_canonical`). -/
theorem decode_after_reset_is_fresh
        (state : DecodeState)
        (chunk : UInt8)
        (rest : List Sym)
        : feedThrough sigil (sigilStep state (.reserved chunk)).1 rest = run sigil rest := by
  rw [reset_is_ground]; rfl

-- ══════════════════════════════════════════════════════════════════════════════
--  IT COMPUTES  — valid block, and recovery from ambiguity
-- ══════════════════════════════════════════════════════════════════════════════

/-- A well-formed think block. -/
example :
    outputs sigil [.tok 65, .modeStart .think, .tok 66, .modeEnd .think, .tok 67]
        = [.token 65, .entered .think, .token 66, .exited .think, .token 67] := by native_decide

/-- Ambiguity mid-block resets to ground, then decoding resumes cleanly from text. -/
example :
    outputs sigil [.modeStart .think, .reserved 0xC8, .tok 9]
        = [.entered .think, .wasReset (.reservedOpcode 0xC8), .token 9] := by native_decide

/-- Unmatched mode-end (think-end while in text) is ambiguous → reset. -/
example : outputs sigil [.modeEnd .think] = [.wasReset (.unmatchedModeEnd .think)] := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
--  THE BYTE LAYER  — a codec decoder plugged in by `lmap` (Box-into-machine)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Simplified SIGIL byte decoder (the real one does varints; modes are faithful):
    `0x00–0xBF` token, `0xC1–0xC6` mode start/end, `0xCF` stream-end, else reserved. -/
def decodeByte (byte : UInt8) : Sym :=
  if byte ≤ 0xBF then
    .tok byte.toNat
  else if byte == 0xC1 then
    .modeStart .toolCall
  else if byte == 0xC2 then
    .modeEnd .toolCall
  else if byte == 0xC3 then
    .modeStart .think
  else if byte == 0xC4 then
    .modeEnd .think
  else if byte == 0xC5 then
    .modeStart .codeBlock
  else if byte == 0xC6 then
    .modeEnd .codeBlock
  else if byte == 0xCF then .streamEnd else .reserved byte

/-- The byte-driven decoder: codec ⋙ semantics, via `lmap`. -/
def sigilBytes : abstract_machine UInt8 sigil_event := lmap decodeByte sigil

/-- Raw bytes through the full stack: 'A', think-start, 'B', think-end. -/
example :
    outputs sigilBytes [65, 0xC3, 66, 0xC4]
        = [.token 65, .entered .think, .token 66, .exited .think] := by native_decide

/-- First-class in the arrow: identity composition is invisible. -/
example (events : List Sym) : outputs (idMachine ⋙ sigil) events = outputs sigil events :=
  id_compose sigil events

end Continuity.Machine.Sigil
