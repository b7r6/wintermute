/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // MACHINE // STACK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Ladder rung 5 — REAL composition. `tls ⋙ http`: a protocol stack assembled
    from two machines with the arrow's `⋙`, the way evring layers TLS under HTTP.

    TLS records in → (decrypt, gated by handshake) → plaintext lines → (parse) →
    HTTP events out. Neither layer knows about the other; the stack is one
    `AbstractMachine`, built by composition, not hand-rolled.

    The point of the rung is what composition BUYS: because
    `outputs (tls ⋙ http) = outputs http ∘ outputs tls` is free (`outputs_compose`),
    a CROSS-LAYER property reduces to single-layer facts. We prove the one that
    matters for a TLS stack —

        no_http_during_handshake : no HTTP events are emitted before the TLS
        handshake completes —

    from a one-line TLS fact and the composition law. That's modular protocol
    verification: prove each layer once, get the stack's guarantees by `⋙`.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.machine.abstract

namespace Continuity.Machine.Stack

open Continuity.Machine
open Continuity.Machine.abstract_machine

-- ══════════════════════════════════════════════════════════════════════════════
-- TLS LAYER  — records in, plaintext lines out (gated by the handshake)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A TLS record arriving on the wire. -/
inductive tls_record where
  | handshake               -- a handshake message (advances the handshake)
  | handshakeDone           -- Finished received → connection established
  | appData (line : String) -- application data (decrypted plaintext line)
  | closeNotify
  deriving DecidableEq, Repr

inductive TlsPhase where
  | handshaking
  | established
  | closed
  deriving DecidableEq, Repr

structure tls_state where
  phase : TlsPhase := .handshaking
  deriving DecidableEq, Repr

/-- TLS decryption: plaintext flows ONLY once established; handshake records and
    pre-handshake app-data emit nothing downstream. -/
def tlsStep (state : tls_state) (record : tls_record) : tls_state × List String :=
  match record, state.phase with
  | .handshakeDone, _ => ({ state with phase := .established }, [])
  | .appData line, .established => (state, [line])
  | .closeNotify, _ => ({ state with phase := .closed }, [])
  | _, _ => (state, [])

/-- The TLS layer as a machine: `TlsRecord → plaintext line`. -/
def tls : abstract_machine tls_record String where
  State := tls_state
  initial := {}
  step := tlsStep

-- ══════════════════════════════════════════════════════════════════════════════
--  HTTP LAYER  — plaintext lines in, parsed HTTP/1.1 events out
-- ══════════════════════════════════════════════════════════════════════════════

inductive http_event where
  | requestLine (method path : String)
  | header (name value : String)
  | complete
  deriving DecidableEq, Repr

inductive HttpPhase where
  | start
  | headers
  | done
  deriving DecidableEq, Repr

structure http_state where
  phase : HttpPhase := .start
  deriving DecidableEq, Repr

private
def word (count : Nat) (line : String) : String := ((line.splitOn " ").drop count).head?.getD ""

private
def hdrName (line : String) : String := (line.splitOn ": ").head?.getD ""

private
def hdrValue (line : String) : String := ((line.splitOn ": ").drop 1).head?.getD ""

/-- Line-based HTTP/1.1 request parsing: request line, then headers until the blank
    line, then `complete`. `done` is absorbing. -/
def httpStep (state : http_state) (line : String) : http_state × List http_event :=
  match state.phase with
  | .start => ({ state with phase := .headers }, [.requestLine (word 0 line) (word 1 line)])
  | .headers =>
    if line == "" then
      ({ state with phase := .done }, [.complete])
    else
      (state, [.header (hdrName line) (hdrValue line)])
  | .done => (state, [])

/-- The HTTP layer as a machine: `plaintext line → HttpEvent`. -/
def http : abstract_machine String http_event where
  State := http_state
  initial := {}
  step := httpStep

-- ══════════════════════════════════════════════════════════════════════════════
-- THE STACK  — composed with `⋙`, never hand-rolled
-- ══════════════════════════════════════════════════════════════════════════════

/-- The full transport+application stack: TLS records in, HTTP events out. -/
def stack : abstract_machine tls_record http_event := tls ⋙ http

/-- LAYERING (free, from `outputs_compose`): the stack's HTTP output is exactly HTTP
    applied to TLS's plaintext output. Cross-layer reasoning reduces to per-layer. -/
theorem stack_factors
        (records : List tls_record)
        : outputs stack records = outputs http (outputs tls records) :=
  outputs_compose tls http records

-- ══════════════════════════════════════════════════════════════════════════════
--  THE CROSS-LAYER THEOREM  — proven by composition, not by hand
-- ══════════════════════════════════════════════════════════════════════════════

/-- TLS emits no plaintext for handshake records (one-line single-layer fact). -/
private
theorem tls_step_handshake (state : tls_state) : tls.step state .handshake = (state, []) := rfl

/-- TLS stays silent across any run of handshake messages. -/
theorem tls_silent_handshakes
        (count : Nat)
        : outputs tls (List.replicate count .handshake) = [] := by
  suffices handshake_silence : ∀ state, feedThrough tls state (List.replicate count .handshake) = (state, []) by
    simp [outputs, run, handshake_silence]
  intro state
  induction count generalizing state with
  | zero => rfl
  | succ handshake_count induction_hypothesis =>
    simp [List.replicate_succ, feedThrough_cons, tls_step_handshake, induction_hypothesis]

/-- THE PAYOFF: no HTTP events are emitted before the TLS handshake completes — no
    matter how many handshake records arrive. Proven from the one-line TLS fact via
    the composition law; HTTP parsing provably cannot begin over unestablished
    transport. -/
theorem no_http_during_handshake
        (count : Nat)
        : outputs stack (List.replicate count .handshake) = [] := by
  rw [stack_factors, tls_silent_handshakes]; rfl

-- ══════════════════════════════════════════════════════════════════════════════
--  IT RUNS  — the whole stack, end to end
-- ══════════════════════════════════════════════════════════════════════════════

/-- Handshake → established → request → header → blank line: a real exchange decoded
    through both layers by one composed machine. -/
example :
    outputs
      stack
      [.handshake, .handshakeDone, .appData "GET / HTTP/1.1", .appData "Host: x", .appData ""]
        = [.requestLine "GET" "/", .header "Host" "x", .complete] := by native_decide

/-- Application data arriving BEFORE the handshake completes is dropped by TLS, so
    HTTP sees nothing — the cross-layer guarantee, concretely. -/
example : outputs stack [.handshake, .appData "GET / HTTP/1.1"] = [] := by native_decide

end Continuity.Machine.Stack
