/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // WINTERMUTE // MAIN
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    wintermute daemon                 watch the state file, reconcile forever
    wintermute get                    print the control state
    wintermute set KEY VALUE …        stamp a fresh generation, mutate fields
                                      (hero/axis/register/ramp/polarity/level)
    wintermute preset NAME            jump to a named corner of the preset space
                                      (villa-straylight / razorgirl / tessier /
                                       bioptic / hosaka-blackwell / hosaka-grace)
    wintermute apply                  one-shot: broadcast + persist right now

    `set`/`preset` only touch the state file; a running daemon notices the
    mtime and does the rest. `apply` is the daemon-less escape hatch.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute

open Wintermute Wintermute.Shell

-- The preset list is DERIVED from `corners`, never hand-typed — the usage
-- can't drift out of sync with the actual corners again (hosaka went missing
-- from the help this way once).
def presetNames : String := String.intercalate " " (corners.map (·.1))

def usage : String :=
  s!"wintermute — hot-reload theme reconciler\n\
   \n\
   usage:\n\
     wintermute daemon              watch + reconcile\n\
     wintermute get                 print control state\n\
     wintermute set KEY VALUE …     KEY ∈ hero axis register ramp polarity level\n\
     wintermute preset NAME         NAME ∈ {presetNames}\n\
     wintermute apply               one-shot broadcast + persist\n\
     wintermute vectors             emit the conformance palettes (parity gate)\n\
     wintermute status              per-surface theme conformance table\n"

def cmdGet : IO UInt32 := do
  IO.print (ControlState.render ((← readControl).getD {}))
  pure 0

/-- Write a desired theme, stamping a FRESH generation from the wall clock
    (`nowGen`) — never `read()+1`. With no old generation read, concurrent
    writers cannot collide on the next value, so the daemon's fence never drops
    a real update (E1). The current theme is read only to seed partial `set`s. -/
def commit (t : ThemeVector) : IO UInt32 := do
  let cs' : ControlState := { generation := ← nowGen, theme := t }
  writeControl cs'
  IO.print (ControlState.render cs')
  pure 0

def cmdSet (args : List String) : IO UInt32 := do
  let base := (← readControl).getD {}
  match applySets base.theme args with
  | some t => commit t
  | none =>
    IO.eprintln s!"wintermute: bad set arguments: {String.intercalate " " args}"
    IO.eprintln usage
    pure 1

def cmdPreset (name : String) : IO UInt32 := do
  match corner? name with
  | some t => commit t
  | none =>
    IO.eprintln s!"wintermute: unknown preset {name} (want: {String.intercalate " " (corners.map (·.1))})"
    pure 1

def cmdApply : IO UInt32 := do
  match ← readControl with
  | some cs =>
    broadcastTheme cs.theme
    persistTheme cs.generation cs.theme
    runAudit cs.generation cs.theme
    pure 0
  | none =>
    IO.eprintln "wintermute: no valid control state to apply"
    pure 1

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] | ["daemon"] => daemon; pure 0
  | ["get"] => cmdGet
  | "set" :: rest => cmdSet rest
  | ["preset", name] => cmdPreset name
  | ["apply"] => cmdApply
  | ["vectors"] => IO.print Wintermute.Vectors.vectorsJson; pure 0
  | ["status"] => statusReport; pure 0
  | ["--help"] | ["-h"] | ["help"] => IO.print usage; pure 0
  | _ => IO.eprintln usage; pure 1
