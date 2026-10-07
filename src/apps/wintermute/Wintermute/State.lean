/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // WINTERMUTE // STATE // KV
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The state file IS the control-plane API. A human-editable KV file in
    XDG_STATE — `echo`-able, `git`-able, out of the Nix store:

        generation 42
        hero 211
        axis 201
        polarity dark
        level carbon
        ramp 211
        register 250

    Parsing is junk-tolerant but TYPED: unknown keys are ignored, malformed
    values fall back to the field default, a level that contradicts the
    polarity falls back to that polarity's default level — BUT an input with
    no recognized key at all (garbage, a truncated blob, an empty file) parses
    to `none`, never to the default theme. A hostile state file can produce a
    wrong theme; it can never wedge the daemon, and it can never silently reset
    a live theme to default (the reader keeps the applied theme on `none`).
    Render ∘ parse round-trips (checked below by computation on every corner).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute.Theme

namespace Wintermute

/-- What the state file denotes: a generation fence + a desired theme. -/
structure ControlState where
  generation : Nat := 0
  theme : ThemeVector := {}
  deriving Repr, BEq, DecidableEq

namespace ControlState

def render (cs : ControlState) : String :=
  let t := cs.theme
  let (polarity, levelName, rampHue) :=
    match t.luminance with
    | .dark lv => ("dark", lv.name, 211)
    | .light lv ramp => ("light", lv.name, ramp)
  String.intercalate "\n"
    [ s!"generation {cs.generation}"
    , s!"hero {t.heroHue}"
    , s!"axis {t.axisHue}"
    , s!"family {t.family.name}"
    , s!"polarity {polarity}"
    , s!"level {levelName}"
    , s!"ramp {rampHue}"
    , s!"register {t.register}"
    ] ++ "\n"

/-- Raw fields as read, before luminance resolution. -/
private structure Raw where
  generation : Nat := 0
  hero : Nat := 211
  axis : Nat := 201
  family : String := "straylight"
  polarity : String := "dark"
  level : String := "carbon"
  ramp : Nat := 211
  register : Nat := 0

private def natOr (dflt : Nat) (s : String) : Nat :=
  (s.toNat?).getD dflt

/-- Fold one line into the accumulator, tracking whether ANY recognized key
    has been seen. Unknown keys and junk leave both the record and the flag
    untouched; a recognized key updates its field and raises the flag. -/
private def applyLine (acc : Raw × Bool) (line : String) : Raw × Bool :=
  let (r, seen) := acc
  match (line.splitOn " ").filter (· ≠ "") with
  | ["generation", v] => ({ r with generation := natOr r.generation v }, true)
  | ["hero", v] => ({ r with hero := natOr r.hero v }, true)
  | ["axis", v] => ({ r with axis := natOr r.axis v }, true)
  | ["family", v] => ({ r with family := v }, true)
  | ["polarity", v] => ({ r with polarity := v }, true)
  | ["level", v] => ({ r with level := v }, true)
  | ["ramp", v] => ({ r with ramp := natOr r.ramp v }, true)
  | ["register", v] => ({ r with register := natOr r.register v }, true)
  | _ => (r, seen)

/-- Parse — junk-tolerant within a control file, TYPED about whether the input
    is a control file at all. An input with NO recognized key parses to `none`
    (see the module docstring): that is the whole of E4 — the daemon reconciles
    a `some` and keeps its applied theme on a `none`, so corruption can never
    masquerade as "the user desires default carbon." -/
def parse (s : String) : Option ControlState :=
  let (r, seen) := (s.splitOn "\n").foldl applyLine ({}, false)
  if !seen then none else
  let luminance :=
    if r.polarity = "light" then
      .light ((WhiteLevel.ofName? r.level).getD .neoform) r.ramp
    else
      Luminance.dark ((BlackLevel.ofName? r.level).getD .carbon)
  some
    { generation := r.generation
    , theme :=
        { heroHue := r.hero
        , axisHue := r.axis
        , family := (PaletteFamily.ofName? r.family).getD .straylight
        , luminance
        , register := r.register
        }
    }

-- Round-trip on the four corners + the default, by computation: render lands
-- in the `some` branch and reconstructs the exact state.
example :
    (corners.map (fun c => parse (render { generation := 7, theme := c.2 })))
      = corners.map (fun c => some { generation := 7, theme := c.2 }) := by
  native_decide

example : parse (render {}) = some ({} : ControlState) := by native_decide

-- Garbage tolerance: unknown keys and junk lines cannot wedge the parse — a
-- single recognized key still yields `some`, carrying that field.
example :
    (parse "garbage\nhero 240\nwat wat wat\nregister 800\n\n").map (·.theme.heroHue)
      = some 240 := by
  native_decide

-- E4, by computation: an input with NO recognized key parses to `none` — the
-- reader will keep the applied theme rather than reconcile to default.
example : parse "" = none := by native_decide
example : parse "\x00\x01\x02 total garbage\nzzz\n" = none := by native_decide

end ControlState

end Wintermute
