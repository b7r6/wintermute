/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // WINTERMUTE // VECTORS // GATE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The conformance surface. The ono-sendai palette math has three
    implementations — the generator (Lean, in nixos-config), lib.nix (Nix,
    eval-time), and THIS one (the daemon's own port). `wintermute vectors`
    emits the same 66-palette grid in the same order as the generator's
    `vectors` command; nixos-config's `checks.ono-sendai-parity` diffs all
    three. One truth, three implementations, zero drift — by CI, not by
    promise.

    ORDER IS THE CONTRACT: darks hue-major then level; lights hue-major,
    then level, then ramp ∈ [211, 36]; then the hosaka block at its
    signature pair (hero 78 / axis 168): blackwell (ramp 165) across the
    black levels, grace (ramp 150) across the white levels.
    6 × 5 + 6 × 3 × 2 + 5 + 3 = 74.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute.Theme

namespace Wintermute.Vectors

open Wintermute

def hues : List (Nat × Nat) :=
  [(211, 201), (36, 26), (0, 350), (120, 110), (262, 252), (300, 290)]

def blackLevels : List BlackLevel := [.void, .deep, .night, .carbon, .github]
def whiteLevels : List WhiteLevel := [.tessier, .neoform, .ghost]
def ramps : List Nat := [211, 36]

private def vectorJson (slug : String) (hero axis ramp : Nat) (p : Palette) : String :=
  let slots := p.slots.map (fun (k, v) => s!"\"{k}\": \"{v}\"")
  "{" ++ String.intercalate ", "
    ([ s!"\"slug\": \"{slug}\""
     , s!"\"heroHue\": {hero}"
     , s!"\"axisHue\": {axis}"
     , s!"\"rampHue\": {ramp}"
     ] ++ slots) ++ "}"

def darkVectors : List String :=
  hues.flatMap fun (h, a) =>
    blackLevels.map fun lv =>
      vectorJson s!"ono-sendai-{lv.name}" h a 211 (makePalette .straylight lv h a)

def lightVectors : List String :=
  hues.flatMap fun (h, a) =>
    whiteLevels.flatMap fun lv =>
      ramps.map fun r =>
        vectorJson s!"maas-{lv.name}" h a r (makePaletteLight lv h a r)

/-- Hosaka pins the family-ramp path at its signature pair: silicon green
    hero 78, plasma teal axis 168; blackwell night ramp 165, grace paper 150. -/
def hosakaDarkVectors : List String :=
  blackLevels.map fun lv =>
    vectorJson s!"hosaka-blackwell-{lv.name}" 110 168 211 (makePalette .hosaka lv 110 168)

def hosakaLightVectors : List String :=
  whiteLevels.map fun lv =>
    vectorJson s!"hosaka-grace-{lv.name}" 110 168 211 (makePaletteLight lv 110 168 211)

def vectorsJson : String :=
  "[\n  " ++ String.intercalate ",\n  "
    (darkVectors ++ lightVectors ++ hosakaDarkVectors ++ hosakaLightVectors) ++ "\n]\n"

-- The grid is the full 74.
example :
    (darkVectors ++ lightVectors ++ hosakaDarkVectors ++ hosakaLightVectors).length = 74 := by
  native_decide

end Wintermute.Vectors
