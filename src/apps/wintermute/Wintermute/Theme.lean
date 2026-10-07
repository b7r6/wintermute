/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // WINTERMUTE // THEME // VECTOR
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The theme 4-vector — the entire desktop appearance as one small value:

      heroHue    accent hue, controls base0A–0F        (default 211)
      axisHue    variable/integer hue, base08–09       (default 201)
      luminance  day ↔ night — dark (ono-sendai black levels) or
                 light (maas white levels + unlockable paper-ramp hue)
      register   affluent ↔ facility, per-mille — effects + typography,
                 NOT color: scanline/brackets/telemetry rise toward the
                 facility pole, glass/bloom/grain toward affluent

    The 211° hue lock is enforced STRUCTURALLY: dark luminance carries no ramp
    hue at all — the grayscale table is written against 211 and no constructor
    argument can reach it. The theorems at the bottom state the consequence:
    accent-hue changes cannot perturb the grayscale ramp.

    Palette tables are exact ports of the ono-sendai generator (the same 66
    conformance vectors pin all implementations).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute.Color

-- The hue-lock theorems below are definitional (`rfl`), but checking them
-- unfolds the whole palette structure through the fixed-point HSL math —
-- deeper than the default elaborator recursion budget.
set_option maxRecDepth 8192

namespace Wintermute

-- ═══════════════════════════════════════════════════════════════════════════════
--  LUMINANCE AXIS  — black levels (ono-sendai) and white levels (maas)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive BlackLevel where
  | void | deep | night | carbon | github
  deriving Repr, BEq, DecidableEq

def BlackLevel.baseL : BlackLevel → Nat
  | .void => 0 | .deep => 4 | .night => 8 | .carbon => 11 | .github => 16

def BlackLevel.name : BlackLevel → String
  | .void => "void" | .deep => "deep" | .night => "night"
  | .carbon => "carbon" | .github => "github"

def BlackLevel.ofName? : String → Option BlackLevel
  | "void" => some .void | "deep" => some .deep | "night" => some .night
  | "carbon" => some .carbon | "github" => some .github
  | _ => none

inductive WhiteLevel where
  | tessier | neoform | ghost
  deriving Repr, BEq, DecidableEq

def WhiteLevel.baseL : WhiteLevel → Nat
  | .tessier => 100 | .neoform => 97 | .ghost => 92

def WhiteLevel.name : WhiteLevel → String
  | .tessier => "tessier" | .neoform => "neoform" | .ghost => "ghost"

def WhiteLevel.ofName? : String → Option WhiteLevel
  | "tessier" => some .tessier | "neoform" => some .neoform | "ghost" => some .ghost
  | _ => none

/-- The manufacturer axis — deep lore made a type. Each family is a
    night/day PAIR of names: `straylight` = ono-sendai (night) / maas (day),
    the 211° house; `hosaka` = blackwell (night) / grace (day), the NVIDIA
    build — the GB10's own die pair naming the polarities. The dark surface
    ramp hue is FAMILY-OWNED; the hue lock is per-family, not global. -/
inductive PaletteFamily where
  | straylight
  | hosaka
  deriving Repr, BEq, DecidableEq

/-- The night-surface ramp hue each family locks to. -/
def PaletteFamily.darkRampHue : PaletteFamily → Nat
  | .straylight => 211
  | .hosaka => 211

def PaletteFamily.name : PaletteFamily → String
  | .straylight => "straylight"
  | .hosaka => "hosaka"

def PaletteFamily.ofName? : String → Option PaletteFamily
  | "straylight" => some .straylight
  | "hosaka" => some .hosaka
  | _ => none

def PaletteFamily.darkSlugPrefix : PaletteFamily → String
  | .straylight => "ono-sendai"
  | .hosaka => "hosaka-blackwell"

def PaletteFamily.lightSlugPrefix : PaletteFamily → String
  | .straylight => "maas"
  | .hosaka => "hosaka-grace"

/-- Day ↔ night. Dark ramps are hue-locked BY CONSTRUCTION (the family owns
    the hue; there is still no free ramp argument); light unlocks the paper
    tint (`bioptic` = neoform + rampHue 36, `grace` = tessier + 150). -/
inductive Luminance where
  | dark  (level : BlackLevel)
  | light (level : WhiteLevel) (rampHue : Nat)
  deriving Repr, BEq, DecidableEq

def Luminance.polarity : Luminance → String
  | .dark _ => "dark"
  | .light _ _ => "light"

-- ═══════════════════════════════════════════════════════════════════════════════
--  THE 4-VECTOR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The whole theme as one value — the 5-VECTOR since hosaka arrived.
    `register` is per-mille along affluent (0) ↔ facility (1000); `family`
    picks the manufacturer (and with it the night ramp hue). -/
structure ThemeVector where
  heroHue   : Nat := 211
  axisHue   : Nat := 201
  family    : PaletteFamily := .straylight
  luminance : Luminance := .dark .carbon
  register  : Nat := 0
  deriving Repr, BEq, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
--  PALETTE  — base16, exact generator port
-- ═══════════════════════════════════════════════════════════════════════════════

structure Palette where
  base00 : String
  base01 : String
  base02 : String
  base03 : String
  base04 : String
  base05 : String
  base06 : String
  base07 : String
  base08 : String
  base09 : String
  base0A : String
  base0B : String
  base0C : String
  base0D : String
  base0E : String
  base0F : String
  deriving Repr, BEq, DecidableEq

/-- Dark (family night ramp): the surface hue comes from the FAMILY, never
    from a call-site argument — the hue lock is the absence of a parameter,
    not a runtime check. straylight locks 211° (ono-sendai); hosaka locks
    165° (blackwell phosphor). -/
def makePalette (family : PaletteFamily) (level : BlackLevel)
    (heroHue : Nat := 211) (axisHue : Nat := 201) : Palette :=
  let L := level.baseL
  let R := family.darkRampHue
  { base00 := hslAt R 12 (L + 0)
  , base01 := hslAt R 16 (L + 3)
  , base02 := hslAt R 17 (L + 8)
  , base03 := hslAt R 15 (L + 17)
  , base04 := hslAt R 12 48
  , base05 := hslAt R 28 81
  , base06 := hslAt R 32 89
  , base07 := hslAt R 36 95
  , base08 := hslAt axisHue 100 86
  , base09 := hslAt axisHue 100 75
  , base0A := hslAt heroHue 100 66
  , base0B := hslAt heroHue 100 57
  , base0C := hslAt heroHue  94 45
  , base0D := hslAt heroHue 100 65
  , base0E := hslAt heroHue 100 71
  , base0F := hslAt heroHue  86 53
  }

/-- Light (maas): the ramp hue is a parameter (warm paper = 36), the accent
    slots are the dark family's deep cuts re-leveled for white backgrounds. -/
def makePaletteLight (level : WhiteLevel) (heroHue : Nat := 211) (axisHue : Nat := 201)
    (rampHue : Nat := 211) : Palette :=
  let W := level.baseL
  let ramp (s l : Nat) : String := hslAt rampHue s l
  { base00 := ramp 33 (W - 0)
  , base01 := ramp 28 (W - 4)
  , base02 := ramp 26 (W - 10)
  , base03 := ramp 15 60
  , base04 := ramp 15 43
  , base05 := ramp 23 23
  , base06 := ramp 25 15
  , base07 := ramp 28 8
  , base08 := hslAt axisHue  90 40
  , base09 := hslAt axisHue 100 34
  , base0A := hslAt heroHue  94 45
  , base0B := hslAt heroHue 100 40
  , base0C := hslAt heroHue 100 34
  , base0D := hslAt heroHue  86 47
  , base0E := hslAt heroHue 100 50
  , base0F := hslAt heroHue  86 38
  }

def ThemeVector.palette (t : ThemeVector) : Palette :=
  match t.luminance with
  | .dark lv => makePalette t.family lv t.heroHue t.axisHue
  | .light lv rampHue => makePaletteLight lv t.heroHue t.axisHue rampHue

/-- The preset's public name: family slug prefix × level. -/
def ThemeVector.slug (t : ThemeVector) : String :=
  match t.luminance with
  | .dark lv => s!"{t.family.darkSlugPrefix}-{lv.name}"
  | .light lv _ => s!"{t.family.lightSlugPrefix}-{lv.name}"

def Palette.slots (p : Palette) : List (String × String) :=
  [("base00", p.base00), ("base01", p.base01), ("base02", p.base02), ("base03", p.base03),
   ("base04", p.base04), ("base05", p.base05), ("base06", p.base06), ("base07", p.base07),
   ("base08", p.base08), ("base09", p.base09), ("base0A", p.base0A), ("base0B", p.base0B),
   ("base0C", p.base0C), ("base0D", p.base0D), ("base0E", p.base0E), ("base0F", p.base0F)]

/-- The grayscale ramp — the slots the hue lock protects. -/
def Palette.ramp (p : Palette) : List String :=
  [p.base00, p.base01, p.base02, p.base03, p.base04, p.base05, p.base06, p.base07]

-- ═══════════════════════════════════════════════════════════════════════════════
--  REGISTER AXIS  — effect tokens, per-mille scalars interpolated along
--  affluent (0) ↔ facility (1000)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Interpolable effect scalars (per-mille). Facility pole raises scanline /
    brackets / telemetry; affluent pole raises glass / bloom / grain. The
    discrete typography switch (Cormorant lowercase ↔ Azonix UPPERCASE) flips
    at the midpoint and is derived, not stored. -/
structure RegisterTokens where
  scanline         : Nat
  bracketSize      : Nat
  telemetryDensity : Nat
  glassBlur        : Nat
  bloom            : Nat
  grainOpacity     : Nat
  deriving Repr, BEq, DecidableEq

def ThemeVector.tokens (t : ThemeVector) : RegisterTokens :=
  let r := min t.register 1000
  { scanline         := r
  , bracketSize      := r
  , telemetryDensity := r
  , glassBlur        := 1000 - r
  , bloom            := 1000 - r
  , grainOpacity     := 1000 - r
  }

/-- Discrete register switch: `false` = affluent typography, `true` = facility. -/
def ThemeVector.facility (t : ThemeVector) : Bool :=
  t.register ≥ 500

-- ═══════════════════════════════════════════════════════════════════════════════
--  THE FOUR CORNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Named corners of the 2D preset space. -/
def corners : List (String × ThemeVector) :=
  [ ("villa-straylight", { luminance := .dark .carbon,        register := 0 })
  , ("razorgirl",        { luminance := .dark .carbon,        register := 1000 })
  , ("tessier",          { luminance := .light .tessier 211,  register := 0 })
  , ("bioptic",          { luminance := .light .neoform 36,   register := 1000 })
  -- the third zaibatsu: silicon green hero (78 = #76B900's hue), plasma
  -- teal axis (168) — the 90° spread is the preset's signature
  , ("hosaka-blackwell", { heroHue := 110, axisHue := 168, family := .hosaka
                         , luminance := .dark .deep,        register := 1000 })
  , ("hosaka-grace",     { heroHue := 110, axisHue := 168, family := .hosaka
                         , luminance := .light .tessier 211, register := 0 })
  ]

def corner? (name : String) : Option ThemeVector :=
  (corners.find? (·.1 = name)).map (·.2)

-- ═══════════════════════════════════════════════════════════════════════════════
--  HUE LOCK  — accent hues cannot reach the grayscale ramp
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Dark hue lock: the ramp is INVARIANT under any change of hero/axis hue.
    Definitional — the ramp slots never mention the hue arguments. -/
theorem makePalette_ramp_hueLocked
        (fam : PaletteFamily)
        (lv : BlackLevel)
        (h₁ a₁ h₂ a₂ : Nat)
        : (makePalette fam lv h₁ a₁).ramp = (makePalette fam lv h₂ a₂).ramp := by

  simp only [Palette.ramp, makePalette]

/-- Light hue lock: at a fixed paper ramp, accent hues cannot touch the ramp. -/
theorem makePaletteLight_ramp_hueLocked
        (lv : WhiteLevel)
        (rampHue : Nat)
        (h₁ a₁ h₂ a₂ : Nat)
        : (makePaletteLight lv h₁ a₁ rampHue).ramp
            = (makePaletteLight lv h₂ a₂ rampHue).ramp := by

  simp only [Palette.ramp, makePaletteLight]

/-- Vector-level: the grayscale ramp is a function of (family, luminance)
    ALONE — two themes agreeing on both agree on every ramp slot, whatever
    their accent hues or register. This is the honest generalization of the
    old luminance-only lock: hosaka moved the night ramp, so family joined
    the invariant instead of breaking it. -/
theorem palette_ramp_family_luminance_only
        (t₁ t₂ : ThemeVector)
        (hf : t₁.family = t₂.family)
        (h : t₁.luminance = t₂.luminance)
        : t₁.palette.ramp = t₂.palette.ramp := by

  unfold ThemeVector.palette
  rw [hf, h]
  cases t₂.luminance with
  | dark lv =>
    exact makePalette_ramp_hueLocked t₂.family lv t₁.heroHue t₁.axisHue t₂.heroHue t₂.axisHue
  | light lv rampHue =>
    exact makePaletteLight_ramp_hueLocked lv rampHue t₁.heroHue t₁.axisHue t₂.heroHue t₂.axisHue

-- Hosaka's surfaces are now the neutral house ramp (211) — its identity is
-- the GREEN/teal accents on neutral dark, not a tinted ramp. The per-family
-- ramp machinery stays (palette_ramp_family_luminance_only holds regardless);
-- a future family can still move its ramp.

-- The register axis is orthogonal to color entirely: palette does not read it.
theorem palette_register_invariant
        (t : ThemeVector)
        (r : Nat)
        : ({ t with register := r } : ThemeVector).palette = t.palette :=

  rfl

-- Anchors: the default vector is carbon; its background is the canonical
-- computed value (one bit bluer than the legacy hand-tuned palette claimed).
example : (({} : ThemeVector)).palette.base00 = "#191c1f" := by native_decide
example : (corner? "tessier").isSome := by native_decide
example : (corner? "hosaka-blackwell").isSome := by native_decide
example : (corner? "hosaka-grace").isSome := by native_decide

end Wintermute
