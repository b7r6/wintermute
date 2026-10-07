/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // WINTERMUTE // COLOR // HSL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Integer HSL→RGB, an EXACT port of the ono-sendai generator
    (nixos-config `modules/flake/themes/packages/ono-sendai-generator/`).

    The math is fixed-point ×1000 with `((base + m1000) * 255 + 500) / 1000`
    rounding — the same formula the generator's 66 conformance vectors pin the
    Nix reimplementation against. Wintermute is a third implementation of the
    same truth; any drift here is caught by the same vector set.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Wintermute

abbrev Channel := Fin 256
abbrev Hue     := Fin 360
abbrev Pct     := Fin 101

structure RGB where
  r : Channel
  g : Channel
  b : Channel
  deriving Repr, BEq, DecidableEq

structure HSL where
  h : Hue
  s : Pct
  l : Pct
  deriving Repr, BEq, DecidableEq

private def hexDigit (n : Fin 16) : Char :=
  if n.val < 10 then Char.ofNat (n.val + 48)
  else Char.ofNat (n.val + 87)

def Channel.toHex (c : Channel) : String :=
  let hi : Fin 16 := ⟨c.val / 16, by omega⟩
  let lo : Fin 16 := ⟨c.val % 16, by omega⟩
  s!"{hexDigit hi}{hexDigit lo}"

def RGB.toHex (c : RGB) : String :=
  s!"#{c.r.toHex}{c.g.toHex}{c.b.toHex}"

def HSL.toRGB (c : HSL) : RGB :=
  let s1000 : Nat := c.s.val * 10
  let l1000 : Nat := c.l.val * 10
  let twoL := 2 * l1000
  let diff := if twoL ≥ 1000 then twoL - 1000 else 1000 - twoL
  let c1000 := ((1000 - diff) * s1000) / 1000
  let hmod := c.h.val % 360
  let sector := hmod / 60
  let pair := hmod % 120
  let absVal := if pair ≥ 60 then pair - 60 else 60 - pair
  let x1000 := (c1000 * (60 - absVal)) / 60
  let m1000 := l1000 - c1000 / 2
  let (r', g', b') := match sector with
    | 0 => (c1000, x1000, 0) | 1 => (x1000, c1000, 0)
    | 2 => (0, c1000, x1000) | 3 => (0, x1000, c1000)
    | 4 => (x1000, 0, c1000) | _ => (c1000, 0, x1000)
  let clamp (v : Int) : Channel :=
    let n := v.toNat
    if h : n < 256 then ⟨n, h⟩ else ⟨255, by omega⟩
  let ch (base : Nat) : Channel :=
    clamp (((base + m1000) * 255 + 500) / 1000 : Int)
  { r := ch r', g := ch g', b := ch b' }

def normalizeHue (n : Int) : Hue :=
  let m := ((n % 360 + 360) % 360).toNat
  if h : m < 360 then ⟨m, h⟩ else ⟨0, by omega⟩

/-- `hslAt h s l` — hex color at hue `h` (any integer, normalized), saturation
    and lightness clamped to `[0, 100]`. The single entry point the palette
    tables call; identical to the generator's `hslAt`. -/
def hslAt (h s l : Nat) : String :=
  (HSL.mk (normalizeHue h)
    (if hs : s ≤ 100 then ⟨s, by omega⟩ else ⟨100, by omega⟩)
    (if hl : l ≤ 100 then ⟨l, by omega⟩ else ⟨100, by omega⟩)).toRGB.toHex

-- The generator's own anchor values: carbon base00 = HSL(211, 12, 11).
example : hslAt 211 12 11 = "#191c1f" := by native_decide
example : hslAt 211 33 97 = "#f5f7fa" := by native_decide

end Wintermute
