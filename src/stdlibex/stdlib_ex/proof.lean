/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // STDLIBEX // PROOF
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The internal FLOOR of StdlibEx. It imports NOTHING from StdlibEx (only Lean core
    + batteries), so every other StdlibEx module can build on it with no cycle — and
    StdlibEx as a whole never reaches UP into `Continuity.*`/`Net.*`/`Aleph.*`.

    It holds the shared verification infrastructure the two module tracks use:

      · `differential` — the Track-A gate harness: run a compiled `@[extern]` path
        against a WHOLLY INDEPENDENT reference over an explicit scope, nonzero exit on
        any mismatch. So each gate `lean_exe` is a few lines, and "the C refines the
        proven Lean body" is *evidence*, not assertion.
      · `closedOn` — the native_decide scope-closure idiom as a checkable `Bool`:
        `theorem foo_on_scope : closedOn scope p = true := by native_decide` is a proof
        on the whole finite scope τ, not a sample of it.

    The bar every StdlibEx module is held to (documented here so it's one place):
      Track A (proof surface — bytes/parsing): the proven Lean body IS the kernel def;
        prove soundness AND completeness by hand (no `sorry`, no axiom, no
        `native_decide` inside the laws); `@[extern]` adds NO axiom (the kernel still
        elaborates the Lean body) so the C is TRUSTED, gated by a `differential`.
      Track B (opaque resources — logging/CLI): wrap a mature C lib behind a flat
        extern-C ABI; only `const char*`/primitives/opaque handles cross; Lean owns
        formatting; correctness is delegated to a separate proven core, not the shim.
      Both: `#print axioms` on each key theorem shows ONLY propext / Quot.sound /
        Classical.choice — the `@[extern]` symbol must never appear as an axiom.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Proof

/-- A property holding on EVERY element of an explicit finite scope, as a `Bool` — the
    native_decide scope-closure idiom. `theorem p_on_scope : closedOn τ p = true := by
    native_decide` is then a proof on the whole of τ, and `τ` is the same enumeration a
    `differential` gate ranges over (proof and gate share one scope). -/
@[inline]
def closedOn
    {elementType : Type _}
    (scope : List elementType)
    (predicate : elementType → Bool)
    : Bool :=
  scope.all predicate

/-- The Track-A differential gate. Run `fast` (the compiled, `@[extern]`-lowered path)
    and `ref` (a WHOLLY INDEPENDENT reference, deliberately different control flow, so
    agreement is real evidence not a tautology) over every element of `scope`; report
    and fail (exit 1) on the first disagreements. A gate exe is then just:

        def main : IO UInt32 := StdlibEx.Proof.differential "findbytes" scope
          (fun (h, n) => findBytes h n) (fun (h, n) => naiveFind h n)

    The scope must be exhaustive-by-construction over its τ (e.g. all short haystacks ×
    short needles), so a clean run is a proof the C matches the proven body on all of τ. -/
def differential
    {inputType : Type _}
    {outputType : Type _}
    [BEq outputType]
    [ToString inputType]
    (label : String)
    (scope : List inputType)
    (fast ref : inputType → outputType)
    : IO UInt32 := do
  let mut bad : Nat := 0
  for input in scope do
    if fast input != ref input then
      bad := bad + 1
      if bad ≤ 10 then IO.eprintln s!"  [{label}] MISMATCH at {input}"
  if bad == 0 then
    IO.println s!"// gate // {label}: {scope.length} cases agree — C ≡ proven ref"
    return 0
  else
    IO.eprintln s!"// gate // {label}: {bad}/{scope.length} MISMATCHES — C ≢ ref"
    return 1

end StdlibEx.Proof
