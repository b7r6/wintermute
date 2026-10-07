/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                              // CONTINUITY // CODEC // WIRE // HPACK INT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The HPACK integer codec (RFC 7541 §5.1) as a VERIFIED reference and the ORACLE
    for the proof-carrying differential harness (STR-212/STR-214). Row 1 of the
    ladder: a finite, explicitly-enumerated scope `τ = prefixWidths × valueScope`,
    over which round-trip is proven by `native_decide` — the "exhaustive rapidcheck
    written in Lean, exhaustiveness guaranteed by the enumeration, not by a trial
    count."

    `diffCases` is rendered from the SAME enumeration into a C++ differential harness
    (`Codegen/Differential`) that runs the GENERATED `hpack::parse_int` on every
    witness under ASan/UBSan. Green ⇒ the C++ refines this reference on all of τ. The
    only unverified link is {C++ compiler, comparison loop}.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.HpackInt

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // the reference codec (mirrors the C++)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Base-128 continuation tail (the bytes after the all-ones prefix). -/
def encTail : Nat → Nat → List Nat
  | _, 0 => []
  | value, Nat.succ frame =>
    if value < 128 then [value] else (value % 128 + 128) :: encTail (value / 128) frame

/-- `encode_int(value, prefixBits)` with flags = 0 (RFC 7541 §5.1). -/
def encodeInt (value prefixBits : Nat) : List Nat :=
  let maxP := 2 ^ prefixBits - 1
  if value < maxP then [value] else maxP :: encTail (value - maxP) (value + 1)

/-- Continuation accumulator: `acc + Σ (bᵢ & 127) · 2^(7·k)`, reporting bytes consumed. -/
def parseTail : List Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | [], _, _, _ => none
  | byte :: rest, key, decodedValue, index =>
    let nextValue := decodedValue + (byte % 128) * 2 ^ (7 * key)
    if byte < 128 then
      some (nextValue, index + 1)
    else
      parseTail rest (key + 1) nextValue (index + 1)

/-- `parse_int(bs, prefixBits)` → `(value, consumed)`, mirroring `hpack::parse_int`
    (offset 0). A truncated continuation is `none`. -/
def parseInt (bytes : List Nat) (prefixBits : Nat) : Option (Nat × Nat) :=
  match bytes with
  | [] => none
  | firstByte :: rest =>
    let maxP := 2 ^ prefixBits - 1
    let first := firstByte % (maxP + 1)
    if first < maxP then some (first, 1) else parseTail rest 0 maxP 1

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Every HPACK prefix width that appears in the wire (indexed 7, literal-name 6,
    without/never 4, size-update 5). -/
def prefixWidths : List Nat := [4, 5, 6, 7]

/-- A value lattice: a dense low band (covers single-byte, the `maxP` boundary, and
    2-byte continuations for every width) plus witnesses that force 3- and 4-byte
    encodings. The scope is the explicit product `prefixWidths × valueScope`. -/
def valueScope : List Nat := List.range 260 ++ [16384, 16385, 100000, 2097150, 268435455]

/-- The round-trip proposition: parse recovers the value and the exact byte count. -/
def roundTrips (prefixBits value : Nat) : Bool :=
  parseInt (encodeInt value prefixBits) prefixBits
      == some (value, (encodeInt value prefixBits).length)

/-- EXHAUSTIVE over the scope τ: round-trip holds for every `(prefixWidth, value)` —
    the enumeration is the whole of `τ`, so this is a proof on `τ`, not a sample. -/
theorem int_roundtrip_on_scope
        : prefixWidths.all
          (fun prefixBits => valueScope.all (fun value => roundTrips prefixBits value))
            = true := by native_decide

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the witness set for the differential
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- One differential case: `(prefixBits, value, encoded bytes)`. The oracle outputs
    are `value` and `bytes.length` (proven correct by `int_roundtrip_on_scope`). -/
abbrev Case := Nat × Nat × List Nat

/-- The witness set, rendered from the SAME enumeration the theorem ranges over —
    so "the harness ran every case" inherits the theorem's completeness. -/
def diffCases : List Case :=
  prefixWidths.flatMap
    (fun prefixBits => valueScope.map (fun value => (prefixBits, value, encodeInt value prefixBits)))

end Continuity.Codec.Wire.HpackInt
