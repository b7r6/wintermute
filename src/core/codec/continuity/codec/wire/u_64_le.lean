/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // CODEC // WIRE // U64LE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The little-endian u64 primitive as a VERIFIED reference + ORACLE for the fleet
    differential (STR-227), mirroring `u64le::{serialize,parse}_u64le`. The simplest
    row: serialize is total (always 8 bytes), parse is total on ≥ 8 bytes; round-trip
    over an explicit value scope is `native_decide`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.U64le

/-- `serialize_u64le(v)` — eight little-endian octets. -/
def serialize (value : Nat) : List Nat :=
  (List.range 8).map (fun idx => value / 2 ^ (8 * idx) % 256)

/-- `parse_u64le(bs)` → the value, or `none` on a short read. -/
def parse (bytes : List Nat) : Option Nat :=
  if bytes.length < 8 then
    none
  else
    some ((List.range 8).foldl (fun result idx => result + bytes.getD idx 0 * 2 ^ (8 * idx)) 0)

/-- A value lattice: low bytes, single-byte boundaries, and witnesses that light up
    each of the eight octet lanes (powers of 256 and their neighbours), plus the
    32- and 64-bit extremes. -/
def valueScope : List Nat :=
  List.range 260
      ++ [
        255,
        256,
        257,
        65535,
        65536,
        16777215,
        16777216,
        4294967295,
        4294967296,
        1099511627775,
        281474976710655,
        72057594037927935,
        18446744073709551615
      ]

/-- Round-trip: parse recovers the value from its 8-octet serialization. -/
def roundTrips (value : Nat) : Bool := parse (serialize value) == some value

/-- EXHAUSTIVE over `valueScope` — a proof on τ, not a sample. -/
theorem u64le_roundtrip_on_scope : valueScope.all (fun value => roundTrips value) = true := by
  native_decide

/-- One differential case: `(value, 8 encoded octets)`. -/
abbrev Case := Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := valueScope.map (fun value => (value, serialize value))

end Continuity.Codec.Wire.U64le
