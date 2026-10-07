/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // CONTINUITY // CODEC // WIRE // HTTP3 VARINT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The QUIC variable-length integer (RFC 9000 §16) as a VERIFIED reference + ORACLE
    for the fleet differential (STR-227), mirroring `http3::{serialize,parse}_varint`.
    The top two bits of the first byte select the length class — 1/2/4/8 bytes,
    big-endian, holding a 6/14/30/62-bit value; `serialize` picks the smallest class.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.Http3Varint

/-- `serialize_varint(v)` — the smallest of the four QUIC classes. -/
def serialize (value : Nat) : List Nat :=
  if value < 64 then
    [value]
  else if value < 16384 then
    [64 + (value / 256 % 64), value % 256]
  else if value < 1073741824 then
    [128 + (value / 2 ^ 24 % 64), value / 2 ^ 16 % 256, value / 2 ^ 8 % 256, value % 256]
  else
    [
      192 + (value / 2 ^ 56 % 64),
      value / 2 ^ 48 % 256,
      value / 2 ^ 40 % 256,
      value / 2 ^ 32 % 256,
      value / 2 ^ 24 % 256,
      value / 2 ^ 16 % 256,
      value / 2 ^ 8 % 256,
      value % 256
    ]

/-- `parse_varint(bs, 0)` → `(value, consumed)`; the class is the first byte's top 2 bits. -/
def parse (bytes : List Nat) : Option (Nat × Nat) :=
  match bytes with
  | [] => none
  | firstByte :: _ =>
    let lenCode := firstByte / 64
    let need := 2 ^ lenCode -- 1, 2, 4, or 8
    if bytes.length < need then
      none
    else
      let val :=
        (List.range need).foldl
          (fun result idx => result * 256 + (if idx == 0 then firstByte % 64 else bytes.getD idx 0))
          0
      some (val, need)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Values straddling each of the four class boundaries (2⁶, 2¹⁴, 2³⁰, 2⁶²). -/
def valueScope : List Nat :=
  List.range 130
      ++ [63, 64, 16383, 16384, 16385, 1073741823, 1073741824, 1073741825, 4611686018427387903]

/-- Round-trip: parse recovers the value and the class byte count. -/
def roundTrips (value : Nat) : Bool :=
  parse (serialize value) == some (value, (serialize value).length)

/-- EXHAUSTIVE over `valueScope` — a proof on τ, not a sample. -/
theorem quic_varint_roundtrip_on_scope : valueScope.all (fun value => roundTrips value) = true := by
  native_decide

/-- One differential case: `(value, encoded bytes)`. -/
abbrev Case := Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := valueScope.map (fun value => (value, serialize value))

end Continuity.Codec.Wire.Http3Varint
