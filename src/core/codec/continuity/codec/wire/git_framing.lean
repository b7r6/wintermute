/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // CONTINUITY // CODEC // WIRE // GIT FRAMING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The git pkt-line as a VERIFIED reference + ORACLE for the fleet differential
    (STR-227), mirroring `git_framing::{serialize,parse}_pkt_line`: a 4-hex-digit
    length (counting the 4 length octets), then the payload. `"0000"` is a flush
    packet. A bad hex digit, a `0 < total < 4`, or a short read is `none`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.GitFraming

/-- `to_hex_char`: lowercase hex (`n<10 ? 48+n : 87+n`). -/
def hexDigit (count : Nat) : Nat := if count < 10 then 48 + count else 87 + count

/-- `from_hex_char` for the lowercase+digit alphabet `serialize` emits. -/
def fromHex (cursor : Nat) : Option Nat :=
  if cursor ≥ 48 ∧ cursor ≤ 57 then
    some (cursor - 48)
  else if cursor ≥ 97 ∧ cursor ≤ 102 then some (cursor - 87) else none

/-- `serialize_pkt_line(payload)` — 4-hex-digit total length, then the payload. -/
def serialize (payload : List Nat) : List Nat :=
  let total := payload.length + 4
  [
    hexDigit (total / 4096 % 16),
    hexDigit (total / 256 % 16),
    hexDigit (total / 16 % 16),
    hexDigit (total % 16)
  ]
      ++ payload

/-- `parse_pkt_line(b)` → `(is_flush, payload, consumed)`. -/
def parse (bytes : List Nat) : Option (Bool × List Nat × Nat) :=
  if bytes.length < 4 then
    none
  else
    match fromHex (bytes.getD 0 0), fromHex (bytes.getD 1 0), fromHex (bytes.getD 2 0), fromHex (bytes.getD 3 0) with
    | some digit0, some digit1, some digit2, some digit3 =>
      let total := digit0 * 4096 + digit1 * 256 + digit2 * 16 + digit3
      if total == 0 then
        some (true, [], 4)
      else if total < 4 then
        none
      else if bytes.length < total then
        none
      else
        some (false, (bytes.drop 4).take (total - 4), total)
    | _, _, _, _ => none

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Payload witnesses across the hex-nibble carries (total = |p|+4). -/
def payloadScope : List (List Nat) :=
  [0, 1, 12, 250, 252].map (fun count => (List.range count).map (fun idx => idx % 256))

/-- A non-flush pkt-line round-trips to `(false, payload, |payload|+4)`. -/
def roundTrips (parser : List Nat) : Bool :=
  parse (serialize parser) == some (false, parser, parser.length + 4)

/-- EXHAUSTIVE over `payloadScope` — a proof on τ, not a sample. -/
theorem pktline_roundtrip_on_scope
        : payloadScope.all (fun payload => roundTrips payload) = true := by native_decide

/-- Flush is recognized (the `"0000"` packet). -/
theorem flush_parses : parse [48, 48, 48, 48] = some (true, [], 4) := by native_decide

/-- One differential case: `(payload, encoded bytes)`; consumed = `|payload| + 4`. -/
abbrev Case := List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := payloadScope.map (fun payload => (payload, serialize payload))

end Continuity.Codec.Wire.GitFraming
