/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // CONTINUITY // CODEC // WIRE // NIX FRAMING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Nix daemon length-prefixed frame as a VERIFIED reference + ORACLE for the
    fleet differential (STR-227), mirroring `nix_framing::{serialize,parse}_frame`:
    an 8-byte little-endian length, then that many payload octets. A short read, or a
    declared length over `MAX_PAYLOAD` (2³²) or past the buffer, is `none`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import continuity.codec.wire.u_64_le

namespace Continuity.Codec.Wire.NixFraming

/-- RFC-less wire constant: the daemon caps a single frame at 2³² octets. -/
def maxPayload : Nat := 4294967296

/-- `serialize_frame(payload)` — 8-byte LE length, then the payload. -/
def serialize (payload : List Nat) : List Nat :=
  Continuity.Codec.Wire.U64le.serialize payload.length ++ payload

/-- The 8-byte LE length at offset 0 (mirrors `read_length`). -/
def readLen (bytes : List Nat) : Nat :=
  (List.range 8).foldl (fun result idx => result + bytes.getD idx 0 * 2 ^ (8 * idx)) 0

/-- `parse_frame(b)` → `(payload, consumed)`. -/
def parse (bytes : List Nat) : Option (List Nat × Nat) :=
  if bytes.length < 8 then
    none
  else
    let len := readLen bytes
    if len > maxPayload then
      none
    else if bytes.length < 8 + len then none else some ((bytes.drop 8).take len, 8 + len)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Payload witnesses: empty, single byte, and the 7/8/255/256-byte neighbourhood
    (the length-field byte boundaries). -/
def payloadScope : List (List Nat) :=
  [0, 1, 7, 8, 255, 256].map (fun count => (List.range count).map (fun idx => idx % 256))

/-- Serialize-then-parse recovers the payload and the exact byte count. -/
def roundTrips (parser : List Nat) : Bool :=
  parse (serialize parser) == some (parser, 8 + parser.length)

/-- EXHAUSTIVE over `payloadScope` — a proof on τ, not a sample. -/
theorem framing_roundtrip_on_scope
        : payloadScope.all (fun payload => roundTrips payload) = true := by native_decide

/-- One differential case: `(payload, encoded bytes)`; consumed = `8 + |payload|`. -/
abbrev Case := List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := payloadScope.map (fun payload => (payload, serialize payload))

end Continuity.Codec.Wire.NixFraming
