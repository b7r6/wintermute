/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // CONTINUITY // CODEC // WIRE // HTTP2 FRAME
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The HTTP/2 frame header (RFC 7540 §4.1) as a VERIFIED reference + ORACLE for the
    fleet differential (STR-227), mirroring `h2::{serialize,parse}_frame_header`:
    a 24-bit big-endian length, an 8-bit type, 8-bit flags, and a 31-bit stream id
    (the reserved high bit is cleared on write and masked on read).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.Http2Frame

/-- A parsed header: `(length, type, flags, streamId)`. -/
abbrev Header := Nat × Nat × Nat × Nat

/-- `serialize_frame_header` — the 9 bytes, big-endian; stream-id high bit cleared. -/
def serialize : Header → List Nat
  | (length, type, flags, streamId) =>
    [
      length / 65536 % 256,
      length / 256 % 256,
      length % 256,
      type,
      flags,
      streamId / 2 ^ 24 % 128,
      streamId / 2 ^ 16 % 256,
      streamId / 2 ^ 8 % 256,
      streamId % 256
    ]

/-- `parse_frame_header` — `none` on a short read; the type byte is taken verbatim
    (the generated parser casts it, it does not validate). -/
def parse (bytes : List Nat) : Option Header :=
  if bytes.length < 9 then
    none
  else
    some
      (
        bytes.getD 0 0 * 65536 + bytes.getD 1 0 * 256 + bytes.getD 2 0,
        bytes.getD 3 0,
        bytes.getD 4 0,
        bytes.getD 5 0 % 128 * 2 ^ 24 + bytes.getD 6 0 * 2 ^ 16 + bytes.getD 7 0 * 2 ^ 8 + bytes.getD 8 0
      )

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The explicit product: lengths across the 24-bit field, the ten real frame types,
    flag extremes, and stream ids up to the 31-bit max (all < 2³¹ so the masked
    round-trip is exact). -/
def scope : List Header :=
  let lengths := [0, 6, 256, 16384, 16777215]
  let types := List.range 10 -- 0..9 (DATA … CONTINUATION)
  let flagsL := [0, 1, 255]
  let streams := [0, 1, 2147483647]
  lengths.flatMap
    (fun lengthValue =>
      types.flatMap
        (fun frameType =>
          flagsL.flatMap
            (fun flags => streams.map (fun streamId => (lengthValue, frameType, flags, streamId)))))

/-- Serialize-then-parse recovers every field exactly. -/
def roundTrips (evidence : Header) : Bool := parse (serialize evidence) == some evidence

/-- EXHAUSTIVE over `scope` — a proof on τ, not a sample. -/
theorem frame_header_roundtrip_on_scope : scope.all (fun header => roundTrips header) = true := by
  native_decide

/-- One differential case: `(length, type, flags, streamId, encoded bytes)`. -/
abbrev Case := Nat × Nat × Nat × Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case :=
  scope.map (fun header => (header.1, header.2.1, header.2.2.1, header.2.2.2, serialize header))

end Continuity.Codec.Wire.Http2Frame
