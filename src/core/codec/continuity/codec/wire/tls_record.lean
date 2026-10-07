/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        // CONTINUITY // CODEC // WIRE // TLS RECORD
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The TLS record header (RFC 8446 §5.1) as a VERIFIED reference + ORACLE for the
    fleet differential (STR-227), mirroring `tls::{parse,serialize}_record`. A record
    is `content_type(1) ‖ version(BE16) ‖ length(BE16) ‖ fragment[length]`. The scope
    is the explicit product `contentTypes × versions × fragments`; serialize-then-
    parse is the identity on it, proven by `native_decide`.

    Note the bound the C++ relies on (`len > b.size() - 5`, subtract-not-add — the
    STR-208/STR-215 overflow-safe shape): every witness here is well-formed, so the
    differential checks the *accepting* path; the rejecting path is the fuzz/negative-
    oracle surface (STR-228).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.tls_record

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the reference codec (mirrors the C++)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- `serialize_record(ct, ver, frag)` — the 5-byte header followed by the fragment. -/
def serialize (ciphertext ver : Nat) (frag : List Nat) : List Nat :=
  [ciphertext, ver / 256 % 256, ver % 256, frag.length / 256 % 256, frag.length % 256] ++ frag

/-- The parsed record: `(content_type, version, fragment, consumed)`. -/
abbrev Parsed := Nat × Nat × List Nat × Nat

/-- `parse_record(bs)` — a short read or an over-long declared length is `none`. The
    `len > bs.length - 5` guard is the overflow-safe form (subtract, never wraps). -/
def parse (bytes : List Nat) : Option Parsed :=
  if bytes.length < 5 then
    none
  else
    let len := bytes.getD 3 0 * 256 + bytes.getD 4 0
    if len > bytes.length - 5 then
      none
    else
      some (bytes.getD 0 0, bytes.getD 1 0 * 256 + bytes.getD 2 0, (bytes.drop 5).take len, 5 + len)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The real ContentType code points (change_cipher_spec, alert, handshake, app_data). -/
def contentTypes : List Nat := [20, 21, 22, 23]

/-- TLS 1.0 and TLS 1.2 legacy_record_version. -/
def versions : List Nat := [0x0301, 0x0303]

/-- Fragment witnesses: empty, single bytes at the byte extremes, a short run, and a
    20-byte body (exercises the length field and the copy). -/
def fragments : List (List Nat) := [[], [0], [255], [1, 2, 3], List.range 20]

/-- The explicit product scope. -/
def scope : List (Nat × Nat × List Nat) :=
  contentTypes.flatMap
    (fun contentType =>
      versions.flatMap (fun value => fragments.map (fun field => (contentType, value, field))))

/-- Serialize-then-parse recovers every field and the exact byte count. -/
def roundTrips : Nat × Nat × List Nat → Bool
  | (contentType, value, frame) =>
    parse (serialize contentType value frame) == some (contentType, value, frame, 5 + frame.length)

/-- EXHAUSTIVE over `scope` — a proof on τ, not a sample. -/
theorem record_roundtrip_on_scope : scope.all roundTrips = true := by native_decide

/-- One differential case: `(content_type, version, fragment, encoded bytes)`. -/
abbrev Case := Nat × Nat × List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := scope.map (fun (ct, v, f) => (ct, v, f, serialize ct v f))

end Continuity.Codec.Wire.tls_record
