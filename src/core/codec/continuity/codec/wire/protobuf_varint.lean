/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                      // CONTINUITY // CODEC // WIRE // PROTOBUF VARINT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The protobuf base-128 varint (LEB128) as a VERIFIED reference + ORACLE for the
    fleet differential (STR-227), mirroring `protobuf::{encode,parse}_varint`. Row 1
    of the ladder: a finite, explicit scope `valueScope`, round-trip proven by
    `native_decide` — the enumeration is the whole scope, so it is a proof on τ, not
    a sample. `diffCases` renders the SAME enumeration into the C++ harness.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.ProtobufVarint

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the reference codec (mirrors the C++)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- LEB128: low 7 bits per byte, high bit = continuation. -/
def encodeAux : Nat → Nat → List Nat
  | _, 0 => []
  | value, Nat.succ frame =>
    if value < 128 then [value] else (value % 128 + 128) :: encodeAux (value / 128) frame

/-- `encode_varint(n)` (RFC: protobuf §base-128). -/
def encodeVarint (count : Nat) : List Nat := encodeAux count (count + 1)

/-- Continuation value: `decoded + Σ (bᵢ & 127) · 2^(7·k)`, reporting bytes consumed. -/
def parseAux : List Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | [], _, _, _ => none
  | byte :: rest, shift, decoded, index =>
    let nextDecoded := decoded + (byte % 128) * 2 ^ shift
    if byte < 128 then
      some (nextDecoded, index + 1)
    else
      parseAux rest (shift + 7) nextDecoded (index + 1)

/-- `parse_varint(bs, 0)` → `(value, consumed)`, mirroring `protobuf::parse_varint`. -/
def parseVarint (bytes : List Nat) : Option (Nat × Nat) := parseAux bytes 0 0 0

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A value lattice: a dense low band (single-byte + the 1↔2-byte boundary + 2-byte
    continuations) plus witnesses forcing 3-, 4-, and 5-byte encodings. -/
def valueScope : List Nat :=
  List.range 260 ++ [16383, 16384, 16385, 2097151, 2097152, 268435455, 34359738367]

/-- The round-trip proposition: parse recovers the value and the exact byte count. -/
def roundTrips (value : Nat) : Bool :=
  parseVarint (encodeVarint value) == some (value, (encodeVarint value).length)

/-- EXHAUSTIVE over `valueScope` — a proof on τ, not a sample. -/
theorem varint_roundtrip_on_scope : valueScope.all (fun value => roundTrips value) = true := by
  native_decide

/-- One differential case: `(value, encoded bytes)`. Oracle outputs = `value` and
    `bytes.length` (proven by `varint_roundtrip_on_scope`). -/
abbrev Case := Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List Case := valueScope.map (fun value => (value, encodeVarint value))

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // length-delimited (varint length ++ payload)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- `encode_length_delimited(data)` — a varint length, then the bytes. -/
def encodeLD (data : List Nat) : List Nat := encodeVarint data.length ++ data

/-- `parse_length_delimited(b, 0)` → `(data, consumed)`. The slice is reached only
    through the overflow-safe bound (`start > size ∨ len > size - start`, STR-208). -/
def parseLD (bytes : List Nat) : Option (List Nat × Nat) :=
  match parseVarint bytes with
  | none => none
  | some (len, code) =>
    if code > bytes.length ∨ len > bytes.length - code then
      none
    else
      some ((bytes.drop code).take len, code + len)

/-- Payload witnesses across the 1↔2-byte varint-length boundary. -/
def ldScope : List (List Nat) :=
  [0, 1, 127, 128, 200].map (fun count => (List.range count).map (fun idx => idx % 256))

/-- Encode-then-parse recovers the payload and the exact byte count. -/
def ldRoundTrips (decoder : List Nat) : Bool :=
  parseLD (encodeLD decoder)
      == some (decoder, (encodeVarint decoder.length).length + decoder.length)

/-- EXHAUSTIVE over `ldScope` — a proof on τ, not a sample. -/
theorem ld_roundtrip_on_scope : ldScope.all (fun digit => ldRoundTrips digit) = true := by
  native_decide

/-- One length-delimited differential case: `(payload, encoded bytes)`. -/
abbrev LDCase := List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def ldDiffCases : List LDCase := ldScope.map (fun digit => (digit, encodeLD digit))

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // gRPC frame (1-byte compressed flag + BE32 length)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- `encode_grpc_frame(compressed, message)` — flag byte, 4-byte BE length, message. -/
def encodeGrpc (compressed : Bool) (msg : List Nat) : List Nat :=
  (if compressed then 1 else 0)
      :: [
        msg.length / 2 ^ 24 % 256,
        msg.length / 2 ^ 16 % 256,
        msg.length / 2 ^ 8 % 256,
        msg.length % 256
      ]
      ++ msg

/-- `parse_grpc_frame(b)` → `(compressed, message, consumed)`. -/
def parseGrpc (bytes : List Nat) : Option (Bool × List Nat × Nat) :=
  if bytes.length < 5 then
    none
  else
    let len :=
      bytes.getD 1 0 * 2 ^ 24 + bytes.getD 2 0 * 2 ^ 16 + bytes.getD 3 0 * 2 ^ 8 + bytes.getD 4 0
    if bytes.length < 5 + len then
      none
    else
      some (bytes.getD 0 0 != 0, (bytes.drop 5).take len, 5 + len)

/-- Message witnesses (both compression flags) across the BE32-length byte boundary. -/
def grpcScope : List (Bool × List Nat) :=
  ([false, true]).flatMap
    (fun certificate =>
      [0, 1, 255, 256].map
        (fun count => (certificate, (List.range count).map (fun idx => idx % 256))))

/-- Encode-then-parse recovers the flag, message, and exact byte count. -/
def grpcRoundTrips : Bool × List Nat → Bool
  | (code, marker) => parseGrpc (encodeGrpc code marker) == some (code, marker, 5 + marker.length)

/-- EXHAUSTIVE over `grpcScope` — a proof on τ, not a sample. -/
theorem grpc_roundtrip_on_scope
        : grpcScope.all (fun compressedMessage => grpcRoundTrips compressedMessage) = true := by
  native_decide

/-- One gRPC differential case: `(compressed, message, encoded bytes)`. -/
abbrev GrpcCase := Bool × List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def grpcDiffCases : List GrpcCase :=
  grpcScope.map
    (fun compressedMessage =>
      (compressedMessage.1, compressedMessage.2, encodeGrpc compressedMessage.1 compressedMessage.2))

end Continuity.Codec.Wire.ProtobufVarint
