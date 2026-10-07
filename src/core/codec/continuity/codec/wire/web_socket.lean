/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // CONTINUITY // CODEC // WIRE // WEBSOCKET
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The WebSocket frame (RFC 6455) — NEW SPEC (Cornell ★ ships C++; Continuity had
    none). The verified reference the generator (`Codec/Codegen/WebSocket`) mirrors:

        byte0:  FIN(1) RSV(3=0) opcode(4)
        byte1:  MASK(1) payload-len(7)   — 0-125 inline · 126 → u16 BE · 127 → u64 BE
        [masking-key: 4 bytes if MASK]
        payload (XOR-unmasked with the key when MASK)

    Opcodes: 0x0 continuation · 0x1 text · 0x2 binary · 0x8 close · 0x9 ping · 0xA pong.
    These are executable references; correctness is pinned by `native_decide`
    round-trips (short / 16-bit-length / masked frames). The generator produces the
    matching C++; control/fragmentation state is the data layer above.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.WebSocket

def OPCODE_CONTINUATION : Nat := 0x0
def OPCODE_TEXT : Nat := 0x1
def OPCODE_BINARY : Nat := 0x2
def OPCODE_CLOSE : Nat := 0x8
def OPCODE_PING : Nat := 0x9
def OPCODE_PONG : Nat := 0xA

structure Frame where
  fin     : Bool
  opcode  : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

/-- The payload-length encoding: inline (< 126), or `126 ++ u16 BE`, or `127 ++ u64 BE`. -/
def encodeLen (count : Nat) : List UInt8 :=
  if count < 126 then
    [count.toUInt8]
  else if count < 65536 then
    [126, (count >>> 8 &&& 0xFF).toUInt8, (count &&& 0xFF).toUInt8]
  else
    127 :: (List.range 8).reverse.map (fun idx => (count >>> (8 * idx) &&& 0xFF).toUInt8)

/-- Serialize a frame (server side — unmasked). -/
def serializeFrame (frame : Frame) : List UInt8 :=
  let firstByte : UInt8 := (if frame.fin then 0x80 else 0) ||| (frame.opcode.toUInt8 &&& 0x0F)
  firstByte :: encodeLen frame.payload.length ++ frame.payload

/-- Parse a frame, unmasking the payload if the MASK bit is set (client→server). -/
def parseFrame (bytes : List UInt8) : Option Frame :=
  if bytes.length ≥ 2 then
    let firstByte := bytes.getD 0 0
    let secondByte := bytes.getD 1 0
    let fin := (firstByte &&& 0x80) != 0
    let opcode := (firstByte &&& 0x0F).toNat
    let masked := (secondByte &&& 0x80) != 0
    let len7 := (secondByte &&& 0x7F).toNat
    let (payloadLen, hdrEnd) : Nat × Nat :=
      if len7 < 126 then
        (len7, 2)
      else if len7 == 126 then
        ((bytes.getD 2 0).toNat <<< 8 ||| (bytes.getD 3 0).toNat, 4)
      else
        (
          (List.range 8).foldl (fun result idx => result <<< 8 ||| (bytes.getD (2 + idx) 0).toNat) 0,
          10
        )
    let dataStart := if masked then hdrEnd + 4 else hdrEnd
    if bytes.length ≥ dataStart + payloadLen then
      let raw := (List.range payloadLen).map (fun idx => bytes.getD (dataStart + idx) 0)
      let payload :=
        if masked then raw.mapIdx fun idx byte => byte ^^^ bytes.getD (hdrEnd + idx % 4) 0 else raw
      some { fin, opcode, payload }
    else
      none
  else
    none

-- ── it round-trips — canonical frames ─────────────────────────────────────────

/-- A short FIN text frame "Hi" round-trips. -/
example :
    parseFrame (serializeFrame { fin := true, opcode := OPCODE_TEXT, payload := [72, 105] })
        = some { fin := true, opcode := OPCODE_TEXT, payload := [72, 105] } := by native_decide

/-- A 200-byte binary frame uses the 16-bit length and round-trips. -/
example :
    let frame : Frame :=
      { fin := true, opcode := OPCODE_BINARY, payload := List.replicate 200 0xAB }
    (serializeFrame frame).length = 4 + 200 ∧ parseFrame (serializeFrame frame) = some frame := by
  native_decide

/-- A MASKED client frame (key 1,2,3,4) unmasks to "Hi". -/
example :
    parseFrame [0x81, 0x82, 1, 2, 3, 4, 72 ^^^ 1, 105 ^^^ 2]
        = some { fin := true, opcode := OPCODE_TEXT, payload := [72, 105] } := by native_decide

/-- A truncated frame (length byte promises more than present) is rejected. -/
example : parseFrame [0x81, 0x05, 72, 105] = none := by native_decide

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // the differential scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The frame scope (STR-227): every (fin × opcode) with payload lengths that
    exercise the inline (< 126), the 126-boundary, and the 16-bit length forms. The
    server-side `serializeFrame` is unmasked, so `parseFrame` sees the unmasked path. -/
def wsScope : List Frame :=
  let opcodes :=
    [OPCODE_CONTINUATION, OPCODE_TEXT, OPCODE_BINARY, OPCODE_CLOSE, OPCODE_PING, OPCODE_PONG]
  let sizes := [0, 1, 125, 126, 130]
  ([true, false]).flatMap
    (fun fin =>
      opcodes.flatMap
        (fun opcode =>
          sizes.map
            (fun length =>
              { fin     := fin,
                opcode  := opcode,
                payload := (List.range length).map (fun idx => (idx % 256).toUInt8) })))

/-- EXHAUSTIVE over `wsScope`: serialize-then-parse is the identity. -/
theorem frame_roundtrip_on_scope
        : wsScope.all (fun frame => parseFrame (serializeFrame frame) == some frame) = true := by
  native_decide

/-- One differential case: `(fin, opcode, payload, encoded bytes)`. -/
abbrev DiffCase := Bool × Nat × List Nat × List Nat

/-- The witness set, from the SAME enumeration the theorem ranges over. -/
def diffCases : List DiffCase :=
  wsScope.map
    (fun field =>
      (field.fin, field.opcode, field.payload.map (·.toNat), (serializeFrame field).map (·.toNat)))

end Continuity.Codec.Wire.WebSocket
