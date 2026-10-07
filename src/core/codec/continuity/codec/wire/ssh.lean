/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // CONTINUITY // CODEC // WIRE // SSH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The SSH transport binary packet (RFC 4253 §6) — NEW SPEC. The evring SSH client
    delegates crypto/kex to libssh2 (the environment boundary, like `ada` for URLs);
    this is the self-contained, verifiable transport FRAMING:

        uint32 packet_length   (= padding_length + payload + padding, BE)
        byte   padding_length
        byte[] payload         (packet_length − padding_length − 1)
        byte[] padding         (padding_length; ≥ 4, total a multiple of 8)

    The verified reference the generator mirrors: `serialize_packet` computes the
    padding so the whole packet is 8-aligned (≥ 4 pad bytes); `parse_packet` recovers
    the payload. `native_decide` pins the round-trip and 8-alignment. The cipher/MAC
    and the kex handshake are the env boundary (libssh2).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.Ssh

-- SSH message numbers (RFC 4253 / 4252 / 4254), the common set.
def SSH_MSG_DISCONNECT : Nat := 1

def SSH_MSG_IGNORE : Nat := 2
def SSH_MSG_SERVICE_REQUEST : Nat := 5
def SSH_MSG_SERVICE_ACCEPT : Nat := 6
def SSH_MSG_KEXINIT : Nat := 20
def SSH_MSG_NEWKEYS : Nat := 21
def SSH_MSG_KEXDH_INIT : Nat := 30
def SSH_MSG_KEXDH_REPLY : Nat := 31
def SSH_MSG_USERAUTH_REQUEST : Nat := 50
def SSH_MSG_USERAUTH_SUCCESS : Nat := 52
def SSH_MSG_CHANNEL_OPEN : Nat := 90
def SSH_MSG_CHANNEL_DATA : Nat := 94

structure Packet where
  payload : List UInt8
  deriving DecidableEq, Repr

private
def beU32 (count : Nat) : List UInt8 :=
  [
    (count >>> 24 &&& 0xFF).toUInt8,
    (count >>> 16 &&& 0xFF).toUInt8,
    (count >>> 8 &&& 0xFF).toUInt8,
    (count &&& 0xFF).toUInt8
  ]

/-- The padding count: pad to an 8-byte boundary, at least 4 bytes (RFC 4253 §6). -/
def padFor (payloadLen : Nat) : Nat :=
  let paddingLength := 8 - ((5 + payloadLen) % 8)
  if paddingLength < 4 then paddingLength + 8 else paddingLength

/-- Serialize a transport packet (pre-encryption: no MAC). -/
def serializePacket (pkt : Packet) : List UInt8 :=
  let pad := padFor pkt.payload.length
  let packetLen := 1 + pkt.payload.length + pad
  beU32 packetLen ++ [pad.toUInt8] ++ pkt.payload ++ List.replicate pad 0

/-- Parse a transport packet, recovering the payload (and total bytes consumed). -/
def parsePacket (bytes : List UInt8) : Option (Packet × Nat) :=
  if bytes.length ≥ 5 then
    let packetLen :=
      (bytes.getD 0 0).toNat <<< 24 ||| (bytes.getD 1 0).toNat <<< 16
          ||| (bytes.getD 2 0).toNat <<< 8
          ||| (bytes.getD 3 0).toNat
    let padLen := (bytes.getD 4 0).toNat
    if bytes.length ≥ 4 + packetLen ∧ packetLen ≥ padLen + 1 then
      let plen := packetLen - padLen - 1
      some ({ payload := (List.range plen).map (fun idx => bytes.getD (5 + idx) 0) }, 4 + packetLen)
    else
      none
  else
    none

/-- The identification string a peer sends first: `SSH-2.0-<software>\r\n`. -/
def serializeVersion (software : String) : String := "SSH-2.0-" ++ software ++ "\r\n"

-- ── it round-trips, 8-aligned — canonical packets ─────────────────────────────

/-- "hello" round-trips and the whole packet is a multiple of 8 bytes. -/
example :
    let packet : Packet := { payload := [104, 101, 108, 108, 111] }
    (serializePacket packet).length % 8 = 0
        ∧ (parsePacket (serializePacket packet)).map Prod.fst = some packet := by native_decide

/-- The empty payload still pads to ≥ 4 and 8-aligns. -/
example :
    let packet : Packet := { payload := [] }
    (serializePacket packet).length = 16
        ∧ (parsePacket (serializePacket packet)).map Prod.fst = some packet := by native_decide

/-- A `KEXINIT` payload (msg byte 20) round-trips. -/
example :
    let packet : Packet := { payload := SSH_MSG_KEXINIT.toUInt8 :: List.replicate 20 0 }
    (parsePacket (serializePacket packet)).map Prod.fst = some packet := by native_decide

example : serializeVersion "Continuity_1.0" = "SSH-2.0-Continuity_1.0\r\n" := by native_decide

end Continuity.Codec.Wire.Ssh
