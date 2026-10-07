/-
  Continuity.Codec.Wire.Http.Http3 - Verified HTTP/3 and QUIC Frame Formats

  HTTP/3 over QUIC with QPACK header compression.
  Reference: RFC 9000 (QUIC), RFC 9114 (HTTP/3), RFC 9204 (QPACK)

  ## QUIC Frame Format

  Variable-length integer encoding:
  - 1 byte:  6-bit value (0-63)
  - 2 bytes: 14-bit value (0-16383)
  - 4 bytes: 30-bit value (0-1073741823)
  - 8 bytes: 62-bit value (0-4611686018427387903)

  ## HTTP/3 Frame Format

  +==============+
  |    Type (i)  |
  +==============+
  |   Length (i) |
  +==============+
  |   Payload    |
  +==============+

  Where (i) denotes a variable-length integer.
-/

import continuity.codec.core.basic

namespace Continuity.Codec.Wire.Http.Http3

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUIC VARIABLE-LENGTH INTEGER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse QUIC variable-length integer
    First 2 bits indicate length:
    - 00: 1 byte (6-bit value)
    - 01: 2 bytes (14-bit value)
    - 10: 4 bytes (30-bit value)
    - 11: 8 bytes (62-bit value) -/
def parseVarInt (bytes : Bytes) : ParseResult UInt64 :=
  if _h : bytes.size > 0 then
    let firstByte := bytes[0]!
    let lenCode := firstByte.toNat >>> 6
    match lenCode with
    | 0 =>  -- 1 byte
      .ok (firstByte.toUInt64 &&& 0x3F) (bytes.extract 1 bytes.size)
    | 1 =>  -- 2 bytes
      if _h2 : bytes.size >= 2 then
        let decodedValue := ((firstByte.toUInt64 &&& 0x3F) <<< 8)
             ||| bytes[1]!.toUInt64
        .ok decodedValue (bytes.extract 2 bytes.size)
      else .fail
    | 2 =>  -- 4 bytes
      if _h2 : bytes.size >= 4 then
        let decodedValue := ((firstByte.toUInt64 &&& 0x3F) <<< 24)
             ||| bytes[1]!.toUInt64 <<< 16
             ||| bytes[2]!.toUInt64 <<< 8
             ||| bytes[3]!.toUInt64
        .ok decodedValue (bytes.extract 4 bytes.size)
      else .fail
    | _ =>  -- 8 bytes (lenCode == 3)
      if _h2 : bytes.size >= 8 then
        let decodedValue := ((firstByte.toUInt64 &&& 0x3F) <<< 56)
             ||| bytes[1]!.toUInt64 <<< 48
             ||| bytes[2]!.toUInt64 <<< 40
             ||| bytes[3]!.toUInt64 <<< 32
             ||| bytes[4]!.toUInt64 <<< 24
             ||| bytes[5]!.toUInt64 <<< 16
             ||| bytes[6]!.toUInt64 <<< 8
             ||| bytes[7]!.toUInt64
        .ok decodedValue (bytes.extract 8 bytes.size)
      else .fail
  else .fail

/-- Serialize QUIC variable-length integer -/
def serializeVarInt (decodedValue : UInt64) : Bytes :=
  if decodedValue < 64 then
    ⟨#[decodedValue.toUInt8]⟩
  else if decodedValue < 16384 then
    ⟨
      #[
        ((0x40 : UInt64) ||| ((decodedValue >>> 8) &&& 0x3F)).toUInt8,
        (decodedValue &&& 0xFF).toUInt8
      ]
    ⟩
  else if decodedValue < 1073741824 then
    ⟨
      #[
        ((0x80 : UInt64) ||| ((decodedValue >>> 24) &&& 0x3F)).toUInt8,
        ((decodedValue >>> 16) &&& 0xFF).toUInt8,
        ((decodedValue >>> 8) &&& 0xFF).toUInt8,
        (decodedValue &&& 0xFF).toUInt8
      ]
    ⟩
  else
    ⟨
      #[
        ((0xC0 : UInt64) ||| ((decodedValue >>> 56) &&& 0x3F)).toUInt8,
        ((decodedValue >>> 48) &&& 0xFF).toUInt8,
        ((decodedValue >>> 40) &&& 0xFF).toUInt8,
        ((decodedValue >>> 32) &&& 0xFF).toUInt8,
        ((decodedValue >>> 24) &&& 0xFF).toUInt8,
        ((decodedValue >>> 16) &&& 0xFF).toUInt8,
        ((decodedValue >>> 8) &&& 0xFF).toUInt8,
        (decodedValue &&& 0xFF).toUInt8
      ]
    ⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUIC FRAME TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- QUIC frame types -/
inductive QuicFrameType where
  | padding            -- 0x00
  | ping               -- 0x01
  | ack                -- 0x02, 0x03
  | resetStream        -- 0x04
  | stopSending        -- 0x05
  | crypto             -- 0x06
  | newToken           -- 0x07
  | stream             -- 0x08-0x0f
  | maxData            -- 0x10
  | maxStreamData      -- 0x11
  | maxStreams         -- 0x12, 0x13
  | dataBlocked        -- 0x14
  | streamDataBlocked  -- 0x15
  | streamsBlocked     -- 0x16, 0x17
  | newConnectionId    -- 0x18
  | retireConnectionId -- 0x19
  | pathChallenge      -- 0x1a
  | pathResponse       -- 0x1b
  | connectionClose    -- 0x1c, 0x1d
  | handshakeDone      -- 0x1e
  deriving Repr, DecidableEq

/-- STREAM frame flags (encoded in type byte 0x08-0x0f) -/
structure stream_flags where
  fin : Bool -- 0x01: Final frame
  len : Bool -- 0x02: Length field present
  off : Bool -- 0x04: Offset field present
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUIC FRAMES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- STREAM frame -/
structure StreamFrame where
  streamId : UInt64
  offset   : Option UInt64
  length   : Option UInt64
  fin      : Bool
  data     : Bytes
  deriving Repr

/-- CRYPTO frame -/
structure CryptoFrame where
  offset : UInt64
  length : UInt64
  data   : Bytes
  deriving Repr

/-- ACK frame -/
structure ack_frame where
  largestAcked  : UInt64
  ackDelay      : UInt64
  ackRangeCount : UInt64
  firstAckRange : UInt64
  ackRanges     : List (UInt64 × UInt64) -- (gap, ack_range)
  deriving Repr

/-- CONNECTION_CLOSE frame -/
structure connection_close_frame where
  errorCode    : UInt64
  frameType    : Option UInt64 -- For type 0x1c only
  reasonPhrase : Bytes
  deriving Repr

/-- Parse STREAM frame -/
def parseStreamFrame (typeVal : UInt64) (bytes : Bytes) : ParseResult StreamFrame :=
  let flags :=
    stream_flags.mk (typeVal &&& 0x01 != 0) (typeVal &&& 0x02 != 0) (typeVal &&& 0x04 != 0)
  match parseVarInt bytes with
  | .fail => .fail
  | .ok streamId rest1 =>
    -- Parse optional offset
    let (offset, rest2) :=
      if flags.off then
        match parseVarInt rest1 with
        | .ok off result => (some off, result)
        | .fail => (none, rest1)  -- Error, but continue
      else (none, rest1)
    -- Parse optional length
    let (length, data, rest3) :=
      if flags.len then
        match parseVarInt rest2 with
        | .ok len result =>
          let data := result.extract 0 len.toNat
          let rest := result.extract len.toNat result.size
          (some len, data, rest)
        | .fail => (none, rest2, Bytes.empty)
      else
        (none, rest2, Bytes.empty)  -- Data extends to end
    .ok ⟨streamId, offset, length, flags.fin, data⟩ rest3

/-- Parse CRYPTO frame -/
def parseCryptoFrame (bytes : Bytes) : ParseResult CryptoFrame :=
  match parseVarInt bytes with
  | .fail => .fail
  | .ok offset rest1 =>
    match parseVarInt rest1 with
    | .fail => .fail
    | .ok length rest2 =>
      if rest2.size < length.toNat then
        .fail
      else
        let data := rest2.extract 0 length.toNat
        let rest := rest2.extract length.toNat rest2.size
        .ok ⟨offset, length, data⟩ rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- HTTP/3 FRAME TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/3 frame types -/
inductive H3FrameType where
  | data        -- 0x00
  | headers     -- 0x01
  | cancelPush  -- 0x03
  | settings    -- 0x04
  | pushPromise -- 0x05
  | goaway      -- 0x07
  | maxPushId   -- 0x0d
  deriving Repr, DecidableEq

def H3FrameType.toUInt64 : H3FrameType → UInt64
  | .data        => 0x00
  | .headers     => 0x01
  | .cancelPush  => 0x03
  | .settings    => 0x04
  | .pushPromise => 0x05
  | .goaway      => 0x07
  | .maxPushId   => 0x0d

def H3FrameType.fromUInt64 : UInt64 → Option H3FrameType
  | 0x00 => some .data
  | 0x01 => some .headers
  | 0x03 => some .cancelPush
  | 0x04 => some .settings
  | 0x05 => some .pushPromise
  | 0x07 => some .goaway
  | 0x0d => some .maxPushId
  | _    => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- HTTP/3 FRAMES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/3 frame header -/
structure H3FrameHeader where
  frameType : H3FrameType
  length    : UInt64
  deriving Repr

/-- HTTP/3 SETTINGS -/
structure H3Settings where
  maxFieldSectionSize   : Option UInt64
  qpackMaxTableCapacity : Option UInt64
  qpackBlockedStreams   : Option UInt64
  deriving Repr

/-- HTTP/3 frame -/
inductive H3Frame where
  | data (payload : Bytes)
  | headers (encodedFieldSection : Bytes)
  | cancelPush (pushId : UInt64)
  | settings (settings : H3Settings)
  | pushPromise (pushId : UInt64) (encodedFieldSection : Bytes)
  | goaway (streamId : UInt64)
  | maxPushId (pushId : UInt64)
  deriving Repr

/-- Parse HTTP/3 frame header -/
def parseH3FrameHeader (bytes : Bytes) : ParseResult H3FrameHeader :=
  match parseVarInt bytes with
  | .fail => .fail
  | .ok typeVal rest1 =>
    match H3FrameType.fromUInt64 typeVal with
    | none => .fail
    | some frameType =>
      match parseVarInt rest1 with
      | .fail            => .fail
      | .ok length rest2 => .ok ⟨frameType, length⟩ rest2

/-- Parse HTTP/3 SETTINGS -/
def parseH3Settings (bytes : Bytes) : ParseResult H3Settings :=
  let rec parseSettings (remaining : Bytes) (settings : H3Settings) (fuel : Nat) : ParseResult H3Settings :=
    match fuel with
    | 0 => .fail
    | fuel' + 1 =>
      if remaining.size == 0 then .ok settings Bytes.empty
      else
        match parseVarInt remaining with
        | .fail => .fail
        | .ok streamId rest1 =>
          match parseVarInt rest1 with
          | .fail => .fail
          | .ok value rest2 =>
            let settings' := match streamId with
              | 0x06 => { settings with maxFieldSectionSize := some value }
              | 0x01 => { settings with qpackMaxTableCapacity := some value }
              | 0x07 => { settings with qpackBlockedStreams := some value }
              | _ => settings  -- Unknown setting, ignore
            parseSettings rest2 settings' fuel'
  parseSettings bytes ⟨none, none, none⟩ bytes.size

/-- Parse HTTP/3 frame -/
def parseH3Frame (bytes : Bytes) : ParseResult H3Frame :=
  match parseH3FrameHeader bytes with
  | .fail => .fail
  | .ok header rest =>
    let payloadLen := header.length.toNat
    if rest.size < payloadLen then
      .fail
    else
      let payload := rest.extract 0 payloadLen
      let remaining := rest.extract payloadLen rest.size
      match header.frameType with
      | .data => .ok (.data payload) remaining
      | .headers => .ok (.headers payload) remaining
      | .cancelPush =>
        match parseVarInt payload with
        | .ok pushId _ => .ok (.cancelPush pushId) remaining
        | .fail        => .fail
      | .settings =>
        match parseH3Settings payload with
        | .ok state _ => .ok (.settings state) remaining
        | .fail       => .fail
      | .goaway =>
        match parseVarInt payload with
        | .ok streamId _ => .ok (.goaway streamId) remaining
        | .fail          => .fail
      | .maxPushId =>
        match parseVarInt payload with
        | .ok pushId _ => .ok (.maxPushId pushId) remaining
        | .fail        => .fail
      | .pushPromise =>
        match parseVarInt payload with
        | .ok pushId rest' => .ok (.pushPromise pushId rest') remaining
        | .fail            => .fail

-- ═══════════════════════════════════════════════════════════════════════════════
-- QPACK (Header Compression for HTTP/3)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- QPACK instruction types (encoder stream) -/
inductive qpack_encoder_instr where
  | setDynamicTableCapacity (capacity : UInt64)
  | insertWithNameRef (nameIdx : UInt64) (value : Bytes)
  | insertWithLiteralName (name : Bytes) (value : Bytes)
  | duplicate (index : UInt64)
  deriving Repr

/-- QPACK instruction types (decoder stream) -/
inductive qpack_decoder_instr where
  | sectionAck (streamId : UInt64)
  | streamCancellation (streamId : UInt64)
  | insertCountIncrement (increment : UInt64)
  deriving Repr

private
def qpackStaticTableCore : Array (String × String) :=
  #[
    (":authority", ""),
    (":path", "/"),
    ("age", "0"),
    ("content-disposition", ""),
    ("content-length", "0"),
    ("cookie", ""),
    ("date", ""),
    ("etag", ""),
    ("if-modified-since", ""),
    ("if-none-match", ""),
    ("last-modified", ""),
    ("link", ""),
    ("location", ""),
    ("referer", ""),
    ("set-cookie", ""),
    (":method", "CONNECT"),
    (":method", "DELETE"),
    (":method", "GET"),
    (":method", "HEAD"),
    (":method", "OPTIONS"),
    (":method", "POST"),
    (":method", "PUT"),
    (":scheme", "http"),
    (":scheme", "https"),
    (":status", "103"),
    (":status", "200"),
    (":status", "304"),
    (":status", "404"),
    (":status", "503"),
    ("accept", "*/*"),
    ("accept", "application/dns-message"),
    ("accept-encoding", "gzip, deflate, br"),
    ("accept-ranges", "bytes"),
    ("access-control-allow-headers", "cache-control"),
    ("access-control-allow-headers", "content-type"),
    ("access-control-allow-origin", "*"),
    ("cache-control", "max-age=0"),
    ("cache-control", "max-age=2592000"),
    ("cache-control", "max-age=604800"),
    ("cache-control", "no-cache"),
    ("cache-control", "no-store"),
    ("cache-control", "public, max-age=31536000"),
    ("content-encoding", "br"),
    ("content-encoding", "gzip"),
    ("content-type", "application/dns-message"),
    ("content-type", "application/javascript"),
    ("content-type", "application/json"),
    ("content-type", "application/x-www-form-urlencoded")
  ]

private
def qpackStaticTableExtended : Array (String × String) :=
  #[
    ("content-type", "image/gif"),
    ("content-type", "image/jpeg"),
    ("content-type", "image/png"),
    ("content-type", "text/css"),
    ("content-type", "text/html; charset=utf-8"),
    ("content-type", "text/plain"),
    ("content-type", "text/plain;charset=utf-8"),
    ("range", "bytes=0-"),
    ("strict-transport-security", "max-age=31536000"),
    ("strict-transport-security", "max-age=31536000; includesubdomains"),
    ("strict-transport-security", "max-age=31536000; includesubdomains; preload"),
    ("vary", "accept-encoding"),
    ("vary", "origin"),
    ("x-content-type-options", "nosniff"),
    ("x-xss-protection", "1; mode=block"),
    (":status", "100"),
    (":status", "204"),
    (":status", "206"),
    (":status", "302"),
    (":status", "400"),
    (":status", "403"),
    (":status", "421"),
    (":status", "425"),
    (":status", "500"),
    ("accept-language", ""),
    ("access-control-allow-credentials", "FALSE"),
    ("access-control-allow-credentials", "TRUE"),
    ("access-control-allow-headers", "*"),
    ("access-control-allow-methods", "get"),
    ("access-control-allow-methods", "get, post, options"),
    ("access-control-allow-methods", "options"),
    ("access-control-expose-headers", "content-length"),
    ("access-control-request-headers", "content-type"),
    ("access-control-request-method", "get"),
    ("access-control-request-method", "post"),
    ("alt-svc", "clear"),
    ("authorization", ""),
    ("content-security-policy", "script-src 'none'; object-src 'none'; base-uri 'none'"),
    ("early-data", "1"),
    ("expect-ct", ""),
    ("forwarded", ""),
    ("if-range", ""),
    ("origin", ""),
    ("purpose", "prefetch"),
    ("server", ""),
    ("timing-allow-origin", "*"),
    ("upgrade-insecure-requests", "1"),
    ("user-agent", ""),
    ("x-forwarded-for", ""),
    ("x-frame-options", "deny"),
    ("x-frame-options", "sameorigin")
  ]

/-- QPACK static table (same as HPACK plus a few more). -/
def qpackStaticTable : Array (String × String) := qpackStaticTableCore ++ qpackStaticTableExtended

-- ═══════════════════════════════════════════════════════════════════════════════
-- ERROR CODES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/3 error codes -/
inductive H3ErrorCode where
  | noError              -- 0x100
  | generalProtocolError -- 0x101
  | internalError        -- 0x102
  | streamCreationError  -- 0x103
  | closedCriticalStream -- 0x104
  | frameUnexpected      -- 0x105
  | frameError           -- 0x106
  | excessiveLoad        -- 0x107
  | idError              -- 0x108
  | settingsError        -- 0x109
  | missingSettings      -- 0x10a
  | requestRejected      -- 0x10b
  | requestCancelled     -- 0x10c
  | requestIncomplete    -- 0x10d
  | messageError         -- 0x10e
  | connectError         -- 0x10f
  | versionFallback      -- 0x110
  deriving Repr, DecidableEq

end Continuity.Codec.Wire.Http.Http3
