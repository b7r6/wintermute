/-
  Continuity.Codec.Wire.Http.Http2 - Verified HTTP/2 Frame Format

  HTTP/2 frame parsing with HPACK header compression.
  Reference: RFC 7540 (HTTP/2), RFC 7541 (HPACK)

  ## Frame Format

  +-----------------------------------------------+
  |                 Length (24)                   |
  +---------------+---------------+---------------+
  |   Type (8)    |   Flags (8)   |
  +-+-------------+---------------+-------------------------------+
  |R|                 Stream Identifier (31)                      |
  +=+=============================================================+
  |                   Frame Payload (0...)                      ...
  +---------------------------------------------------------------+

  ## Frame Types

  - DATA (0x0): Stream data
  - HEADERS (0x1): Header block
  - PRIORITY (0x2): Stream priority
  - RST_STREAM (0x3): Stream termination
  - SETTINGS (0x4): Connection settings
  - PUSH_PROMISE (0x5): Server push
  - PING (0x6): Connection liveness
  - GOAWAY (0x7): Connection shutdown
  - WINDOW_UPDATE (0x8): Flow control
  - CONTINUATION (0x9): Header continuation
-/

import continuity.codec.core.basic

namespace Continuity.Codec.Wire.Http.Http2

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME TYPES AND FLAGS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/2 frame types -/
inductive FrameType where
  | data         -- 0x0
  | headers      -- 0x1
  | priority     -- 0x2
  | rstStream    -- 0x3
  | settings     -- 0x4
  | pushPromise  -- 0x5
  | ping         -- 0x6
  | goaway       -- 0x7
  | windowUpdate -- 0x8
  | continuation -- 0x9
  deriving Repr, DecidableEq

def FrameType.toUInt8 : FrameType → UInt8
  | .data         => 0x0
  | .headers      => 0x1
  | .priority     => 0x2
  | .rstStream    => 0x3
  | .settings     => 0x4
  | .pushPromise  => 0x5
  | .ping         => 0x6
  | .goaway       => 0x7
  | .windowUpdate => 0x8
  | .continuation => 0x9

def FrameType.fromUInt8 : UInt8 → Option FrameType
  | 0x0 => some .data
  | 0x1 => some .headers
  | 0x2 => some .priority
  | 0x3 => some .rstStream
  | 0x4 => some .settings
  | 0x5 => some .pushPromise
  | 0x6 => some .ping
  | 0x7 => some .goaway
  | 0x8 => some .windowUpdate
  | 0x9 => some .continuation
  | _   => none

/-- Frame flags -/
structure frame_flags where
  raw : UInt8
  deriving Repr

namespace frame_flags
def endStream (function : frame_flags) : Bool := function.raw &&& 0x1 != 0

def ack (function : frame_flags) : Bool := function.raw &&& 0x1 != 0 -- Same bit, different meaning
def endHeaders (function : frame_flags) : Bool := function.raw &&& 0x4 != 0
def padded (function : frame_flags) : Bool := function.raw &&& 0x8 != 0
def priority (function : frame_flags) : Bool := function.raw &&& 0x20 != 0
end frame_flags

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME HEADER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/2 frame header (9 bytes) -/
structure FrameHeader where
  length    : UInt32      -- 24 bits (max 16384 default, 16777215 max)
  frameType : FrameType
  flags     : frame_flags
  streamId  : UInt32      -- 31 bits (high bit reserved)
  deriving Repr

/-- Maximum frame payload size -/
def MAX_FRAME_SIZE : UInt32 := 16384

def MAX_FRAME_SIZE_ALLOWED : UInt32 := 16777215

/-- Parse frame header (9 bytes, big-endian) -/
def parseFrameHeader (bytes : Bytes) : ParseResult FrameHeader :=
  if _h : bytes.size >= 9 then
    -- Length (24 bits, big-endian)
    let length := bytes[0]!.toUInt32 <<< 16
              ||| bytes[1]!.toUInt32 <<< 8
              ||| bytes[2]!.toUInt32
    -- Type (8 bits)
    let typeRaw := bytes[3]!
    match FrameType.fromUInt8 typeRaw with
    | none => .fail
    | some frameType =>
      -- Flags (8 bits)
      let flags := frame_flags.mk bytes[4]!
      -- Stream ID (31 bits, big-endian, high bit reserved)
      let streamId := (bytes[5]!.toUInt32 &&& 0x7F) <<< 24
                  ||| bytes[6]!.toUInt32 <<< 16
                  ||| bytes[7]!.toUInt32 <<< 8
                  ||| bytes[8]!.toUInt32
      .ok ⟨length, frameType, flags, streamId⟩ (bytes.extract 9 bytes.size)
  else .fail

/-- Serialize frame header -/
def serializeFrameHeader (evidence : FrameHeader) : Bytes :=
  ⟨
    #[
      ((evidence.length >>> 16) &&& 0xFF).toUInt8,
      ((evidence.length >>> 8) &&& 0xFF).toUInt8,
      (evidence.length &&& 0xFF).toUInt8,
      evidence.frameType.toUInt8,
      evidence.flags.raw,
      (((evidence.streamId >>> 24) &&& 0x7F).toUInt8), -- Mask high bit
      ((evidence.streamId >>> 16) &&& 0xFF).toUInt8,
      ((evidence.streamId >>> 8) &&& 0xFF).toUInt8,
      (evidence.streamId &&& 0xFF).toUInt8
    ]
  ⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME PAYLOADS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- DATA frame payload -/
structure DataPayload where
  padLength : Option UInt8 -- Present if PADDED flag set
  data      : Bytes
  deriving Repr

/-- HEADERS frame payload -/
structure headers_payload where
  padLength   : Option UInt8
  exclusive   : Option Bool   -- Present if PRIORITY flag set
  streamDep   : Option UInt32 -- Present if PRIORITY flag set
  weight      : Option UInt8  -- Present if PRIORITY flag set
  headerBlock : Bytes         -- HPACK-encoded headers
  deriving Repr

/-- PRIORITY frame payload (5 bytes) -/
structure PriorityPayload where
  exclusive : Bool
  streamDep : UInt32
  weight    : UInt8
  deriving Repr

/-- RST_STREAM frame payload (4 bytes) -/
structure rst_stream_payload where
  errorCode : UInt32
  deriving Repr

/-- SETTINGS frame payload -/
structure SettingsPayload where
  settings : List (UInt16 × UInt32) -- (identifier, value) pairs
  deriving Repr

/-- PUSH_PROMISE frame payload -/
structure push_promise_payload where
  padLength        : Option UInt8
  promisedStreamId : UInt32
  headerBlock      : Bytes
  deriving Repr

/-- PING frame payload (8 bytes) -/
structure ping_payload where
  opaqueData : Bytes -- Must be 8 bytes
  deriving Repr

/-- GOAWAY frame payload -/
structure GoawayPayload where
  lastStreamId : UInt32
  errorCode    : UInt32
  debugData    : Bytes
  deriving Repr

/-- WINDOW_UPDATE frame payload (4 bytes) -/
structure WindowUpdatePayload where
  windowSizeIncrement : UInt32 -- 31 bits
  deriving Repr

/-- Frame with payload -/
inductive Frame where
  | data (evidence : FrameHeader) (parser : DataPayload)
  | headers (evidence : FrameHeader) (parser : headers_payload)
  | priority (evidence : FrameHeader) (parser : PriorityPayload)
  | rstStream (evidence : FrameHeader) (parser : rst_stream_payload)
  | settings (evidence : FrameHeader) (parser : SettingsPayload)
  | pushPromise (evidence : FrameHeader) (parser : push_promise_payload)
  | ping (evidence : FrameHeader) (parser : ping_payload)
  | goaway (evidence : FrameHeader) (parser : GoawayPayload)
  | windowUpdate (evidence : FrameHeader) (parser : WindowUpdatePayload)
  | continuation (evidence : FrameHeader) (headerBlock : Bytes)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- PAYLOAD PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse DATA frame payload -/
def parseDataPayload (flags : frame_flags) (bytes : Bytes) : ParseResult DataPayload :=
  if flags.padded then
    if _h : bytes.size > 0 then
      let padLen := bytes[0]!
      let dataEnd := bytes.size - padLen.toNat
      if dataEnd <= 1 then
        .fail
      else
        let data := bytes.extract 1 dataEnd
        .ok ⟨some padLen, data⟩ Bytes.empty
    else
      .fail
  else
    .ok ⟨none, bytes⟩ Bytes.empty

/-- Parse PRIORITY payload (5 bytes) -/
def parsePriorityPayload (bytes : Bytes) : ParseResult PriorityPayload :=
  if _h : bytes.size >= 5 then
    let firstByte := bytes[0]!
    let exclusive := firstByte &&& 0x80 != 0
    let streamDep :=
      ((firstByte.toUInt32 &&& 0x7F) <<< 24) ||| bytes[1]!.toUInt32 <<< 16
          ||| bytes[2]!.toUInt32 <<< 8
          ||| bytes[3]!.toUInt32
    let weight := bytes[4]!
    .ok ⟨exclusive, streamDep, weight⟩ (bytes.extract 5 bytes.size)
  else
    .fail

/-- Parse SETTINGS payload -/
def parseSettingsPayload (bytes : Bytes) : ParseResult SettingsPayload :=
  if bytes.size % 6 != 0 then
    .fail
  else
    let rec parseSettings (remaining : Bytes) (result : List (UInt16 × UInt32)) (fuel : Nat) : ParseResult SettingsPayload :=
      match fuel with
      | 0 => .fail
      | fuel' + 1 =>
        if remaining.size == 0 then
          .ok ⟨result.reverse⟩ Bytes.empty
        else if _h : remaining.size >= 6 then
          let settingId := remaining[0]!.toUInt16 <<< 8 ||| remaining[1]!.toUInt16
          let value :=
            remaining[2]!.toUInt32 <<< 24 ||| remaining[3]!.toUInt32 <<< 16
                ||| remaining[4]!.toUInt32 <<< 8
                ||| remaining[5]!.toUInt32
          parseSettings (remaining.extract 6 remaining.size) ((settingId, value) :: result) fuel'
        else
          .fail
    parseSettings bytes [] (bytes.size / 6 + 1)

/-- Parse GOAWAY payload -/
def parseGoawayPayload (bytes : Bytes) : ParseResult GoawayPayload :=
  if _h : bytes.size >= 8 then
    let lastStreamId :=
      (bytes[0]!.toUInt32 &&& 0x7F) <<< 24 ||| bytes[1]!.toUInt32 <<< 16
          ||| bytes[2]!.toUInt32 <<< 8
          ||| bytes[3]!.toUInt32
    let errorCode :=
      bytes[4]!.toUInt32 <<< 24 ||| bytes[5]!.toUInt32 <<< 16 ||| bytes[6]!.toUInt32 <<< 8
          ||| bytes[7]!.toUInt32
    let debugData := bytes.extract 8 bytes.size
    .ok ⟨lastStreamId, errorCode, debugData⟩ Bytes.empty
  else
    .fail

/-- Parse WINDOW_UPDATE payload (4 bytes) -/
def parseWindowUpdatePayload (bytes : Bytes) : ParseResult WindowUpdatePayload :=
  if _h : bytes.size >= 4 then
    let increment :=
      (bytes[0]!.toUInt32 &&& 0x7F) <<< 24 ||| bytes[1]!.toUInt32 <<< 16
          ||| bytes[2]!.toUInt32 <<< 8
          ||| bytes[3]!.toUInt32
    .ok ⟨increment⟩ (bytes.extract 4 bytes.size)
  else
    .fail

private
def parseControlFramePayload
    (frameType : FrameType)
    (header : FrameHeader)
    (payload remaining : Bytes)
    : ParseResult Frame :=
  match frameType with
  | .ping => if payload.size != 8 then .fail else .ok (.ping header ⟨payload⟩) remaining
  | .rstStream =>
    if _h : payload.size >= 4 then
      let code :=
        payload[0]!.toUInt32 <<< 24 ||| payload[1]!.toUInt32 <<< 16 ||| payload[2]!.toUInt32 <<< 8
            ||| payload[3]!.toUInt32
      .ok (.rstStream header ⟨code⟩) remaining
    else
      .fail
  | .continuation => .ok (.continuation header payload) remaining
  | .headers => .ok (.headers header ⟨none, none, none, none, payload⟩) remaining
  | .pushPromise => .ok (.pushPromise header ⟨none, 0, payload⟩) remaining
  | _ => .fail

private
def parseFramePayload (header : FrameHeader) (payload remaining : Bytes) : ParseResult Frame :=
  match header.frameType with
  | .data =>
    match parseDataPayload header.flags payload with
    | .ok parsed _ => .ok (.data header parsed) remaining
    | .fail        => .fail
  | .priority =>
    match parsePriorityPayload payload with
    | .ok parsed _ => .ok (.priority header parsed) remaining
    | .fail        => .fail
  | .settings =>
    match parseSettingsPayload payload with
    | .ok parsed _ => .ok (.settings header parsed) remaining
    | .fail        => .fail
  | .goaway =>
    match parseGoawayPayload payload with
    | .ok parsed _ => .ok (.goaway header parsed) remaining
    | .fail        => .fail
  | .windowUpdate =>
    match parseWindowUpdatePayload payload with
    | .ok parsed _ => .ok (.windowUpdate header parsed) remaining
    | .fail        => .fail
  | frameType => parseControlFramePayload frameType header payload remaining

/-- Parse complete frame -/
def parseFrame (bytes : Bytes) : ParseResult Frame :=
  match parseFrameHeader bytes with
  | .fail => .fail
  | .ok header rest =>
    let payloadLen := header.length.toNat
    if rest.size < payloadLen then
      .fail
    else
      let payload := rest.extract 0 payloadLen
      let remaining := rest.extract payloadLen rest.size
      parseFramePayload header payload remaining

-- ═══════════════════════════════════════════════════════════════════════════════
-- HPACK (Header Compression)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HPACK integer encoding (prefix bits vary by context) -/
def parseHpackInt (prefixBits : Nat) (bytes : Bytes) : ParseResult Nat :=
  if _h : bytes.size > 0 && prefixBits ≤ 8 then
    let mask := (1 <<< prefixBits) - 1
    let firstByte := bytes[0]!.toNat &&& mask
    if firstByte < mask then
      .ok firstByte (bytes.extract 1 bytes.size)
    else
      -- Multi-byte encoding
      let rec parseVarint (index : Nat) (result : Nat) (shift : Nat) : ParseResult Nat :=
        if h2 : index < bytes.size then
          let byte := bytes[index]!
          let result' := result + ((byte.toNat &&& 0x7F) <<< shift)
          if byte &&& 0x80 == 0 then
            .ok (mask + result') (bytes.extract (index + 1) bytes.size)
          else
            parseVarint (index + 1) result' (shift + 7)
        else .fail
      termination_by bytes.size - index
      parseVarint 1 0 0
  else .fail

/-- Static table entry (predefined headers) -/
structure HpackEntry where
  name  : String
  value : String
  deriving Repr

private
def staticTableFirst : Array HpackEntry :=
  #[
    ⟨":authority", ""⟩,
    ⟨":method", "GET"⟩,
    ⟨":method", "POST"⟩,
    ⟨":path", "/"⟩,
    ⟨":path", "/index.html"⟩,
    ⟨":scheme", "http"⟩,
    ⟨":scheme", "https"⟩,
    ⟨":status", "200"⟩,
    ⟨":status", "204"⟩,
    ⟨":status", "206"⟩,
    ⟨":status", "304"⟩,
    ⟨":status", "400"⟩,
    ⟨":status", "404"⟩,
    ⟨":status", "500"⟩,
    ⟨"accept-charset", ""⟩,
    ⟨"accept-encoding", "gzip, deflate"⟩,
    ⟨"accept-language", ""⟩,
    ⟨"accept-ranges", ""⟩,
    ⟨"accept", ""⟩,
    ⟨"access-control-allow-origin", ""⟩,
    ⟨"age", ""⟩,
    ⟨"allow", ""⟩,
    ⟨"authorization", ""⟩,
    ⟨"cache-control", ""⟩,
    ⟨"content-disposition", ""⟩,
    ⟨"content-encoding", ""⟩,
    ⟨"content-language", ""⟩,
    ⟨"content-length", ""⟩,
    ⟨"content-location", ""⟩,
    ⟨"content-range", ""⟩,
    ⟨"content-type", ""⟩,
    ⟨"cookie", ""⟩
  ]

private
def staticTableSecond : Array HpackEntry :=
  #[
    ⟨"date", ""⟩,
    ⟨"etag", ""⟩,
    ⟨"expect", ""⟩,
    ⟨"expires", ""⟩,
    ⟨"from", ""⟩,
    ⟨"host", ""⟩,
    ⟨"if-match", ""⟩,
    ⟨"if-modified-since", ""⟩,
    ⟨"if-none-match", ""⟩,
    ⟨"if-range", ""⟩,
    ⟨"if-unmodified-since", ""⟩,
    ⟨"last-modified", ""⟩,
    ⟨"link", ""⟩,
    ⟨"location", ""⟩,
    ⟨"max-forwards", ""⟩,
    ⟨"proxy-authenticate", ""⟩,
    ⟨"proxy-authorization", ""⟩,
    ⟨"range", ""⟩,
    ⟨"referer", ""⟩,
    ⟨"refresh", ""⟩,
    ⟨"retry-after", ""⟩,
    ⟨"server", ""⟩,
    ⟨"set-cookie", ""⟩,
    ⟨"strict-transport-security", ""⟩,
    ⟨"transfer-encoding", ""⟩,
    ⟨"user-agent", ""⟩,
    ⟨"vary", ""⟩,
    ⟨"via", ""⟩,
    ⟨"www-authenticate", ""⟩
  ]

/-- HPACK static table (first 61 entries) -/
def staticTable : Array HpackEntry := staticTableFirst ++ staticTableSecond

-- ═══════════════════════════════════════════════════════════════════════════════
-- ERROR CODES
-- ═══════════════════════════════════════════════════════════════════════════════

inductive ErrorCode where
  | noError            -- 0x0
  | protocolError      -- 0x1
  | internalError      -- 0x2
  | flowControlError   -- 0x3
  | settingsTimeout    -- 0x4
  | streamClosed       -- 0x5
  | frameSizeError     -- 0x6
  | refusedStream      -- 0x7
  | cancel             -- 0x8
  | compressionError   -- 0x9
  | connectError       -- 0xa
  | enhanceYourCalm    -- 0xb
  | inadequateSecurity -- 0xc
  | http11Required     -- 0xd
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONNECTION STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Stream state -/
inductive StreamState where
  | idle
  | reservedLocal
  | reservedRemote
  | open_
  | halfClosedLocal
  | halfClosedRemote
  | closed
  deriving Repr, DecidableEq

/-- Connection settings -/
structure connection_settings where
  headerTableSize      : UInt32 := 4096
  enablePush           : Bool := true
  maxConcurrentStreams : Option UInt32 := none
  initialWindowSize    : UInt32 := 65535
  maxFrameSize         : UInt32 := 16384
  maxHeaderListSize    : Option UInt32 := none
  deriving Repr

end Continuity.Codec.Wire.Http.Http2
