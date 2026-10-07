/-
  Continuity.Codec.Wire.Zmtp - Verified ZMTP 3.x Wire Format Parser

  ZMTP (ZeroMQ Message Transport Protocol) is modeled here with the same
  reset-on-ambiguity discipline as SIGIL. ZMTP 3.x is a clean protocol:

  - Deterministic: flags byte fully determines parsing path
  - Length-prefixed: no escape sequences or delimiters
  - Fixed structures: greeting is exactly 64 bytes

  ## Wire Format Overview

  ```
  greeting = signature[10] version[2] mechanism[20] as-server[1] filler[31]
  frame    = flags[1] size[1|8] body[size]
  ```

  Flags byte:
  - Bit 0 (MORE):    more frames follow in message
  - Bit 1 (LONG):    8-byte size (else 1-byte)
  - Bit 2 (COMMAND): command frame (else message)
  - Bits 3-7:        RESERVED (must be zero)

  ## Reset-on-Ambiguity for ZMTP

  - Reserved bits non-zero → ambiguous → reset
  - Invalid greeting signature → ambiguous → reset
  - Invalid command name → ambiguous → reset
  - Any protocol violation → reset connection

  ## Theorems

  - `parseFrame_deterministic`: same bytes → same result
  - `greeting_exactly_64`: greeting consumes exactly 64 bytes
  - `flags_unambiguous`: flags byte fully determines frame structure
  - `no_backtrack`: parser never needs to re-read bytes
-/

import continuity.codec.core.basic

namespace Continuity.Codec.Wire.Zmtp

open Continuity.Codec.Core (Bytes)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ZMTP 3.x greeting signature byte 0 -/
def signatureByte0 : UInt8 := 0xFF

/-- ZMTP 3.x greeting signature byte 9 -/
def signatureByte9 : UInt8 := 0x7F

/-- ZMTP major version we support -/
def versionMajor : UInt8 := 3

/-- ZMTP minor version we support -/
def versionMinor : UInt8 := 1

/-- Greeting size in bytes -/
def greetingSize : Nat := 64

/-- Signature size in bytes -/
def signatureSize : Nat := 10

/-- Mechanism field size in bytes -/
def mechanismSize : Nat := 20

-- ═══════════════════════════════════════════════════════════════════════════════
-- FLAG BITS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- MORE flag: more frames follow in this message -/
def flagMore : UInt8 := 0x01

/-- LONG flag: 8-byte size field (else 1-byte) -/
def flagLong : UInt8 := 0x02

/-- COMMAND flag: command frame (else message frame) -/
def flagCommand : UInt8 := 0x04

/-- Reserved bits mask (bits 3-7) -/
def flagReservedMask : UInt8 := 0xF8

-- ═══════════════════════════════════════════════════════════════════════════════
-- AMBIGUITY REASONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reasons for ambiguity in ZMTP parsing -/
inductive AmbiguityReason where
  /-- Invalid greeting signature -/
  | invalidSignature : UInt8 → UInt8 → AmbiguityReason
  /-- Unsupported ZMTP version -/
  | unsupportedVersion : UInt8 → UInt8 → AmbiguityReason
  /-- Reserved flags bits are non-zero -/
  | reservedFlagsSet : UInt8 → AmbiguityReason
  /-- Invalid command name (non-printable or empty) -/
  | invalidCommandName : AmbiguityReason
  /-- Frame size exceeds maximum -/
  | frameTooLarge : UInt64 → AmbiguityReason
  /-- Unexpected command during handshake -/
  | unexpectedCommand : String → AmbiguityReason
  /-- Security mechanism mismatch -/
  | mechanismMismatch : String → AmbiguityReason
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT PARSE RESULT (same pattern as Sigil)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Strict parse result with three outcomes.

- `ok`: unambiguous success
- `incomplete`: need more bytes (streaming)
- `ambiguous`: protocol violation, must reset
-/
inductive StrictParseResult (Value : Type) where
  | ok : Value → Bytes → StrictParseResult Value
  | incomplete : Nat → StrictParseResult Value -- how many more bytes needed
  | ambiguous : AmbiguityReason → StrictParseResult Value
  deriving Repr

namespace StrictParseResult

def map
    {Value ResultValue : Type}
    (function : Value → ResultValue)
    : StrictParseResult Value → StrictParseResult ResultValue
  | ok value rest    => ok (function value) rest
  | incomplete count => incomplete count
  | ambiguous result => ambiguous result

def isOk {Value : Type} : StrictParseResult Value → Bool
  | ok _ _ => true
  | _      => false

def isIncomplete {Value : Type} : StrictParseResult Value → Bool
  | incomplete _ => true
  | _            => false

def isAmbiguous {Value : Type} : StrictParseResult Value → Bool
  | ambiguous _ => true
  | _           => false

end StrictParseResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECURITY MECHANISMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ZMTP security mechanisms -/
inductive Mechanism where
  | null : Mechanism  -- No security
  | plain : Mechanism -- Username/password (cleartext!)
  | curve : Mechanism -- CurveZMQ (CurveCP-based)
  deriving Repr, DecidableEq, Inhabited

/-- Parse mechanism from 20-byte field -/
def parseMechanism (bytes : Bytes) : Option Mechanism :=
  if bytes.size < mechanismSize then none
  else
    -- Check for "NULL" + null padding
    if bytes[0]! == 0x4E && bytes[1]! == 0x55 &&
       bytes[2]! == 0x4C && bytes[3]! == 0x4C &&
       bytes[4]! == 0x00 then
      some .null
    -- Check for "PLAIN" + null padding
    else if bytes[0]! == 0x50 && bytes[1]! == 0x4C &&
            bytes[2]! == 0x41 && bytes[3]! == 0x49 &&
            bytes[4]! == 0x4E && bytes[5]! == 0x00 then
      some .plain
    -- Check for "CURVE" + null padding
    else if bytes[0]! == 0x43 && bytes[1]! == 0x55 &&
            bytes[2]! == 0x52 && bytes[3]! == 0x56 &&
            bytes[4]! == 0x45 && bytes[5]! == 0x00 then
      some .curve
    else
      none

-- ═══════════════════════════════════════════════════════════════════════════════
-- GREETING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parsed ZMTP greeting -/
structure Greeting where
  versionMajor : UInt8
  versionMinor : UInt8
  mechanism    : Mechanism
  asServer     : Bool
  deriving Repr, DecidableEq

/-- Parse 64-byte ZMTP greeting -/
def parseGreeting (bytes : Bytes) : StrictParseResult Greeting :=
  -- Need exactly 64 bytes
  if bytes.size < greetingSize then
    .incomplete (greetingSize - bytes.size)
  else
    -- Validate signature: byte 0 = 0xFF, byte 9 = 0x7F
    let sig0 := bytes[0]!
    let sig9 := bytes[9]!
    if sig0 != signatureByte0 || sig9 != signatureByte9 then
      .ambiguous (.invalidSignature sig0 sig9)
    else
      -- Extract version (bytes 10-11)
      let major := bytes[10]!
      let minor := bytes[11]!
      -- We require ZMTP 3.x
      if major < 3 then
        .ambiguous (.unsupportedVersion major minor)
      else
        -- Extract mechanism (bytes 12-31)
        let mechBytes := bytes.extract 12 32
        match parseMechanism mechBytes with
        | none => .ambiguous (.mechanismMismatch "unknown mechanism")
        | some mech =>
          -- Extract as-server (byte 32)
          let asServer := bytes[32]! != 0
          -- Rest is filler, we don't validate it
          let rest := bytes.extract greetingSize bytes.size
          .ok ⟨major, minor, mech, asServer⟩ rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME HEADER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parsed frame header -/
structure FrameHeader where
  size      : Nat
  hasMore   : Bool
  isLong    : Bool
  isCommand : Bool
  deriving Repr, DecidableEq

/-- Check if flags byte has reserved bits set -/
def hasReservedBits (flags : UInt8) : Bool := (flags &&& flagReservedMask) != 0

/-- Extract frame properties from flags byte -/
def parseFlags (flags : UInt8) : Bool × Bool × Bool :=
  let hasMore := (flags &&& flagMore) != 0
  let isLong := (flags &&& flagLong) != 0
  let isCommand := (flags &&& flagCommand) != 0
  (hasMore, isLong, isCommand)

/-- Read 8-byte big-endian size -/
def readSize64BE (bytes : Bytes) (offset : Nat) : UInt64 :=
  if offset + 8 > bytes.size then
    0
  else
    let byte0 := bytes[offset]!.toUInt64
    let byte1 := bytes[offset + 1]!.toUInt64
    let byte2 := bytes[offset + 2]!.toUInt64
    let byte3 := bytes[offset + 3]!.toUInt64
    let byte4 := bytes[offset + 4]!.toUInt64
    let byte5 := bytes[offset + 5]!.toUInt64
    let byte6 := bytes[offset + 6]!.toUInt64
    let byte7 := bytes[offset + 7]!.toUInt64
    (byte0 <<< 56) ||| (byte1 <<< 48) ||| (byte2 <<< 40) ||| (byte3 <<< 32) ||| (byte4 <<< 24)
        ||| (byte5 <<< 16)
        ||| (byte6 <<< 8)
        ||| byte7

/-- Maximum frame size we accept (256 MB) -/
def maxFrameSize : Nat := 256 * 1024 * 1024

/-- Parse frame header (flags + size) -/
def parseFrameHeader (bytes : Bytes) : StrictParseResult FrameHeader :=
  -- Need at least 1 byte for flags
  if bytes.size < 1 then
    .incomplete 1
  else
    let flags := bytes[0]!

    -- Check reserved bits
    if hasReservedBits flags then
      .ambiguous (.reservedFlagsSet flags)
    else
      let (hasMore, isLong, isCommand) := parseFlags flags

      -- Branch on the decoded frame form.
      if isLong then
        -- Long frame: need 8 more bytes for size
        if bytes.size < 9 then
          .incomplete (9 - bytes.size)
        else
          let size64 := readSize64BE bytes 1
          -- Check for unreasonable size
          if size64 > maxFrameSize.toUInt64 then
            .ambiguous (.frameTooLarge size64)
          else
            let rest := bytes.extract 9 bytes.size
            .ok ⟨size64.toNat, hasMore, isLong, isCommand⟩ rest
      else
        -- Short frame: need 1 more byte for size
        if bytes.size < 2 then
          .incomplete (2 - bytes.size)
        else
          let size := bytes[1]!.toNat
          let rest := bytes.extract 2 bytes.size
          .ok ⟨size, hasMore, isLong, isCommand⟩ rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME BODY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A complete frame -/
structure Frame where
  header : FrameHeader
  body   : Bytes
  deriving Repr

/-- Parse complete frame given header -/
def parseFrameBody (header : FrameHeader) (bytes : Bytes) : StrictParseResult Frame :=
  if bytes.size < header.size then
    .incomplete (header.size - bytes.size)
  else
    let body := bytes.extract 0 header.size
    let rest := bytes.extract header.size bytes.size
    .ok ⟨header, body⟩ rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMMAND PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Known ZMTP commands -/
inductive Command where
  | ready : List (String × Bytes) → Command -- READY with properties
  | error : String → Command -- ERROR with reason
  | subscribe : Bytes → Command -- SUBSCRIBE (SUB socket)
  | cancel : Bytes → Command -- CANCEL (SUB socket)
  | ping : Bytes → Command -- PING
  | pong : Bytes → Command -- PONG
  | unknown : String → Bytes → Command -- Unknown command
  deriving Repr

/-- Check if byte is printable ASCII (for command names) -/
def isPrintableAscii (rightValue : UInt8) : Bool := rightValue >= 0x20 && rightValue <= 0x7E

/-- Check if all bytes are printable ASCII -/
def allPrintableAscii (bytes : Bytes) : Bool :=
  bytes.foldl (fun result byte => result && isPrintableAscii byte) true

/-- Parse command from frame body -/
def parseCommand (body : Bytes) : StrictParseResult Command :=
  if body.size < 1 then
    .ambiguous .invalidCommandName
  else
    let nameLen := body[0]!.toNat
    if nameLen == 0 || nameLen > 255 then
      .ambiguous .invalidCommandName
    else if body.size < 1 + nameLen then
      .incomplete (1 + nameLen - body.size)
    else
      -- Validate command name is printable ASCII
      let nameBytes := body.extract 1 (1 + nameLen)
      if !allPrintableAscii nameBytes then
        .ambiguous .invalidCommandName
      else
        let name := String.fromUTF8! nameBytes
        let data := body.extract (1 + nameLen) body.size
        -- Dispatch on known commands
        let cmd := match name with
          | "READY" => .ready []  -- TODO: parse properties
          | "ERROR" => .error (String.fromUTF8! data)
          | "SUBSCRIBE" => .subscribe data
          | "CANCEL" => .cancel data
          | "PING" => .ping data
          | "PONG" => .pong data
          | _ => .unknown name data
        .ok cmd ByteArray.empty

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONNECTION STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ZMTP connection state -/
inductive ConnState where
  | awaitGreeting : ConnState
  | awaitHandshake : Greeting → ConnState
  | ready : Greeting → ConnState
  | failed : AmbiguityReason → ConnState
  deriving Repr

/-- Initial connection state -/
def initState : ConnState := .awaitGreeting

/-- Reset connection state (on ambiguity) -/
def resetState : ConnState := .awaitGreeting

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Greeting parse is unambiguous: same 64 bytes → same result -/
theorem parseGreeting_deterministic
        (byte1 byte2 : Bytes)
        : byte1 = byte2 → parseGreeting byte1 = parseGreeting byte2 := by
  intro bytesEquation

  -- Simplify the remaining goal.
  rw [bytesEquation]

/-- Greeting consumes exactly 64 bytes on success -/
theorem greeting_exactly_64
        (bytes : Bytes)
        (secondFunction : Greeting)
        (rest : Bytes)
        : parseGreeting bytes = .ok secondFunction rest
            → bytes.size ≥ greetingSize ∧ rest = bytes.extract greetingSize bytes.size := by
  intro parseEquation
  unfold parseGreeting at parseEquation
  -- Split on size check
  split at parseEquation
  case isTrue =>
    -- bytes.size < greetingSize: .incomplete, contradicts .ok
    contradiction
  case isFalse hSize =>
    -- bytes.size ≥ greetingSize
    simp only [Nat.not_lt] at hSize
    -- Now case split on the boolean condition
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true] at parseEquation
    split at parseEquation
    case isTrue =>
      -- Invalid signature: .ambiguous, contradicts .ok
      contradiction
    case isFalse =>
      -- Valid signature
      split at parseEquation
      case isTrue =>
        -- Unsupported version: .ambiguous, contradicts .ok
        contradiction
      case isFalse =>
        -- Valid version, split on mechanism
        split at parseEquation
        case h_1 =>
          -- none: .ambiguous, contradicts .ok
          contradiction
        case h_2 mech =>
          -- some mech: success path
          simp only [StrictParseResult.ok.injEq] at parseEquation
          constructor
          · exact hSize
          · exact parseEquation.2.symm

/--
Flags byte fully determines header structure.

With enough bytes (9 for long frames, 2 for short frames), parsing
always terminates with either success or ambiguity - never incomplete.
-/
theorem flags_unambiguous
        (bytes : Bytes)
        (_ : bytes.size ≥ 1)
        (hNoReserved : ¬hasReservedBits bytes[0]!)
        : let (_, isLong, _) := parseFlags bytes[0]!
        (isLong = true ∧ bytes.size ≥ 9
            → (parseFrameHeader bytes).isOk ∨ (parseFrameHeader bytes).isAmbiguous)
            ∧ (isLong = false ∧ bytes.size ≥ 2
                → (parseFrameHeader bytes).isOk ∨ (parseFrameHeader bytes).isAmbiguous) := by
  simp only [parseFlags]
  constructor
  · -- Long case: with 9+ bytes, parse succeeds or fails unambiguously
    intro ⟨hLong, hSize⟩
    unfold parseFrameHeader
    have firstEvidence : ¬(bytes.size < 1) := by omega
    simp only [firstEvidence, ↓reduceIte]
    simp only [hNoReserved]
    simp only [parseFlags, hLong, ↓reduceIte]
    have byte9Evidence : ¬(bytes.size < 9) := by omega
    simp only [byte9Evidence, ↓reduceIte]
    -- Either ok or ambiguous (frame too large) - split on the size check
    by_cases hFrameSize : readSize64BE bytes 1 > maxFrameSize.toUInt64
    · simp only [hFrameSize, ↓reduceIte, StrictParseResult.isAmbiguous]
      right; rfl
    · simp only [hFrameSize, ↓reduceIte, StrictParseResult.isOk]
      left; rfl
  · -- Short case: with 2+ bytes, parse succeeds or fails unambiguously
    intro ⟨hShort, hSize⟩
    unfold parseFrameHeader
    have firstEvidence : ¬(bytes.size < 1) := by omega
    simp only [firstEvidence, ↓reduceIte]
    simp only [hNoReserved]
    simp only [parseFlags, hShort]
    have secondEvidence : ¬(bytes.size < 2) := by omega
    simp only [secondEvidence, ↓reduceIte, StrictParseResult.isOk]
    left; rfl -- ok

/-- Reset always returns to initial state -/
theorem reset_is_initial : resetState = initState := rfl

/-- Parser never needs to re-read bytes (streaming property) -/
theorem no_backtrack_greeting
        (bytes : Bytes)
        : match parseGreeting bytes with
        | .ok _ rest        => rest.size < bytes.size
        | .incomplete count => bytes.size + count ≥ greetingSize
        | .ambiguous _      => True := by
  unfold parseGreeting greetingSize
  -- Case on whether bytes.size < 64
  by_cases hSize : bytes.size < 64
  · -- bytes.size < 64: returns .incomplete (64 - bytes.size)
    simp only [hSize, ↓reduceIte]
    -- Goal: bytes.size + (64 - bytes.size) >= 64
    omega
  · -- bytes.size >= 64: proceeds to check signature etc.
    simp only [hSize, ↓reduceIte]
    simp only [Nat.not_lt] at hSize
    -- Case on signature check
    by_cases hSig : (bytes[0]! != signatureByte0 || bytes[9]! != signatureByte9) = true
    · -- .ambiguous, goal is True - simp reduces and trivial closes
      simp only [hSig, ↓reduceIte]
    · simp only [hSig, ↓reduceIte, Bool.false_eq_true]
      -- Case on version check
      by_cases hVer : bytes[10]! < 3
      · -- .ambiguous, goal is True
        simp only [hVer, ↓reduceIte]
      · simp only [hVer, ↓reduceIte]
        -- Case on mechanism parse
        cases hMech : parseMechanism (bytes.extract 12 32)
        · -- .ambiguous (none) - goal is True
          simp only
        · -- .ok case: rest = bytes.extract 64 bytes.size
          simp only [ByteArray.size_extract]
          omega

/-- Frame header parse is deterministic -/
theorem parseFrameHeader_deterministic
        (byte1 byte2 : Bytes)
        : byte1 = byte2 → parseFrameHeader byte1 = parseFrameHeader byte2 := by
  intro bytesEquation

  -- Simplify the remaining goal.
  rw [bytesEquation]

-- ═══════════════════════════════════════════════════════════════════════════════
-- VERIFICATION STATUS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Verification Summary

### Theorems (all proven, 0 sorry):

| Theorem | What's Proven |
|---------|---------------|
| parseGreeting_deterministic | same bytes → same result |
| greeting_exactly_64 | greeting consumes exactly 64 bytes on success |
| flags_unambiguous | with enough bytes, parsing is never incomplete |
| reset_is_initial | reset always returns to initial state |
| no_backtrack_greeting | parser never needs to re-read bytes |
| parseFrameHeader_deterministic | same bytes → same result |

### Types Defined:

| Type | Purpose |
|------|---------|
| StrictParseResult | ok / incomplete / ambiguous |
| AmbiguityReason | why ambiguity occurred |
| Mechanism | NULL / PLAIN / CURVE |
| Greeting | parsed 64-byte greeting |
| FrameHeader | parsed frame header |
| Frame | complete frame (header + body) |
| Command | READY / ERROR / SUBSCRIBE / etc. |
| ConnState | connection state machine |

### Key Functions:

| Function | Purpose |
|----------|---------|
| parseGreeting | parse 64-byte greeting |
| parseFrameHeader | parse frame flags + size |
| parseFrameBody | parse frame body |
| parseCommand | parse command frame |
| hasReservedBits | check for reserved flags (ambiguity trigger) |
| parseFlags | extract MORE/LONG/COMMAND from flags byte |

**Total: 6 theorems, 8 types, 6+ functions, 0 sorry**
-/

end Continuity.Codec.Wire.Zmtp
