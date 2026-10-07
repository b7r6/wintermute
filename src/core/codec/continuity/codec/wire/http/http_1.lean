import continuity.codec.core.scanner
import continuity.codec.wire.http.headers
import continuity.codec.core.bytes

/-!
  HTTP/1.1 Scanner — request/response parsing via delimiter scanning.

  Power level: Scanner (delimiter-based, one-way).
  NOT a Box (no serialize — HTTP is asymmetric, request ≠ response).

  Parses: request line, status line, headers, content-length body, chunked body.
-/

namespace Continuity.Codec.Wire.Http.Http1

open Continuity.Codec.Core.Scanner
open Continuity.Codec.Core
open Continuity.Codec.Wire.Http.Headers

-- ════════════════════════════════════════════════════════════════════════════
-- §1 STATUS LINE (HTTP response)
-- ════════════════════════════════════════════════════════════════════════════

structure HttpStatusLine where
  version      : String -- "HTTP/1.1"
  statusCode   : Nat    -- 200, 404, etc.
  reasonPhrase : String -- "OK", "Not Found", etc.
  deriving Repr

private
def bytesToNat (bytes : Bytes) : Option Nat :=
  let digits := bytes.toList.map fun byte => byte.toNat - 48
  if digits.all (· < 10) && !digits.isEmpty then
    some (digits.foldl (fun decimalValue digit => decimalValue * 10 + digit) 0)
  else
    none

def scanHttpStatusLine : Scanner HttpStatusLine where
  consumption := fun _ _ _ => trivial
  scan bs :=
    match (scanUntilByte SPACE).scan bs with
    | .found versionBytes rest1 =>
      match (scanUntilByte SPACE).scan rest1 with
      | .found codeBytes rest2 =>
        match scanCRLFLine.scan rest2 with
        | .found reasonBytes rest3 =>
          match String.fromUTF8? versionBytes, bytesToNat codeBytes, String.fromUTF8? reasonBytes with
          | some value, some code, some result => .found ⟨value, code, result⟩ rest3
          | _, _, _ => .notFound
        | .notFound => .notFound
        | .incomplete count => .incomplete count
      | .notFound => .notFound
      | .incomplete count => .incomplete count
    | .notFound => .notFound
    | .incomplete count => .incomplete count

-- ════════════════════════════════════════════════════════════════════════════
-- §2 FULL HTTP REQUEST
-- ════════════════════════════════════════════════════════════════════════════

structure HttpRequest where
  method  : String
  uri     : String
  version : String
  headers : List HttpHeader
  body    : Bytes
  deriving Repr

-- ════════════════════════════════════════════════════════════════════════════
-- §2a ASCII CASE-INSENSITIVE COMPARISON (allocation-free)
-- ════════════════════════════════════════════════════════════════════════════

/-- Byte `i` of the UTF-8 encoding of `s`. Constant time, no allocation. -/
@[inline]
private
def utf8Byte (state : String) (index : Nat) (evidence : index < state.utf8ByteSize) : UInt8 :=
  state.getUTF8Byte ⟨index⟩ (String.Pos.Raw.lt_iff.mpr evidence)

/-- ASCII case fold: uppercase letters `'A'..'Z'` map to `'a'..'z'` (`+ 32`);
    every other byte — including all bytes of multi-byte UTF-8 sequences,
    which are `≥ 0x80` — is unchanged. -/
@[inline]
def foldAsciiCase (byte : UInt8) : UInt8 :=
  if byte >= 0x41 && byte <= 0x5A then byte + 0x20 else byte

/-- `true` iff `byte` encodes ASCII whitespace: space, tab, CR, or LF —
    exactly the set trimmed by `String.trimAscii`. -/
@[inline]
def isAsciiWhitespaceByte (byte : UInt8) : Bool :=
  byte == 0x20 || byte == 0x09 || byte == 0x0D || byte == 0x0A

/-- Compare `fuel` bytes of `a` (from index `i`) against `byte` (from index `j`)
    under ASCII case folding. `false` if either range runs off its string. -/
private
def eqFoldAsciiFrom (leftValue byte : String) (index nextIndex fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if ha : index < leftValue.utf8ByteSize then
      if hb : nextIndex < byte.utf8ByteSize then
        foldAsciiCase (utf8Byte leftValue index ha) == foldAsciiCase (utf8Byte byte nextIndex hb)
            && eqFoldAsciiFrom leftValue byte (index + 1) (nextIndex + 1) fuel
      else
        false
    else
      false

/-- ASCII case-insensitive string equality without allocation: walks the UTF-8
    bytes of both strings in place (no `String.toLower` copies). ASCII letters
    compare case-insensitively; all other bytes compare exactly. Agrees with
    `a.toLower == byte.toLower` for every input, since `Char.toLower` folds only
    `'A'..'Z'`. -/
def eqIgnoreAsciiCase (leftValue byte : String) : Bool :=
  leftValue.utf8ByteSize == byte.utf8ByteSize
      && eqFoldAsciiFrom leftValue byte 0 0 leftValue.utf8ByteSize

/-- First index `≥ i` in `s` that is not ASCII whitespace (or `s.utf8ByteSize`). -/
private
def skipWsLeft (state : String) (index fuel : Nat) : Nat :=
  match fuel with
  | 0 => index
  | fuel + 1 =>
    if h : index < state.utf8ByteSize then
      if isAsciiWhitespaceByte (utf8Byte state index h) then
        skipWsLeft state (index + 1) fuel
      else
        index
    else
      index

/-- Exclusive end index of `s` after dropping ASCII whitespace below `stop`. -/
private
def skipWsRight (state : String) (stop fuel : Nat) : Nat :=
  match fuel, stop with
  | 0, _ => stop
  | _ + 1, 0 => 0
  | fuel + 1, index + 1 =>
    if h : index < state.utf8ByteSize then
      if isAsciiWhitespaceByte (utf8Byte state index h) then
        skipWsRight state index fuel
      else
        index + 1
    else
      index + 1

/-- ASCII case-insensitive equality of `a` against `byte`, ignoring ASCII
    whitespace surrounding `a`. Trimming adjusts byte-index bounds only — no
    trimmed string is allocated. Agrees with
    `a.trimAscii.toString.toLower == byte.toLower` for lowercase-ASCII `byte`. -/
def eqIgnoreAsciiCaseTrim (leftValue byte : String) : Bool :=
  let trimStart := skipWsLeft leftValue 0 leftValue.utf8ByteSize
  let trimEnd := skipWsRight leftValue leftValue.utf8ByteSize leftValue.utf8ByteSize
  trimEnd - trimStart == byte.utf8ByteSize
      && eqFoldAsciiFrom leftValue byte trimStart 0 byte.utf8ByteSize

private
def findContentLength (headers : List HttpHeader) : Option Nat :=
  headers.find? (fun header => eqIgnoreAsciiCase header.name "content-length")
    |>.bind (fun boundProof => boundProof.value.trimAscii.toString.toNat?)

private
def isChunked (headers : List HttpHeader) : Bool :=
  headers.any
    (fun header =>
      eqIgnoreAsciiCase header.name "transfer-encoding"
          && eqIgnoreAsciiCaseTrim header.value "chunked")
-- §3 CHUNKED TRANSFER ENCODING
-- chunk = chunk-size CRLF chunk-data CRLF
-- last-chunk = "0" CRLF CRLF
-- ════════════════════════════════════════════════════════════════════════════

private
def hexToNat (bytes : Bytes) : Option Nat :=
  let digits :=
    bytes.toList.map fun byte =>
      if byte >= 0x30 && byte <= 0x39 then
        some (byte.toNat - 0x30)
      else if byte >= 0x41 && byte <= 0x46 then
        some (byte.toNat - 0x41 + 10)
      else if byte >= 0x61 && byte <= 0x66 then some (byte.toNat - 0x61 + 10) else none
  if digits.any (·.isNone) || digits.isEmpty then
    none
  else
    some (digits.foldl (fun hexValue digit => hexValue * 16 + digit.getD 0) 0)

def scanChunkedBody : Scanner Bytes where
  consumption := fun _ _ _ => trivial
  scan bs :=
    let rec scanChunks (bodyBytes : ByteArray) (remaining : Bytes) (fuel : Nat) : scan_result Bytes :=
      match fuel with
      | 0 => .found bodyBytes remaining  -- safety valve
      | fuel' + 1 =>
        -- Read chunk size (hex) until CRLF
        match scanCRLFLine.scan remaining with
        | .found sizeLine rest1 =>
          match hexToNat sizeLine with
          | some 0 =>
            -- Last chunk. Skip trailing CRLF.
            match (exact CRLF).scan rest1 with
            | .found () rest2 => .found bodyBytes rest2
            | _ => .found bodyBytes rest1  -- tolerate missing trailing CRLF
          | some count =>
            if rest1.size >= count + 2 then  -- chunk data + CRLF
              let chunk := rest1.extract 0 count
              let afterCrlf := rest1.extract (count + 2) rest1.size
              scanChunks (bodyBytes ++ chunk) afterCrlf fuel'
            else .incomplete (count + 2 - rest1.size)
          | none => .notFound  -- invalid chunk size
        | .notFound => .notFound
        | .incomplete count => .incomplete count
    scanChunks ByteArray.empty bs bs.size

-- ════════════════════════════════════════════════════════════════════════════
def scanHttpRequest : Scanner HttpRequest where
  consumption := fun _ _ _ => trivial
  scan bs :=
    match scanHttpRequestLine.scan bs with
    | .found reqLine rest1 =>
      match scanHttpHeaders.scan rest1 with
      | .found headers rest2 =>
        -- Determine body handling
        if isChunked headers then
          -- Chunked: scan chunks (see §3)
          match scanChunkedBody.scan rest2 with
          | .found body rest3 => .found ⟨reqLine.method, reqLine.uri, reqLine.version, headers, body⟩ rest3
          | .notFound => .notFound
          | .incomplete count => .incomplete count
        else match findContentLength headers with
          | some len =>
            -- Content-Length: take exactly len bytes
            if rest2.size >= len then
              .found ⟨reqLine.method, reqLine.uri, reqLine.version, headers,
                      rest2.extract 0 len⟩ (rest2.extract len rest2.size)
            else .incomplete (len - rest2.size)
          | none =>
            -- No body
            .found ⟨reqLine.method, reqLine.uri, reqLine.version, headers, ByteArray.empty⟩ rest2
      | .notFound => .notFound
      | .incomplete count => .incomplete count
    | .notFound => .notFound
    | .incomplete count => .incomplete count

-- ════════════════════════════════════════════════════════════════════════════
-- §4 FULL HTTP RESPONSE
-- ════════════════════════════════════════════════════════════════════════════

structure HttpResponse where
  version      : String
  statusCode   : Nat
  reasonPhrase : String
  headers      : List HttpHeader
  body         : Bytes
  deriving Repr

def scanHttpResponse : Scanner HttpResponse where
  consumption := fun _ _ _ => trivial
  scan bs :=
    match scanHttpStatusLine.scan bs with
    | .found statusLine rest1 =>
      match scanHttpHeaders.scan rest1 with
      | .found headers rest2 =>
        if isChunked headers then
          match scanChunkedBody.scan rest2 with
          | .found body rest3 =>
            .found
              ⟨statusLine.version, statusLine.statusCode, statusLine.reasonPhrase, headers, body⟩
              rest3
          | .notFound => .notFound
          | .incomplete count => .incomplete count
        else
          match findContentLength headers with
          | some len =>
            if rest2.size >= len then
              .found
                ⟨
                  statusLine.version,
                  statusLine.statusCode,
                  statusLine.reasonPhrase,
                  headers,
                  rest2.extract 0 len
                ⟩
                (rest2.extract len rest2.size)
            else
              .incomplete (len - rest2.size)
          | none =>
            .found
              ⟨
                statusLine.version,
                statusLine.statusCode,
                statusLine.reasonPhrase,
                headers,
                ByteArray.empty
              ⟩
              rest2
      | .notFound => .notFound
      | .incomplete count => .incomplete count
    | .notFound => .notFound
    | .incomplete count => .incomplete count

-- ════════════════════════════════════════════════════════════════════════════
-- §4b FRAME-ONLY SCANNER  (Tier-0 hot-path optimization of §2 / §4)
--
-- A trusted, allocation-light optimization of the proven `scanHttpRequest` /
-- `scanHttpResponse` above (UNTOUCHED — this is BESIDE them). It returns ONLY the
-- consumed byte length of one complete HTTP message (the frame boundary), plus a
-- span for the `Host` value — no String extraction, no header List, no struct.
-- The reverse proxy forwards the raw wire bytes verbatim, so the frame length +
-- the routing key are the ONLY things it ever needs from a parse.
--
-- CORRECTNESS DISCIPLINE. `scanHttpFrame`'s consumed length is pinned to the
-- proven scanners, byte-for-byte, by the differential conformance test
-- `framescan-gate` (aleph/tests/FrameScanGate.lean): over a corpus of real
-- request/response wire-strings (Content-Length incl. 0, chunked, pipelined,
-- byte-segmented) it asserts `scanHttpFrame` consumed == `acc.size - rest.size`
-- from the proven scanner wherever the header block is complete, and that
-- `scanHttpFrame` never frames before the header block terminator arrives. This
-- differential test IS the discipline: the frame scanner is a trusted optimization
-- of a proven reference, mechanically checked against it.
--
-- The one intentional divergence: a response with neither Content-Length nor
-- Transfer-Encoding: chunked is connection-close delimited; we return `.incomplete`
-- (wait) rather than mis-frame it as a zero-length body. A keepalive origin never
-- sends one, so the proxy never hits it.
-- ════════════════════════════════════════════════════════════════════════════

/-- The header/body separator `\r\n\r\n`. -/
private
def CRLFCRLF : Bytes := ⟨#[0x0D, 0x0A, 0x0D, 0x0A]⟩

private
def clNeedle : Bytes := "content-length".toUTF8

private
def teNeedle : Bytes := "transfer-encoding".toUTF8

private
def chunkedNeedle : Bytes := "chunked".toUTF8

private
def hostNeedle : Bytes := "host".toUTF8

/-- First index `i ∈ [p, limit)` with `bs[i]=CR ∧ bs[i+1]=LF`, else none. Direct
    ByteArray indexing (no allocation). Fuel is `bs.size`; the `i+1 ≥ limit` guard
    terminates well inside it. -/
private
def crlfFrom (bytes : Bytes) (parser limit : Nat) : Option Nat :=
  let rec findCrlf (index fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if index + 1 ≥ limit then
        none
      else if bytes[index]! == CR && bytes[index+1]! == LF then
        some index
      else
        findCrlf (index + 1) fuel'
  findCrlf parser bytes.size

/-- First index `i ∈ [p, limit)` with `bs[i] = ':'`, else none. -/
private
def colonFrom (bytes : Bytes) (parser limit : Nat) : Option Nat :=
  let rec findColon (index fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if index ≥ limit then
        none
      else if bytes[index]! == (0x3A : UInt8) then some index else findColon (index + 1) fuel'
  findColon parser bytes.size

/-- Advance past leading ASCII whitespace in `[s, e)`. -/
private
def trimStart (bytes : Bytes) (state element : Nat) : Nat :=
  let rec advanceTrimStart (index fuel : Nat) : Nat :=
    match fuel with
    | 0 => index
    | fuel' + 1 =>
      if index < element && isAsciiWhitespaceByte bytes[index]! then
        advanceTrimStart (index + 1) fuel'
      else
        index
  advanceTrimStart state bytes.size

/-- Retract past trailing ASCII whitespace in `[s, e)` (never below `s`). -/
private
def trimEnd (bytes : Bytes) (state element : Nat) : Nat :=
  let rec retractTrimEnd (nextIndex fuel : Nat) : Nat :=
    match fuel with
    | 0 => nextIndex
    | fuel' + 1 =>
      if nextIndex > state && isAsciiWhitespaceByte bytes[nextIndex-1]! then
        retractTrimEnd (nextIndex - 1) fuel'
      else
        nextIndex
  retractTrimEnd element bytes.size

/-- ASCII case-insensitive equality of the byte range `[s, e)` against a
    lowercase-ASCII `needle`, in place (no extract). -/
private
def rangeFoldEq (bytes : Bytes) (state element : Nat) (needle : Bytes) : Bool :=
  if element - state != needle.size then
    false
  else
    let rec compareFoldedRange (key fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel' + 1 =>
        if key ≥ needle.size then
          true
        else if foldAsciiCase bytes[state+key]! == foldAsciiCase needle[key]! then
          compareFoldedRange (key + 1) fuel'
        else
          false
    compareFoldedRange 0 needle.size

/-- Trimmed value span `(start, len)` of the FIRST header line in `[lineStart,
    bodyStart)` whose name matches `name` (case-insensitive). None if absent.
    Mirrors `headers.find? (eqIgnoreAsciiCase ·.name name)` on the raw bytes:
    walks each `name: value\r\n` line via `crlfFrom`, stopping at the blank line. -/
private
def headerValueRange
    (bytes : Bytes)
    (name : Bytes)
    (lineStart bodyStart : Nat)
    : Option (Nat × Nat) :=
  let rec findHeaderValue (parser fuel : Nat) : Option (Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match crlfFrom bytes parser bodyStart with
      | none => none
      | some code =>
        if code ≤ parser then none                      -- blank line: end of header block
        else
          match colonFrom bytes parser code with
          | none => findHeaderValue (code + 2) fuel'             -- no colon: skip malformed line
          | some col =>
            if rangeFoldEq bytes parser col name then
              let valueStart := trimStart bytes (col + 1) code
              let valueEnd := trimEnd bytes valueStart code
              some (valueStart, valueEnd - valueStart)
            else findHeaderValue (code + 2) fuel'
  findHeaderValue lineStart bytes.size

/-- `true` iff a `Transfer-Encoding: chunked` header is present (first TE header,
    value trimmed + case-folded == "chunked"). Mirrors `isChunked`. -/
private
def teIsChunked (bytes : Bytes) (lineStart bodyStart : Nat) : Bool :=
  match headerValueRange bytes teNeedle lineStart bodyStart with
  | none                => false
  | some (values, vlen) => rangeFoldEq bytes values (values + vlen) chunkedNeedle

/-- Content-Length value (first CL header, decimal, in place). None if the header
    is absent OR its value is not a plain decimal — matching `findContentLength`
    (`find?` then `toNat?`), which then falls through to the no-body path. -/
private
def contentLengthOf (bytes : Bytes) (lineStart bodyStart : Nat) : Option Nat :=
  match headerValueRange bytes clNeedle lineStart bodyStart with
  | none => none
  | some (values, vlen) =>
    let valueStart := values
    let valueEnd := values + vlen
    if valueEnd ≤ valueStart then
      none
    else
      let rec parseDecimalLength (index decimalValue fuel : Nat) : Option Nat :=
        match fuel with
        | 0 => some decimalValue
        | fuel' + 1 =>
          if index ≥ valueEnd then
            some decimalValue
          else
            let byte := bytes[index]!
            if byte ≥ 0x30 && byte ≤ 0x39 then
              parseDecimalLength (index + 1) (decimalValue * 10 + (byte.toNat - 0x30)) fuel'
            else
              none
      parseDecimalLength valueStart 0 (valueEnd - valueStart)

/-- One hex digit's value, or none. -/
private
def hexDigit (byte : UInt8) : Option Nat :=
  if byte ≥ 0x30 && byte ≤ 0x39 then
    some (byte.toNat - 0x30)
  else if byte ≥ 0x41 && byte ≤ 0x46 then
    some (byte.toNat - 0x41 + 10)
  else if byte ≥ 0x61 && byte ≤ 0x66 then some (byte.toNat - 0x61 + 10) else none

/-- Parse the byte range `[s, e)` as a hex chunk-size (non-empty, all hex), or
    none. Mirrors `hexToNat`. -/
private
def hexRange (bytes : Bytes) (state element : Nat) : Option Nat :=
  if element ≤ state then
    none
  else
    let rec parseHexRange (index hexValue fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => some hexValue
      | fuel' + 1 =>
        if index ≥ element then
          some hexValue
        else
          match hexDigit bytes[index]! with
          | some digit => parseHexRange (index + 1) (hexValue * 16 + digit) fuel'
          | none       => none
    parseHexRange state 0 (element - state)

/-- Frame a chunked body starting at byte `p`; returns the absolute end index
    (`.found endIdx rest`), mirroring `scanChunkedBody` byte-for-byte — including
    its tolerance of a missing trailing CRLF after the 0-chunk. -/
private
def frameChunked (bytes : Bytes) (parser : Nat) : scan_result Nat :=
  let rec frameChunks (continuation fuel : Nat) : scan_result Nat :=
    match fuel with
    | 0 => .found continuation (bytes.extract continuation bytes.size)          -- safety valve (== scanChunkedBody)
    | fuel' + 1 =>
      match crlfFrom bytes continuation bytes.size with
      | none => .notFound
      | some code =>
        match hexRange bytes continuation code with
        | none => .notFound
        | some 0 =>
          let chunkEnd := code + 2                            -- last chunk; consume trailing CRLF if present
          if chunkEnd + 2 ≤ bytes.size && bytes[chunkEnd]! == CR && bytes[chunkEnd+1]! == LF then
            .found (chunkEnd + 2) (bytes.extract (chunkEnd + 2) bytes.size)
          else
            .found chunkEnd (bytes.extract chunkEnd bytes.size)
        | some count =>
          let chunkEnd := code + 2                            -- chunk data + CRLF = n + 2 bytes
          if bytes.size ≥ chunkEnd + count + 2 then frameChunks (chunkEnd + count + 2) fuel'
          else .incomplete (count + 2 - (bytes.size - chunkEnd))
  -- Fuel = REMAINING byte count (`bs.size - p`), matching `scanChunkedBody`'s
  -- `frameChunks … bs.size` where its `bs` is the post-header remainder: an empty chunked
  -- body (p == bs.size) hits the fuel-0 safety valve exactly as the proven scanner does.
  frameChunks parser (bytes.size - parser)

/-- `true` iff `bs` begins with `"HTTP/"` — i.e. it is a response status line,
    not a request line (whose first token is a method). -/
private
def startsWithHTTP (bytes : Bytes) : Bool :=
  bytes.size ≥ 5 && bytes[0]! == (0x48 : UInt8) && bytes[1]! == (0x54 : UInt8)
      && bytes[2]! == (0x54 : UInt8)
      && bytes[3]! == (0x50 : UInt8)
      && bytes[4]! == (0x2F : UInt8)

/-- Frame ONE complete HTTP message (request OR response), returning the consumed
    byte count as `.found consumed rest`, `.incomplete n` (need more), or
    `.notFound` (malformed). A trusted framing-length optimization of the proven
    `scanHttpRequest`/`scanHttpResponse`, pinned to them by `framescan-gate`.

    Body length is read IN PLACE: `Transfer-Encoding: chunked` (chunk-size lines
    to the 0-chunk) takes precedence, else Content-Length, else no body (request)
    or connection-close (response → `.incomplete`, so it waits rather than
    mis-frames). No `String.fromUTF8?`, no header List, no struct is allocated. -/
def scanHttpFrame (bytes : Bytes) : scan_result Nat :=
  match findBytes CRLFCRLF bytes with
  | none => .incomplete 1 -- header block not yet terminated
  | some termIdx =>
    let bodyStart := termIdx + 4
    match crlfFrom bytes 0 bodyStart with
    | none => .notFound -- no request/status line
    | some firstCrlf =>
      let lineStart := firstCrlf + 2
      if teIsChunked bytes lineStart bodyStart then
        frameChunked bytes bodyStart
      else
        match contentLengthOf bytes lineStart bodyStart with
        | some len =>
          if bytes.size ≥ bodyStart + len then
            .found (bodyStart + len) (bytes.extract (bodyStart + len) bytes.size)
          else
            .incomplete (bodyStart + len - bytes.size)
        | none =>
          if startsWithHTTP bytes then .incomplete 1      -- connection-close response
          else .found bodyStart (bytes.extract bodyStart bytes.size) -- request: no body

/-- Byte span `(start, len)` of the `Host:` header value (case-insensitive name
    match, value trimmed) — the CHBL routing key, extracted with NO String
    re-encode. None if the message has no Host header. -/
def hostValueRange (bytes : Bytes) : Option (Nat × Nat) :=
  match findBytes CRLFCRLF bytes with
  | none => none
  | some termIdx =>
    match crlfFrom bytes 0 (termIdx + 4) with
    | none           => none
    | some firstCrlf => headerValueRange bytes hostNeedle (firstCrlf + 2) (termIdx + 4)

-- ════════════════════════════════════════════════════════════════════════════
-- §4c  RFC-7230 §3 FRAMING GRAMMAR + SOUNDNESS OF `scanHttpFrame`
--
-- `IsH1Frame bs n` is an INDEPENDENT, declarative statement of "the first `n`
-- bytes of `bs` are exactly one complete HTTP/1 message per RFC-7230 §3". It is
-- written as a message grammar (request-line ⟨CRLF⟩ · header-field-lines ⟨CRLF⟩ ·
-- empty ⟨CRLF⟩ · body) with the body length fixed by RFC §3.3.3, over a
-- from-scratch LIST-based header model (`h1Fields`) that materializes the whole
-- field list — the opposite of `scanHttpFrame`, which decides framing in place
-- with early exit and never builds a list. `scanHttpFrame_sound` proves the
-- in-place scanner refines this grammar (SOUNDNESS: every frame it reports is a
-- genuine RFC frame). Low-level lexical primitives (CRLF line split, colon
-- name/value split, OWS trim, ASCII digit / hex value) are shared with the
-- scanner — they are RFC lexical tokens, not the framing logic; the framing
-- logic (which header sizes the body, the §3.3.3 precedence, the chunk grammar,
-- the header-block boundary) is stated independently here.
-- ════════════════════════════════════════════════════════════════════════════

/-- A CRLF pair sits at byte `i` (RFC-7230 line terminator). -/
def CrlfAt (bytes : Bytes) (index : Nat) : Prop := bytes[index]! = CR ∧ bytes[index+1]! = LF

/-- The header/body separator `\r\n\r\n` starts at byte `t`. -/
def CrlfCrlfAt (bytes : Bytes) (token : Nat) : Prop :=
  bytes[token]! = CR ∧ bytes[token+1]! = LF ∧ bytes[token+2]! = CR ∧ bytes[token+3]! = LF

-- ── `crlfFrom` characterization (first CRLF in `[p, limit)`) ──────────────────

private
theorem crlfFrom.go_sound
        (bytes : Bytes)
        (limit : Nat)
        : ∀ (index fuel cursor : Nat),
            crlfFrom.findCrlf bytes limit index fuel = some cursor
                → index ≤ cursor
                    ∧ cursor + 1 < limit
                    ∧ bytes[cursor]! = CR
                    ∧ bytes[cursor+1]! = LF
                    ∧ (∀ j, index ≤ j → j < cursor → ¬CrlfAt bytes j) := by
  intro startIndex fuel
  induction fuel generalizing startIndex with
  | zero =>
    intro foundIndex scanEquation
    rw [crlfFrom.findCrlf] at scanEquation
    exact absurd scanEquation (by simp)
  | succ remainingFuel inductionHypothesis =>
    intro foundIndex scanEquation
    rw [crlfFrom.findCrlf] at scanEquation
    split at scanEquation
    · exact absurd scanEquation (by simp)
    · rename_i hlim
      split at scanEquation
      · rename_i hcr
        obtain rfl : foundIndex = startIndex := (Option.some.inj scanEquation).symm
        have hcr' : bytes[foundIndex]! = CR ∧ bytes[foundIndex+1]! = LF := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcr; exact hcr
        refine ⟨Nat.le_refl _, by omega, hcr'.1, hcr'.2, ?_⟩
        intro candidateIndex hStartCandidate hCandidateFound; omega
      · rename_i hcr
        obtain ⟨_, hlc, hcrc, hlfc, hfirst⟩ :=
          inductionHypothesis (startIndex + 1) foundIndex scanEquation
        refine ⟨by omega, hlc, hcrc, hlfc, ?_⟩
        intro candidateIndex hStartCandidate hCandidateFound
        rcases Nat.eq_or_lt_of_le hStartCandidate with hji | hji
        · subst hji
          simp only [CrlfAt, Bool.and_eq_true, beq_iff_eq] at hcr ⊢; exact hcr
        · exact hfirst candidateIndex hji hCandidateFound

/-- If `crlfFrom bs p limit = some c`, then `c` is the first CRLF at or after `p`
    and strictly inside `limit`. -/
private
theorem crlfFrom_sound
        (bytes : Bytes)
        (parser limit cursor : Nat)
        (evidence : crlfFrom bytes parser limit = some cursor)
        : parser ≤ cursor
            ∧ cursor + 1 < limit
            ∧ CrlfAt bytes cursor
            ∧ (∀ j, parser ≤ j → j < cursor → ¬CrlfAt bytes j) := by
  unfold crlfFrom at evidence

  -- Establish the next intermediate fact.
  obtain ⟨startBound, limitBound, crByte, lfByte, firstCrlf⟩ :=
    crlfFrom.go_sound bytes limit parser bytes.size cursor evidence

  -- Close the remaining goal.
  exact ⟨startBound, limitBound, ⟨crByte, lfByte⟩, firstCrlf⟩

-- ── Independent list-based header model (RFC-7230 §3.2) ───────────────────────

/-- The header field-lines of `[p, bodyStart)` as `(nameLo, nameHi, valLo, valHi)`
    — name span and OWS-trimmed value span — parsed by walking CRLF-delimited lines
    and splitting each at its first colon (dropping colon-less lines), stopping at
    the empty line. A from-scratch reference parser that materializes the WHOLE
    field list (unlike `scanHttpFrame`, which searches in place with early exit). -/
def h1Fields (bytes : Bytes) (bodyStart parser fuel : Nat) : List (Nat × Nat × Nat × Nat) :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    match crlfFrom bytes parser bodyStart with
    | none => []
    | some code =>
      if code ≤ parser then
        []
      else
        match colonFrom bytes parser code with
        | none => h1Fields bytes bodyStart (code + 2) fuel'
        | some col =>
          let valueStart := trimStart bytes (col + 1) code
          let valueEnd := trimEnd bytes valueStart code
          (parser, col, valueStart, valueEnd) :: h1Fields bytes bodyStart (code + 2) fuel'

/-- First field value span `(start, len)` whose name case-folds to `name`. -/
def h1Lookup (bytes name : Bytes) (parser bodyStart : Nat) : Option (Nat × Nat) :=
  ((h1Fields bytes bodyStart parser bytes.size).find?
    (fun fieldRange => rangeFoldEq bytes fieldRange.1 fieldRange.2.1 name)).map
    (fun field => (field.2.2.1, field.2.2.2 - field.2.2.1))

/-- RFC §3.3.1 chunked declaration: the first `Transfer-Encoding` field value
    case-folds to `chunked`. -/
def h1IsChunked (bytes : Bytes) (parser bodyStart : Nat) : Bool :=
  match h1Lookup bytes teNeedle parser bodyStart with
  | none                => false
  | some (values, vlen) => rangeFoldEq bytes values (values + vlen) chunkedNeedle

/-- Decimal value of the ASCII-digit run in `[i, e)` (independent digit-accumulation;
    `none` on a non-digit). -/
def h1DecDigits (bytes : Bytes) (element index decimalValue fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => some decimalValue
  | fuel' + 1 =>
    if index ≥ element then
      some decimalValue
    else
      let byte := bytes[index]!
      if byte ≥ 0x30 && byte ≤ 0x39 then
        h1DecDigits bytes element (index + 1) (decimalValue * 10 + (byte.toNat - 0x30)) fuel'
      else
        none

/-- RFC §3.3.2 message length from Content-Length: the decimal value of the first
    `Content-Length` field value (`none` if absent or non-decimal). -/
def h1ContentLength (bytes : Bytes) (parser bodyStart : Nat) : Option Nat :=
  match h1Lookup bytes clNeedle parser bodyStart with
  | none => none
  | some (values, vlen) =>
    let valueStart := values
    let valueEnd := values + vlen
    if valueEnd ≤ valueStart then
      none
    else
      h1DecDigits bytes valueEnd valueStart 0 (valueEnd - valueStart)

-- ── The in-place scanners refine the list model ───────────────────────────────

private
theorem headerValueRange.go_eq
        (bytes name : Bytes)
        (bodyStart : Nat)
        : ∀ (parser fuel : Nat),
            headerValueRange.findHeaderValue bytes name bodyStart parser fuel
                = ((h1Fields bytes bodyStart parser fuel).find?
                  (fun fieldRange => rangeFoldEq bytes fieldRange.1 fieldRange.2.1 name)).map
                  (fun field => (field.2.2.1, field.2.2.2 - field.2.2.1)) := by
  intro position fuel
  induction fuel generalizing position with
  | zero => rw [headerValueRange.findHeaderValue, h1Fields]; rfl
  | succ remainingFuel inductionHypothesis =>
    rw [headerValueRange.findHeaderValue, h1Fields]
    cases hcrlf : crlfFrom bytes position bodyStart with
    | none => rfl
    | some crlfIndex =>
      dsimp only
      by_cases hcp : crlfIndex ≤ position
      · simp [hcp]
      · simp only [hcp, if_false]
        cases hcol : colonFrom bytes position crlfIndex with
        | none => dsimp only; exact inductionHypothesis (crlfIndex + 2)
        | some col =>
          dsimp only
          cases hfold : rangeFoldEq bytes position col name with
          | true => simp [hfold]
          | false =>
            simp only [List.find?_cons, hfold, Bool.false_eq_true, if_false]
            exact inductionHypothesis (crlfIndex + 2)

private
theorem headerValueRange_eq
        (bytes name : Bytes)
        (lineStart bodyStart : Nat)
        : headerValueRange bytes name lineStart bodyStart = h1Lookup bytes name lineStart bodyStart := by
  unfold headerValueRange h1Lookup

  -- Close the remaining goal.
  exact headerValueRange.go_eq bytes name bodyStart lineStart bytes.size

private
theorem teIsChunked_eq
        (bytes : Bytes)
        (lineStart bodyStart : Nat)
        : teIsChunked bytes lineStart bodyStart = h1IsChunked bytes lineStart bodyStart := by
  unfold teIsChunked h1IsChunked

  -- Simplify the remaining goal.
  rw [headerValueRange_eq]

private
theorem contentLengthOf.go_eq
        (bytes : Bytes)
        (element : Nat)
        : ∀ (index decimalValue fuel : Nat),
            contentLengthOf.parseDecimalLength bytes element index decimalValue fuel
                = h1DecDigits bytes element index decimalValue fuel := by
  intro digitIndex decimalValue fuel
  induction fuel generalizing digitIndex decimalValue with
  | zero => rw [contentLengthOf.parseDecimalLength, h1DecDigits]
  | succ remainingFuel inductionHypothesis =>
    rw [contentLengthOf.parseDecimalLength, h1DecDigits]
    dsimp only
    split
    · rfl
    · split
      · exact inductionHypothesis _ _
      · rfl

private
theorem contentLengthOf_eq
        (bytes : Bytes)
        (lineStart bodyStart : Nat)
        : contentLengthOf bytes lineStart bodyStart = h1ContentLength bytes lineStart bodyStart := by
  unfold contentLengthOf h1ContentLength
  rw [headerValueRange_eq]
  cases h1Lookup bytes clNeedle lineStart bodyStart with
  | none => rfl
  | some valuePair =>
    obtain ⟨valueStart, valueLength⟩ := valuePair
    dsimp only
    split
    · rfl
    · exact
        contentLengthOf.go_eq
          bytes
          (valueStart + valueLength)
          valueStart
          0
          (valueStart + valueLength - valueStart)

-- ── Chunked transfer-coding body grammar (RFC-7230 §4.1) ──────────────────────

/-- `IsChunkedFraming bs p n`: the bytes `[p, n)` are a valid chunked message body
    — a run of `chunk-size ⟨CRLF⟩ chunk-data ⟨CRLF⟩` chunks ending at the `0`-sized
    last-chunk (with an optional trailing `CRLF`). The degenerate `empty` case
    (`p = n` at end-of-buffer) mirrors the scanner's buffer-exhaustion behavior. -/
inductive is_chunked_framing (bytes : Bytes) : Nat → Nat → Prop where
  | empty {parser : Nat} : bytes.size ≤ parser → is_chunked_framing bytes parser parser
  | last {parser cursor : Nat} :
            CrlfAt bytes cursor
                → hexRange bytes parser cursor = some 0
                → is_chunked_framing bytes parser (cursor + 2)
  | lastCrlf {parser cursor : Nat} :
            CrlfAt bytes cursor
                → hexRange bytes parser cursor = some 0
                → CrlfAt bytes (cursor + 2)
                → is_chunked_framing bytes parser (cursor + 4)
  | more {parser cursor size count : Nat} :
            CrlfAt bytes cursor
                → hexRange bytes parser cursor = some size
                → size ≠ 0
                → is_chunked_framing bytes (cursor + 2 + size + 2) count
                → is_chunked_framing bytes parser count

private
theorem frameChunked.go_sound
        (bytes : Bytes)
        : ∀ (continuation fuel count : Nat) (rest : Bytes),
            continuation ≤ bytes.size
                → bytes.size ≤ continuation + fuel
                → frameChunked.frameChunks bytes continuation fuel = .found count rest
                → is_chunked_framing bytes continuation count
                    ∧ rest = bytes.extract count bytes.size
                    ∧ count ≤ bytes.size := by
  intro chunkStart fuel
  induction fuel generalizing chunkStart with
  | zero =>
    intro frameEnd rest startBound fuelBound frameEquation
    rw [frameChunked.frameChunks] at frameEquation
    simp only [scan_result.found.injEq] at frameEquation
    obtain ⟨rfl, rfl⟩ := frameEquation
    have hqe : chunkStart = bytes.size := by omega
    subst hqe
    exact ⟨is_chunked_framing.empty (Nat.le_refl _), rfl, Nat.le_refl _⟩
  | succ remainingFuel inductionHypothesis =>
    intro frameEnd rest startBound fuelBound frameEquation
    rw [frameChunked.frameChunks] at frameEquation
    split at frameEquation
    · exact absurd frameEquation (by simp)
    · rename_i crlfIndex hcrlf
      obtain ⟨hqc, hc2, hCR, _⟩ := crlfFrom_sound bytes chunkStart bytes.size crlfIndex hcrlf
      split at frameEquation
      · exact absurd frameEquation (by simp)
      · rename_i hhex0
        dsimp only at frameEquation
        split at frameEquation
        · rename_i hcond
          simp only [scan_result.found.injEq] at frameEquation
          obtain ⟨rfl, rfl⟩ := frameEquation
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          refine ⟨is_chunked_framing.lastCrlf hCR hhex0 ⟨hcond.1.2, hcond.2⟩, rfl, by omega⟩
        · simp only [scan_result.found.injEq] at frameEquation
          obtain ⟨rfl, rfl⟩ := frameEquation
          refine ⟨is_chunked_framing.last hCR hhex0, rfl, by omega⟩
      · rename_i chunkSize hsznz hhex
        dsimp only at frameEquation
        split at frameEquation
        · rename_i hguard
          obtain ⟨hcf, hre, hnle⟩ :=
            inductionHypothesis
              (crlfIndex + 2 + chunkSize + 2)
              frameEnd
              rest
              (by omega)
              (by omega)
              frameEquation
          exact ⟨is_chunked_framing.more hCR hhex hsznz hcf, hre, hnle⟩
        · exact absurd frameEquation (by simp)

private
theorem frameChunked_sound
        (bytes : Bytes)
        (parser count : Nat)
        (rest : Bytes)
        (parserEvidence : parser ≤ bytes.size)
        (evidence : frameChunked bytes parser = .found count rest)
        : is_chunked_framing bytes parser count
            ∧ rest = bytes.extract count bytes.size
            ∧ count ≤ bytes.size := by
  unfold frameChunked at evidence

  -- Close the remaining goal.
  exact
    frameChunked.go_sound
      bytes
      parser
      (bytes.size - parser)
      count
      rest
      parserEvidence
      (by omega)
      evidence

private
theorem hexRange_lt
        (bytes : Bytes)
        (parser cursor value : Nat)
        (evidence : hexRange bytes parser cursor = some value)
        : parser < cursor := by
  unfold hexRange at evidence

  -- Split the remaining proof cases.
  split at evidence

  -- Close the next proof branch.
  · exact absurd evidence (by simp)

  -- Close the next proof branch.
  · rename_i hcp; omega

/-- A chunked body never has a negative length: `p ≤ n`. -/
private
theorem IsChunkedFraming_le
        (bytes : Bytes)
        (parser count : Nat)
        (evidence : is_chunked_framing bytes parser count)
        : parser ≤ count := by
  induction evidence with
  | empty startBound => exact Nat.le_refl _
  | last _ hhex => have := hexRange_lt bytes _ _ _ hhex; omega
  | lastCrlf _ hhex _ => have := hexRange_lt bytes _ _ _ hhex; omega
  | more _ hhex _ _ recursiveBound => have := hexRange_lt bytes _ _ _ hhex; omega

-- ── The framing grammar + soundness of `scanHttpFrame` ────────────────────────

/-- The header section `[0, bodyStart)`: a request-line terminated by the FIRST
    CRLF (at `firstCrlf`), then header field-lines, terminated by the FIRST empty
    line — `bodyStart` sits right after the first `\r\n\r\n`. -/
def H1HeaderBlock (bytes : Bytes) (firstCrlf bodyStart : Nat) : Prop :=
  CrlfAt bytes firstCrlf
      ∧ (∀ j, j < firstCrlf → ¬CrlfAt bytes j)
      ∧ firstCrlf + 2 ≤ bodyStart
      ∧ 4 ≤ bodyStart
      ∧ bodyStart ≤ bytes.size
      ∧ CrlfCrlfAt bytes (bodyStart - 4)
      ∧ (∀ t, t < bodyStart - 4 → ¬CrlfCrlfAt bytes t)

/-- `IsH1Frame bs n`: the first `n` bytes of `bs` are exactly one RFC-7230 §3
    HTTP/1 message — a request-line ⟨CRLF⟩, header field-lines each ⟨CRLF⟩, an
    empty ⟨CRLF⟩, then a body whose length is fixed by RFC §3.3.3: `chunked`
    Transfer-Encoding ⇒ chunked framing (§4.1); else Content-Length ⇒ that many
    octets; else empty. Header semantics are read via the independent list model
    (`h1IsChunked` / `h1ContentLength`), so the three body modes are mutually
    exclusive by construction (deterministic functions). -/
def IsH1Frame (bytes : Bytes) (count : Nat) : Prop :=
  ∃ firstCrlf bodyStart,
      H1HeaderBlock bytes firstCrlf bodyStart
          ∧ bodyStart ≤ count
          ∧ count ≤ bytes.size
          ∧ ((h1IsChunked bytes (firstCrlf + 2) bodyStart = true
              ∧ is_chunked_framing bytes bodyStart count)
              ∨ (h1IsChunked bytes (firstCrlf + 2) bodyStart = false
                  ∧ ∃ len,
                      h1ContentLength bytes (firstCrlf + 2) bodyStart = some len
                          ∧ count = bodyStart + len)
              ∨ (h1IsChunked bytes (firstCrlf + 2) bodyStart = false
                  ∧ h1ContentLength bytes (firstCrlf + 2) bodyStart = none
                  ∧ count = bodyStart))

private
theorem CRLFCRLF_bytes
        : CRLFCRLF[0]! = CR ∧ CRLFCRLF[1]! = LF ∧ CRLFCRLF[2]! = CR ∧ CRLFCRLF[3]! = LF := by decide

private
theorem scanHttpFrame_header_block
        (bytes : Bytes)
        (termIdx firstCrlf : Nat)
        (hfb : findBytes CRLFCRLF bytes = some termIdx)
        (hfc : crlfFrom bytes 0 (termIdx + 4) = some firstCrlf)
        : H1HeaderBlock bytes firstCrlf (termIdx + 4) := by
  obtain ⟨htb, hmatch, hraw⟩ := findBytes_sound CRLFCRLF bytes termIdx (by decide) hfb
  obtain ⟨_, hfc2, hCRfc, hfcfirst⟩ := crlfFrom_sound bytes 0 (termIdx + 4) firstCrlf hfc
  obtain ⟨firstCr, firstLf, secondCr, secondLf⟩ := CRLFCRLF_bytes
  have hsz4 : CRLFCRLF.size = 4 := by decide
  have hcc : CrlfCrlfAt bytes (termIdx + 4 - 4) := by
    have byte0Evidence := hmatch 0 (by decide)
    have firstLfEvidence := hmatch 1 (by decide)
    have secondEvidence := hmatch 2 (by decide)
    have thirdEvidence := hmatch 3 (by decide)
    rw [firstCr] at byte0Evidence
    rw [firstLf] at firstLfEvidence
    rw [secondCr] at secondEvidence
    rw [secondLf] at thirdEvidence
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all
  have hccfirst : ∀ t, t < termIdx + 4 - 4 → ¬CrlfCrlfAt bytes t := by
    intro candidateIndex candidateBound candidateCrlf
    obtain ⟨offset, offsetBound, mismatch⟩ := hraw candidateIndex (by omega)
    rw [hsz4] at offsetBound
    have hj4 : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by omega
    rcases hj4 with rfl | rfl | rfl | rfl
    · rw [firstCr] at mismatch; exact mismatch (by simpa using candidateCrlf.1)
    · rw [firstLf] at mismatch; exact mismatch (by simpa using candidateCrlf.2.1)
    · rw [secondCr] at mismatch; exact mismatch (by simpa using candidateCrlf.2.2.1)
    · rw [secondLf] at mismatch; exact mismatch (by simpa using candidateCrlf.2.2.2)
  exact
    ⟨
      hCRfc,
      fun jdx rangeBound => hfcfirst jdx (Nat.zero_le _) rangeBound,
      by omega,
      by omega,
      htb,
      hcc,
      hccfirst
    ⟩

private
theorem isH1Frame_chunked
        (bytes : Bytes)
        (firstCrlf bodyStart frameEnd : Nat)
        (headerBlock : H1HeaderBlock bytes firstCrlf bodyStart)
        (chunkedFraming : is_chunked_framing bytes bodyStart frameEnd)
        (frameEndLe : frameEnd ≤ bytes.size)
        (isChunked : h1IsChunked bytes (firstCrlf + 2) bodyStart = true)
        : IsH1Frame bytes frameEnd :=
  ⟨
    firstCrlf,
    bodyStart,
    headerBlock,
    IsChunkedFraming_le bytes _ _ chunkedFraming,
    frameEndLe,
    Or.inl ⟨isChunked, chunkedFraming⟩
  ⟩

/-- SOUNDNESS: every frame `scanHttpFrame` reports is a genuine RFC-7230 §3 frame.
    `IsH1Frame` is the independent trusted spec; `scanHttpFrame` refines it. -/
theorem scanHttpFrame_sound
        (bytes : Bytes)
        (count : Nat)
        (rest : Bytes)
        (evidence : scanHttpFrame bytes = .found count rest)
        : IsH1Frame bytes count ∧ rest = bytes.extract count bytes.size ∧ count ≤ bytes.size := by
  unfold scanHttpFrame at evidence
  split at evidence
  · exact absurd evidence (by simp)
  · rename_i termIdx hfb
    obtain ⟨htb, _, _⟩ := findBytes_sound CRLFCRLF bytes termIdx (by decide) hfb
    dsimp only at evidence
    split at evidence
    · exact absurd evidence (by simp)
    · rename_i firstCrlf hfc
      -- header block, established once
      have hhb := scanHttpFrame_header_block bytes termIdx firstCrlf hfb hfc
      rw [teIsChunked_eq, contentLengthOf_eq] at evidence
      split at evidence
      · -- chunked
        rename_i htec
        obtain ⟨hcf, hre, hnle⟩ := frameChunked_sound bytes (termIdx + 4) count rest htb evidence
        exact ⟨isH1Frame_chunked bytes firstCrlf (termIdx + 4) count hhb hcf hnle htec, hre, hnle⟩
      · -- not chunked
        rename_i htec
        have htecf : h1IsChunked bytes (firstCrlf + 2) (termIdx + 4) = false := by simpa using htec
        split at evidence
        · -- content-length
          rename_i len hcl
          split at evidence
          · rename_i hsz
            simp only [scan_result.found.injEq] at evidence
            obtain ⟨rfl, rfl⟩ := evidence
            exact
              ⟨
                ⟨
                  firstCrlf,
                  termIdx + 4,
                  hhb,
                  by omega,
                  by omega,
                  Or.inr (Or.inl ⟨htecf, len, hcl, rfl⟩)
                ⟩,
                rfl,
                by omega
              ⟩
          · exact absurd evidence (by simp)
        · -- no framing header
          rename_i hcl
          split at evidence
          · exact absurd evidence (by simp)
          · simp only [scan_result.found.injEq] at evidence
            obtain ⟨rfl, rfl⟩ := evidence
            exact
              ⟨
                ⟨firstCrlf, termIdx + 4, hhb, by omega, htb, Or.inr (Or.inr ⟨htecf, hcl, rfl⟩)⟩,
                rfl,
                htb
              ⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §5 URI PARSING
-- ════════════════════════════════════════════════════════════════════════════

structure Uri where
  path     : String
  query    : Option String -- after ?
  fragment : Option String -- after #
  deriving Repr

def scanUri : Scanner Uri where
  consumption := fun _ _ _ => trivial
  scan bs :=
    -- Path: everything until ?, #, or space
    match (scanUntil (fun byte => byte == 0x3F || byte == 0x23 || byte == SPACE)).scan bs with
    | .found pathBytes rest =>
      match String.fromUTF8? pathBytes with
      | none => .notFound
      | some path =>
        if rest.size > 0 && rest[0]! == 0x3F then
          -- Has query
          match (scanUntil (fun byte => byte == 0x23 || byte == SPACE)).scan (rest.extract 1 rest.size) with
          | .found queryBytes rest2 =>
            match String.fromUTF8? queryBytes with
            | none => .notFound
            | some query =>
              if rest2.size > 0 && rest2[0]! == 0x23 then
                match (scanUntil (fun byte => byte == SPACE)).asString.scan (rest2.extract 1 rest2.size) with
                | .found frag rest3 => .found ⟨path, some query, some frag⟩ rest3
                | _ => .found ⟨path, some query, none⟩ rest2
              else .found ⟨path, some query, none⟩ rest2
          | _ => .found ⟨path, none, none⟩ rest
        else if rest.size > 0 && rest[0]! == 0x23 then
          match (scanUntil (fun byte => byte == SPACE)).asString.scan (rest.extract 1 rest.size) with
          | .found frag rest2 => .found ⟨path, none, some frag⟩ rest2
          | _ => .found ⟨path, none, none⟩ rest
        else .found ⟨path, none, none⟩ rest
    | .notFound => .notFound
    | .incomplete count => .incomplete count

-- ════════════════════════════════════════════════════════════════════════════
-- §6 BASE64 (for JWT)
-- ════════════════════════════════════════════════════════════════════════════

private
def isBase64Char (byte : UInt8) : Bool :=
  isAlphaNum byte || byte == 0x2B || byte == 0x2F || byte == 0x3D -- +, /, =

private
def isBase64UrlChar (byte : UInt8) : Bool := isAlphaNum byte || byte == 0x2D || byte == 0x5F -- -, _

def scanBase64 : Scanner Bytes := scanWhile isBase64Char
def scanBase64Url : Scanner Bytes := scanWhile isBase64UrlChar

-- ════════════════════════════════════════════════════════════════════════════
-- §7 JWT (JSON Web Token)
-- header.payload.signature (base64url-encoded segments separated by .)
-- ════════════════════════════════════════════════════════════════════════════

structure JWT where
  header    : Bytes -- base64url-encoded (decode separately)
  payload   : Bytes -- base64url-encoded
  signature : Bytes -- base64url-encoded
  deriving Repr

def scanJWT : Scanner JWT where
  consumption := fun _ _ _ => trivial
  scan bs :=
    match (scanUntilByte 0x2E).scan bs with  -- scan until '.'
    | .found header rest1 =>
      match (scanUntilByte 0x2E).scan rest1 with
      | .found payload rest2 =>
        -- Signature: rest until whitespace or end
        match (scanWhile isBase64UrlChar).scan rest2 with
        | .found sig rest3 => .found ⟨header, payload, sig⟩ rest3
        | .notFound => .notFound
        | .incomplete count => .incomplete count
      | .notFound => .notFound
      | .incomplete count => .incomplete count
    | .notFound => .notFound
    | .incomplete count => .incomplete count

-- ════════════════════════════════════════════════════════════════════════════

-- §8 JSON: deferred to Parser module (context-free grammar, needs LL(k))

-- ════════════════════════════════════════════════════════════════════════════
-- §9 COMPUTATIONAL TESTS
-- ════════════════════════════════════════════════════════════════════════════

end Continuity.Codec.Wire.Http.Http1
