/-
  Continuity.Codec.Wire.Http.Http1.Headers - HTTP/1.1 header & request-line scanners

  The HTTP-specific Scanner instances, kept in the Continuity.Codec.Core.Scanner
  namespace (so existing `open` sites resolve), extracted out of the generic
  Scanner engine.
-/

import continuity.codec.core.scanner

namespace Continuity.Codec.Wire.Http.Headers

open Continuity.Codec.Core.Scanner

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- HTTP/1.1 EXAMPLE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP header: name: value -/
structure HttpHeader where
  name  : String
  value : String
  deriving Repr

/-- Scan a single HTTP header -/
def scanHttpHeader : Scanner HttpHeader where
  scan bs :=
    match scanUntilColon.scan bs with
    | .found nameBytes rest1 =>
      match skipWhitespace.scan rest1 with
      | .found () rest2 =>
        match scanCRLFLine.scan rest2 with
        | .found valueBytes rest3 =>
          match String.fromUTF8? nameBytes, String.fromUTF8? valueBytes with
          | some name, some value => .found ⟨name, (value.trimAsciiEnd).toString⟩ rest3
          | _, _ => .notFound
        | .notFound => .notFound
        | .incomplete count => .incomplete count
      | _ => .notFound
    | .notFound => .notFound
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial

/-- Scan HTTP headers until empty line -/
def scanHttpHeaders : Scanner (List HttpHeader) where
  scan bs :=
    let rec parseHeaders (result : List HttpHeader) (remaining : Bytes) (fuel : Nat) : scan_result (List HttpHeader) :=
      match fuel with
      | 0 => .found result.reverse remaining
      | fuel' + 1 =>
        match (exact CRLF).scan remaining with
        | .found () rest => .found result.reverse rest
        | _ =>
          match scanHttpHeader.scan remaining with
          | .found header rest => parseHeaders (header :: result) rest fuel'
          | .notFound          => .found result.reverse remaining
          | .incomplete count  => .incomplete count
    parseHeaders [] bs bs.size
  consumption := fun _ _ _ => trivial

/-- HTTP request line: METHOD SP URI SP VERSION CRLF -/
structure HttpRequestLine where
  method  : String
  uri     : String
  version : String
  deriving Repr

/-- Scan HTTP request line -/
def scanHttpRequestLine : Scanner HttpRequestLine where
  scan bs :=
    match (scanUntilByte SPACE).scan bs with
    | .found methodBytes rest1 =>
      match (scanUntilByte SPACE).scan rest1 with
      | .found uriBytes rest2 =>
        match scanCRLFLine.scan rest2 with
        | .found versionBytes rest3 =>
          match String.fromUTF8? methodBytes, String.fromUTF8? uriBytes, String.fromUTF8? versionBytes with
          | some marker, some unit, some value => .found ⟨marker, unit, value⟩ rest3
          | _, _, _ => .notFound
        | .notFound => .notFound
        | .incomplete count => .incomplete count
      | .notFound => .notFound
      | .incomplete count => .incomplete count
    | .notFound => .notFound
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial

end Continuity.Codec.Wire.Http.Headers
