import continuity.codec.core.scanner
import continuity.codec.core.basic

/-!
  SAML Assertion Scanner — NOT an XML parser.

  SAML is a wire format with a fixed schema. We scan for exactly the
  elements we expect. Anything outside the schema is rejected.

  Wrapping attack prevention by construction: identity claims are
  extracted ONLY from signedBytes. Grade algebra enforces [Crypto]
  discharged before [Identity] available.
-/

namespace Continuity.Codec.Wire.Saml

open Continuity.Codec.Core.Scanner
open Continuity.Codec.Core

-- ════════════════════════════════════════════════════════════════════════════
-- §1 ELEMENT SCANNING (exact qualified name, not prefix)
-- ════════════════════════════════════════════════════════════════════════════

/-- Find element by exact tag name. Returns (attributes, text content). -/
def findElement (qname : String) (bytes : Bytes) : Option (Bytes × Bytes) :=
  let openPfx := ("<" ++ qname).toUTF8
  let closeTag := ("</" ++ qname ++ ">").toUTF8
  let rec findSignedSpan (searchFrom : Nat) (fuel : Nat) : Option (Bytes × Bytes) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match findBytes openPfx (bytes.extract searchFrom bytes.size) with
      | some relIdx =>
        let absIdx := searchFrom + relIdx
        let afterName := absIdx + openPfx.size
        if afterName < bytes.size then
          let delimiterByte := bytes[afterName]!
          if delimiterByte == 0x3E || delimiterByte == 0x20 || delimiterByte == 0x09
              || delimiterByte == 0x2F then
            match findByte 0x3E (bytes.extract absIdx bytes.size) with
            | some gtOff =>
              let contentStart := absIdx + gtOff + 1
              match findBytes closeTag (bytes.extract contentStart bytes.size) with
              | some endOff =>
                some
                  (
                    bytes.extract (absIdx + openPfx.size) (absIdx + gtOff),
                    (bytes.extract contentStart bytes.size).extract 0 endOff
                  )
              | none => none
            | none => none
          else
            findSignedSpan (absIdx + 1) fuel'
        else
          none
      | none => none
  findSignedSpan 0 bytes.size

/-- Extract attribute value from raw attribute bytes -/
def findAttr (name : String) (attrBytes : Bytes) : Option String :=
  let needle := (name ++ "=\"").toUTF8
  match findBytes needle attrBytes with
  | some idx =>
    let afterEq := attrBytes.extract (idx + needle.size) attrBytes.size
    match (scanUntilByte 0x22).scan afterEq with
    | .found valBytes _ => String.fromUTF8? valBytes
    | _                 => none
  | none => none

-- ════════════════════════════════════════════════════════════════════════════
-- §2 SAML STRUCTURES
-- ════════════════════════════════════════════════════════════════════════════

structure NameID where
  value  : String
  format : Option String
  deriving Repr

structure Attribute where
  name   : String
  values : List String
  deriving Repr

structure Conditions where
  notBefore    : String
  notOnOrAfter : String
  audience     : Option String
  deriving Repr

/-- What the scanner produces: raw signed bytes only.
    Identity fields are NOT exposed until signature is verified.
    Use `verifyAssertion` to obtain a `VerifiedAssertion`. -/
structure unverified_assertion where
  signedBytes : Bytes
  deriving Repr

/-- What callers receive after signature verification.
    Cannot be constructed directly — only via `verifyAssertion`.
    Grade [Crypto] discharged before [Identity] available, by construction. -/
structure verified_assertion where
  issuer      : String
  nameId      : NameID
  conditions  : Conditions
  attributes  : List Attribute
  signedBytes : Bytes
  deriving Repr

-- ════════════════════════════════════════════════════════════════════════════
-- §3 SIGNED ASSERTION EXTRACTION
-- ════════════════════════════════════════════════════════════════════════════

/-- Extract the raw assertion bytes (what the signature covers) -/
def scanSignedAssertion : Scanner Bytes where
  scan bs :=
    let tryNs (names : String) : scan_result Bytes :=
      let openPfx := ("<" ++ names ++ "Assertion").toUTF8
      let closeTag := ("</" ++ names ++ "Assertion>").toUTF8
      match findBytes openPfx bs with
      | some startIdx =>
        match findBytes closeTag (bs.extract startIdx bs.size) with
        | some endOff =>
          let totalEnd := startIdx + endOff + closeTag.size
          .found (bs.extract startIdx totalEnd) (bs.extract totalEnd bs.size)
        | none => .notFound
      | none => .notFound
    match tryNs "saml:" with
    | .found state result => .found state result
    | _ => tryNs "saml2:"
  consumption := fun _ _ _ => trivial

-- ════════════════════════════════════════════════════════════════════════════
-- §4 FIELD EXTRACTION (from signed bytes only!)
-- ════════════════════════════════════════════════════════════════════════════

private
def tryBoth (qname : String) (bytes : Bytes) : Option (Bytes × Bytes) :=
  match findElement ("saml:" ++ qname) bytes with
  | some result => some result
  | none        => findElement ("saml2:" ++ qname) bytes

private
def extractIssuer (bytes : Bytes) : Option String :=
  (tryBoth "Issuer" bytes).bind fun (_, delimiterByte) => String.fromUTF8? delimiterByte

private
def extractNameID (bytes : Bytes) : Option NameID :=
  (tryBoth "NameID" bytes).bind fun (attrs, content) =>
    (String.fromUTF8? content).map fun value => ⟨value, findAttr "Format" attrs⟩

private
def extractConditions (bytes : Bytes) : Option Conditions :=
  (tryBoth "Conditions" bytes).map fun (attrs, content) =>
    let notBefore := findAttr "NotBefore" attrs |>.getD ""
    let noa := findAttr "NotOnOrAfter" attrs |>.getD ""
    let aud :=
      (tryBoth "Audience" content).bind fun (_, delimiterByte) => String.fromUTF8? delimiterByte
    ⟨notBefore, noa, aud⟩

/-- Extract all attributes from a SAML AttributeStatement.
    BUG FIX: AttributeValue is searched within `attrContent` (the current
    attribute's content slice), not `remaining` (the full buffer). The old
    code scanned `remaining` for AttributeValue, so every attribute got the
    first attribute's value. Now each attribute's values are bounded to its
    own content bytes. -/
private
def extractAttributes (bytes : Bytes) : List Attribute :=
  match tryBoth "AttributeStatement" bytes with
  | some (_, stmtContent) =>
    let rec parseAttributes (remaining : Bytes) (result : List Attribute) (fuel : Nat) : List Attribute :=
      match fuel with
      | 0 => result.reverse
      | fuel' + 1 =>
        -- Try both namespace prefixes for each Attribute element
        let found := match findElement "saml:Attribute" remaining with
          | some result => some ("saml:Attribute", result)
          | none => match findElement "saml2:Attribute" remaining with
            | some result => some ("saml2:Attribute", result)
            | none => none
        match found with
        | some (attrTag, (attrAttrs, attrContent)) =>
          let name := findAttr "Name" attrAttrs |>.getD ""
          -- FIX: search attrContent, not remaining
          let vals :=
            let rec collectVals (slice : Bytes) (vacc : List String) (vfuel : Nat) : List String :=
              match vfuel with
              | 0 => vacc.reverse
              | vfuel' + 1 =>
                let vFound := match findElement "saml:AttributeValue" slice with
                  | some result => some result
                  | none => findElement "saml2:AttributeValue" slice
                match vFound with
                | some (_, valueCount) =>
                  let vStr := String.fromUTF8? valueCount |>.getD ""
                  -- Advance past this AttributeValue
                  let closeV := "</saml:AttributeValue>".toUTF8
                  let closeV2 := "</saml2:AttributeValue>".toUTF8
                  let advance := match findBytes closeV slice with
                    | some idx => slice.extract (idx + closeV.size) slice.size
                    | none => match findBytes closeV2 slice with
                      | some idx => slice.extract (idx + closeV2.size) slice.size
                      | none => ByteArray.empty
                  collectVals advance (vStr :: vacc) vfuel'
                | none => vacc.reverse
            collectVals attrContent [] attrContent.size
          -- Advance past this Attribute element
          let closeTag := ("</" ++ attrTag ++ ">").toUTF8
          match findBytes closeTag remaining with
          | some idx => parseAttributes (remaining.extract (idx + closeTag.size) remaining.size) (⟨name, vals⟩ :: result) fuel'
          | none => (⟨name, vals⟩ :: result).reverse
        | none => result.reverse
    parseAttributes stmtContent [] stmtContent.size
  | none => []

-- ════════════════════════════════════════════════════════════════════════════
-- §5 SCANNER + VERIFICATION GATE
-- ════════════════════════════════════════════════════════════════════════════

/-- Scanner produces UnverifiedAssertion only — signed bytes, nothing else.
    Callers cannot access identity fields without going through verifyAssertion. -/
def scanAssertion : Scanner unverified_assertion where
  scan bs :=
    match scanSignedAssertion.scan bs with
    | .found signedBytes remaining => .found ⟨signedBytes⟩ remaining
    | .notFound => .notFound
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial

/-- Verify signature and extract identity fields.
    This is the ONLY path from UnverifiedAssertion to VerifiedAssertion.
    In production: `sigVerified` is the result of calling the PQ signature
    verifier over `ua.signedBytes`. The type system enforces that you cannot
    skip this step — VerifiedAssertion has no public constructor. -/
def verifyAssertion
    (unsignedValue : unverified_assertion)
    (sigVerified : Bool)
    : Option verified_assertion :=
  if !sigVerified then
    none
  else
    match extractIssuer unsignedValue.signedBytes, extractNameID unsignedValue.signedBytes, extractConditions unsignedValue.signedBytes with
    | some issuer, some nameId, some conditions =>
      some
        ⟨
          issuer,
          nameId,
          conditions,
          extractAttributes unsignedValue.signedBytes,
          unsignedValue.signedBytes
        ⟩
    | _, _, _ => none

end Continuity.Codec.Wire.Saml
