import continuity.codec.core.scanner

/-!
  JSON value scanner. Recursive (partial). For OIDC discovery, JWT payloads, API responses.
-/

namespace Continuity.Codec.Wire.Json

open Continuity.Codec.Core.Scanner
open Continuity.Codec.Core

inductive JsonValue where
  | null
  | bool : Bool → JsonValue
  | number : String → JsonValue
  | string : String → JsonValue
  | array : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue
  deriving Repr

private partial
def scanStringContent
    (bytes : Bytes)
    (pos : Nat)
    (decodedBytes : ByteArray)
    : Option (String × Nat) :=
  if pos >= bytes.size then
    none
  else
    let byte := bytes[pos]!
    if byte == 0x22 then
      match String.fromUTF8? decodedBytes with
      | some state => some (state, pos + 1)
      | none       => none
    else if byte == 0x5C then
      if pos + 1 >= bytes.size then
        none
      else
        let escapedByte := bytes[pos+1]!
        let esc :=
          if escapedByte == 0x6E then
            0x0A
          else if escapedByte == 0x74 then
            0x09
          else if escapedByte == 0x72 then
            0x0D
          else if escapedByte == 0x22 then
            0x22
          else if escapedByte == 0x5C then
            0x5C
          else if escapedByte == 0x2F then 0x2F else escapedByte
        scanStringContent bytes (pos + 2) (decodedBytes.push esc)
    else
      scanStringContent bytes (pos + 1) (decodedBytes.push byte)

private
def whitespace (bytes : Bytes) : Bytes :=
  match skipWhitespace.scan bytes with
  | .found () result => result
  | _                => bytes

private
def scanKeyword (word : String) (value : JsonValue) (bytes : Bytes) : scan_result JsonValue :=
  match (exact word.toUTF8).scan bytes with
  | .found () rest => .found value rest
  | _              => .notFound

private
def scanNumber (bytes : Bytes) : scan_result JsonValue :=
  let numberByte :=
    fun char =>
      isDigit char || char == 0x2E || char == 0x65 || char == 0x45 || char == 0x2D || char == 0x2B
  match (scanWhile numberByte).scan bytes with
  | .found bytes rest =>
    match String.fromUTF8? bytes with
    | some number => .found (.number number) rest
    | none        => .notFound
  | _ => .notFound

mutual
  partial
  def scan (bytes : Bytes) : scan_result JsonValue :=
    let inputBytes := whitespace bytes
    if inputBytes.size == 0 then .notFound
    else
      let firstByte := inputBytes[0]!
      if firstByte == 0x22 then
        match scanStringContent inputBytes 1 ByteArray.empty with
        | some (state, errorPosition) =>
          .found (.string state) (inputBytes.extract errorPosition inputBytes.size)
        | none => .notFound
      else if firstByte == 0x7B then scanObject (inputBytes.extract 1 inputBytes.size)
      else if firstByte == 0x5B then scanArray (inputBytes.extract 1 inputBytes.size)
      else if firstByte == 0x74 then scanKeyword "true" (.bool true) inputBytes
      else if firstByte == 0x66 then scanKeyword "false" (.bool false) inputBytes
      else if firstByte == 0x6E then scanKeyword "null" .null inputBytes
      else if isDigit firstByte || firstByte == 0x2D then scanNumber inputBytes
      else .notFound

  private partial
  def scanObject (bytes : Bytes) : scan_result JsonValue :=
    let rec scanObjectFields
        (fields : List (String × JsonValue))
        (remainingBytes : Bytes)
        (fuel : Nat)
        : scan_result JsonValue :=
      match fuel with
      | 0 => .notFound
      | fuel' + 1 =>
        let fieldInput := whitespace remainingBytes
        if fieldInput.size > 0 && fieldInput[0]! == 0x7D then
          .found (.object fields.reverse) (fieldInput.extract 1 fieldInput.size)
        else
          let commaInput :=
            if !fields.isEmpty then
              match (exact ⟨#[0x2C]⟩).scan fieldInput with
              | .found () result => result
              | _ => fieldInput
            else
              fieldInput
          let keyInput := whitespace commaInput
          if keyInput.size == 0 || keyInput[0]! != 0x22 then .notFound
          else match scanStringContent keyInput 1 ByteArray.empty with
          | none => .notFound
          | some (key, errorPosition) =>
            let valueInput := whitespace (keyInput.extract errorPosition keyInput.size)
            match (exactByte 0x3A).scan valueInput with
            | .found () result => match scan (whitespace result) with
              | .found val rest => scanObjectFields ((key, val) :: fields) rest fuel'
              | _ => .notFound
            | _ => .notFound
    scanObjectFields [] bytes bytes.size

  private partial
  def scanArray (bytes : Bytes) : scan_result JsonValue :=
    let rec scanArrayElements
        (elements : List JsonValue)
        (remainingBytes : Bytes)
        (fuel : Nat)
        : scan_result JsonValue :=
      match fuel with
      | 0 => .notFound
      | fuel' + 1 =>
        let elementInput := whitespace remainingBytes
        if elementInput.size > 0 && elementInput[0]! == 0x5D then
          .found (.array elements.reverse) (elementInput.extract 1 elementInput.size)
        else
          let commaInput :=
            if !elements.isEmpty then
              match (exact ⟨#[0x2C]⟩).scan elementInput with
              | .found () result => result
              | _ => elementInput
            else
              elementInput
          match scan (whitespace commaInput) with
          | .found val rest => scanArrayElements (val :: elements) rest fuel'
          | _ => .notFound
    scanArrayElements [] bytes bytes.size
end

def scanJson : Scanner JsonValue where
  consumption := fun _ _ _ => trivial
  scan := Json.scan

end Continuity.Codec.Wire.Json
