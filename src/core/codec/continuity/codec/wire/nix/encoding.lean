/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // CONTINUITY // CODEC // WIRE // NIX // ENCODING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The base encodings the Nix store speaks — the verified reference the generator
    (`Codec/Codegen/NixEncoding`) mirrors. Ported from the hand-rolled
    `nix/crypto/encoding.{h,cpp}`:

      · base16  — lowercase hex (2 chars / byte)
      · base64  — RFC 4648, standard alphabet, `=` padding
      · nix32   — Nix's base32: alphabet `0123456789abcdfghijklmnpqrsvwxyz`
                  (omits e/o/u/t), **LSB-first / reversed** (`result[len-1-i]`)

    nix32 is the legacy crux: store-path hashes are nix32. The bit layout is the
    fiddly part — output char `i` reads bits `[5i, 5i+5)` LSB-first, masked to 5 bits,
    and the whole string is reversed. These are executable references; correctness is
    pinned by `native_decide` round-trips and canonical legacy vectors (`deadbeef`,
    `TWFu`, …). Universal roundtrip proofs are a follow-up; the value here is matching
    real Nix output byte-for-byte (the generated C++ cross-checks the SAME vectors).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.Nix.Encoding

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                      // base16
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def hexAlphabet : List Char := "0123456789abcdef".toList

def base16Encode (data : List UInt8) : List Char :=
  data.flatMap fun byte =>
    [hexAlphabet.getD (byte.toNat >>> 4) '0', hexAlphabet.getD (byte.toNat &&& 0xf) '0']

/-- Hex digit value, case-insensitive; `none` for a non-hex char. -/
def hexVal (cursor : Char) : Option Nat :=
  if '0' ≤ cursor ∧ cursor ≤ '9' then
    some (cursor.toNat - '0'.toNat)
  else if 'a' ≤ cursor ∧ cursor ≤ 'f' then
    some (cursor.toNat - 'a'.toNat + 10)
  else if 'A' ≤ cursor ∧ cursor ≤ 'F' then some (cursor.toNat - 'A'.toNat + 10) else none

def base16Decode : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | high :: low :: rest =>
    hexVal high |>.bind fun highValue =>
      hexVal low |>.bind fun lowValue =>
        base16Decode rest |>.map fun decodedRest =>
          UInt8.ofNat (highValue * 16 + lowValue) :: decodedRest

def base16EncodeStr (data : List UInt8) : String := String.ofList (base16Encode data)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                      // base64
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def b64Alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

private
def b64Chr (count : Nat) : Char := b64Alphabet.getD (count &&& 63) 'A'

def base64Encode : List UInt8 → List Char
  | [] => []
  | [value] =>
    let encodedWord := value.toNat <<< 16
    [b64Chr (encodedWord >>> 18), b64Chr (encodedWord >>> 12), '=', '=']
  | [value, byte] =>
    let encodedWord := (value.toNat <<< 16) ||| (byte.toNat <<< 8)
    [b64Chr (encodedWord >>> 18), b64Chr (encodedWord >>> 12), b64Chr (encodedWord >>> 6), '=']
  | value :: byte :: code :: rest =>
    let encodedWord := (value.toNat <<< 16) ||| (byte.toNat <<< 8) ||| code.toNat
    [
      b64Chr (encodedWord >>> 18),
      b64Chr (encodedWord >>> 12),
      b64Chr (encodedWord >>> 6),
      b64Chr encodedWord
    ]
        ++ base64Encode rest

def b64Val (cursor : Char) : Option Nat :=
  match b64Alphabet.idxOf? cursor with
  | some index => some index
  | none       => none

private
def decodeBase64Chunk
    (leftValue rightValue cursor decoder : Char)
    (rest : List Char)
    (decodeRest : Unit → Option (List UInt8))
    : Option (List UInt8) := do
  let sextetA ← b64Val leftValue
  let sextetB ← b64Val rightValue
  if cursor = '=' then
    if decoder = '=' ∧ rest = [] then some [UInt8.ofNat ((sextetA <<< 2) ||| (sextetB >>> 4))]
    else none
  else do
    let sextetC ← b64Val cursor
    let byte0 := UInt8.ofNat ((sextetA <<< 2) ||| (sextetB >>> 4))
    let byte1 := UInt8.ofNat (((sextetB &&& 0xf) <<< 4) ||| (sextetC >>> 2))
    if decoder = '=' then
      if rest = [] then some [byte0, byte1]
      else none
    else do
      let sextetD ← b64Val decoder
      let byte2 := UInt8.ofNat (((sextetC &&& 3) <<< 6) ||| sextetD)
      let decodedRest ← decodeRest ()
      some (byte0 :: byte1 :: byte2 :: decodedRest)

def base64Decode : List Char → Option (List UInt8)
  | [] => some []
  | value :: byte :: code :: digit :: rest =>
    decodeBase64Chunk value byte code digit rest fun () => base64Decode rest
  | _ => none
  termination_by chars => chars.length

def base64EncodeStr (data : List UInt8) : String := String.ofList (base64Encode data)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // nix32 (the crux)
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def nix32Alphabet : List Char := "0123456789abcdfghijklmnpqrsvwxyz".toList

/-- `ceil(n*8/5)` — the encoded length (0 for empty). -/
def nix32EncodedLen (count : Nat) : Nat := if count = 0 then 0 else (count * 8 + 4) / 5

/-- nix32 encode — one 5-bit group per output char, LSB-first, the whole string
    reversed (`result[len-1-i]`, mirroring `nix32::encode`). -/
def nix32Encode (data : List UInt8) : List Char :=
  let len := nix32EncodedLen data.length
  let groups :=
    (List.range len).map fun idx =>
      let bitPos := idx * 5
      let bytePos := bitPos / 8
      let bitOff := bitPos % 8
      let lowBits : Nat :=
        if bytePos < data.length then (data.getD bytePos 0).toNat >>> bitOff else 0
      let highBits : Nat :=
        if bitOff > 3 ∧ bytePos + 1 < data.length then
          (data.getD (bytePos + 1) 0).toNat <<< (8 - bitOff)
        else
          0
      nix32Alphabet.getD ((lowBits ||| highBits) &&& 0x1f) '0'
  groups.reverse

/-- nix32 char → 5-bit value; `none` for e/o/u/t and any non-alphabet char. -/
def nix32Val (cursor : Char) : Option Nat :=
  match nix32Alphabet.idxOf? cursor with
  | some index => some index
  | none       => none

/-- nix32 decode — reverse of encode: read chars back-to-front, scatter 5-bit groups
    into the output bytes (mirroring `nix32::decode_to`). `none` on an invalid char. -/
def nix32Decode (state : List Char) : Option (List UInt8) :=
  if state.isEmpty then
    some []
  else
    let encodedLength := state.length
    let outLen := (encodedLength * 5) / 8
    let vals :=
      (List.range encodedLength).map fun idx => nix32Val (state.getD (encodedLength - 1 - idx) '0')
    if vals.any Option.isNone then
      none
    else
      let out :=
        (List.range encodedLength).foldl (init := (Array.replicate outLen (0 : UInt8))) fun arr idx =>
          let val := (vals.getD idx none).getD 0
          let bitPos := idx * 5
          let bytePos := bitPos / 8
          let bitOff := bitPos % 8
          let arr :=
            if bytePos < arr.size then
              arr.set! bytePos (arr.getD bytePos 0 ||| UInt8.ofNat (val <<< bitOff))
            else
              arr
          if bitOff > 3 ∧ bytePos + 1 < arr.size then
            arr.set! (bytePos + 1) (arr.getD (bytePos + 1) 0 ||| UInt8.ofNat (val >>> (8 - bitOff)))
          else
            arr
      some out.toList

def nix32EncodeStr (data : List UInt8) : String := String.ofList (nix32Encode data)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // it matches Nix — canonical vectors
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- base16: the universally-known `deadbeef`.
example : base16EncodeStr [0xde, 0xad, 0xbe, 0xef] = "deadbeef" := by native_decide

example : base16Decode "DeadBeef".toList = some [0xde, 0xad, 0xbe, 0xef] := by native_decide

example : base16Decode (base16Encode [1, 2, 3, 250, 255]) = some [1, 2, 3, 250, 255] := by
  native_decide

-- base64: RFC 4648 vectors — "Man"/"Ma"/"M" → TWFu / TWE= / TQ==.
example : base64EncodeStr [77, 97, 110] = "TWFu" := by native_decide

example : base64EncodeStr [77, 97] = "TWE=" := by native_decide
example : base64EncodeStr [77] = "TQ==" := by native_decide
example : base64Decode "TWFu".toList = some [77, 97, 110] := by native_decide

example : base64Decode (base64Encode [0, 1, 2, 3, 4, 250]) = some [0, 1, 2, 3, 4, 250] := by
  native_decide

-- nix32: empty, and round-trips (incl. a 32-byte SHA256-sized buffer → 52 chars).
example : nix32EncodeStr [] = "" := by native_decide

example : (nix32EncodeStr (List.replicate 32 0)).length = 52 := by native_decide
example : nix32Decode (nix32Encode [1, 2, 3, 4, 5]) = some [1, 2, 3, 4, 5] := by native_decide

example :
    nix32Decode (nix32Encode (List.range 20 |>.map (·.toUInt8)))
        = some (List.range 20 |>.map (·.toUInt8)) := by native_decide
-- an out-of-alphabet char (e/o/u/t) is rejected.
example : nix32Decode "eee".toList = none := by native_decide

end Continuity.Codec.Wire.Nix.Encoding
