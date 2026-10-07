/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // CONTINUITY // CODEC // WIRE // NIX // URL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The verifiable core of the Nix URL surface — the verified reference the generator
    (`Codec/Codegen/NixUrl`) mirrors. Ported from `nix/url/url.{h,cpp}`:

      · percent_encode / percent_decode  — RFC 3986 %-encoding (unreserved =
        ALPHA / DIGIT / `-` `.` `_` `~`; everything else `%XX`, uppercase hex)
      · parse_scheme                     — compound schemes `git+https` → (git, https)
      · is_special_scheme / default_port — the WHATWG special set + their ports

    The full RFC 3986 `parse` (a 19 KB state machine; the project's fast path delegates
    to the third-party `ada`) is NOT reimplemented here — it's not a faithful
    generation target. This is the pure, round-trippable heart that the rest builds on.
    Correctness is pinned by `native_decide` (`%20`/`%2F` encoding, round-trips,
    `git+https`, `https`→443); the generated C++ cross-checks the SAME vectors.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Codec.Wire.Nix.Url

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // percent-encoding
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

private
def inR (lowerBound codepoint upperBound : Nat) : Bool :=
  lowerBound.ble codepoint && codepoint.ble upperBound

/-- RFC 3986 unreserved: `ALPHA / DIGIT / - . _ ~`. -/
def isUnreserved (cursor : Char) : Bool :=
  let codepoint := cursor.toNat
  inR 65 codepoint 90 || inR 97 codepoint 122 || inR 48 codepoint 57 || cursor == '-'
      || cursor == '.'
      || cursor == '_'
      || cursor == '~'

def hexUpper : List Char := "0123456789ABCDEF".toList

/-- Hex digit value (case-insensitive); `none` if not a hex digit. -/
def hexVal (cursor : Char) : Option Nat :=
  if '0' ≤ cursor ∧ cursor ≤ '9' then
    some (cursor.toNat - '0'.toNat)
  else if 'a' ≤ cursor ∧ cursor ≤ 'f' then
    some (cursor.toNat - 'a'.toNat + 10)
  else if 'A' ≤ cursor ∧ cursor ≤ 'F' then some (cursor.toNat - 'A'.toNat + 10) else none

/-- Percent-encode: keep unreserved chars (and any in `keep`); `%XX` everything else. -/
def percentEncode (input keep : List Char) : List Char :=
  input.flatMap fun character =>
    if isUnreserved character || keep.contains character then
      [character]
    else
      ['%', hexUpper.getD (character.toNat >>> 4) '0', hexUpper.getD (character.toNat &&& 0xf) '0']

/-- Percent-decode: `%XX` (two valid hex digits) → byte; anything else passes through.
    Mirrors the C++ index scan (`%` needs two hex digits following, else literal `%`). -/
def percentDecode : List Char → List Char
  | [] => []
  | '%' :: value :: byte :: rest =>
    match hexVal value, hexVal byte with
    | some high, some low => Char.ofNat ((high <<< 4) ||| low) :: percentDecode rest
    | _, _                => '%' :: percentDecode (value :: byte :: rest)
  | code :: rest => code :: percentDecode rest

def percentEncodeStr (input keep : String) : String :=
  String.ofList (percentEncode input.toList keep.toList)

def percentDecodeStr (input : String) : String := String.ofList (percentDecode input.toList)

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // scheme helpers
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compound scheme `git+https` → (`some "git"`, `"https"`); plain `https` → (`none`, `https`).
    Splits on the FIRST `+` (the `application+transport` form). -/
def parseScheme (state : String) : Option String × String :=
  match state.splitOn "+" with
  | [tail]        => (none, tail)
  | value :: rest => (some value, String.intercalate "+" rest)
  | []            => (none, "")

/-- The WHATWG "special" schemes. -/
def isSpecialScheme (state : String) : Bool :=
  state == "http" || state == "https" || state == "ws" || state == "wss" || state == "ftp"
      || state == "file"

/-- Default port for a special scheme (`0` = none). -/
def defaultPort (state : String) : Nat :=
  if state == "http" || state == "ws" then
    80
  else if state == "https" || state == "wss" then 443 else if state == "ftp" then 21 else 0

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // it matches — canonical vectors
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

example : percentEncodeStr "a b/c?" "" = "a%20b%2Fc%3F" := by native_decide

example : percentEncodeStr "a/b" "/" = "a/b" := by native_decide -- keep '/'
example : percentDecodeStr "%41%42-z" = "AB-z" := by native_decide
example : percentDecodeStr "%4" = "%4" := by native_decide -- truncated → literal
example : percentDecodeStr (percentEncodeStr "Hello, World! /?#" "") = "Hello, World! /?#" := by
  native_decide

example : parseScheme "git+https" = (some "git", "https") := by native_decide
example : parseScheme "https" = (none, "https") := by native_decide
example : isSpecialScheme "file" = true := by native_decide
example : defaultPort "https" = 443 := by native_decide
example : defaultPort "ssh" = 0 := by native_decide

end Continuity.Codec.Wire.Nix.Url
