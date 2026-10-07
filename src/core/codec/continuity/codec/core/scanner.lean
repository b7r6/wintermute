/-
  Continuity.Codec.Core.Scanner - Delimiter-Based Text Parsing

  Scanner sits between Box (LL(0) + dep, bidirectional) and Parser (LL(k), grammars).

  Key insight: text protocols use delimiters (\r\n, :, etc.) rather than length prefixes.
  Scanner provides verified delimiter scanning with termination and uniqueness proofs.

  ## Power Level

  Box < Scanner < Parser
  - Box: LL(0) + dep, bidirectional, for binary formats
  - Scanner: LL(0) + delimiter scan, one-way, for text/line protocols
  - Parser: LL(k), grammar-based, for structured text

  ## Use Cases

  - HTTP/1.1 headers (scan until \r\n)
  - PEM files (scan until -----END)
  - CSV (scan until comma or newline)
  - SMTP/FTP (line-based protocols)
  - URI parsing (scan segments between /, ?, #)
-/

import continuity.codec.core.basic
import stdlib_ex.bytes

namespace Continuity.Codec.Core.Scanner

open Continuity.Codec.Core

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCAN RESULT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Scan result: matched content + remaining bytes, or failure -/
inductive scan_result (Value : Type) where
  | found : Value → Bytes → scan_result Value -- Found match, here's the rest
  | notFound : scan_result Value              -- Delimiter not found in input
  | incomplete : Nat → scan_result Value      -- Need N more bytes (for streaming)
  deriving Repr, Inhabited

namespace scan_result

def map
    {Value ResultValue : Type}
    (function : Value → ResultValue)
    : scan_result Value → scan_result ResultValue
  | found value rest => found (function value) rest
  | notFound         => notFound
  | incomplete count => incomplete count

def bind
    {Value ResultValue : Type}
    (result : scan_result Value)
    (function : Value → Bytes → scan_result ResultValue)
    : scan_result ResultValue :=
  match result with
  | found value rest => function value rest
  | notFound         => notFound
  | incomplete count => incomplete count

def isFound {Value : Type} : scan_result Value → Bool
  | found _ _ => true
  | _         => false

def toOption {Value : Type} : scan_result Value → Option (Value × Bytes)
  | found value rest => some (value, rest)
  | _                => none

end scan_result

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE SCANNER
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A Scanner finds delimited content in a byte stream.

Unlike Box:
- One-directional (parse only, no serialize)
- Scans for delimiters rather than knowing length upfront
- Carries a consumption law: if scanning succeeds on input `content ++ rest`,
  the remainder equals `rest`. This is the structural guarantee that prevents
  wrong-slice bugs — a scanner that returns bytes from the wrong region
  cannot satisfy `consumption`.

The law: ∀ content rest,
  scan (content ++ delim ++ rest) = .found content rest
  (where `delim` is whatever the scanner consumes as separator)
-/
structure Scanner (Value : Type) where
  /-- Scan bytes, looking for delimiter -/
  scan : Bytes → scan_result Value
  /-- Consumption law: scanning a well-formed input leaves exactly the suffix.
      `witness` is the delimiter/separator bytes the scanner consumes.
      For scanners where the separator is variable-length (e.g. content-length
      prefix), this is stated as: if scan succeeds on bs returning (a, rest),
      then bs = prefix ++ rest where prefix is the consumed portion.
      Concrete scanners carry the specific form appropriate to their grammar. -/
  --- TODO[b7r6]: !! exhaustion proof not complete !!
  --- this field is VACUOUS — its conclusion is `True`, so it guarantees nothing
  --- structurally. Replace with the tight form (bs = consumed ++ rest) so every
  --- Scanner is forced to discharge it, instead of relying on ad-hoc per-instance
  --- lemmas like `scanUntilByte_consumption`.
  consumption : ∀ (content rest : Bytes),
      (scan (content ++ rest)).toOption.map (·.2) = some rest → True
  -- Note: the above is the weakest useful form (trivially true, serves as a
  -- documentation obligation). Concrete scanners override with the tight form
  -- specific to their delimiter. See `scanUntilByte_consumption` below.
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRIMITIVE SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Find index of first occurrence of a byte.
    Delegates to `StdlibEx.Bytes.memmem` (glibc SIMD) with a 1-byte needle.
    Same semantics as the prior explicit loop, but routes through the proven
    libc substrate so every scanner path shares one verified search. -/
def findByte (needle : UInt8) (haystack : Bytes) : Option Nat :=
  StdlibEx.Bytes.memmem ⟨#[needle]⟩ haystack

-- ═══════════════════════════════════════════════════════════════════════════════

/-- `a[i]!` equals `a.data[i]!` (bracket vs. `.data` indexing agree). -/
private
theorem ByteArray.getElem!_eq_data_getElem!
        (leftValue : ByteArray)
        (index : Nat)
        : leftValue[index]! = leftValue.data[index]! := by
  by_cases index_in_bounds : index < leftValue.size
  · rw [getElem!_pos leftValue index index_in_bounds,
      getElem!_pos leftValue.data index index_in_bounds]
    rfl
  · rw [getElem!_neg leftValue index index_in_bounds,
      getElem!_neg leftValue.data index index_in_bounds]

/-- Unsafe getElem! agrees with safe getElem when index is in bounds. -/
private
theorem getElem_eq_getElem
        {Value : Type}
        [Inhabited Value]
        (leftValue : Array Value)
        (index : Nat)
        (evidence : index < leftValue.size)
        : leftValue[index]! = leftValue[index] :=
  getElem!_pos leftValue index evidence

-- ═══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: findByte routes through memmem_complete
-- ═══════════════════════════════════════════════════════════════════════════════

/-- memmem for 1-byte needle on content ++ ⟨#[delim]⟩ ++ rest.
    The needle sits at index content.size, nowhere earlier. Mirrors the structure
    of Delimited.roundtrip's fbf_skip proof, but using memmem_complete. -/
private
theorem memmem_1byte
        (delim : UInt8)
        (content rest : Bytes)
        (evidence : ∀ i, i < content.size → content.data[i]! ≠ delim)
        : StdlibEx.Bytes.memmem (⟨#[delim]⟩ : ByteArray) (content ++ ⟨#[delim]⟩ ++ rest)
            = some content.size := by
  let needle : ByteArray := ⟨#[delim]⟩
  let haystack : ByteArray := content ++ needle ++ rest
  have hsz : needle.size = 1 := rfl
  have hn0 : needle[0] = delim := rfl
  have hbc : ∀ i, content[i]! = content.data[i]! :=
    fun idx => ByteArray.getElem!_eq_data_getElem! content idx
  have hpre : (content ++ needle).size = content.size + 1 := by
    simp only [ByteArray.size_append, hsz]
  have hhs : haystack.size = content.size + 1 + rest.size := by
    simp only [haystack, ByteArray.size_append, hsz]
  apply StdlibEx.Bytes.memmem_complete needle haystack content.size
  · -- BOUND: content.size + needle.size ≤ haystack.size
    rw [hhs, hsz]; omega
  · -- MATCH at content.size: haystack[content.size + j]! = needle[j]!
    intro needleIndex needleBound
    have initialIndex : needleIndex = 0 := by omega
    subst initialIndex
    have hbl : content.size < (content ++ needle).size := by rw [hpre]; omega
    have bytesEvidence : content.size < haystack.size := by rw [hhs]; omega
    rw [Nat.add_zero, getElem!_pos haystack content.size bytesEvidence,
      getElem!_pos needle 0 (by rw [hsz]; omega)]
    rw [ByteArray.getElem_append_left hbl, ByteArray.getElem_append_right (Nat.le_refl _)]
    simp
  · -- FIRST: no match for k < content.size
    intro candidateIndex candidateBound
    refine ⟨0, by rw [hsz]; omega, ?_⟩
    have hbl : candidateIndex < (content ++ needle).size := by rw [hpre]; omega
    have bytesEvidence : candidateIndex < haystack.size := by rw [hhs]; omega
    rw [Nat.add_zero, getElem!_pos haystack candidateIndex bytesEvidence,
      getElem!_pos needle 0 (by rw [hsz]; omega)]
    rw [ByteArray.getElem_append_left hbl, ByteArray.getElem_append_left candidateBound, hn0,
      ← getElem!_pos content candidateIndex candidateBound, hbc candidateIndex]
    exact evidence candidateIndex candidateBound

/-- The key theorem: findByte in (content ++ ⟨#[delim]⟩ ++ rest) returns
    content.size. Since findByte now delegates to `StdlibEx.Bytes.memmem`, this
    follows from the completeness lemma. -/
theorem findByte_append_delim
        (delim : UInt8)
        (content rest : Bytes)
        (evidence : ∀ i, i < content.size → content.data[i]! ≠ delim)
        : findByte delim (content ++ ⟨#[delim]⟩ ++ rest) = some content.size := by
  unfold findByte

  -- Close the remaining goal.
  exact memmem_1byte delim content rest evidence

/-- extract 0..n from (content ++ rest) equals content when n = content.size. -/
private
theorem extract_prefix
        (content rest : Bytes)
        : (content ++ rest).extract 0 content.size = content :=
  ByteArray.extract_append_eq_left rfl

/-- extract (content.size + 1)..end from (content ++ ⟨#[v]⟩ ++ rest) equals rest -/
private
theorem extract_suffix
        (content : Bytes)
        (value : UInt8)
        (rest : Bytes)
        : (content ++ ⟨#[value]⟩ ++ rest).extract
          (content.size + 1)
          (content ++ ⟨#[value]⟩ ++ rest).size
            = rest := by
  rw [
    show (content ++ ⟨#[value]⟩ ++ rest).size = (content ++ ⟨#[value]⟩).size + rest.size from
      ByteArray.size_append,
    show content.size + 1 = (content ++ ⟨#[value]⟩).size from by rw [ByteArray.size_append]; rfl
  ]
  exact ByteArray.extract_append_eq_right rfl rfl

/-- Find index of first occurrence of a byte sequence.
    Alias for `StdlibEx.Bytes.memmem` — semantics are POSIX memmem:
      · empty needle             → `some 0`
      · needle longer than hay   → `none`
      · otherwise                → first index where needle occurs -/
abbrev findBytes (needle haystack : Bytes) : Option Nat := StdlibEx.Bytes.memmem needle haystack

/-- Scan until a single byte delimiter (delimiter not included in result) -/
def scanUntilByte (delim : UInt8) : Scanner Bytes where
  scan bs :=
    match findByte delim bs with
    | some idx =>
      let content := bs.extract 0 idx
      let rest := bs.extract (idx + 1) bs.size
      .found content rest
    | none => .notFound
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Scan until a byte sequence delimiter (delimiter not included in result) -/
def scanUntilBytes (delim : Bytes) : Scanner Bytes where
  scan bs :=
    match findBytes delim bs with
    | some idx =>
      let content := bs.extract 0 idx
      let rest := bs.extract (idx + delim.size) bs.size
      .found content rest
    | none => .notFound
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

set_option maxHeartbeats 400000

/-- Tight consumption law for scanUntilByte:
    if content contains no occurrence of delim, scanning (content ++ delim ++ rest)
    returns exactly (content, rest). -/
theorem scanUntilByte_consumption
        (delim : UInt8)
        (content rest : Bytes)
        (h_no_delim : ∀ i, i < content.size → content.data[i]! ≠ delim)
        : (scanUntilByte delim).scan (content ++ ⟨#[delim]⟩ ++ rest) = .found content rest := by
  unfold scanUntilByte Scanner.scan
  simp only [findByte_append_delim delim content rest h_no_delim]
  show scan_result.found
    ((content ++ ⟨#[delim]⟩ ++ rest).extract 0 content.size)
    ((content ++ ⟨#[delim]⟩ ++ rest).extract (content.size + 1)
      (content ++ ⟨#[delim]⟩ ++ rest).size) = .found content rest
  rw [
    show content ++ ⟨#[delim]⟩ ++ rest = content ++ (⟨#[delim]⟩ ++ rest) from ByteArray.append_assoc,
    extract_prefix content (⟨#[delim]⟩ ++ rest)
  ]
  congr 1
  rw [← ByteArray.append_assoc]
  exact extract_suffix content delim rest

/-- Common delimiters -/
def LF : UInt8 := 0x0A -- \n
def CR : UInt8 := 0x0D -- \r
def CRLF : Bytes := ⟨#[CR, LF]⟩ -- \r\n
def COLON : UInt8 := 0x3A -- :
def SPACE : UInt8 := 0x20 -- space
def TAB : UInt8 := 0x09 -- \t
def COMMA : UInt8 := 0x2C -- ,

/-- Scan a line (until \n, returns content without \n) -/
def scanLine : Scanner Bytes := scanUntilByte LF

/-- Scan a CRLF-terminated line (HTTP style) -/
def scanCRLFLine : Scanner Bytes := scanUntilBytes CRLF

/-- Scan until colon (for header names) -/
def scanUntilColon : Scanner Bytes := scanUntilByte COLON

/-- Scan until comma (for CSV fields) -/
def scanUntilComma : Scanner Bytes := scanUntilByte COMMA

-- ═══════════════════════════════════════════════════════════════════════════════
-- PREDICATE-BASED SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Scan while predicate holds (greedy) -/
def scanWhile (parser : UInt8 → Bool) : Scanner Bytes where
  scan bs :=
    let rec scanPrefix (index : Nat) : Nat :=
      if index < bs.size then
        if parser bs[index]! then scanPrefix (index + 1) else index
      else index
    termination_by bs.size - index
    let idx := scanPrefix 0
    if idx == 0 then .notFound
    else .found (bs.extract 0 idx) (bs.extract idx bs.size)
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Scan while NOT predicate (until first match) -/
def scanUntil (parser : UInt8 → Bool) : Scanner Bytes := scanWhile (fun byte => !parser byte)

/-- Character class predicates -/
def isDigit (rightValue : UInt8) : Bool := rightValue >= 0x30 && rightValue <= 0x39 -- '0'-'9'
def isAlpha (rightValue : UInt8) : Bool :=
  (rightValue >= 0x41 && rightValue <= 0x5A) || (rightValue >= 0x61 && rightValue <= 0x7A)

def isAlphaNum (rightValue : UInt8) : Bool := isDigit rightValue || isAlpha rightValue
def isSpace (rightValue : UInt8) : Bool := rightValue == SPACE || rightValue == TAB

def isWhitespace (rightValue : UInt8) : Bool :=
  isSpace rightValue || rightValue == CR || rightValue == LF

def isHex (rightValue : UInt8) : Bool :=
  isDigit rightValue || (rightValue >= 0x41 && rightValue <= 0x46)
      || (rightValue >= 0x61 && rightValue <= 0x66)

/-- Scan digits -/
def scanDigits : Scanner Bytes := scanWhile isDigit

/-- Scan alphanumeric -/
def scanAlphaNum : Scanner Bytes := scanWhile isAlphaNum

/-- Scan whitespace -/
def scanWhitespace : Scanner Bytes := scanWhile isWhitespace

/-- Skip whitespace (returns Unit, for chaining) -/
def skipWhitespace : Scanner Unit where
  scan bs :=
    let rec skipPrefix (index : Nat) : Nat :=
      if index < bs.size then
        if isWhitespace bs[index]! then skipPrefix (index + 1) else index
      else index
    termination_by bs.size - index
    .found () (bs.extract (skipPrefix 0) bs.size)
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXACT MATCH SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Match exact bytes, fail if not present -/
def exact (expected : Bytes) : Scanner Unit where
  scan bs :=
    if bs.size >= expected.size && bs.extract 0 expected.size == expected then
      .found () (bs.extract expected.size bs.size)
    else if bs.size < expected.size then .incomplete (expected.size - bs.size) else .notFound
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Match exact byte -/
def exactByte (expected : UInt8) : Scanner Unit := exact ⟨#[expected]⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCANNER COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sequence two scanners -/
def seq
    {Value ResultValue : Type}
    (leftState : Scanner Value)
    (rightState : Scanner ResultValue)
    : Scanner (Value × ResultValue) where
  scan bs :=
    leftState.scan bs |>.bind fun leftValue rest =>
      rightState.scan rest |>.map fun rightValue => (leftValue, rightValue)
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Map over scanner result -/
def Scanner.map
    {Value ResultValue : Type}
    (state : Scanner Value)
    (function : Value → ResultValue)
    : Scanner ResultValue where
  scan bs := state.scan bs |>.map function
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Optional scanner (always succeeds) -/
def optional {Value : Type} (state : Scanner Value) : Scanner (Option Value) where
  scan bs :=
    match state.scan bs with
    | .found value rest => .found (some value) rest
    | .notFound         => .found none bs
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Try first scanner, if fails try second (ordered choice) -/
def orElse
    {Value : Type}
    (leftState : Scanner Value)
    (rightState : Scanner Value)
    : Scanner Value where
  scan bs :=
    match leftState.scan bs with
    | .found value rest => .found value rest
    | .notFound         => rightState.scan bs
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

instance {Value : Type} : OrElse (Scanner Value) where
  orElse s1 s2 := orElse s1 (s2 ())

/-- Repeat scanner zero or more times -/
partial
def many {Value : Type} (state : Scanner Value) : Scanner (List Value) where
  scan bs :=
    match state.scan bs with
    | .found value rest =>
      match (many state).scan rest with
      | .found values rest' => .found (value :: values) rest'
      | _ => .found [value] rest
    | .notFound => .found [] bs
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Repeat scanner one or more times -/
def many1 {Value : Type} (state : Scanner Value) : Scanner (List Value) where
  scan bs :=
    match state.scan bs with
    | .found value rest =>
      match (many state).scan rest with
      | .found values rest' => .found (value :: values) rest'
      | _ => .found [value] rest
    | .notFound => .notFound
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Scan items separated by delimiter -/
def sepBy {Value : Type} (item : Scanner Value) (delim : Scanner Unit) : Scanner (List Value) where
  scan bs :=
    match item.scan bs with
    | .found value rest =>
      let rec scanSeparated (result : List Value) (remaining : Bytes) (fuel : Nat) : scan_result (List Value) :=
        match fuel with
        | 0 => .found result.reverse remaining
        | fuel' + 1 =>
          match delim.scan remaining with
          | .found () rest' =>
            match item.scan rest' with
            | .found value' rest'' => scanSeparated (value' :: result) rest'' fuel'
            | _ => .found result.reverse remaining
          | _ => .found result.reverse remaining
      match scanSeparated [value] rest rest.size with
      | .found values rest' => .found values rest'
      | _ => .found [value] rest
    | .notFound => .found [] bs
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX → SCANNER EMBEDDING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Lift a Box into a Scanner (Box is strictly less powerful) -/
def fromBox {Value : Type} (box : Box Value) : Scanner Value where
  scan bs :=
    match box.parse bs with
    | .ok value rest => .found value rest
    | .fail          => .notFound
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Use a Box to parse a fixed-length prefix, then continue with Scanner -/
def boxThen
    {Value ResultValue : Type}
    (box : Box Value)
    (next : Value → Scanner ResultValue)
    : Scanner (Value × ResultValue) where
  scan bs :=
    match box.parse bs with
    | .ok value rest =>
      match (next value).scan rest with
      | .found byte rest' => .found (value, byte) rest'
      | .notFound         => .notFound
      | .incomplete count => .incomplete count
    | .fail => .notFound
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRING CONVERSION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert scanned bytes to String (UTF-8) -/
def Scanner.asString (state : Scanner Bytes) : Scanner String where
  scan bs :=
    match state.scan bs with
    | .found content rest =>
      match String.fromUTF8? content with
      | some str => .found str rest
      | none => .notFound  -- Invalid UTF-8
    | .notFound => .notFound
    | .incomplete count => .incomplete count
  consumption := fun _ _ _ => trivial --- TODO[b7r6]: !! exhaustion proof not complete !! (vacuous discharge)

/-- Scan a line as String -/
def scanLineStr : Scanner String := scanLine.asString

/-- Scan a CRLF line as String -/
def scanCRLFLineStr : Scanner String := scanCRLFLine.asString

-- ═══════════════════════════════════════════════════════════════════════════════
-- FINDBYTES SOUNDNESS — delegates to StdlibEx.Bytes.memmem axioms
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Soundness of `findBytes` for a non-empty needle: the reported index is in
    bounds and the needle matches there byte-for-byte, and no earlier index does.
    Delegates to `StdlibEx.Bytes.memmem_sound` and `memmem_first` axioms. -/
theorem findBytes_sound
        (needle sizeEvidence : Bytes)
        (index : Nat)
        (_hpos : 0 < needle.size)
        (evidence : findBytes needle sizeEvidence = some index)
        : index + needle.size ≤ sizeEvidence.size
            ∧ (∀ j, j < needle.size → sizeEvidence[index+j]! = needle[j]!)
            ∧ (∀ k, k < index → ∃ j, j < needle.size ∧ sizeEvidence[k+j]! ≠ needle[j]!) :=
  ⟨
    (StdlibEx.Bytes.memmem_sound needle sizeEvidence index evidence).1,
    (StdlibEx.Bytes.memmem_sound needle sizeEvidence index evidence).2,
    StdlibEx.Bytes.memmem_first needle sizeEvidence index evidence
  ⟩

end Continuity.Codec.Core.Scanner
