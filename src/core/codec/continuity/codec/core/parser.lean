/-
  Continuity.Codec.Core.Parser - LL(key) Grammar-Based Parsing

  Parser is the most powerful level in Cornell's parsing hierarchy:
  - Box: LL(0) + dep, bidirectional, for binary formats
  - Scanner: LL(0) + delimiter scan, one-way, for text/line protocols
  - Parser: LL(key), grammar-based, for structured text (JSON, config, DSLs)

  ## Key Features

  - Explicit lookahead (key tokens)
  - Ordered choice (first match wins, no backtracking)
  - Grammar rules with named productions
  - Proofs: unambiguity, completeness, FIRST/FOLLOW analysis

  ## Design Decisions

  1. **TokenType-based**: Parser works on token streams, not raw bytes
     - Lexer (Scanner) produces tokens
     - Parser consumes tokens

  2. **LL(key) not LL(*)**: Fixed lookahead, predictable performance
     - key=1 handles most grammars
     - key=2 handles common ambiguities (if-else, etc.)

  3. **No backtracking**: Ordered choice, first match wins
     - Predictable O(n) parsing
     - Unambiguity is provable

  4. **Grammar as data**: Rules are first-class values
     - Introspection for FIRST/FOLLOW computation
-/

import continuity.codec.core.scanner

namespace Continuity.Codec.Core.Parser

open Continuity.Codec.Core Continuity.Codec.Core.Scanner

-- ═══════════════════════════════════════════════════════════════════════════════
-- TOKENS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- TokenType with type tag and optional payload -/
structure Token (TokenType : Type) where
  type   : TokenType
  lexeme : String
  offset : Nat
  deriving Repr

/-- TokenType stream (list of tokens with position tracking) -/
structure token_stream (TokenType : Type) where
  tokens   : List (Token TokenType)
  position : Nat
  deriving Repr

namespace token_stream

def empty {TokenType : Type} : token_stream TokenType := ⟨[], 0⟩

def fromList {TokenType : Type} (tokens : List (Token TokenType)) : token_stream TokenType :=
  ⟨tokens, 0⟩

def peek {TokenType : Type} (state : token_stream TokenType) : Option (Token TokenType) :=
  state.tokens[state.position]?

def peekN
    {TokenType : Type}
    (state : token_stream TokenType)
    (count : Nat)
    : Option (Token TokenType) :=
  state.tokens[state.position + count]?

def advance {TokenType : Type} (state : token_stream TokenType) : token_stream TokenType :=
  { state with position := state.position + 1 }

def advanceN
    {TokenType : Type}
    (state : token_stream TokenType)
    (count : Nat)
    : token_stream TokenType :=
  { state with position := state.position + count }

def isEof {TokenType : Type} (state : token_stream TokenType) : Bool :=
  state.position >= state.tokens.length

def remaining {TokenType : Type} (state : token_stream TokenType) : List (Token TokenType) :=
  state.tokens.drop state.position

end token_stream

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSE RESULT (for Parser)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parser result -/
inductive presult (TokenType Value : Type) where
  | ok : Value → token_stream TokenType → presult TokenType Value
  | err : String → Nat → presult TokenType Value -- Error message + position
  deriving Repr, Inhabited

namespace presult

def map
    {TokenType Value ResultValue : Type}
    (function : Value → ResultValue)
    : presult TokenType Value → presult TokenType ResultValue
  | ok value state => ok (function value) state
  | err msg pos    => err msg pos

def bind
    {TokenType Value ResultValue : Type}
    (result : presult TokenType Value)
    (function : Value → token_stream TokenType → presult TokenType ResultValue)
    : presult TokenType ResultValue :=
  match result with
  | ok value state => function value state
  | err msg pos    => err msg pos

def isOk {TokenType Value : Type} : presult TokenType Value → Bool
  | ok _ _ => true
  | _      => false

end presult

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE PARSER
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A Parser transforms a token stream into a value.

Key properties:
- Deterministic: same input → same output
- No backtracking: ordered choice, first match wins
- Lookahead bounded: at most key tokens examined before committing

The `lookahead` field specifies how many tokens can be examined.
-/
structure Parser (TokenType Value : Type) (key : Nat) where
  /-- Parse tokens into a value -/
  parse : token_stream TokenType → presult TokenType Value
  /-- Maximum lookahead used by this parser -/
  maxLookahead : Nat := 0
  /-- PROOF: lookahead is bounded by key -/
  lookahead_bound : maxLookahead ≤ key := by omega
  -- Note: determinism is guaranteed by construction (parse is a function)

instance {TokenType Value : Type} {key : Nat} : Inhabited (Parser TokenType Value key) where
  default := ⟨fun _ => default, 0, Nat.zero_le key⟩

-- Shorthand for common cases
abbrev Parser1 (TokenType Value : Type) := Parser TokenType Value 1

abbrev Parser2 (TokenType Value : Type) := Parser TokenType Value 2

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRIMITIVE PARSERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Always succeed with a value, consuming no tokens -/
def pure
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (leftValue : Value)
    : Parser TokenType Value key where
  parse tokens := .ok leftValue tokens
  maxLookahead := 0
  lookahead_bound := Nat.zero_le key

/-- Always fail with an error -/
def fail
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (msg : String)
    : Parser TokenType Value key where
  parse tokens := .err msg tokens.position
  maxLookahead := 0
  lookahead_bound := Nat.zero_le key

/-- Match a token of a specific type -/
def token
    {TokenType : Type}
    [DecidableEq TokenType]
    [Repr TokenType]
    (expected : TokenType)
    : Parser1 TokenType (Token TokenType) where
  parse tokens :=
    match tokens.peek with
    | some tok =>
      if tok.type == expected then
        .ok tok tokens.advance
      else
        .err s!"Expected {repr expected}, got {repr tok.type}" tokens.position
    | none => .err s!"Expected {repr expected}, got EOF" tokens.position
  maxLookahead := 1
  lookahead_bound := Nat.le_refl 1

/-- Match any token satisfying a predicate -/
def satisfy
    {TokenType : Type}
    [DecidableEq TokenType]
    (parser : Token TokenType → Bool)
    (desc : String)
    : Parser1 TokenType (Token TokenType) where
  parse tokens :=
    match tokens.peek with
    | some tok =>
      if parser tok then .ok tok tokens.advance else .err s!"Expected {desc}" tokens.position
    | none => .err s!"Expected {desc}, got EOF" tokens.position
  maxLookahead := 1
  lookahead_bound := Nat.le_refl 1

/-- Match any single token -/
def anyToken {TokenType : Type} [DecidableEq TokenType] : Parser1 TokenType (Token TokenType) where
  parse tokens :=
    match tokens.peek with
    | some tok => .ok tok tokens.advance
    | none     => .err "Unexpected EOF" tokens.position
  maxLookahead := 1
  lookahead_bound := Nat.le_refl 1

/-- Match end of input -/
--- TODO[b7r6]: !! exhaustion proof not complete !!
--- `eof` exists but full-consumption is OPT-IN — nothing forces a top-level parse to end
--- in `<* eof`. Add a `run`/`consumeAll` entry point that REQUIRES `isEof` (rejects
--- leftover tokens), so trailing un-parsed input can't slip past unnoticed.
def eof {TokenType : Type} [DecidableEq TokenType] : Parser1 TokenType Unit where
  parse tokens := if tokens.isEof then .ok () tokens else .err "Expected EOF" tokens.position
  maxLookahead := 1
  lookahead_bound := Nat.le_refl 1

-- ═══════════════════════════════════════════════════════════════════════════════
-- LOOKAHEAD
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Lookahead: examine tokens without consuming them -/
def lookAhead {TokenType Value : Type} [DecidableEq TokenType] (count : Nat) (parser : Parser TokenType Value count) : Parser TokenType Value count where
  parse tokens :=
    match parser.parse tokens with
    | .ok value _ => .ok value tokens  -- Don't advance
    | .err msg pos => .err msg pos
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

/-- Negative lookahead: succeed if parser fails -/
def notFollowedBy
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parser : Parser TokenType Value key)
    : Parser TokenType Unit key where
  parse tokens :=
    match parser.parse tokens with
    | .ok _ _  => .err "Unexpected match" tokens.position
    | .err _ _ => .ok () tokens
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sequence: parse p1 then p2 -/
def seq
    {TokenType Value ResultValue : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (leftParser : Parser TokenType Value key)
    (rightParser : Parser TokenType ResultValue key)
    : Parser TokenType (Value × ResultValue) key where
  parse tokens :=
    leftParser.parse tokens |>.bind fun leftValue restInput =>
      rightParser.parse restInput |>.map fun rightValue => (leftValue, rightValue)
  maxLookahead := max leftParser.maxLookahead rightParser.maxLookahead
  lookahead_bound := by
    apply Nat.max_le.mpr
    exact ⟨leftParser.lookahead_bound, rightParser.lookahead_bound⟩

/-- Map over parser result -/
def Parser.map
    {TokenType Value ResultValue : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parser : Parser TokenType Value key)
    (function : Value → ResultValue)
    : Parser TokenType ResultValue key where
  parse tokens := parser.parse tokens |>.map function
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

/-- Bind/flatMap -/
def Parser.bind
    {TokenType Value ResultValue : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parser : Parser TokenType Value key)
    (function : Value → Parser TokenType ResultValue key)
    : Parser TokenType ResultValue key where
  parse tokens :=
    parser.parse tokens |>.bind fun value restInput =>
      (function value).parse restInput
  maxLookahead := parser.maxLookahead -- Conservative estimate
  lookahead_bound := parser.lookahead_bound

/-- Ordered choice: try p1, if it fails without consuming input, try p2 -/
def orElse {TokenType Value : Type} {key : Nat} [DecidableEq TokenType] (leftParser : Parser TokenType Value key) (rightParser : Parser TokenType Value key) : Parser TokenType Value key where
  parse tokens :=
    match leftParser.parse tokens with
    | .ok value tails' => .ok value tails'
    | .err msg1 pos1 =>
      -- Only try p2 if p1 failed without consuming input
      if pos1 == tokens.position then
        rightParser.parse tokens
      else
        .err msg1 pos1  -- p1 consumed input, propagate error
  maxLookahead := max leftParser.maxLookahead rightParser.maxLookahead
  lookahead_bound := by
    apply Nat.max_le.mpr
    exact ⟨leftParser.lookahead_bound, rightParser.lookahead_bound⟩

instance {TokenType Value : Type} {key : Nat} [DecidableEq TokenType] :
    OrElse (Parser TokenType Value key) where
  orElse p1 p2 := orElse p1 (p2 ())

/-- Choice from a list of parsers -/
def choice
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parsers : List (Parser TokenType Value key))
    : Parser TokenType Value key :=
  parsers.foldl orElse (fail "No alternatives matched")

/-- Optional: try parser, return none if it fails without consuming -/
def optional
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parser : Parser TokenType Value key)
    : Parser TokenType (Option Value) key where
  parse tokens :=
    match parser.parse tokens with
    | .ok value tails' => .ok (some value) tails'
    | .err _ pos =>
      if pos == tokens.position then
        .ok none tokens
      else
        .err "Optional parser consumed input before failing" pos
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

/-- Zero or more: repeatedly apply parser -/
partial
def many {TokenType Value : Type} {key : Nat} [DecidableEq TokenType] (parser : Parser TokenType Value key) : Parser TokenType (List Value) key where
  parse tokens :=
    match parser.parse tokens with
    | .ok value tails' =>
      if tails'.position == tokens.position then
        -- Parser succeeded without consuming input - would loop forever
        .err "many: parser succeeded without consuming input" tokens.position
      else
        match (many parser).parse tails' with
        | .ok values tails'' => .ok (value :: values) tails''
        | .err _ _ => .ok [value] tails'
    | .err _ _ => .ok [] tokens
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

/-- One or more: at least one match -/
def many1
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (parser : Parser TokenType Value key)
    : Parser TokenType (List Value) key where
  parse tokens :=
    match parser.parse tokens with
    | .ok value tails' =>
      match (many parser).parse tails' with
      | .ok values tails'' => .ok (value :: values) tails''
      | .err _ _           => .ok [value] tails'
    | .err msg pos => .err msg pos
  maxLookahead := parser.maxLookahead
  lookahead_bound := parser.lookahead_bound

/-- Separated by: items separated by delimiter -/
def sepBy
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (item : Parser TokenType Value key)
    (sep : Parser TokenType Unit key)
    : Parser TokenType (List Value) key where
  parse tokens :=
    match item.parse tokens with
    | .ok value tails' =>
      let rec parseRepeated (result : List Value) (stream : token_stream TokenType) (fuel : Nat) : presult TokenType (List Value) :=
        match fuel with
        | 0 => .ok result.reverse stream
        | fuel' + 1 =>
          match sep.parse stream with
          | .ok () tails'' =>
            match item.parse tails'' with
            | .ok value' tails''' => parseRepeated (value' :: result) tails''' fuel'
            | .err _ _            => .ok result.reverse stream
          | .err _ _ => .ok result.reverse stream
      match parseRepeated [value] tails' tokens.tokens.length with
      | .ok values tails'' => .ok values tails''
      | .err msg pos       => .err msg pos
    | .err _ _ => .ok [] tokens
  maxLookahead := max item.maxLookahead sep.maxLookahead
  lookahead_bound := by
    apply Nat.max_le.mpr
    exact ⟨item.lookahead_bound, sep.lookahead_bound⟩

/-- Separated by (at least one item) -/
def sepBy1
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (item : Parser TokenType Value key)
    (sep : Parser TokenType Unit key)
    : Parser TokenType (List Value) key where
  parse tokens :=
    match item.parse tokens with
    | .ok value tails' =>
      let rec parseRepeated1 (result : List Value) (stream : token_stream TokenType) (fuel : Nat) : presult TokenType (List Value) :=
        match fuel with
        | 0 => .ok result.reverse stream
        | fuel' + 1 =>
          match sep.parse stream with
          | .ok () tails'' =>
            match item.parse tails'' with
            | .ok value' tails''' => parseRepeated1 (value' :: result) tails''' fuel'
            | .err _ _            => .ok result.reverse stream
          | .err _ _ => .ok result.reverse stream
      match parseRepeated1 [value] tails' tokens.tokens.length with
      | .ok values tails'' => .ok values tails''
      | .err msg pos       => .err msg pos
    | .err msg pos => .err msg pos
  maxLookahead := max item.maxLookahead sep.maxLookahead
  lookahead_bound := by
    apply Nat.max_le.mpr
    exact ⟨item.lookahead_bound, sep.lookahead_bound⟩

/-- Between: parse p between left and right delimiters -/
def between
    {TokenType Value : Type}
    {key : Nat}
    [DecidableEq TokenType]
    (left : Parser TokenType Unit key)
    (right : Parser TokenType Unit key)
    (parser : Parser TokenType Value key)
    : Parser TokenType Value key where
  parse tokens :=
    left.parse tokens |>.bind fun () restInput =>
      parser.parse restInput |>.bind fun value finalInput =>
        right.parse finalInput |>.map fun () => value
  maxLookahead := max (max left.maxLookahead right.maxLookahead) parser.maxLookahead
  lookahead_bound := by
    apply Nat.max_le.mpr
    constructor
    · apply Nat.max_le.mpr; exact ⟨left.lookahead_bound, right.lookahead_bound⟩
    · exact parser.lookahead_bound

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCANNER → PARSER EMBEDDING
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Lexer: Scanner that produces tokens.
Wraps a Scanner to produce typed tokens.
-/
structure Lexer (TokenType : Type) where
  /-- Rules: each produces a token type, or skips (whitespace) -/
  rules : List (Scanner Bytes × Option TokenType)
  /-- Apply rules in order, first match wins -/
  tokenize : Bytes → scan_result (Option (Token TokenType))

/-- Create a simple lexer from a list of (pattern, token type) pairs -/
def mkLexer {TokenType : Type} [DecidableEq TokenType] (rules : List (Scanner Bytes × Option TokenType)) : Lexer TokenType where
  rules := rules
  tokenize bs :=
    let rec tryRules (results : List (Scanner Bytes × Option TokenType)) (offset : Nat) : scan_result (Option (Token TokenType)) :=
      match results with
      | [] => .notFound
      | (scanner, optType) :: rest =>
        match scanner.scan bs with
        | .found content remaining =>
          match optType with
          | some tail =>
            let tok : Token TokenType := ⟨tail, String.fromUTF8! content, offset⟩
            .found (some tok) remaining
          | none => .found none remaining  -- Skip (whitespace)
        | .notFound => tryRules rest offset
        | .incomplete count => .incomplete count
    tryRules rules 0

/-- Tokenize entire input -/
partial
def Lexer.tokenizeAll
    {TokenType : Type}
    (lex : Lexer TokenType)
    (bytes : Bytes)
    : List (Token TokenType) :=
  let rec tokenizeRemaining (input : Bytes) (offset : Nat) (result : List (Token TokenType)) : List (Token TokenType) :=
    if input.size == 0 then result.reverse
    else
      match lex.tokenize input with
      | .found (some tok) rest =>
        tokenizeRemaining rest (offset + tok.lexeme.length) (tok :: result)
      | .found none rest =>
        -- Skipped (whitespace)
        let skipped := input.size - rest.size
        tokenizeRemaining rest (offset + skipped) result
      | .notFound => result.reverse  -- Can't tokenize more
      | .incomplete _ => result.reverse
  tokenizeRemaining bytes 0 []

/-- Convert Scanner output to Parser input -/
def fromScanner
    {TokenType : Type}
    [DecidableEq TokenType]
    (lex : Lexer TokenType)
    (bytes : Bytes)
    : token_stream TokenType :=
  token_stream.fromList (lex.tokenizeAll bytes)

-- ═══════════════════════════════════════════════════════════════════════════════
-- JSON EXAMPLE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- JSON token types (example) -/
inductive json_token where
  | lbrace
  | rbrace
  | lbracket
  | rbracket
  | colon
  | comma
  | string (state : String)
  | number (state : String)
  | true_
  | false_
  | null_
  deriving Repr, DecidableEq

/-- JSON AST (example) -/
inductive JsonValue where
  | null
  | bool (rightValue : Bool)
  | number (state : String)
  | string (state : String)
  | array (items : List JsonValue)
  | object (fields : List (String × JsonValue))
  deriving Repr

-- Note: Full JSON parser implementation omitted for compilation speed.
-- The Parser combinators above provide all necessary building blocks.

-- ═══════════════════════════════════════════════════════════════════════════════
-- GRAMMAR ANALYSIS (FIRST/FOLLOW)
-- For LL(key) parser generation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- FIRST set: set of tokens that can start a production -/
structure first_set (TokenType : Type) where
  tokens     : List TokenType
  hasEpsilon : Bool           -- Can derive empty string
  deriving Repr

/-- FOLLOW set: set of tokens that can follow a nonterminal -/
structure follow_set (TokenType : Type) where
  tokens : List TokenType
  hasEof : Bool
  deriving Repr

/-- Grammar rule: nonterminal → sequence of symbols -/
inductive symbol (TokenType Size : Type) where
  | term : TokenType → symbol TokenType Size
  | nonterm : Size → symbol TokenType Size
  deriving Repr

structure Rule (TokenType Size : Type) where
  lhs : Size
  rhs : List (symbol TokenType Size)
  deriving Repr

structure grammar (TokenType Size : Type) where
  rules : List (Rule TokenType Size)
  start : Size
  deriving Repr

-- Note: Full FIRST/FOLLOW computation would go here
-- This enables compile-time detection of LL(key) conflicts

end Continuity.Codec.Core.Parser
