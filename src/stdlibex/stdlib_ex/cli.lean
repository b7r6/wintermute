/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // STDLIBEX // CLI
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Command-line argument parsing — schema defined in Lean, parsing in Lean.

    Design:
      · Schema is data: `Opt`, `Flag`, `Cmd` structures
      · Parsing is pure: `parse : Schema → List String → ParseResult`
      · Help generation from schema
      · No FFI — this is pure Lean

    The schema-in-Lean approach means:
      · Adding a flag is a Lean change, not a C++ recompile
      · Types flow through: `--jobs` parses to `Nat`, not `String`
      · Subcommand dispatch is pattern matching

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.CLI

-- ══════════════════════════════════════════════════════════════════════════════
-- PARSE RESULTS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A parsed value with its type erased (for heterogeneous storage). -/
inductive Value where
  | string : String → Value
  | nat : Nat → Value
  | int : Int → Value
  | bool : Bool → Value
  | strings : List String → Value
  deriving Repr, Inhabited

/-- Result of parsing command line. -/
structure Parsed where
  /-- The subcommand path (empty if no subcommand). -/
  command : List String
  /-- Named options: `--foo=bar` or `--foo bar`. -/
  options : List (String × Value)
  /-- Positional arguments. -/
  positionals : List String
  /-- Flags present (e.g., `--verbose`). -/
  flags : List String
  deriving Repr, Inhabited

namespace Parsed

def getOpt (parsed : Parsed) (name : String) : Option Value :=
  parsed.options.find? (·.1 == name) |>.map (·.2)

def getOptString (parsed : Parsed) (name : String) : Option String :=
  match parsed.getOpt name with
  | some (.string value) => some value
  | _ => none

def getOptNat (parsed : Parsed) (name : String) : Option Nat :=
  match parsed.getOpt name with
  | some (.nat value) => some value
  | _                 => none

def getOptInt (parsed : Parsed) (name : String) : Option Int :=
  match parsed.getOpt name with
  | some (.int value) => some value
  | _                 => none

def hasFlag (parsed : Parsed) (name : String) : Bool := parsed.flags.contains name

def getPositional (parsed : Parsed) (idx : Nat) : Option String := parsed.positionals[idx]?

end Parsed

/-- Parse error with context. -/
structure ParseError where
  message : String
  context : Option String := none
  deriving Repr, Inhabited

instance : ToString ParseError where
  toString e :=
    match e.context with
    | some ctx => s!"error: {e.message} (at {ctx})"
    | none     => s!"error: {e.message}"

abbrev ParseResult := Except ParseError Parsed

-- ══════════════════════════════════════════════════════════════════════════════
-- SCHEMA DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Type of a named option's value. -/
inductive OptType where
  | string
  | nat
  | int
  | bool
  | strings -- can be repeated: `--include foo --include bar`
  deriving Repr, DecidableEq

/-- A named option: `--name[=value]` or `-n [value]`. -/
structure Opt where
  /-- Long name (without `--`). -/
  long : String
  /-- Short name (without `-`), or empty. -/
  short : String := ""
  /-- Description for help text. -/
  desc : String := ""
  /-- Value type. -/
  type : OptType := .string
  /-- Default value if not provided. -/
  default : Option Value := none
  /-- Is this option required? -/
  required : Bool := false
  deriving Repr, Inhabited

/-- A flag: `--flag` or `-f` (no value, presence is boolean). -/
structure Flag where
  long  : String
  short : String := ""
  desc  : String := ""
  deriving Repr, Inhabited

/-- A subcommand with its own options. -/
structure Cmd where
  /-- Command name. -/
  name : String
  /-- Description for help text. -/
  desc : String := ""
  /-- Options specific to this command. -/
  opts : List Opt := []
  /-- Flags specific to this command. -/
  flags : List Flag := []
  /-- Nested subcommands. -/
  subcommands : List Cmd := []
  /-- Names of required positional arguments. -/
  positionals : List String := []
  deriving Repr, Inhabited

/-- Top-level CLI schema. -/
structure Schema where
  /-- Program name (for help text). -/
  name : String
  /-- Program description. -/
  desc : String := ""
  /-- Version string. -/
  version : String := ""
  /-- Global options (apply to all subcommands). -/
  globalOpts : List Opt := []
  /-- Global flags. -/
  globalFlags : List Flag := []
  /-- Subcommands. -/
  commands : List Cmd := []
  /-- Positional args if no subcommand. -/
  positionals : List String := []
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════════════════
-- PARSING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Try to parse a value according to its expected type. -/
def parseValue (optionType : OptType) (text : String) : Except String Value :=
  match optionType with
  | .string => .ok (.string text)
  | .nat =>
    match text.toNat? with
    | some value => .ok (.nat value)
    | none       => .error s!"expected natural number, got '{text}'"
  | .int =>
    match text.toInt? with
    | some value => .ok (.int value)
    | none       => .error s!"expected integer, got '{text}'"
  | .bool =>
    match text.toLower with
    | "true" | "1" | "yes" => .ok (.bool true)
    | "false" | "0" | "no" => .ok (.bool false)
    | _ => .error s!"expected boolean, got '{text}'"
  | .strings => .ok (.string text) -- accumulated later

/-- Find an option by long or short name. -/
def findOpt (opts : List Opt) (name : String) : Option Opt :=
  opts.find? fun option => option.long == name || (option.short != "" && option.short == name)

/-- Find a flag by long or short name. -/
def findFlag (flags : List Flag) (name : String) : Option Flag :=
  flags.find? fun flag => flag.long == name || (flag.short != "" && flag.short == name)

/-- Find a subcommand by name. -/
def findCmd (cmds : List Cmd) (name : String) : Option Cmd := cmds.find? (·.name == name)

/-- Internal parse state. -/
structure ParseState where
  command             : List String := []
  options             : List (String × Value) := []
  positionals         : List String := []
  flags               : List String := []
  currentOpts         : List Opt := []
  currentFlags        : List Flag := []
  currentCmds         : List Cmd := []
  expectedPositionals : List String := []

private
def store_option
    (state : ParseState)
    (opt : Opt)
    (value : Value)
    (rest : List String)
    : Except ParseError (ParseState × List String) :=
  let options :=
    if opt.type == OptType.strings then
      state.options ++ [(opt.long, value)]
    else
      state.options.filter (fun entry => entry.1 != opt.long) ++ [(opt.long, value)]
  pure ({ state with options }, rest)

private
def parseOptionValue
    (state : ParseState)
    (opt : Opt)
    (context value : String)
    (rest : List String)
    : Except ParseError (ParseState × List String) :=
  match parseValue opt.type value with
  | .ok parsedValue => store_option state opt parsedValue rest
  | .error message  => throw { message, context := some context }

private
def parse_joined_long_argument
    (state : ParseState)
    (arg optName : String)
    (valueParts rest : List String)
    : Except ParseError (ParseState × List String) := do
  let value := "=".intercalate valueParts
  let some opt := findOpt state.currentOpts optName
      | throw { message := s!"unknown option --{optName}", context := some arg }
  parseOptionValue state opt arg value rest

private
def parse_long_argument
    (state : ParseState)
    (arg : String)
    (rest : List String)
    : Except ParseError (ParseState × List String) := do
  match (arg.drop 2).toString.splitOn "=" with
  | [optName, value] =>
    if let some opt := findOpt state.currentOpts optName then
      parseOptionValue state opt arg value rest
    else if findFlag state.currentFlags optName |>.isSome then
      throw { message := s!"flag --{optName} does not take a value", context := some arg }
    else
      throw { message := s!"unknown option --{optName}", context := some arg }
  | [name] =>
    if let some _ := findFlag state.currentFlags name then
      return ({ state with flags := state.flags ++ [name] }, rest)
    else if let some opt := findOpt state.currentOpts name then
      match rest with
      | [] => throw { message := s!"option --{name} requires a value" }
      | value :: remaining => parseOptionValue state opt s!"--{name}" value remaining
    else
      throw { message := s!"unknown option --{name}", context := some arg }
  | optName :: valueParts => parse_joined_long_argument state arg optName valueParts rest
  | [] => throw { message := "empty option name", context := some arg }

private
def parse_short_argument
    (state : ParseState)
    (arg : String)
    (rest : List String)
    : Except ParseError (ParseState × List String) := do
  let name := (arg.drop 1).toString
  if name.length > 0 && (name.toList[0]? |>.map Char.isDigit |>.getD false) then
    return ({ state with positionals := state.positionals ++ [arg] }, rest)
  if let some _ := findFlag state.currentFlags name then
    return ({ state with flags := state.flags ++ [name] }, rest)
  if let some opt := findOpt state.currentOpts name then
    match rest with
    | [] => throw { message := s!"option -{name} requires a value" }
    | value :: remaining => parseOptionValue state opt s!"-{name}" value remaining
  else
    throw { message := s!"unknown option -{name}", context := some arg }

/-- Parse a single argument, updating state. -/
def parseArg
    (state : ParseState)
    (arg : String)
    (rest : List String)
    : Except ParseError (ParseState × List String) := do
  if arg.startsWith "--" then
    parse_long_argument state arg rest
  else if arg.startsWith "-" && arg.length > 1 then
    parse_short_argument state arg rest
  -- Check for subcommand
  else if let some cmd := findCmd state.currentCmds arg then
    let state' := { state with
      command := state.command ++ [cmd.name]
      currentOpts := state.currentOpts ++ cmd.opts
      currentFlags := state.currentFlags ++ cmd.flags
      currentCmds := cmd.subcommands
      expectedPositionals := cmd.positionals
    }
    return (state', rest)
  -- Positional argument
  else
    return ({ state with positionals := state.positionals ++ [arg] }, rest)

mutual

  /-- Main parse loop. -/
  partial
  def parseLoop (state : ParseState) (args : List String) : Except ParseError ParseState := do
    match args with
    | [] => return state
    | arg :: rest => parseNext state arg rest

  partial
  def parseNext
      (state : ParseState)
      (arg : String)
      (rest : List String)
      : Except ParseError ParseState := do
    let (nextState, remaining) ← parseArg state arg rest
    parseLoop nextState remaining

end

/-- Parse command line arguments against a schema. -/
def parse (schema : Schema) (args : List String) : ParseResult := do
  let initialState : ParseState := {
    currentOpts := schema.globalOpts
    currentFlags := schema.globalFlags
    currentCmds := schema.commands
    expectedPositionals := schema.positionals
  }
  let finalState ← parseLoop initialState args

  -- Check every required option.
  for opt in schema.globalOpts do
    if opt.required then
      if finalState.options.find? (fun entry => entry.1 == opt.long) |>.isNone then
        throw { message := s!"required option --{opt.long} not provided" }

  -- Apply defaults for omitted options.
  let options :=
    finalState.options
        ++ (schema.globalOpts.filterMap fun opt =>
          if finalState.options.find? (fun entry => entry.1 == opt.long) |>.isNone then
            opt.default.map fun defaultValue => (opt.long, defaultValue)
          else
            none)

  -- Return the fully resolved parse result.
  return {
    command := finalState.command
    options := options
    positionals := finalState.positionals
    flags := finalState.flags
  }

-- ══════════════════════════════════════════════════════════════════════════════
-- HELP GENERATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Format an option for help text. -/
def formatOpt (opt : Opt) : String :=
  let short := if opt.short != "" then s!"-{opt.short}, " else "    "
  let long := s!"--{opt.long}"
  let typeStr :=
    match opt.type with
    | .string  => " <string>"
    | .nat     => " <number>"
    | .int     => " <int>"
    | .bool    => " <bool>"
    | .strings => " <string>..."
  let req := if opt.required then " (required)" else ""
  s!"  {short}{long}{typeStr}{req}\n      {opt.desc}"

/-- Format a flag for help text. -/
def formatFlag (flag : Flag) : String :=
  let short := if flag.short != "" then s!"-{flag.short}, " else "    "
  s!"  {short}--{flag.long}\n      {flag.desc}"

/-- Format a command for help text. -/
def formatCmd (cmd : Cmd) : String := s!"  {cmd.name}\n      {cmd.desc}"

/-- Generate help text from schema. -/
def help (schema : Schema) (_forCommand : List String := []) : String :=
  let header :=
    if schema.version != "" then s!"{schema.name} {schema.version}\n" else s!"{schema.name}\n"
  let desc := if schema.desc != "" then s!"{schema.desc}\n\n" else "\n"
  let cmds :=
    if schema.commands.isEmpty then
      ""
    else
      "Commands:\n" ++ String.join (schema.commands.map fun command => formatCmd command ++ "\n")
          ++ "\n"
  let opts :=
    if schema.globalOpts.isEmpty then
      ""
    else
      "Options:\n" ++ String.join (schema.globalOpts.map fun option => formatOpt option ++ "\n")
          ++ "\n"
  let flgs :=
    if schema.globalFlags.isEmpty then
      ""
    else
      "Flags:\n" ++ String.join (schema.globalFlags.map fun flag => formatFlag flag ++ "\n")
  header ++ desc ++ cmds ++ opts ++ flgs

-- ══════════════════════════════════════════════════════════════════════════════
-- CONVENIENCE CONSTRUCTORS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Create a string option. -/
def stringOpt
    (long : String)
    (desc : String)
    (short : String := "")
    (default : Option String := none)
    (required := false)
    : Opt :=
  { long, short, desc, type := .string, default := default.map .string, required }

/-- Create a numeric option. -/
def natOpt
    (long : String)
    (desc : String)
    (short : String := "")
    (default : Option Nat := none)
    (required := false)
    : Opt :=
  { long, short, desc, type := .nat, default := default.map .nat, required }

/-- Create an integer option. -/
def intOpt
    (long : String)
    (desc : String)
    (short : String := "")
    (default : Option Int := none)
    (required := false)
    : Opt :=
  { long, short, desc, type := .int, default := default.map .int, required }

/-- Create a flag. -/
def flag (long : String) (desc : String) (short : String := "") : Flag := { long, short, desc }

/-- Create a subcommand. -/
def cmd
    (name : String)
    (desc : String)
    (opts : List Opt := [])
    (flags : List Flag := [])
    (positionals : List String := [])
    : Cmd := { name, desc, opts, flags, positionals }

end StdlibEx.CLI
