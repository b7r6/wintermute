/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // WINTERMUTE // SHELL // IO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The IO shell around the pure reconciler. Everything here is a thin,
    fallible adapter; the DISCIPLINE is that no adapter failure ever
    propagates — a dead kitty socket or a missing emacs server costs one
    channel one update (repaired by the next anti-entropy tick), never the
    daemon. `bestEffort` is the five-nines primitive.

    Live channels (broadcast):
      hyprctl --batch     borders + shadow, one round trip
      kitty remote        full 16-color + UI colors via `kitten @ set-colors`
      OSC 4/10/11/12      every /dev/pts — any VTE/foot/alacritty converges
      emacsclient         `ono-sendai-set-hero` / `-set-axis` (generator-built)
      nvim --remote       `:OnoSendaiHero` / `:OnoSendaiAxis` on every socket
      gsettings           portal color-scheme — the day/night signal GTK/Qt
                          apps actually follow

    Durable channel (persist):
      theme.json          generation-stamped palette + register tokens in
                          XDG_STATE, atomic temp+rename — the file Quickshell
                          FileView watches; ALSO the wallpaper's uniform feed.

    Stdlib IO today; EVRing once inotify/subprocess land in the ring.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute.Reconcile
import Wintermute.State
import Std.Time

namespace Wintermute.Shell

open Wintermute
open System (FilePath)

-- ═══════════════════════════════════════════════════════════════════════════════
--  FIVE-NINES PRIMITIVES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Swallow every failure: a broken adapter costs one channel one update. -/
def bestEffort (act : IO Unit) : IO Unit :=
  try act catch _ => pure ()

/-- Spawn quietly, wait, ignore the exit code — theme pushes are fire-and-forget. -/
def runQuiet (cmd : String) (args : Array String) : IO Unit :=
  bestEffort do
    let child ← IO.Process.spawn
      { cmd, args, stdin := .null, stdout := .null, stderr := .null }
    let _ ← child.wait
    pure ()

-- ═══════════════════════════════════════════════════════════════════════════════
--  PATHS  — XDG_STATE, out of the Nix store by design
-- ═══════════════════════════════════════════════════════════════════════════════

def stateDir : IO FilePath := do
  match ← IO.getEnv "XDG_STATE_HOME" with
  | some d => pure (FilePath.mk d / "wintermute")
  | none =>
    let home := (← IO.getEnv "HOME").getD "/tmp"
    pure (FilePath.mk home / ".local" / "state" / "wintermute")

def configDir : IO FilePath := do
  match ← IO.getEnv "XDG_CONFIG_HOME" with
  | some d => pure (FilePath.mk d)
  | none =>
    let home := (← IO.getEnv "HOME").getD "/tmp"
    pure (FilePath.mk home / ".config")

def statePath : IO FilePath := return (← stateDir) / "theme.state"
def tokensPath : IO FilePath := return (← stateDir) / "theme.json"

/-- Atomic durable write: temp + rename(2) — readers see old or new, never torn.

    The temp name is WRITER-UNIQUE — pid (distinct across concurrent processes)
    plus mono-nanos (distinct within one) — so two `set`s racing on the same
    path never share a temp file. A shared temp name is itself a raced mutable
    handle: writer B's rename(2) would hit ENOENT after writer A renamed the
    shared temp away (~38% of a concurrent burst died that way). With private
    temps each rename is an independent atomic swap into the final path — the
    last writer wins the file, nobody renames another's half-written temp, and
    no `set` ever crashes on a lost race. Same directory as `path`, so the
    rename stays a single-filesystem atomic operation. -/
def atomicWrite (path : FilePath) (contents : String) : IO Unit := do
  let pid ← IO.Process.getPID
  let uniq ← IO.monoNanosNow
  let tmp := path.addExtension s!"{pid}.{uniq}.tmp"
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

/-- The generation stamp: wall-clock nanoseconds since the epoch. COMPUTED,
    never read-then-incremented — so two concurrent `set`s can never mint the
    same generation, and the reconciler's fence never rejects a genuine update
    as a stale collision. This is E1, the structural death of the write race:
    there is no shared counter left to race on. Monotone across processes (the
    realtime clock); a backward clock step degrades to a missed update that the
    next write or the anti-entropy tick repairs — never to corruption.

    MICROseconds, not nanos: 1.78e15 is exactly representable as an IEEE double
    (< 2^53, good past year 2200), so the stamp survives JSON/QML's double
    semantics losslessly downstream — while staying collision-free for separate
    `set` process spawns (two invocations never share a microsecond). -/
def nowGen : IO Nat := do
  let ts ← Std.Time.Timestamp.now
  pure (ts.toNanosecondsSinceUnixEpoch.toInt.toNat / 1000)

/-- Clock-skew tolerance (µs) for the fence's future-plausibility guard. A
    generation is a wall-clock stamp; writer and daemon share the machine clock,
    so a valid generation is never meaningfully ahead of the daemon's own `now`.
    5 s absorbs any read-after-write jitter without admitting a poison stamp. -/
def futureSlackMicros : Nat := 5000000

/-- A well-formed control file is < 200 bytes; anything past this is not a
    control file. The cap is what makes the parser's cost bounded (no O(n²)
    bignum parse of a megabyte line) — E2. -/
def maxControlBytes : UInt64 := 65536

/-- The read boundary for EVERY small state/config-dir file wintermute ingests
    — the control file, the ack ledger, the zellij verify — E2 + E3. `stat`
    first (never blocks, even on a FIFO): reject anything that is not a REGULAR
    file (a FIFO/dir/socket would block or is nonsense) and anything past the
    size cap, BEFORE any content read can hang or blow up. A malformed monster
    is turned into `none` here and never reaches a parser, `status`, or the
    daemon's tick. Every read of a tamperable file goes through this one door. -/
def readBoundedText (path : FilePath) : IO (Option String) := do
  try
    let md ← path.metadata
    if md.type != .file then return none
    if md.byteSize > maxControlBytes then return none
    some <$> IO.FS.readFile path
  catch _ => pure none

-- ═══════════════════════════════════════════════════════════════════════════════
--  RENDERERS  — theme → channel payloads
-- ═══════════════════════════════════════════════════════════════════════════════

def stripHash (s : String) : String :=
  if s.startsWith "#" then (s.drop 1).toString else s

def hyprlandBatch (p : Palette) : String :=
  String.intercalate " ; "
    [ s!"keyword general:col.active_border rgba({stripHash p.base0C}ee) rgba({stripHash p.base0D}ee) 45deg"
    , s!"keyword general:col.inactive_border rgba({stripHash p.base02}aa)"
    , s!"keyword decoration:shadow:color rgba({stripHash p.base00}ee)"
    ]

/-- base16 → kitty: UI colors + the standard 16-slot ANSI mapping. -/
def kittyPairs (p : Palette) : Array String :=
  #[ s!"background={p.base00}", s!"foreground={p.base05}"
   , s!"cursor={p.base0C}", s!"cursor_text_color={p.base00}"
   , s!"selection_background={p.base02}", s!"selection_foreground={p.base07}"
   , s!"active_border_color={p.base0C}", s!"inactive_border_color={p.base02}"
   , s!"color0={p.base00}", s!"color1={p.base08}", s!"color2={p.base0B}"
   , s!"color3={p.base0A}", s!"color4={p.base0D}", s!"color5={p.base0E}"
   , s!"color6={p.base0C}", s!"color7={p.base05}", s!"color8={p.base03}"
   , s!"color9={p.base08}", s!"color10={p.base0B}", s!"color11={p.base0A}"
   , s!"color12={p.base0D}", s!"color13={p.base0E}", s!"color14={p.base0C}"
   , s!"color15={p.base07}" ]

/-- The OSC payload every terminal understands: 10 fg, 11 bg, 12 cursor,
    4;N the ANSI slots. ST-terminated. -/
def oscPayload (p : Palette) : String :=
  let esc := String.singleton (Char.ofNat 27)
  let st := esc ++ "\\"
  let osc (body : String) : String := esc ++ "]" ++ body ++ st
  let ansi : List (Nat × String) :=
    [ (0, p.base00), (1, p.base08), (2, p.base0B), (3, p.base0A)
    , (4, p.base0D), (5, p.base0E), (6, p.base0C), (7, p.base05)
    , (8, p.base03), (9, p.base08), (10, p.base0B), (11, p.base0A)
    , (12, p.base0D), (13, p.base0E), (14, p.base0C), (15, p.base07) ]
  String.join
    ([osc s!"10;{p.base05}", osc s!"11;{p.base00}", osc s!"12;{p.base0C}"]
      ++ ansi.map (fun (n, c) => osc s!"4;{n};{c}"))

/-- Per-mille → decimal string: 250 → "0.250", 1000 → "1.000". -/
def permille (n : Nat) : String :=
  let n := min n 1000
  let frac := n % 1000
  let pad := if frac < 10 then "00" else if frac < 100 then "0" else ""
  s!"{n / 1000}.{pad}{frac}"

/-- The generation-stamped token file — palette + register scalars, the single
    artifact Quickshell/wallpaper watch. -/
def tokensJson (gen : Nat) (t : ThemeVector) : String :=
  let p := t.palette
  let tok := t.tokens
  let slots := String.intercalate ",\n    "
    (p.slots.map fun (k, v) => s!"\"{k}\": \"{v}\"")
  "{\n" ++
  s!"  \"generation\": {gen},\n" ++
  s!"  \"slug\": \"{t.slug}\",\n" ++
  s!"  \"family\": \"{t.family.name}\",\n" ++
  s!"  \"polarity\": \"{t.luminance.polarity}\",\n" ++
  s!"  \"heroHue\": {t.heroHue},\n" ++
  s!"  \"axisHue\": {t.axisHue},\n" ++
  s!"  \"register\": {permille t.register},\n" ++
  s!"  \"facility\": {if t.facility then "true" else "false"},\n" ++
  "  \"palette\": {\n    " ++ slots ++ "\n  },\n" ++
  "  \"tokens\": {\n" ++
  s!"    \"scanline\": {permille tok.scanline},\n" ++
  s!"    \"bracketSize\": {permille tok.bracketSize},\n" ++
  s!"    \"telemetryDensity\": {permille tok.telemetryDensity},\n" ++
  s!"    \"glassBlur\": {permille tok.glassBlur},\n" ++
  s!"    \"bloom\": {permille tok.bloom},\n" ++
  s!"    \"grainOpacity\": {permille tok.grainOpacity}\n" ++
  "  }\n}\n"

-- ═══════════════════════════════════════════════════════════════════════════════
--  LIVE ADAPTERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- OSC-paint every pty WITHOUT ever blocking. A pty whose reader is gone
    (severed SSH, orphaned mux pane) stops draining; once its buffer fills,
    a plain `write()` parks this daemon forever mid-broadcast — the observed
    control-plane wedge: `persist` starved behind `broadcast`, theme.json
    frozen while theme.state marches on, every surface downstream stuck.
    `dd oflag=nonblock` turns the full-buffer case into an instant EAGAIN
    (`bestEffort` eats the nonzero exit), and the outer `timeout` is the
    belt to that suspender. A live terminal drains and repaints; a dead one
    is skipped in microseconds. -/
def oscBroadcast (p : Palette) : IO Unit :=
  bestEffort do
    let payload := oscPayload p
    let tmp := (← stateDir) / ".osc-payload"
    atomicWrite tmp payload
    let entries ← FilePath.readDir "/dev/pts"
    for entry in entries do
      if entry.fileName.all Char.isDigit then
        bestEffort do
          runQuiet "timeout"
            #["1", "dd", s!"if={tmp}", s!"of={entry.path}"
             , "oflag=nonblock", "status=none"]

/-- Restyle the tmux server's chrome in ONE round-trip (`;`-chained set
    commands, server-wide `-g`). The OSC broadcast reaches every terminal's
    colors, but tmux's status bar / pane borders / message line come from
    config variables no escape sequence touches — the server outlives every
    rebuild holding its birth palette. This mirrors the build-time mapping
    in modules/home/shell (nixos-config) exactly; change them together. -/
def tmuxRestyle (p : Palette) : IO Unit :=
  let sets : List (List String) :=
    [ ["set", "-g", "message-style", s!"fg={p.base05},bg={p.base01}"]
    , ["set", "-g", "mode-style", s!"fg={p.base05},bg={p.base03}"]
    , ["set", "-g", "pane-active-border-style", s!"fg={p.base03}"]
    , ["set", "-g", "pane-border-style", s!"fg={p.base03}"]
    , ["set", "-g", "status-style", s!"fg={p.base04},bg=default"]
    , ["set", "-g", "status-right"
      , s!" #[fg={p.base0D}]%H:%M #[fg={p.base0D}]#h#[default] #[fg={p.base0D}]#(whoami)#[default] "]
    , ["set", "-g", "window-status-current-format"
      , s!" #[fg={p.base05},bg=default]#W#[default]"]
    , ["set", "-g", "window-status-format", s!" #[fg={p.base04}]#W#[default] "]
    ]
  let args := (sets.intersperse [";"]).flatten.toArray
  runQuiet "tmux" args

/-- Hit every live nvim server socket in XDG_RUNTIME_DIR. -/
def nvimBroadcast (t : ThemeVector) : IO Unit :=
  bestEffort do
    let runDir := (← IO.getEnv "XDG_RUNTIME_DIR").getD "/tmp"
    let entries ← FilePath.readDir runDir
    for entry in entries do
      if entry.fileName.startsWith "nvim." then
        runQuiet "nvim"
          #[ "--server", entry.path.toString, "--remote-send"
           , s!"<Cmd>OnoSendaiHero {t.heroHue}<CR><Cmd>OnoSendaiAxis {t.axisHue}<CR>" ]

-- ═══════════════════════════════════════════════════════════════════════════════
--  ACCOUNTABILITY  — the ack protocol + audit
--
--  Every surface acknowledges the generation it APPLIED into
--  $XDG_STATE_HOME/wintermute/ack/<surface> ("<gen> <epoch>"). Self-aware
--  surfaces (quickshell, emacs) write their own; the daemon VERIFIES the
--  mute ones (tmux, hyprland) by querying their actual live state and acks
--  on their behalf. `wintermute status` renders the conformance table;
--  every anti-entropy tick emits one JSON audit line to stdout → journald →
--  the otel/ClickHouse pipeline. "Which theme is even running" becomes a
--  query, not an investigation.
-- ═══════════════════════════════════════════════════════════════════════════════

def ackDir : IO FilePath := return (← stateDir) / "ack"

def writeAck (surface : String) (gen : Nat) : IO Unit :=
  bestEffort do
    let dir ← ackDir
    IO.FS.createDirAll dir
    let now ← IO.monoMsNow
    -- monotonic ms is fine for AGE math within a boot; wall time via date
    -- would need subprocess. Record epoch seconds via the filesystem instead:
    -- the ack file's own mtime is the timestamp; content carries the gen.
    let _ := now
    IO.FS.writeFile (dir / surface) s!"{gen}\n"

def readAck (surface : String) : IO (Option Nat) := do
  -- Through the bounded boundary: a FIFO or oversized ack file (the ack dir is
  -- user-writable) would otherwise hang `status` AND the daemon's audit tick.
  match ← readBoundedText ((← ackDir) / surface) with
  | some txt => pure txt.trim.toNat?
  | none => pure none

/-- Run and capture stdout (empty on any failure). -/
def runCapture (cmd : String) (args : Array String) : IO String :=
  try
    let out ← IO.Process.output { cmd, args }
    pure (if out.exitCode == 0 then out.stdout else "")
  catch _ => pure ""

/-- The live hyprland instance, discovered from the runtime dir — NEVER
    from env: the systemd-imported signature goes stale whenever a
    compositor dies uncleanly, and a long-lived daemon would carry the
    corpse's address forever. Newest-mtime dirs first, first socket that
    answers wins. -/
def hyprlandInstances : IO (List String) := do
  let base := ((← IO.getEnv "XDG_RUNTIME_DIR").getD "/tmp") ++ "/hypr"
  try
    let entries ← FilePath.readDir base
    let mut xs : List (Nat × String) := []
    for e in entries do
      match (← try pure (some (← e.path.metadata)) catch _ => pure none) with
      | some m => xs := (m.modified.sec.toNat, e.fileName) :: xs
      | none => pure ()
    pure (((xs.toArray.qsort (fun a b => a.1 > b.1)).toList).map (·.2))
  catch _ => pure []

/-- hyprctl against whichever instance actually answers. -/
def hyprctlLive (args : Array String) : IO String := do
  for sig in (← hyprlandInstances).take 4 do
    let out ← runCapture "hyprctl" (#["-i", sig] ++ args)
    if out ≠ "" then return out
  pure ""

/-- Zellij: the DECLARATIVE multiplexer channel — write the theme file,
    zellij hot-reloads it. Verification is reading it back: the cleanest
    ledger row in the fleet (tmux, by contrast, is write-only imperative
    and verified by string-matching its live vars). -/
def zellijThemeKdl (p : Palette) : String :=
  String.intercalate "\n"
    [ "// WRITTEN BY WINTERMUTE — do not edit (repo config points at theme \"ono-sendai\")"
    , "themes {"
    , "    ono-sendai {"
    , s!"        fg \"{p.base05}\""
    , s!"        bg \"{p.base00}\""
    , s!"        black \"{p.base01}\""
    , s!"        red \"{p.base08}\""
    , s!"        green \"{p.base0B}\""
    , s!"        yellow \"{p.base0A}\""
    , s!"        blue \"{p.base0D}\""
    , s!"        magenta \"{p.base0E}\""
    , s!"        cyan \"{p.base0C}\""
    , s!"        white \"{p.base07}\""
    , s!"        orange \"{p.base09}\""
    , "    }"
    , "}"
    , ""
    ]

-- ── fzf: the options file (read fresh on every launch — genuinely live) ────
-- fzf reads $FZF_DEFAULT_OPTS_FILE at each invocation, so rewriting this file
-- retints every subsequent fzf with zero shell involvement. base16 → the fzf
-- color roles; bg/gutter track the surface, hl/prompt the hero.
def fzfOpts (p : Palette) : String :=
  "--color=fg:" ++ p.base05 ++ ",bg:" ++ p.base00 ++ ",hl:" ++ p.base0A ++
  ",fg+:" ++ p.base07 ++ ",bg+:" ++ p.base01 ++ ",hl+:" ++ p.base0A ++
  ",info:" ++ p.base04 ++ ",border:" ++ p.base02 ++ ",prompt:" ++ p.base0A ++
  ",pointer:" ++ p.base0C ++ ",marker:" ++ p.base0B ++ ",spinner:" ++ p.base0C ++
  ",header:" ++ p.base04 ++ ",gutter:" ++ p.base00 ++ "\n"

def fzfOptsPath : IO FilePath := return (← stateDir) / "fzf.opts"

def fzfPersist (p : Palette) : IO Unit :=
  bestEffort do
    IO.FS.createDirAll (← stateDir)
    atomicWrite (← fzfOptsPath) (fzfOpts p)

-- ── atuin: a theme file (read on every `atuin search` — live per Ctrl-R) ───
-- atuin's Meaning palette (Base/Title/Guidance/Important/Annotation/Alert*),
-- selected by `theme.name = "wintermute"` in config.toml.
def atuinTheme (p : Palette) : String :=
  String.intercalate "\n"
    [ "# WRITTEN BY WINTERMUTE — do not edit"
    , "[theme]"
    , "name = \"wintermute\""
    , ""
    , "[colors]"
    , s!"Base = \"{p.base05}\""
    , s!"Title = \"{p.base0A}\""
    , s!"Guidance = \"{p.base04}\""
    , s!"Important = \"{p.base07}\""
    , s!"Annotation = \"{p.base03}\""
    , s!"AlertInfo = \"{p.base0B}\""
    , s!"AlertWarn = \"{p.base0A}\""
    , s!"AlertError = \"{p.base08}\""
    , s!"Muted = \"{p.base04}\""
    , ""
    ]

def atuinThemePath : IO FilePath :=
  return (← configDir) / "atuin" / "themes" / "wintermute.toml"

def atuinPersist (p : Palette) : IO Unit :=
  bestEffort do
    IO.FS.createDirAll ((← configDir) / "atuin" / "themes")
    atomicWrite (← atuinThemePath) (atuinTheme p)

def zellijThemePath : IO FilePath :=
  return (← configDir) / "zellij" / "themes" / "ono-sendai.kdl"

def zellijPersist (p : Palette) : IO Unit :=
  bestEffort do
    let path ← zellijThemePath
    IO.FS.createDirAll ((← configDir) / "zellij" / "themes")
    atomicWrite path (zellijThemeKdl p)

def verifyZellij (gen : Nat) (p : Palette) : IO Bool := do
  -- Through the bounded boundary: the daemon reads this every audit tick, and
  -- a FIFO/oversized theme file would hang the tick otherwise.
  match ← readBoundedText (← zellijThemePath) with
  | some txt =>
    let ok := (txt.splitOn p.base00).length > 1
    if ok then writeAck "zellij" gen
    pure ok
  | none => pure false



/-- tmux can't self-report: verify its live chrome carries this palette
    (status-style must reference base01) and ack on its behalf. -/
def verifyTmux (gen : Nat) (p : Palette) : IO Bool := do
  let out ← runCapture "tmux" #["show", "-g", "status-style"]
  let ok := (out.splitOn p.base01).length > 1
  if ok then writeAck "tmux" gen
  pure ok

/-- hyprland likewise: the active-border keyword must carry base0C. -/
def verifyHyprland (gen : Nat) (p : Palette) : IO Bool := do
  let out ← hyprctlLive #["getoption", "general:col.active_border"]
  let ok := (out.toLower.splitOn (stripHash p.base0C).toLower).length > 1
  if ok then writeAck "hyprland" gen
  pure ok

def ackSurfaces : List String := ["quickshell", "emacs", "tmux", "hyprland", "zellij"]

/-- One structured audit line: expected gen + each surface's acked gen.
    Lands in journald (unit wintermute.service) → otel → ClickHouse. -/
def auditLine (gen : Nat) (slug : String) : IO Unit := do
  let mut fields : List String := []
  for surface in ackSurfaces do
    let a := (← readAck surface).getD 0
    fields := fields ++ [s!"\"{surface}\": {a}"]
  IO.println
    ("{\"wm\": \"audit\", \"gen\": " ++ toString gen ++
     ", \"slug\": \"" ++ slug ++ "\", \"acks\": {" ++
     String.intercalate ", " fields ++ "}}")
  (← IO.getStdout).flush

/-- Tick-time audit: verify the mute surfaces, then publish the ledger. -/
def runAudit (gen : Nat) (t : ThemeVector) : IO Unit :=
  bestEffort do
    let p := t.palette
    let _ ← verifyTmux gen p
    let _ ← verifyHyprland gen p
    let _ ← verifyZellij gen p
    auditLine gen t.slug

def broadcastTheme (t : ThemeVector) : IO Unit := do
  let p := t.palette
  bestEffort do
    let _ ← hyprctlLive #["--batch", hyprlandBatch p]
  tmuxRestyle p
  runQuiet "kitten" (#["@", "set-colors", "--all", "--configured"] ++ kittyPairs p)
  oscBroadcast p
  -- One command covers the whole 4-vector: sync re-reads theme.state (this
  -- daemon just wrote it) and recomputes in-editor. Falls back to the
  -- hue-only setters for configs that predate hypermodern-palette.el.
  runQuiet "emacsclient"
    #[ "--no-wait", "--eval"
     , s!"(if (fboundp 'ono-sendai-sync) (ono-sendai-sync) (progn (ono-sendai-set-hero {t.heroHue}) (ono-sendai-set-axis {t.axisHue})))" ]
  nvimBroadcast t
  runQuiet "gsettings"
    #[ "set", "org.gnome.desktop.interface", "color-scheme"
     , match t.luminance with | .dark _ => "prefer-dark" | .light _ _ => "prefer-light" ]

def persistTheme (gen : Nat) (t : ThemeVector) : IO Unit :=
  bestEffort do
    IO.FS.createDirAll (← stateDir)
    atomicWrite (← tokensPath) (tokensJson gen t)
    zellijPersist t.palette
    fzfPersist t.palette
    atuinPersist t.palette
/-- Command interpreter — the ONLY bridge from the pure machine to the world. -/
def applyCommand : Command → IO Unit
  | .broadcast _ t => broadcastTheme t
  | .persist g t => persistTheme g t

-- ═══════════════════════════════════════════════════════════════════════════════
--  THE DAEMON  — mtime watch → events → reconciler → commands
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Poll interval (ms) and heartbeat cadence (polls per anti-entropy tick). -/
def pollMs : UInt32 := 250
def ticksPerHeartbeat : Nat := 120

private def sameTime (a : Option IO.FS.SystemTime) (b : IO.FS.SystemTime) : Bool :=
  match a with
  | none => false
  | some a => a.sec == b.sec && a.nsec == b.nsec

/-- Ensure the state file exists (first run seeds the default vector). -/
def ensureState : IO FilePath := do
  IO.FS.createDirAll (← stateDir)
  let path ← statePath
  unless (← path.pathExists) do
    atomicWrite path (ControlState.render {})
  pure path

partial def daemonLoop
    (path : FilePath)
    (s : ReconState)
    (lastSeen : Option IO.FS.SystemTime)
    (polls : Nat)
    : IO Unit := do

  IO.sleep pollMs
  let md? ← try pure (some (← path.metadata)) catch _ => pure none
  let (event?, seen', polls') ←
    match md? with
    | some md =>
      if sameTime lastSeen md.modified then
        if polls + 1 ≥ ticksPerHeartbeat then
          pure (some Event.tick, lastSeen, 0)
        else
          pure (none, lastSeen, polls + 1)
      else do
        -- The mtime moved. Read through the bounded/typed boundary and parse.
        -- A `none` at EITHER stage (oversized/FIFO/unreadable, or no recognized
        -- key) consumes the mtime but emits NO event — the applied theme stands.
        -- Corruption can never reconcile the desktop to default (E4).
        let cs? ← (do match ← readBoundedText path with
                      | some txt => pure (ControlState.parse txt)
                      | none => pure none)
        match cs? with
        | some cs =>
          -- A generation IS a µs timestamp (E1). One implausibly far in the
          -- future — corruption, or a clock that stepped forward then back —
          -- would advance the monotone fence past wall-clock and wedge every
          -- later `set` (its current-µs generation would read as stale). Reject
          -- it like an unparseable file: consume the mtime, keep the applied
          -- theme. Legitimate sets (gen ≤ now, read ~250 ms later) always pass.
          if cs.generation > (← nowGen) + futureSlackMicros then
            pure (none, some md.modified, 0)
          else
            pure (some (Event.desired cs.generation cs.theme), some md.modified, 0)
        | none => pure (none, some md.modified, 0)
    | none => pure (none, lastSeen, polls + 1)
  match event? with
  | none => daemonLoop path s seen' polls'
  | some e =>
    let (s', cmds) := stepFn s e
    for c in cmds do
      applyCommand c
    -- reconcile events log; ticks audit — both land in the journal
    (match e with
     | .desired g t =>
       bestEffort do
         IO.println
           ("{\"wm\": \"reconcile\", \"gen\": " ++ toString g ++
            ", \"slug\": \"" ++ t.slug ++
            "\", \"commands\": " ++ toString cmds.length ++ "}")
         (← IO.getStdout).flush
     | .tick =>
       match s'.applied with
       | some t => runAudit s'.gen t
       | none => pure ())
    daemonLoop path s' seen' polls'

def daemon : IO Unit := do
  let path ← ensureState
  IO.eprintln s!"wintermute: watching {path}"
  daemonLoop path {} none 0

-- ═══════════════════════════════════════════════════════════════════════════════
--  CONTROL-PLANE WRITER  — `wintermute set …` / `preset …` mutate the file;
--  the daemon (this process or another) notices via mtime.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Read the desired control state through the bounded/typed boundary. `none`
    when the file is unreadable, oversized, not a regular file, or carries no
    recognized key — callers decide what a missing desire means (the daemon
    keeps its applied theme; the CLI falls back to the default vector). -/
def readControl : IO (Option ControlState) := do
  let path ← ensureState
  match ← readBoundedText path with
  | some txt => pure (ControlState.parse txt)
  | none => pure none

/-- The conformance table: which theme is even running, per surface. -/
def statusReport : IO Unit := do
  let cs := (← readControl).getD {}
  let expected := cs.generation
  IO.println s!"// wintermute // gen {expected} // {cs.theme.slug} //"
  IO.println ""
  IO.println "  surface     acked  lag"
  IO.println "  ─────────── ────── ─────"
  for surface in ackSurfaces do
    match ← readAck surface with
    | some g =>
      let lag := expected - g
      let mark := if lag == 0 then "" else s!"  ← behind by {lag}"
      IO.println s!"  {surface.pushn ' ' (11 - surface.length)} {g}{mark}"
    | none =>
      IO.println s!"  {surface.pushn ' ' (11 - surface.length)} —      never acked"

def writeControl (cs : ControlState) : IO Unit := do
  IO.FS.createDirAll (← stateDir)
  atomicWrite (← statePath) (ControlState.render cs)

/-- `register` is fixed-point thousandths (0–1000), but the natural CLI
    spelling is the unit interval. Accept both: `800` (raw thousandths) and
    `0.8` / `.8` / `1.0` (decimal, ≤3 fraction digits). Clamped to 1000. -/
def parseRegister? (v : String) : Option Nat :=
  if v.contains '.' then
    match v.splitOn "." with
    | [i, f] =>
      if f.isEmpty || f.length > 3 then none
      else
        let whole := if i.isEmpty then some 0 else i.toNat?
        whole.bind fun w =>
          ((f ++ "").pushn '0' (3 - f.length)).toNat?.map fun frac =>
            min (w * 1000 + frac) 1000
    | _ => none
  else v.toNat?.map (min · 1000)

/-- One field update; `none` = unknown key or bad value. -/
def applySet (t : ThemeVector) : String → String → Option ThemeVector
  | "hero", v => v.toNat?.map fun n => { t with heroHue := n % 360 }
  | "axis", v => v.toNat?.map fun n => { t with axisHue := n % 360 }
  | "register", v => (parseRegister? v).map fun n => { t with register := n }
  | "ramp", v =>
    v.toNat?.bind fun n =>
      match t.luminance with
      | .light lv _ => some { t with luminance := .light lv (n % 360) }
      | .dark _ => none  -- the hue lock: dark ramps are not a knob
  | "polarity", "dark" =>
    some { t with luminance := match t.luminance with
                               | .dark lv => .dark lv
                               | .light _ _ => .dark .carbon }
  | "polarity", "light" =>
    some { t with luminance := match t.luminance with
                               | .light lv r => .light lv r
                               | .dark _ => .light .neoform 211 }
  | "level", v =>
    match t.luminance with
    | .dark _ => (BlackLevel.ofName? v).map fun lv => { t with luminance := .dark lv }
    | .light _ r => (WhiteLevel.ofName? v).map fun lv => { t with luminance := .light lv r }
  | _, _ => none

def applySets (t : ThemeVector) : List String → Option ThemeVector
  | [] => some t
  | key :: value :: rest => (applySet t key value).bind (applySets · rest)
  | _ => none

end Wintermute.Shell
