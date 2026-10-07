/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // stdlibex // logging
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Track-B logging: wraps spdlog via `Logging/log.cpp`. Logging is not proof
    surface — there is nothing to verify about emitting a timestamped line.
    Lean owns formatting (`s!"…"`); spdlog owns everything that's actually hard:
    leveled sinks, colored console, file/rotating sinks, async queue,
    thread-safety, microsecond timestamps.

    The shim passes only `const char*` across the boundary, so the C++ stdlib
    never crosses into Lean.

    The C++ shim lives at `Logging/log.cpp`.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Logging

--  ── levels ───────────────────────────────────────────────────────────────────

/-- spdlog levels (matches `spdlog::level::level_enum`). -/
inductive Level where
  | trace
  | debug
  | info
  | warn
  | error
  | critical
  | off
  deriving Repr, DecidableEq, Inhabited

def Level.toUInt32 : Level → UInt32
  | .trace    => 0
  | .debug    => 1
  | .info     => 2
  | .warn     => 3
  | .error    => 4
  | .critical => 5
  | .off      => 6

--  ── FFI ──────────────────────────────────────────────────────────────────────

/-- Initialize logging: `console` adds a colored stderr sink; non-empty
    `file` adds a file sink; `pattern` is spdlog's format ("" = default);
    `level` is the threshold below which messages are dropped. -/
@[extern "stdlibex_log_init"]
opaque initRaw (console : UInt8) (file : @& String) (pattern : @& String) (level : UInt32) : IO Unit

/-- Initialize with a size-capped rotating file sink (`maxSize` bytes,
    `maxFiles` rotations kept). -/
@[extern "stdlibex_log_init_rotating"]
opaque initRotatingRaw (file : @& String) (maxSize : USize) (maxFiles : USize) (level : UInt32) :
    IO Unit

/-- Log a pre-formatted message at the given level. -/
@[extern "stdlibex_log_at"]
opaque logAtRaw (level : UInt32) (msg : @& String) : IO Unit

/-- Set the default log level. -/
@[extern "stdlibex_log_set_level"]
opaque setLevelRaw (level : UInt32) : IO Unit

/-- Flush all sinks. -/
@[extern "stdlibex_log_flush"]
opaque flush : IO Unit

--  ── lean4 API ────────────────────────────────────────────────────────────────

/-- Initialize a colored console logger at the given level, default pattern. -/
def initConsole (level : Level := .info) : IO Unit :=
  initRaw 1 "" "[%H:%M:%S.%e] [%^%l%$] %v" level.toUInt32

/-- Initialize console + file sink, default pattern. -/
def initConsoleAndFile (file : String) (level : Level := .info) : IO Unit :=
  initRaw 1 file "[%H:%M:%S.%e] [%^%l%$] %v" level.toUInt32

/-- Initialize file-only sink, default pattern. -/
def initFile (file : String) (level : Level := .info) : IO Unit :=
  initRaw 0 file "[%Y-%m-%d %H:%M:%S.%e] [%l] %v" level.toUInt32

/-- Initialize a rotating file logger. -/
def initRotating
    (file : String)
    (maxSize : USize)
    (maxFiles : USize)
    (level : Level := .info)
    : IO Unit :=
  initRotatingRaw file maxSize maxFiles level.toUInt32

/-- Set the log level at runtime. -/
def setLevel (level : Level) : IO Unit := setLevelRaw level.toUInt32

/-- Log a message at the given level. -/
def log (level : Level) (msg : String) : IO Unit := logAtRaw level.toUInt32 msg

/-- Log at trace level. -/
def trace (msg : String) : IO Unit := log .trace msg

/-- Log at debug level. -/
def debug (msg : String) : IO Unit := log .debug msg

/-- Log at info level. -/
def info (msg : String) : IO Unit := log .info msg

/-- Log at warn level. -/
def warn (msg : String) : IO Unit := log .warn msg

/-- Log at error level. -/
def error (msg : String) : IO Unit := log .error msg

/-- Log at critical level. -/
def critical (msg : String) : IO Unit := log .critical msg

end StdlibEx.Logging
