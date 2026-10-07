import Lean

open Lean Elab Parser

/-- Swallow stdout (parser/elaborator diagnostics) during `act`. -/
def quietly {resultType : Type} (action : IO resultType) : IO resultType := do
  let buffer ← IO.mkRef { : IO.FS.Stream.Buffer }
  IO.withStdout (IO.FS.Stream.ofBuffer buffer) action

/-- Best (min) wall-nanoseconds over `n` runs of `act`. Min = least-noisy estimate
    (fewest preemptions / cache misses). Pure Lean timing — no FFI, so it can't
    trip the libc++/libstdc++ boundary that a C++ bench shim would. -/
def time_action_iterated (num_iters : Nat) (action : IO Unit) : IO Nat := do
  let mut best_time_ns : Nat := 0
  for idx in [ 0 : num_iters ] do
    let start_time_ns ← IO.monoNanosNow
    action
    let end_time_ns ← IO.monoNanosNow

    -- Compute and retain the best elapsed time.
    let elapsed := end_time_ns - start_time_ns
    if idx == 0 || elapsed < best_time_ns then best_time_ns := elapsed

  -- Return the least noisy sample.
  pure best_time_ns

def fmt_us (nanoseconds : Nat) : String := s!"{nanoseconds / 1000}us"

def megabytes_per_s (num_bytes : Nat) (nanoseconds : Nat) : String :=
  if nanoseconds == 0 then "-" else s!"{(num_bytes * 1000) / nanoseconds} MB/s" -- bytes/ns*1000 ≈ MB/s

/-- For one file: build its env once, then time (a) cheap parse (testParseModule),
    (b) full interleaved elaborate, and (c) tablesOnly elaborate — `by` blocks
    treated as `sorry` (`debug.byAsSorry`), i.e. parser tables kept current but
    proof-checking skipped. -/
unsafe
def benchmark_parsing_src (runs : Nat) (path : String) : IO Unit := do

  -- synchronous read of file contents and input context
  let contents ← IO.FS.readFile path
  let num_bytes := contents.toUTF8.size
  let ictx := mkInputContext contents path

  -- header handling
  let (hdr, mps, msgs) ← parseHeader ictx
  let (env, _) ← processHeader hdr {} msgs ictx (trustLevel := 1024)

  -- Configure table-only elaboration to skip proofs.
  let tables_only_parse_options : Options := Options.empty.setBool `debug.byAsSorry true

  -- Measure parser-only throughput.
  let parse_time_ns ← time_action_iterated
    runs
    (quietly do
        try
          let _ ← testParseModule env path contents
          pure ()
        catch _ => pure ()
      )

  -- Measure full elaboration throughput.
  let elabNs ← time_action_iterated
    runs
    (quietly do
      let _ ← Lean.Elab.IO.processCommands ictx mps (Command.mkState env msgs {})
      pure ())

  -- Measure elaboration with proofs treated as sorry.
  let tablesNs ← time_action_iterated
    runs
    (quietly do
      let _ ←
        Lean.Elab.IO.processCommands ictx mps (Command.mkState env msgs tables_only_parse_options)
      pure ())

  -- Compute the full-elaboration overhead.
  let ratio := if parse_time_ns == 0 then 0 else elabNs / parse_time_ns

  -- Compute the percentage saved by table-only elaboration.
  let saved := if elabNs == 0 then 0 else 100 - (tablesNs * 100 / elabNs)

  -- Report all benchmark measurements.
  IO.println
    s!"{num_bytes}B  parse={fmt_us parse_time_ns}  elab={fmt_us elabNs} ({megabytes_per_s num_bytes elabNs})  tablesOnly={fmt_us tablesNs} ({megabytes_per_s num_bytes tablesNs}, -{saved}%)  elab/parse={ratio}x  {path}"

unsafe
def run_benchmark (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution

  -- Run each source benchmark with a fixed sample count.
  let runs := 3
  for src_file in args do
    try benchmark_parsing_src runs src_file
    catch ex => IO.eprintln s!"skip {src_file}: {ex}"

  -- Report the sampling discipline.
  IO.eprintln s!"(best of {runs} runs each)"

@[implemented_by run_benchmark]
opaque benchMain (args : List String) : IO Unit

def main (args : List String) : IO Unit := benchMain args
