/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // stdlibex // benchmark
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Microbenchmarking, backed by nanobench (vendored single header, MIT). Lean
    owns the thing under test (any `IO Unit`); nanobench owns the hard part:
    adaptive iteration counts, warmup, wall-clock + perf counters (cycles,
    instructions, branches, branch-misses where `perf_event_paranoid` allows),
    and a tidy stdout table with error estimates.

    The `IO Unit` action is run once per iteration inside nanobench's loop (the
    C++ shim calls back into Lean); its result is passed through
    `doNotOptimizeAway` so the compiler can't hoist the work out.

    The C++ shim lives at `Benchmark/bench.cpp`; nanobench at `Benchmark/nanobench.h`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Benchmark

/-- Benchmark `action` under nanobench, auto-tuning the iteration count (or, if
    `minIters > 0`, running at least that many per epoch). Prints a stats row for
    `name`. -/
@[extern "stdlibex_bench_run"]
opaque runRaw (name : @& String) (minIters : USize) (action : IO Unit) : IO Unit

/-- Benchmark `action`, reporting per `batch` units of work (bytes, items, …) so
    the row shows time and throughput per unit. -/
@[extern "stdlibex_bench_run_batch"]
opaque runBatchRaw (name : @& String) (batch : USize) (action : IO Unit) : IO Unit

/-- Benchmark an `IO Unit` action, letting nanobench pick the iteration count. -/
def bench (name : String) (action : IO Unit) : IO Unit := runRaw name 0 action

/-- Benchmark with a floor of `minIters` iterations per epoch (steadier numbers
    for very fast actions). -/
def benchAtLeast (name : String) (minIters : Nat) (action : IO Unit) : IO Unit :=
  runRaw name (USize.ofNat minIters) action

/-- Benchmark reporting throughput per `batch` units of work per call. -/
def benchBatch (name : String) (batch : Nat) (action : IO Unit) : IO Unit :=
  runBatchRaw name (USize.ofNat batch) action

end StdlibEx.Benchmark
