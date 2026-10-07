// ─────────────────────────────────────────────────────────────────────────────
//                                                    // STDLIBEX // BENCHMARK // SHIM
// ─────────────────────────────────────────────────────────────────────────────
//
//   C++ shim over nanobench (vendored, single header, MIT). Bridges a Lean
//   `IO Unit` action into nanobench's measurement loop: nanobench decides how
//   many iterations to run, calls back into Lean each time, and reports
//   wall-time (+ perf counters where the kernel permits) to stdout.
//
//   Only `const char*` and `lean_object*` (the closure) cross the boundary; the
//   C++ stdlib never leaks into Lean. `ANKERL_NANOBENCH_IMPLEMENT` is defined in
//   THIS translation unit only (nanobench's one-TU implementation rule).
// ─────────────────────────────────────────────────────────────────────────────

#define ANKERL_NANOBENCH_IMPLEMENT
#include <cstdio>
#include <exception>

#include <lean/lean.h>

#include "nanobench.h"

// Run one iteration of a Lean `IO Unit` action. `action` is borrowed by the
// caller; we inc before applying because `lean_apply_1` consumes one reference.
// `world` is the IO world token (`lean_box(0)`, a scalar) — hoisted out of the
// loop and reused, since scalars aren't refcounted so applying it repeatedly is
// free and safe. A Lean-level C++ exception (panic / internal error) that
// escapes the action is caught so the harness survives; its message is reported
// once so the failure is visible rather than silent.
static void run_lean_action(lean_object* action, lean_object* world, const char* name,
                            bool& reported) {
  lean_inc(action);
  try {
    lean_object* res = lean_apply_1(action, world);
    ankerl::nanobench::doNotOptimizeAway(res);
    lean_dec(res);
  } catch (const std::exception& ex) {
    if (!reported) {
      std::fprintf(stderr, "[bench] %s: exception: %s\n", name, ex.what());
      reported = true;
    }
  } catch (...) {
    if (!reported) {
      std::fprintf(stderr, "[bench] %s: unknown exception\n", name);
      reported = true;
    }
  }
}

extern "C" {

// stdlibex_bench_run (name : @& String) (minIters : USize) (action : IO Unit) : IO Unit
// minIters = 0 lets nanobench auto-tune; otherwise a floor on iterations/epoch.
LEAN_EXPORT lean_object* stdlibex_bench_run(b_lean_obj_arg name, size_t min_iters,
                                            lean_obj_arg action, lean_obj_arg /*world*/) {
  const char* nm = lean_string_cstr(name);
  lean_object* w = lean_io_mk_world();
  bool reported = false;
  ankerl::nanobench::Bench bench;
  bench.performanceCounters(true);
  if (min_iters > 0) {
    bench.minEpochIterations(static_cast<uint64_t>(min_iters));
  }
  bench.run(nm, [&] { run_lean_action(action, w, nm, reported); });
  lean_dec(action);
  return lean_io_result_mk_ok(lean_box(0));
}

// stdlibex_bench_run_batch (name : @& String) (batch : USize) (action : IO Unit) : IO Unit
// Reports results per `batch` unit of work (nanobench's .batch()), e.g. bytes or
// items processed per call, so the row shows time and throughput per unit.
LEAN_EXPORT lean_object* stdlibex_bench_run_batch(b_lean_obj_arg name, size_t batch,
                                                  lean_obj_arg action, lean_obj_arg /*world*/) {
  const char* nm = lean_string_cstr(name);
  lean_object* w = lean_io_mk_world();
  bool reported = false;
  ankerl::nanobench::Bench bench;
  bench.performanceCounters(true);
  bench.batch(static_cast<double>(batch));
  bench.run(nm, [&] { run_lean_action(action, w, nm, reported); });
  lean_dec(action);
  return lean_io_result_mk_ok(lean_box(0));
}

} // extern "C"
