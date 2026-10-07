/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // STDLIBEX
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The continuity-scoped standard library — the LOWEST package in the DAG. A companion
    to Lean's stdlib, tuned for systems work: proven references paired with `@[extern]`
    fast paths and differential gates, over the native shims in `../cpp`. Its own root
    namespace (`StdlibEx.*`), because it is the foundation everything — Continuity
    included — stands on, and it depends UP on nothing.

      StdlibEx.Proof            the internal floor: the differential-gate harness, the
                                native_decide scope-closure idiom, the standard checklist
      StdlibEx.Datastructures   proven containers (Fifo, …)
      — growing: Bytes · Logging · CLI · String · IO · FFI —

    See the book (docs/book → "StdlibEx — a scoped standard library").
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/
import stdlib_ex.proof
import stdlib_ex.datastructures
import stdlib_ex.bytes
import stdlib_ex.logging
import stdlib_ex.cli
import stdlib_ex.linux
import stdlib_ex.tls
