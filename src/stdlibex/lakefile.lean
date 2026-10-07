import Lake
open Lake DSL

open Lean (Name)
open System (FilePath)

/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // STDLIBEX // LAKEFILE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The audit floor. C/C++ shims live NEXT TO the Lean modules that import them,
    grouped by what the shim IS (not by which higher artifact consumes it):

      StdlibEx/Bytes/       bytes.c         (glibc memmem, SIMD)
      StdlibEx/Logging/     log.cpp         (spdlog)         [TODO: migrate]
      StdlibEx/CLI/         cli.cpp         (CLI11)          [TODO: migrate]
      StdlibEx/Linux/       uring.c, ...    (io_uring)       [TODO: migrate]
      StdlibEx/TLS/         tls.c, ...      (libressl)       [TODO: migrate]

    Legacy bridge/ structure (being migrated):
      cpp/bridge/evring/    io_uring: evring.c evring_loop.c evring_mesh.c
      cpp/bridge/net/       transport: straylight_tls.c straylight_tls_bio.c straylight_h3.c
      cpp/bridge/nix/       straylight-nix: straylight_cas.cpp straylight_ffi.c
      cpp/bridge/linux/     kernel API: fanotify_shim.c
      cpp/logging/          straylight_log.cpp
      cpp/cli/              straylight_cli.cpp

    All shims are archived into one `extern_lib «straylight-shims»`. Every
    consumer (aleph, …) `require`s this package; Lake links the extern_lib from
    the dependency closure into each executable automatically.

    Native search paths come from the environment, not hardcoded prefixes.
    The flake devshell (../flake.nix) exports:

      ALEPH_INCLUDE_PATH   colon-separated header dirs (liburing, ngtcp2,
                           nghttp3, gnutls, libressl, spdlog, fmt, CLI11)
      ALEPH_LIB_PATH       colon-separated lib dirs for the same
      STRAYLIGHT_NIX_PREFIX  optional; enables the CAS shim (decision XV)
                             when <prefix>/lib/libstraylight_nix.a exists

    Outside the shell everything still elaborates; the C shims fall back to
    default system search paths.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

def splitPaths (paths : String) : Array String := (paths.splitOn ":").filter (· ≠ "") |>.toArray

def includeDirs : Array String := splitPaths ((run_io (IO.getEnv "ALEPH_INCLUDE_PATH")).getD "")

def libDirs : Array String := splitPaths ((run_io (IO.getEnv "ALEPH_LIB_PATH")).getD "")

def includeFlags : Array String := includeDirs.flatMap (#["-I", ·])

-- straylight-nix prefix for the CAS bridge (ca_store + vendored blake3).
-- The shim is the CONTENT layer (decision XV); flake resolution / dir import
-- remain the nix-evaluator surface and are a separate, heavier binding.
def straylightNixPrefix : String :=
  (run_io (IO.getEnv "STRAYLIGHT_NIX_PREFIX")).getD "/usr/local/straylight-nix"

def straylightNixLib : FilePath := FilePath.mk straylightNixPrefix / "lib" / "libstraylight_nix.a"

def hasStraylightNix : Bool := run_io straylightNixLib.pathExists

package «stdlibex» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- StdlibEx.* — the Lean foundation over the native shims in `cpp/`. The LOWEST package
-- in the DAG: it imports only Lean core + batteries, never anything under Continuity.*/
-- Net.*/Aleph.*/an app.
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "fa08db58b30eb033edcdab331bba000827f9f785"

lean_lib «StdlibEx» where
  srcDir := "."
  globs := #[.andSubmodules `stdlib_ex]

-- ── C/C++ shim targets ────────────────────────────────────────────────────────

-- One .o per shim; the consumer's exe pulls them in through the extern_lib in
-- this package's dependency closure. C shims stay C (they must pull no C++
-- stdlib); C++ shims compile with the same stdlib the link names via -lstdc++
-- (decision VII: never mix libc++ and libstdc++).

/-- Compile a single C/C++ shim to an object file. `subdir` selects the shim's
directory under this package's `cpp/` (`bytes`/`logging`/`cli` for the foundation,
`bridge/<edge>` for the housed bridges). The full command line is mixed into the
dep trace so flag or include-path changes rebuild the .o. -/
def compileShim
    (pkg : NPackage __name__)
    (subdir stem ext : String)
    (compiler : String)
    (flags : Array String)
    : FetchM (Job FilePath) := do
  let src :=
    if subdir.isEmpty then
      pkg.dir / "cpp" / (stem ++ "." ++ ext)
    else
      pkg.dir / "cpp" / subdir / (stem ++ "." ++ ext)

  -- Select the output object path and Lean headers.
  let dst := pkg.buildDir / "c" / (stem ++ ".o")
  let leanInc := (← getLeanIncludeDir).toString

  -- Assemble the shim compiler invocation.
  let args :=
    flags ++ includeFlags
        ++ #["-c", src.toString, "-o", dst.toString, "-I", leanInc, "-fPIC", "-O2"]

  -- Hash the complete compiler invocation.
  let argTrace :=
    BuildTrace.ofHash <| Hash.ofString <| compiler ++ " " ++ " ".intercalate args.toList

  -- Compile after the source dependency is available.
  buildFileAfterDep dst (← inputTextFile src) (extraDepTrace := pure argTrace) fun _ => do
    createParentDirs dst
    proc { cmd := compiler, args }

/-- Compile a shim that lives next to its Lean module (new layout). `modPath` is
the module path relative to package root (e.g. "StdlibEx/Bytes"). -/
def compileModShim
    (pkg : NPackage __name__)
    (modPath stem ext : String)
    (compiler : String)
    (flags : Array String)
    : FetchM (Job FilePath) := do
  let src := pkg.dir / modPath / (stem ++ "." ++ ext)
  let dst := pkg.buildDir / "c" / (stem ++ ".o")
  let leanInc := (← getLeanIncludeDir).toString

  -- Assemble the module-adjacent shim invocation.
  let args :=
    flags ++ includeFlags
        ++ #["-c", src.toString, "-o", dst.toString, "-I", leanInc, "-fPIC", "-O2"]

  -- Hash the complete compiler invocation.
  let argTrace :=
    BuildTrace.ofHash <| Hash.ofString <| compiler ++ " " ++ " ".intercalate args.toList

  -- Compile after the source dependency is available.
  buildFileAfterDep dst (← inputTextFile src) (extraDepTrace := pure argTrace) fun _ => do
    createParentDirs dst
    proc { cmd := compiler, args }

-- ── StdlibEx.TLS — new canonical TLS FFI layer ────────────────────────────────
-- High-level libtls client (Client.lean/client.c) + async memory BIO (Bio.lean/bio.c).
-- Renamed from straylight_tls_* / sl_bio_* to tls_* / bio_*.

target tls_client.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/TLS" "client" "c" "cc" #["-std=gnu11"]

target tls_bio.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/TLS" "bio" "c" "cc" #["-std=gnu11"]

-- ── StdlibEx.Net.Http3 — HTTP/3 over QUIC (ngtcp2 + nghttp3 + GnuTLS) ─────────
target h3.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Net/Http3" "h3" "c" "cc" #["-std=gnu11"]

-- ── Legacy TLS (straylight_tls_*, sl_bio_*) — kept during migration ───────────

-- TLS bridge (LibreSSL libtls).
target straylight_tls.o pkg : FilePath :=
  compileShim pkg "bridge/net" "straylight_tls" "c" "cc" #["-std=gnu11"]

-- HTTP/3 + QUIC bridge (ngtcp2 + nghttp3 + GnuTLS).
target straylight_h3.o pkg : FilePath :=
  compileShim pkg "bridge/net" "straylight_h3" "c" "cc" #["-std=gnu11"]

-- async TLS via libssl over memory BIOs (crypto decoupled from socket I/O, so
-- io_uring can drive the network side). Userspace AEAD; no new dep.
target straylight_tls_bio.o pkg : FilePath :=
  compileShim pkg "bridge/net" "straylight_tls_bio" "c" "cc" #["-std=gnu11"]

-- ── Legacy Nix FFI (straylight_*) — kept for Aleph consumers ──────────────────
target straylight_ffi.o pkg : FilePath :=
  compileShim pkg "bridge/nix" "straylight_ffi" "c" "cc" #["-std=gnu11"]

-- ── StdlibEx.Nix — new canonical Nix FFI layer ────────────────────────────────
target nix_ffi.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Nix" "ffi" "c" "cc" #["-std=gnu11"]

-- CAS bridge (straylight-nix ca_store). Decision XV: the digest is the
-- authorization. Only built when STRAYLIGHT_NIX_PREFIX provides the static
-- lib + headers; everything else works without it.
target cas.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Nix" "cas" "cpp" "c++"
    #["-std=gnu++23", "-I", straylightNixPrefix ++ "/include"]

-- Legacy CAS (straylight_cas_*) for Aleph consumers
target straylight_cas.o pkg : FilePath :=
  compileShim pkg "bridge/nix" "straylight_cas" "cpp" "c++"
    #["-std=gnu++23", "-I", straylightNixPrefix ++ "/include"]

-- StdlibEx.Bytes general byte primitives: memmem = the proven StdlibEx.Bytes.memmem
-- lowered to glibc memmem (SIMD). The C lives next to the Lean that imports it.
target bytes.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Bytes" "bytes" "c" "cc" #["-std=gnu11", "-D_GNU_SOURCE"]

-- fanotify watcher shim (Linux-only kernel API). New location.
target fanotify.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Linux/Fanotify" "fanotify" "c" "cc" #["-std=gnu11"]

-- Legacy: old location, kept until Aleph.Watcher is migrated
target fanotify_shim.o pkg : FilePath :=
  compileShim pkg "bridge/linux" "fanotify_shim" "c" "cc" #["-std=gnu11"]

-- ── StdlibEx.IOUring — new canonical io_uring FFI layer ───────────────────────
-- Pure-C core (ur_*, ul_*, um_*) + Lean-ABI wrappers (uring_*, uloop_*, umesh_*).
-- The core is testable standalone against a live ring; URING_WITH_LEAN enables
-- the lean_object wrappers for the on-box link. C files live next to their Lean.

target uring_core.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/IOUring" "core" "c" "cc" #["-std=gnu11", "-DURING_WITH_LEAN"]

target uring_loop.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/IOUring" "loop" "c" "cc" #["-std=gnu11", "-DURING_WITH_LEAN"]

target uring_mesh.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/IOUring" "mesh" "c" "cc" #["-std=gnu11", "-DURING_WITH_LEAN"]

-- ── Legacy io_uring (evring_*) — kept for EVRing.* consumers during migration ─
-- io_uring bridge (evring). Pure-C core + Lean-ABI wrappers; the core is
-- proven against a live ring. The EVRING_WITH_LEAN guard enables the
-- lean_object wrappers for the on-box link.
target evring.o pkg : FilePath :=
  compileShim pkg "bridge/evring" "evring" "c" "cc" #["-std=gnu11", "-DEVRING_WITH_LEAN"]

-- io_uring proactor (evring_loop): the batched event-loop ring — multishot
-- accept/recv, provided buffer ring, flat completion records. Same layering
-- as evring.c; same live-ring proof discipline.
target evring_loop.o pkg : FilePath :=
  compileShim pkg "bridge/evring" "evring_loop" "c" "cc" #["-std=gnu11", "-DEVRING_WITH_LEAN"]

-- shared-nothing MESH wire (evring_mesh): thin IORING_OP_MSG_RING transport
-- between core-pinned rings. Pure em_* core + Lean-ABI emesh_* wrappers; same
-- layering + live-ring discipline as evring_loop.c.
target evring_mesh.o pkg : FilePath :=
  compileShim pkg "bridge/evring" "evring_mesh" "c" "cc" #["-std=gnu11", "-DEVRING_WITH_LEAN"]

-- spdlog logging shim (C++ → extern C). Lives next to StdlibEx.Logging.
target log.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Logging" "log" "cpp" "c++" #["-std=gnu++17"]

-- nanobench microbenchmark shim (C++ header-only, vendored → extern C). Lives
-- next to StdlibEx.Benchmark; the header is included from the shim's own dir.
-- Compiled with Lean's OWN clang + libc++ (not the system c++/libstdc++): the
-- shim catches Lean-runtime C++ exceptions that escape a benchmarked action, and
-- Lean's runtime throws them via libc++ — mixing libc++/libstdc++ would make the
-- catch a cross-ABI no-op → std::terminate (decision VII).
target bench.o pkg : FilePath :=
  compileModShim pkg "StdlibEx/Benchmark" "bench" "cpp" "c++" #["-std=gnu++17"]

-- Legacy: old location, kept until Aleph.Log is migrated
target straylight_log.o pkg : FilePath :=
  compileShim pkg "logging" "straylight_log" "cpp" "c++" #["-std=gnu++17"]

-- CLI11 argument-parsing shim (C++ header-only → extern C).
target straylight_cli.o pkg : FilePath :=
  compileShim pkg "cli" "straylight_cli" "cpp" "c++" #["-std=gnu++17"]

-- All shim objects archived as an extern_lib: built with the package and
-- LINKED into every dependent exe (Lake links extern_libs from the dependency
-- closure automatically).
extern_lib «straylight-shims» pkg := do
  let mut objs : Array (Job FilePath) := #[]

  -- New TLS FFI (stdlibex_tls_*, bio_*, sock_*)
  objs := objs.push (← tls_client.o.fetch)
  objs := objs.push (← tls_bio.o.fetch)

  -- New HTTP/3 FFI (h3_*)
  objs := objs.push (← h3.o.fetch)

  -- New Nix FFI (nix_*)
  objs := objs.push (← nix_ffi.o.fetch)

  -- Legacy TLS (straylight_tls_*, sl_bio_*) for consumers during migration
  objs := objs.push (← straylight_tls.o.fetch)
  objs := objs.push (← straylight_tls_bio.o.fetch)
  objs := objs.push (← straylight_h3.o.fetch)  -- legacy h3 (straylight_h3_*)
  objs := objs.push (← straylight_ffi.o.fetch)  -- legacy nix (straylight_*)
  objs := objs.push (← bytes.o.fetch)
  objs := objs.push (← log.o.fetch)
  objs := objs.push (← bench.o.fetch)
  objs := objs.push (← fanotify.o.fetch)
  objs := objs.push (← fanotify_shim.o.fetch)  -- legacy, for Aleph.Watcher

  -- New IOUring FFI (uring_*, uloop_*, umesh_*)
  objs := objs.push (← uring_core.o.fetch)
  objs := objs.push (← uring_loop.o.fetch)
  objs := objs.push (← uring_mesh.o.fetch)

  -- Legacy evring_* symbols (for EVRing.* consumers during migration)
  objs := objs.push (← evring.o.fetch)
  objs := objs.push (← evring_loop.o.fetch)
  objs := objs.push (← evring_mesh.o.fetch)
  objs := objs.push (← straylight_log.o.fetch)  -- legacy, for Aleph.Log
  objs := objs.push (← straylight_cli.o.fetch)

  if hasStraylightNix then
    objs := objs.push (← cas.o.fetch)  -- new CAS (cas_*)
    objs := objs.push (← straylight_cas.o.fetch)  -- legacy CAS (straylight_cas_*)

  buildStaticLib (pkg.staticLibDir / nameToStaticLib "straylight-shims") objs

-- dev tool: benchmark parse-vs-elaborate cost per file (StdlibEx.Benchmark).
lean_exe «bench-elab» where
  root := `bench_elab
