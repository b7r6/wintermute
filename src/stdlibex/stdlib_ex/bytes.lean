/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // STDLIBEX // BYTES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Byte primitives backed by libc. These are AXIOMATIZED — we trust glibc's
    contract, not a Lean reference implementation. The axioms state exactly
    what POSIX/glibc promises; downstream proofs build on those axioms.

    Current citizens:
      · `memmem` — substring search (glibc `memmem`, SIMD)

    The C shim lives at `Bytes/bytes.c`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Bytes

-- ══════════════════════════════════════════════════════════════════════════════
-- MEMMEM — substring search
-- ══════════════════════════════════════════════════════════════════════════════

/-- Find first occurrence of `needle` in `haystack`. Returns the byte offset
    of the first match, or `none` if not found.

    Wraps glibc `memmem` (SIMD, heavily fuzzed). The semantics are POSIX:
      · empty needle             → `some 0`
      · needle longer than hay   → `none`
      · otherwise                → first index where needle occurs -/
@[extern "stdlibex_memmem"]
opaque memmem (needle haystack : ByteArray) : Option Nat

-- ══════════════════════════════════════════════════════════════════════════════
-- MEMMEM AXIOMS — the libc contract
-- ══════════════════════════════════════════════════════════════════════════════

/-- Empty needle always matches at position 0. -/
axiom memmem_empty (haystack : ByteArray) : memmem ⟨#[]⟩ haystack = some 0

/-- If needle is longer than haystack, no match. -/
axiom memmem_too_long (needle haystack : ByteArray) (proof : haystack.size < needle.size) :
    memmem needle haystack = none

/-- If memmem returns `some i`, the needle actually occurs at index `i`:
    - `i + needle.size ≤ haystack.size` (in bounds)
    - bytes match: `∀ j < needle.size, haystack[i+j] = needle[j]` -/
axiom memmem_sound (needle haystack : ByteArray) (idx : Nat) (proof : memmem needle haystack = some idx) :
    idx + needle.size ≤ haystack.size
        ∧ ∀ jdx, jdx < needle.size → haystack[idx + jdx]! = needle[jdx]!

/-- If memmem returns `some i`, it's the FIRST occurrence:
    no earlier index has a complete match. -/
axiom memmem_first (needle haystack : ByteArray) (idx : Nat) (proof : memmem needle haystack = some idx) :
    ∀ kdx, kdx < idx → ∃ jdx, jdx < needle.size ∧ haystack[kdx + jdx]! ≠ needle[jdx]!

/-- If the needle occurs at index `i` and nowhere earlier, memmem finds it. -/
axiom memmem_complete (needle haystack : ByteArray) (idx : Nat) (hbound : idx + needle.size ≤ haystack.size) (hmatch : ∀ jdx, jdx < needle.size → haystack[idx + jdx]! = needle[jdx]!) (hfirst : ∀ kdx,
    kdx < idx → ∃ jdx, jdx < needle.size ∧ haystack[kdx + jdx]! ≠ needle[jdx]!) :
    memmem needle haystack = some idx

end StdlibEx.Bytes
