/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // VERIFY // BOUNDS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Row-2 of the proof-carrying-codegen ladder (STR-212/STR-213): a length bound
    governed by integer arithmetic, where the dangerous behaviour is decided by a
    REDUCTION, not enumeration. `∀ (start, n) : ℕ²` is infinite, but the property is
    piecewise-linear, so `omega` closes it in one shot — a category-level guarantee
    over the whole domain, not a sampled scope.

    This is the proof that STR-208's fix is total. The generated bound emitter cites
    `guard_accepts_iff_fits`; `wrap_admits_oob` is the exact characterization of the
    bug the unsafe form had.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Verify.Bounds

/-- The overflow-safe guard accepts a slice `[start, start+n)` of a buffer of `size`
    bytes **iff** it genuinely fits — `start + n ≤ size` in true (ℕ) arithmetic. This
    is the emitted guard's specification, proven for every input. -/
theorem guard_accepts_iff_fits
        (size start count : Nat)
        : (start ≤ size ∧ count ≤ size - start) ↔ start + count ≤ size := by omega

/-- The complementary rejection form actually emitted (`start > size || n > size - start`),
    proven equivalent to the true overflow test `size < start + n`. -/
theorem guard_rejects_iff_overflows
        (size start count : Nat)
        : (size < start ∨ size - start < count) ↔ size < start + count := by omega

/-- The exact bug the UNSAFE form had: when the true offset+length exceeds the machine
    word `W`, the wrapped comparison the old C++ used (`size < (start+n) mod W`) can
    *accept* — `¬ (size < (start+n) % W)` — a slice that true arithmetic *rejects*
    (`size < start + n`). That gap is the out-of-bounds read. No enumeration: it holds
    for every `(size, start, n)` once the sum wraps and the wrapped value fits. -/
theorem wrap_admits_oob
        (world size start count : Nat)
        (hsz : size < world)
        (hover : world ≤ start + count)
        (hfit : (start + count) % world ≤ size)
        : ¬(size < (start + count) % world) ∧ size < start + count := by
  generalize (start + count) % world = wrappedEnd at hfit ⊢

  exact ⟨by omega, by omega⟩

/-- Conversely, when the sum does NOT wrap (`start + n < W`), the wrapped guard and the
    true guard agree exactly — so the bug is confined precisely to the wrapping inputs,
    and the overflow-safe form (which never wraps) is correct everywhere. -/
theorem no_wrap_agrees
        (world size start count : Nat)
        (hnowrap : start + count < world)
        : (size < (start + count) % world) = (size < start + count) := by
  rw [Nat.mod_eq_of_lt hnowrap]

end Continuity.Verify.Bounds
