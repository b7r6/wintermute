/*
 * bytes.c — StdlibEx.Bytes native shims (@[extern], SIMD).
 *
 * memmem : ByteArray -> ByteArray -> Option Nat
 *   The proven `StdlibEx.Bytes.memmem` lowered to glibc `memmem` (SIMD; among
 *   the most-fuzzed C functions alive). Its semantics match the Lean body
 *   EXACTLY:
 *     - empty needle              -> glibc returns haystack  -> some 0
 *     - needle longer than hay    -> glibc returns NULL      -> none
 *     - otherwise                 -> first in-place match    -> some idx
 *
 *   Kept honest by a differential fuzz gate against the proven Lean reference
 *   (the @[extern] Lean body stays the kernel definition; this adds no axiom).
 */

/* _GNU_SOURCE (for memmem) comes from the -D_GNU_SOURCE compile flag. */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

/* stdlibex_memmem (needle haystack : ByteArray) : Option Nat.
 * Pure @[extern]: both args are owned references, consumed here. */
LEAN_EXPORT lean_object* stdlibex_memmem(lean_object* needle, lean_object* haystack) {
  size_t nn = lean_sarray_size(needle);
  size_t hn = lean_sarray_size(haystack);
  const uint8_t* np = lean_sarray_cptr(needle);
  const uint8_t* hp = lean_sarray_cptr(haystack);

  const void* r = memmem(hp, hn, np, nn);

  lean_object* res;
  if (r == NULL) {
    res = lean_box(0); /* Option.none */
  } else {
    size_t idx = (const uint8_t*)r - hp;
    res = lean_alloc_ctor(1, 1, 0); /* Option.some _ */
    lean_ctor_set(res, 0, lean_usize_to_nat(idx));
  }

  lean_dec(needle);
  lean_dec(haystack);
  return res;
}
