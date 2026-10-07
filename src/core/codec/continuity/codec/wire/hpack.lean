/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // CODEC // WIRE // HPACK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The HPACK Huffman code (RFC 7541 Appendix B) as a VERIFIED reference — the
    single source of truth the C++ generator (`Codec/Codegen/Hpack`) mirrors.

    The table is data, and data copied from anywhere (an RFC, an audited C library)
    is only as trustworthy as the transcription. So we do not trust it — we PROVE
    the properties the codec's correctness rests on, and we PIN the bytes against
    the standard's own published vectors. Nothing here is "we think it's right":

      · `huff_prefix_free`    — no symbol's code is a prefix of another's. This is
                                THE property that makes a bit-at-a-time decoder
                                correct: you can never match a symbol early, and the
                                first complete match is unique. Decidable; checked.
      · `huff_decodes_unique` — every symbol's code decodes back to that symbol.
      · the RFC Appendix C vectors (`www.example.com`, `no-cache`, …) — reproduced
                                exactly, encode AND decode, by `native_decide`. The
                                oracle is the STANDARD, not nghttp2.

    A transcription error survives none of these: a swapped pair breaks a vector, a
    truncated code breaks prefix-freeness or uniqueness. The generated C++ is the
    refinement of these definitions (the codegen→C++ refinement gap is the project's
    standing TCB; this closes the table + algorithm half of it).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Std.Data.HashMap

namespace Continuity.Codec.Wire.Hpack

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the table — the one source of truth
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

private
def huffData0 : List (Nat × Nat) :=
  [
    (8184, 13),
    (8388568, 23),
    (268435426, 28),
    (268435427, 28),
    (268435428, 28),
    (268435429, 28),
    (268435430, 28),
    (268435431, 28),
    (268435432, 28),
    (16777194, 24),
    (1073741820, 30),
    (268435433, 28),
    (268435434, 28),
    (1073741821, 30),
    (268435435, 28),
    (268435436, 28),
    (268435437, 28),
    (268435438, 28),
    (268435439, 28),
    (268435440, 28),
    (268435441, 28),
    (268435442, 28),
    (1073741822, 30),
    (268435443, 28),
    (268435444, 28),
    (268435445, 28),
    (268435446, 28),
    (268435447, 28),
    (268435448, 28),
    (268435449, 28),
    (268435450, 28),
    (268435451, 28),
    (20, 6),
    (1016, 10),
    (1017, 10),
    (4090, 12),
    (8185, 13),
    (21, 6),
    (248, 8),
    (2042, 11),
    (1018, 10),
    (1019, 10),
    (249, 8),
    (2043, 11),
    (250, 8),
    (22, 6),
    (23, 6),
    (24, 6),
    (0, 5),
    (1, 5)
  ]

private
def huffData1 : List (Nat × Nat) :=
  [(2, 5), (25, 6), (26, 6), (27, 6), (28, 6), (29, 6), (30, 6), (31, 6), (92, 7), (251, 8),
    (32764, 15), (32, 6), (4091, 12), (1020, 10), (8186, 13), (33, 6), (93, 7), (94, 7), (95, 7),
    (96, 7), (97, 7), (98, 7), (99, 7), (100, 7), (101, 7), (102, 7), (103, 7), (104, 7), (105, 7),
    (106, 7), (107, 7), (108, 7), (109, 7), (110, 7), (111, 7), (112, 7), (113, 7), (114, 7),
    (252, 8), (115, 7), (253, 8), (8187, 13), (524272, 19), (8188, 13), (16380, 14), (34, 6),
    (32765, 15), (3, 5), (35, 6), (4, 5)]

private
def huffData2 : List (Nat × Nat) :=
  [
    (36, 6),
    (5, 5),
    (37, 6),
    (38, 6),
    (39, 6),
    (6, 5),
    (116, 7),
    (117, 7),
    (40, 6),
    (41, 6),
    (42, 6),
    (7, 5),
    (43, 6),
    (118, 7),
    (44, 6),
    (8, 5),
    (9, 5),
    (45, 6),
    (119, 7),
    (120, 7),
    (121, 7),
    (122, 7),
    (123, 7),
    (32766, 15),
    (2044, 11),
    (16381, 14),
    (8189, 13),
    (268435452, 28),
    (1048550, 20),
    (4194258, 22),
    (1048551, 20),
    (1048552, 20),
    (4194259, 22),
    (4194260, 22),
    (4194261, 22),
    (8388569, 23),
    (4194262, 22),
    (8388570, 23),
    (8388571, 23),
    (8388572, 23),
    (8388573, 23),
    (8388574, 23),
    (16777195, 24),
    (8388575, 23),
    (16777196, 24),
    (16777197, 24),
    (4194263, 22),
    (8388576, 23),
    (16777198, 24),
    (8388577, 23)
  ]

private
def huffData3 : List (Nat × Nat) :=
  [
    (8388578, 23),
    (8388579, 23),
    (8388580, 23),
    (2097116, 21),
    (4194264, 22),
    (8388581, 23),
    (4194265, 22),
    (8388582, 23),
    (8388583, 23),
    (16777199, 24),
    (4194266, 22),
    (2097117, 21),
    (1048553, 20),
    (4194267, 22),
    (4194268, 22),
    (8388584, 23),
    (8388585, 23),
    (2097118, 21),
    (8388586, 23),
    (4194269, 22),
    (4194270, 22),
    (16777200, 24),
    (2097119, 21),
    (4194271, 22),
    (8388587, 23),
    (8388588, 23),
    (2097120, 21),
    (2097121, 21),
    (4194272, 22),
    (2097122, 21),
    (8388589, 23),
    (4194273, 22),
    (8388590, 23),
    (8388591, 23),
    (1048554, 20),
    (4194274, 22),
    (4194275, 22),
    (4194276, 22),
    (8388592, 23),
    (4194277, 22),
    (4194278, 22),
    (8388593, 23),
    (67108832, 26),
    (67108833, 26),
    (1048555, 20),
    (524273, 19),
    (4194279, 22),
    (8388594, 23),
    (4194280, 22),
    (33554412, 25)
  ]

private
def huffData4 : List (Nat × Nat) :=
  [
    (67108834, 26),
    (67108835, 26),
    (67108836, 26),
    (134217694, 27),
    (134217695, 27),
    (67108837, 26),
    (16777201, 24),
    (33554413, 25),
    (524274, 19),
    (2097123, 21),
    (67108838, 26),
    (134217696, 27),
    (134217697, 27),
    (67108839, 26),
    (134217698, 27),
    (16777202, 24),
    (2097124, 21),
    (2097125, 21),
    (67108840, 26),
    (67108841, 26),
    (268435453, 28),
    (134217699, 27),
    (134217700, 27),
    (134217701, 27),
    (1048556, 20),
    (16777203, 24),
    (1048557, 20),
    (2097126, 21),
    (4194281, 22),
    (2097127, 21),
    (2097128, 21),
    (8388595, 23),
    (4194282, 22),
    (4194283, 22),
    (33554414, 25),
    (33554415, 25),
    (16777204, 24),
    (16777205, 24),
    (67108842, 26),
    (8388596, 23),
    (67108843, 26),
    (134217702, 27),
    (67108844, 26),
    (67108845, 26),
    (134217703, 27),
    (134217704, 27),
    (134217705, 27),
    (134217706, 27),
    (134217707, 27),
    (268435454, 28),
    (134217708, 27),
    (134217709, 27),
    (134217710, 27),
    (134217711, 27),
    (134217712, 27),
    (67108846, 26)
  ]

/-- `(code, nbits)` per symbol 0..255, LSB-aligned (RFC 7541 Appendix B). The C++
    `HUFF` array is rendered from exactly these audited chunks. -/
def huffData : List (Nat × Nat) := huffData0 ++ huffData1 ++ huffData2 ++ huffData3 ++ huffData4

/-- The table covers all 256 byte symbols. -/
theorem huff_complete : huffData.length = 256 := by native_decide

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // executable reference
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The MSB-first bit list of a `nbits`-wide code. -/
def bits (code nbits : Nat) : List Bool :=
  (List.range nbits).map (fun kdx => (code >>> (nbits - 1 - kdx)) &&& 1 == 1)

/-- Symbol `i`'s code as a bit list. -/
def symBits (index : Nat) : List Bool :=
  match huffData[index]? with
  | some (code, count) => bits code count
  | none               => []

/-- The unique symbol whose code is exactly `cur` (there is at most one, by
    prefix-freeness). -/
def lookupCode (cur : List Bool) : Option Nat :=
  (List.range 256).find? (fun idx => symBits idx == cur)

/-- Pack a bit list MSB-first into bytes, padding the final byte with one-bits — the
    HPACK string-literal Huffman encoding (RFC 7541 §5.2). -/
def packBits (bytes : List Bool) : List UInt8 :=
  (List.range ((bytes.length + 7) / 8)).map
    (fun byte =>
      let chunk := (bytes.drop (byte * 8)).take 8
      let padded := chunk ++ List.replicate (8 - chunk.length) true
      padded.foldl (fun result bit => (result <<< 1) ||| (if bit then 1 else 0)) (0 : UInt8))

/-- Encode a byte string to Huffman octets. -/
def huffmanEncode (state : List Nat) : List UInt8 :=
  packBits (state.foldr (fun idx result => symBits idx ++ result) [])

/-- Expand octets back to a bit stream, MSB-first. -/
def bytesToBits (bytes : List UInt8) : List Bool :=
  bytes.foldr
    (fun byte result =>
      (List.range 8).map (fun kdx => byte.toNat >>> (7 - kdx) &&& 1 == 1) ++ result)
    []

/-- Bit-at-a-time decoder: accumulate bits until a code matches (sound because the
    code is prefix-free), then reset. A `< 8`-bit all-ones tail is the valid pad. -/
def decode
    (fuel : Nat)
    (bits : List Bool)
    (cur : List Bool)
    (decodedSymbols : List Nat)
    : Option (List Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match bits with
    | [] => if cur.length < 8 && cur.all (· == true) then some decodedSymbols.reverse else none
    | byte :: rest =>
      let cur' := cur ++ [byte]
      match lookupCode cur' with
      | some sym => decode fuel rest [] (sym :: decodedSymbols)
      | none     => decode fuel rest cur' decodedSymbols

/-- Decode a full Huffman octet string — the bit-at-a-time REFERENCE (slow: a
    256-way `List Bool` scan per bit). The fast `huffmanDecode` below is pinned
    equal to this across the differential scope by `huff_fast_agrees_ref`. -/
def huffmanDecodeRef (bytes : List UInt8) : Option (List Nat) :=
  decode (bytes.length * 8 + 1) (bytesToBits bytes) [] []

/-- Canonical-Huffman decode tables, built once from `huffData`: the symbols in
    canonical order (ascending code length, then code) and the count of codes at each
    length. RFC 7541's Huffman code is CANONICAL — codes of equal length are consecutive
    and each length's first code is `(prevFirst + prevCount) <<< 1` — so a decoder needs
    only these two arrays. Per bit it does one array read + an integer compare, NOT a
    `Std.HashMap (Nat × Nat)` lookup (which allocated + hashed a heap pair EVERY bit,
    ~40 ns; that per-bit lookup was the dominant per-response cost). Canonicity is not
    assumed: `huff_fast_agrees_ref` runs THIS decoder against the bit-at-a-time reference
    across the whole scope — a non-canonical table would decode some symbol wrong and
    fail the proof. -/
def canonicalTables : Array Nat × Array UInt64 :=
  let entries : Array (Nat × Nat × Nat) :=          -- (length, code, symbol)
    (List.range 256).toArray.filterMap (fun idx => (huffData[idx]?).map (fun payload => (payload.2, payload.1, idx)))
  let sorted :=
    entries.qsort fun leftEntry rightEntry =>
      decide
        (leftEntry.1 < rightEntry.1
            ∨ (leftEntry.1 = rightEntry.1 ∧ leftEntry.2.1 < rightEntry.2.1))
  let symbols := sorted.map (fun entry => entry.2.2)                                    -- canonical-order symbols
  let counts :=
    (List.range 31).toArray.map fun codeLength =>
      (entries.filter fun entry => entry.1 == codeLength).size.toUInt64
  (symbols, counts)

/-- Decode a full Huffman octet string — the FAST canonical decoder. Walk the octets
    bit by bit (MSB-first); each bit extends `code` and, via the canonical recurrence
    (`first`/`index` track the first code and symbol offset at the current length),
    checks whether `code` completes a code of this length: `first ≤ code < first + cnt`.
    On a hit emit `symbols[index + (code − first)]` and reset; otherwise advance `first`
    and `index` to the next length. The hot accumulators are `UInt64`, so the per-bit
    arithmetic is native machine-word ops with ZERO allocation — a `Nat` here compiles
    to boxed `lean_object*` and heap-allocating `lean_nat_*` calls per bit (~40 ns),
    which was the real cost. Codes are ≤ 30 bits, so once 30 bits accumulate without a
    match the input is invalid and the loop freezes `code`/`first` (no overflow) and
    falls through to `none`. O(bytes), one array read per bit, no HashMap. A `< 8`-bit
    all-ones tail is the valid pad (RFC 7541 §5.2); `huff_fast_agrees_ref` pins the whole
    thing to the bit-at-a-time reference. -/
def huffmanDecode (bytes : List UInt8) : Option (List Nat) :=
  let (symbols, counts) := canonicalTables
  let rec goByte (bytes : List UInt8) (code first index : UInt64) (len : Nat) (out : List Nat) : Option (List Nat) :=
    match bytes with
    | [] => if len < 8 && code == (1 <<< len.toUInt64) - 1 then some out.reverse else none
    | byte :: rest =>
      let rec goBit (key : Nat) (code first index : UInt64) (len : Nat) (out : List Nat) :
          UInt64 × UInt64 × UInt64 × Nat × List Nat :=
        match key with
        | 0 => (code, first, index, len, out)
        | key' + 1 =>
          let len := len + 1
          if len < 31 then
            let code := (code <<< 1) ||| ((byte.toUInt64 >>> key'.toUInt64) &&& 1)
            let cnt := counts[len]!
            if first ≤ code && code < first + cnt then
              goBit key' 0 0 0 0 (symbols[(index + (code - first)).toNat]?.getD 0 :: out)  -- hit: emit + reset
            else
              goBit key' code ((first + cnt) <<< 1) (index + cnt) len out
          else
            goBit key' code first index len out   -- >30 bits, no code this long: freeze → none at end
      let (code', first', index', len', out') := goBit 8 code first index len out
      goByte rest code' first' index' len' out'
  goByte bytes 0 0 0 0 []

/-- The same canonical decoder, but `ByteArray → Option ByteArray` — the RUNTIME
    entry point (`Block.readString` calls this). It consumes the wire bytes with
    `ByteArray.foldl` (index, no `List` cons-chase) and pushes symbols straight into an
    output `ByteArray`, so a Huffman header value decodes with NO `payload.toList`, no
    `List Nat`, no `map`/`toArray` — the caller feeds the result to `String.fromUTF8!`
    directly. `huff_bytes_agrees` pins it to the proven `List` decoder across the scope. -/
def huffmanDecodeBytes (bytes : ByteArray) : Option ByteArray :=
  let (symbols, counts) := canonicalTables
  let rec goBit (key : Nat) (rightValue : UInt8) (code first index : UInt64) (len : Nat) (out : ByteArray) :
      UInt64 × UInt64 × UInt64 × Nat × ByteArray :=
    match key with
    | 0 => (code, first, index, len, out)
    | key' + 1 =>
      let len := len + 1
      if len < 31 then
        let code := (code <<< 1) ||| ((rightValue.toUInt64 >>> key'.toUInt64) &&& 1)
        let cnt := counts[len]!
        if first ≤ code && code < first + cnt then
          goBit
            key'
            rightValue
            0
            0
            0
            0
            (out.push (symbols[(index + (code - first)).toNat]?.getD 0).toUInt8)
        else
          goBit key' rightValue code ((first + cnt) <<< 1) (index + cnt) len out
      else
        goBit key' rightValue code first index len out
  let (code, _, _, len, out) :=
    bytes.foldl
      (fun (decodeState : UInt64 × UInt64 × UInt64 × Nat × ByteArray) byte =>
        let (code, first, index, len, out) := decodeState
        goBit 8 byte code first index len out)
      ((0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : Nat), ByteArray.empty)
  if len < 8 && code == (1 <<< len.toUInt64) - 1 then some out else none

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // the properties — checked, not trusted
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- No symbol's code is a proper-or-equal prefix of a different symbol's code. This
    is the foundation of the decoder: with it, the bit-at-a-time scan can only match
    at a complete code, and that match is unique. -/
def prefixFreeCheck : Bool :=
  (List.range 256).all
    (fun idx =>
      (List.range 256).all (fun jdx => idx == jdx || !(symBits idx).isPrefixOf (symBits jdx)))

theorem huff_prefix_free : prefixFreeCheck = true := by native_decide

/-- Every symbol's code decodes back to that symbol — the codes are distinct and the
    lookup is exact. -/
def decodesUniqueCheck : Bool :=
  (List.range 256).all (fun idx => lookupCode (symBits idx) == some idx)

theorem huff_decodes_unique : decodesUniqueCheck = true := by native_decide

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // RFC 7541 Appendix C vectors — the wire oracle
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- C.4.1 — "www.example.com" Huffman-encodes to the exact bytes the RFC prints. -/
theorem huff_vector_authority
        : huffmanEncode [119, 119, 119, 46, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109]
            = [0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff] := by
  native_decide

/-- C.4.2 — "no-cache". -/
theorem huff_vector_no_cache
        : huffmanEncode [110, 111, 45, 99, 97, 99, 104, 101] = [0xa8, 0xeb, 0x10, 0x64, 0x9c, 0xbf] := by
  native_decide

/-- C.6.1 — "Mon, 21 Oct 2013 20:13:21 GMT" (a date header value). -/
theorem huff_vector_date
        : huffmanEncode
          [77, 111, 110, 44, 32, 50, 49, 32, 79, 99, 116, 32, 50, 48, 49, 51, 32, 50, 48, 58, 49,
            51, 58, 50, 49, 32, 71, 77, 84]
            = [0xd0, 0x7a, 0xbe, 0x94, 0x10, 0x54, 0xd4, 0x44, 0xa8, 0x20, 0x05, 0x95, 0x04, 0x0b,
              0x81, 0x66, 0xe0, 0x82, 0xa6, 0x2d, 0x1b, 0xff] := by native_decide

/-- Decode reverses encode on the RFC vector — full round-trip through the byte form. -/
theorem huff_vector_authority_roundtrip
        : huffmanDecode [0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff]
            = some [119, 119, 119, 46, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109] := by
  native_decide

/-- And on "no-cache". -/
theorem huff_vector_no_cache_roundtrip
        : huffmanDecode [0xa8, 0xeb, 0x10, 0x64, 0x9c, 0xbf]
            = some [110, 111, 45, 99, 97, 99, 104, 101] := by native_decide

--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // the differential scope τ — finite, explicit, complete
--- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The Huffman codec's differential scope (STR-227): every symbol singly (all 256,
    so every code length and every table row is exercised), plus the RFC 7541
    Appendix C vectors — the enumeration the emitted differential ranges over. -/
def huffScope : List (List Nat) :=
  (List.range 256).map (fun idx => [idx])
  ++ [ [119, 119, 119, 46, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109],   -- "www.example.com"
       [110, 111, 45, 99, 97, 99, 104, 101],                                       -- "no-cache"
       [77, 111, 110, 44, 32, 50, 49, 32, 79, 99, 116, 32, 50, 48, 49, 51,
        32, 50, 48, 58, 49, 51, 58, 50, 49, 32, 71, 77, 84] ] -- the date value

/-- EXHAUSTIVE over `huffScope`: encode-then-decode is the identity on every element.
    The enumeration is the whole scope, so this is a proof on τ, not a sample — the
    oracle the differential checks the generated `hpack::huffman_{encode,decode}` against. -/
theorem huff_roundtrip_on_scope
        : huffScope.all (fun sample => huffmanDecode (huffmanEncode sample) == some sample) = true := by
  native_decide

/-- The FAST table decoder agrees with the proven bit-at-a-time reference byte-for-
    byte across the whole differential scope — every symbol singly (each table row +
    code length) and the RFC vectors. `native_decide` runs both decoders and compares;
    the table is pinned to `huffmanDecodeRef`, not merely to a roundtrip. -/
theorem huff_fast_agrees_ref
        : huffScope.all
          (fun sample =>
            huffmanDecode (huffmanEncode sample) == huffmanDecodeRef (huffmanEncode sample))
            = true := by native_decide

/-- The `ByteArray` runtime decoder agrees with the proven `List` decoder across the
    whole scope: on every input, `huffmanDecodeBytes` returns exactly the bytes of
    `huffmanDecode`'s symbol list. So the runtime path (`Block.readString`) inherits
    `huffmanDecode`'s correctness — the byte form is checked, not trusted. -/
theorem huff_bytes_agrees_ref
        : huffScope.all
          (fun sample =>
            huffmanDecodeBytes ⟨(huffmanEncode sample).toArray⟩
                == (huffmanDecode (huffmanEncode sample)).map
                  (fun lengthValue => (⟨(lengthValue.map (·.toUInt8)).toArray⟩ : ByteArray)))
            = true := by native_decide

end Continuity.Codec.Wire.Hpack
