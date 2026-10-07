/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // CONTINUITY // CODEC // WIRE // HPACK BLOCK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The HPACK header-block codec (RFC 7541 §6): the layer between the proven
    primitives — huffman (Hpack), integers (parseHpackInt), the 61-entry static
    table (Http2) — and a decoded header list. This is what turns curl's
    huffman-compressed, dynamic-table-indexed request headers into (name, value)
    pairs, and a server's response headers back into wire bytes.

    Decode threads a DYNAMIC TABLE across the whole connection (curl indexes
    incrementally), handling all representations: indexed (§6.1), literal with
    incremental indexing (§6.2.1), literal without / never indexed (§6.2.2-3),
    and dynamic-table size updates (§6.3). Encode is the stateless
    literal-without-indexing form (§6.2.2) — always valid, needs no encoder
    table, and every HTTP/2 client accepts it.

    Gated on the RFC 7541 Appendix C wire vectors (C.3.1 plaintext + C.4.1
    huffman), which exercise indexed lookup, literal-incremental insertion, the
    dynamic table, and huffman decode together.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/
import continuity.codec.wire.http.http_2
import continuity.codec.wire.hpack
import continuity.codec.wire.hpack_int

namespace Continuity.Codec.Wire.Hpack.Block

open Continuity.Codec.Core (Bytes ParseResult)
open Continuity.Codec.Wire.Http.Http2 (HpackEntry staticTable)
open Continuity.Codec.Wire.Hpack (huffmanDecodeBytes)

local instance : Inhabited HpackEntry := ⟨⟨"", ""⟩⟩

/-- The decoder's dynamic table: newest-first entries, current byte size, and
    the negotiated capacity (SETTINGS_HEADER_TABLE_SIZE, default 4096). -/
structure dyn_table where
  entries  : Array HpackEntry := #[]
  size     : Nat := 0
  capacity : Nat := 4096
  deriving Repr, Inhabited

namespace dyn_table

/-- RFC 7541 §4.1: an entry costs name + value octets + 32. -/
def entryCost (entry : HpackEntry) : Nat := entry.name.utf8ByteSize + entry.value.utf8ByteSize + 32

/-- Evict oldest entries until `size ≤ capacity`. -/
partial
def evict (updatedTable : dyn_table) : dyn_table :=
  if updatedTable.size ≤ updatedTable.capacity || updatedTable.entries.isEmpty then
    updatedTable
  else
    let last := updatedTable.entries[updatedTable.entries.size - 1]!
    evict
      { updatedTable with
        entries := updatedTable.entries.pop,
        size := updatedTable.size - entryCost last }

/-- Insert at the front (§6.2.1). If the entry alone exceeds capacity the table
    is emptied (RFC 7541 §4.4). -/
def insert (updatedTable : dyn_table) (entry : HpackEntry) : dyn_table :=
  let cost := entryCost entry
  if cost > updatedTable.capacity then
    { updatedTable with entries := #[], size := 0 }
  else
    let updatedTable :=
      evict
        { updatedTable with
          entries := #[entry] ++ updatedTable.entries,
          size := updatedTable.size + cost }
    updatedTable

/-- Set a new capacity (§6.3) and evict to fit. -/
def setCapacity (updatedTable : dyn_table) (cap : Nat) : dyn_table :=
  evict { updatedTable with capacity := cap }

/-- Table lookup by HPACK index: 1..61 static, 62+ dynamic (newest = 62). -/
def lookup (updatedTable : dyn_table) (idx : Nat) : Option HpackEntry :=
  if idx == 0 then
    none
  else if idx ≤ staticTable.size then
    staticTable[idx - 1]?
  else
    updatedTable.entries[idx - 1 - staticTable.size]?

end dyn_table

/-- Bytes → String, assuming a UTF-8 header (HTTP headers are ASCII in practice). -/
private
def bytesToString (bytes : Bytes) : String := String.fromUTF8! bytes

/-- Read an HPACK varint at `off` (RFC 7541 §5.1): a `prefixBits`-wide prefix then 7-bit
    continuation octets. Returns `(value, nextOffset)`. Offset-threaded — no tail
    `extract`, which is the whole point: `.extract k bs.size` per field made a K-header
    block O(K·B) in tail recopies. (Mirrors the offset form the codegen already emits.) -/
private
def parseIntAt (prefixBits : Nat) (bytes : Bytes) (off : Nat) : Option (Nat × Nat) :=
  if off < bytes.size then
    let mask := (1 <<< prefixBits) - 1
    let firstByte := bytes[off]!.toNat &&& mask
    if firstByte < mask then
      some (firstByte, off + 1)
    else
      let rec parseInteger (index result shift : Nat) : Option (Nat × Nat) :=
        if h : index < bytes.size then
          let byte := bytes[index]!
          let result' := result + ((byte.toNat &&& 0x7F) <<< shift)
          if byte &&& 0x80 == 0 then some (mask + result', index + 1)
          else parseInteger (index + 1) result' (shift + 7)
        else none
      termination_by bytes.size - index
      parseInteger (off + 1) 0 0
  else
    none

/-- Read an HPACK string literal (§5.2) at `off`: H-bit + 7-bit length, then the octets,
    huffman-decoded when H is set. Extracts ONLY the payload; returns the string and the
    next offset. -/
private
def readStringAt (bytes : Bytes) (off : Nat) : Option (String × Nat) := do
  if off ≥ bytes.size then none
  else
    let huff := bytes[off]! &&& 0x80 != 0
    match parseIntAt 7 bytes off with
    | none => none
    | some (len, off1) =>
      if off1 + len > bytes.size then none
      else
        let payload := bytes.extract off1 (off1 + len)
        if huff then
          match huffmanDecodeBytes payload with
          | none => none
          | some plain => some (String.fromUTF8! plain, off1 + len)
        else some (bytesToString payload, off1 + len)

/-- Read a header name at `off`: an index (nonzero prefix → name from the table) or a
    following string literal (zero prefix). -/
private
def readNameAt
    (updatedTable : dyn_table)
    (prefixBits : Nat)
    (bytes : Bytes)
    (off : Nat)
    : Option (String × Nat) := do
  match parseIntAt prefixBits bytes off with
  | none => none
  | some (idx, off1) =>
    if idx == 0 then readStringAt bytes off1
    else
      match updatedTable.lookup idx with
      | some entry => some (entry.name, off1)
      | none => none

/-- Decode one full header block, threading the dynamic table and a byte OFFSET into
    `bs` — so no per-header tail `extract`, only each payload is copied. Returns the
    ordered headers and the table advanced by any insertions / size updates. -/
partial
def decode (updatedTable : dyn_table) (bytes : Bytes) : Option (List HpackEntry × dyn_table) :=
  decodeEntries updatedTable 0 #[]
  where
    decodeEntries (updatedTable : dyn_table) (off : Nat) (result : Array HpackEntry) :
        Option (List HpackEntry × dyn_table) :=
      if off ≥ bytes.size then some (result.toList, updatedTable)
      else
        let firstByte := bytes[off]!
        if firstByte &&& 0x80 != 0 then
          -- §6.1 Indexed
          match parseIntAt 7 bytes off with
          | none => none
          | some (idx, off1) => match updatedTable.lookup idx with
            | some entry => decodeEntries updatedTable off1 (result.push entry)
            | none => none
        else if firstByte &&& 0x40 != 0 then
          -- §6.2.1 Literal with incremental indexing
          match readNameAt updatedTable 6 bytes off with
          | none => none
          | some (name, off1) => match readStringAt bytes off1 with
            | none => none
            | some (value, off2) =>
              let entry : HpackEntry := ⟨name, value⟩
              decodeEntries (updatedTable.insert entry) off2 (result.push entry)
        else if firstByte &&& 0x20 != 0 then
          -- §6.3 Dynamic table size update (no header emitted)
          match parseIntAt 5 bytes off with
          | none => none
          | some (cap, off1) => decodeEntries (updatedTable.setCapacity cap) off1 result
        else
          -- §6.2.2 / §6.2.3 Literal without / never indexed (4-bit prefix)
          match readNameAt updatedTable 4 bytes off with
          | none => none
          | some (name, off1) => match readStringAt bytes off1 with
            | none => none
            | some (value, off2) => decodeEntries updatedTable off2 (result.push ⟨name, value⟩)

-- ═══════════════════════════════════════════════════════════════════════════════
--  ENCODE — stateless literal-without-indexing (§6.2.2), plaintext strings
-- ═══════════════════════════════════════════════════════════════════════════════

open Continuity.Codec.Wire.HpackInt (encodeInt)

/-- Append a plaintext string literal (no huffman): 7-bit length prefix + octets,
    written straight into `buf` — no intermediate `List`→`Array`→`ByteArray` per
    string, just `push` the length octets and bulk-`append` the UTF-8. -/
private
def encStringInto (buf : ByteArray) (state : String) : ByteArray :=
  let utf8Bytes := state.toUTF8
  ((encodeInt utf8Bytes.size 7).foldl (fun buffer value => buffer.push value.toUInt8) buf)
      ++ utf8Bytes

/-- Append one header as literal-without-indexing with a literal name: a `0x00`
    representation byte, then the name and value string literals. -/
private
def encodeHeaderInto (buf : ByteArray) (name value : String) : ByteArray :=
  encStringInto (encStringInto (buf.push 0x00) name) value

/-- Encode a full header block. Stateless (the encoder never touches a dynamic table),
    and threads ONE growing `ByteArray`: `push`/`append` on the uniquely-owned buffer,
    so no per-header intermediate allocation and no quadratic `result ++ …` recopy. -/
def encode (headers : List (String × String)) : Bytes :=
  headers.foldl (fun buf (n, v) => encodeHeaderInto buf n v) ByteArray.empty

-- ═══════════════════════════════════════════════════════════════════════════════
--  RFC 7541 Appendix C wire vectors — the decode oracle
-- ═══════════════════════════════════════════════════════════════════════════════

private
def bytes (length : List Nat) : Bytes := ⟨(length.map (·.toUInt8)).toArray⟩

/-- The four request pseudo-headers C.3.1 / C.4.1 decode to. -/
private
def expectedReq : List (String × String) :=
  [(":method", "GET"), (":scheme", "http"), (":path", "/"), (":authority", "www.example.com")]

private
def decodedNames
    (result : Option (List HpackEntry × dyn_table))
    : Option (List (String × String)) :=
  result.map (fun (hs, _) => hs.map (fun entry => (entry.name, entry.value)))

/-- C.3.1 — plaintext first request: indexed 2/6/4 + literal-incremental
    `:authority`. Decodes to the four pseudo-headers, and inserts one dynamic
    entry (`:authority: www.example.com`, cost 57). -/
theorem decode_c31
        : decodedNames
          (decode
            {}
            (bytes
              [0x82, 0x86, 0x84, 0x41, 0x0f, 0x77, 0x77, 0x77, 0x2e, 0x65, 0x78, 0x61, 0x6d, 0x70,
                0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]))
            = some expectedReq := by native_decide

/-- The C.3.1 dynamic table ends with exactly the one inserted entry. -/
theorem decode_c31_table
        : ((decode
          {}
          (bytes
            [0x82, 0x86, 0x84, 0x41, 0x0f, 0x77, 0x77, 0x77, 0x2e, 0x65, 0x78, 0x61, 0x6d, 0x70,
              0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d])).map
          (fun (_, updatedTable) => (updatedTable.entries.size, updatedTable.size)))
            = some (1, 57) := by native_decide

/-- C.4.1 — the SAME request huffman-encoded (`8c` = huffman, len 12). Exercises
    huffman string decode inside the block. -/
theorem decode_c41_huffman
        : decodedNames
          (decode
            {}
            (bytes
              [0x82, 0x86, 0x84, 0x41, 0x8c, 0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab,
                0x90, 0xf4, 0xff]))
            = some expectedReq := by native_decide

/-- Encode → decode round-trips a response header set (our stateless literal
    form decodes back through the general decoder). -/
theorem encode_roundtrip
        : decodedNames
          (decode
            {}
            (encode [(":status", "200"), ("content-type", "text/plain"), ("content-length", "5")]))
            = some [(":status", "200"), ("content-type", "text/plain"), ("content-length", "5")] := by
  native_decide

end Continuity.Codec.Wire.Hpack.Block
