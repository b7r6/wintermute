/-
  Continuity.Codec.Wire.Nix.Daemon.Nar - NAR (Nix ARchive) format codec
-/

import continuity.codec.wire.nix.daemon

-- ═══════════════════════════════════════════════════════════════════════════════
-- NAR (Nix ARchive) FORMAT
-- Deterministic archive format for store paths
-- ═══════════════════════════════════════════════════════════════════════════════

namespace Continuity.Codec.Wire.Nix.Nar

open Continuity.Codec.Core Continuity.Codec.Wire.Nix.Daemon

/-- NAR magic string -/
def NAR_MAGIC : String := "nix-archive-1"

/-- NAR node type -/
inductive NarNodeType where
  | regular   -- Regular file
  | directory -- Directory
  | symlink   -- Symbolic link
  deriving Repr, DecidableEq

/-- Convert string to NarNodeType -/
def NarNodeType.fromString : String → Option NarNodeType
  | "regular"   => some .regular
  | "directory" => some .directory
  | "symlink"   => some .symlink
  | _           => none

/-- Convert NarNodeType to string -/
def NarNodeType.toString : NarNodeType → String
  | .regular   => "regular"
  | .directory => "directory"
  | .symlink   => "symlink"

-- NAR node and entry (mutually recursive)
mutual
  inductive NarNode where
    | file : (executable : Bool) → (contents : Bytes) → NarNode
    | dir : (entries : Array NarEntry) → NarNode
    | link : (target : String) → NarNode

  structure NarEntry where
    name : String
    node : NarNode
end

-- Derive instances after mutual block
deriving instance Repr for NarNode
deriving instance Repr for NarEntry

-- Manual Inhabited instance since NarEntry contains NarNode
instance : Inhabited NarNode where
  default := .link ""

instance : Inhabited NarEntry where
  default := { name := "", node := default }

/-- Predicate: array of entries is sorted by name (strictly ascending) -/
def NarEntries.IsSorted (entries : Array NarEntry) : Prop :=
  ∀ i j : Nat, i < j → j < entries.size → entries[i]!.name < entries[j]!.name

/-- NAR archive -/
structure Nar where
  root : NarNode
  deriving Repr

/-- sizeOf e.node < sizeOf e for NarEntry -/
theorem NarEntry.sizeOf_node_lt (element : NarEntry) : sizeOf element.node < sizeOf element := by
  cases element with
  | mk name node =>
    simp only [NarEntry.mk.sizeOf_spec]
    omega

/-- A wellformed NarNode has sorted directory entries (recursively) -/
def NarNode.WellFormed : NarNode → Prop
  | .file _ _    => True
  | .link _      => True
  | .dir entries => NarEntries.IsSorted entries ∧ ∀ e ∈ entries, e.node.WellFormed
  termination_by node => sizeOf node
  decreasing_by
    simp_wf
    rename_i entryMembership
    exact Nat.lt_trans
      (Nat.lt_trans (NarEntry.sizeOf_node_lt _) (Array.sizeOf_lt_of_mem entryMembership))
          (by omega : _ < 1 + _)

/-- A wellformed NAR archive -/
structure well_formed_nar where
  nar        : Nar
  wellformed : nar.root.WellFormed

-- ═══════════════════════════════════════════════════════════════════════════════
-- NAR PARSING (Streaming-compatible)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- NAR parse error reasons -/
inductive nar_error where
  | invalidMagic : String → nar_error
  | invalidNodeType : String → nar_error
  | unexpectedToken : String → String → nar_error -- expected, got
  | truncated : Nat → nar_error -- bytes needed
  | nameTooLarge : Nat → nar_error
  | contentsTooLarge : Nat → nar_error
  | unsortedEntry : String → String → nar_error -- prev, current (must be sorted)
  | duplicateEntry : String → nar_error
  | recursionTooDeep : Nat → nar_error
  deriving Repr, DecidableEq

/-- NAR strict parse result -/
inductive nar_parse_result (Value : Type) where
  | ok : Value → Bytes → nar_parse_result Value
  | incomplete : Nat → nar_parse_result Value
  | error : nar_error → nar_parse_result Value
  deriving Repr

namespace nar_parse_result

def bind
    {Value ResultValue : Type}
    (result : nar_parse_result Value)
    (function : Value → Bytes → nar_parse_result ResultValue)
    : nar_parse_result ResultValue :=
  match result with
  | ok value rest    => function value rest
  | incomplete count => incomplete count
  | error entry      => error entry

def map
    {Value ResultValue : Type}
    (function : Value → ResultValue)
    : nar_parse_result Value → nar_parse_result ResultValue
  | ok value rest    => ok (function value) rest
  | incomplete count => incomplete count
  | error entry      => error entry

end nar_parse_result

/-- Maximum recursion depth (prevents stack overflow on malicious input) -/
def maxNarDepth : Nat := 256

/-- Maximum entry name length -/
def maxEntryNameLen : Nat := 4096

/-- Maximum file size (1 GB) -/
def maxFileSize : Nat := 1024 * 1024 * 1024

-- ═══════════════════════════════════════════════════════════════════════════════
-- NAR SERIALIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Serialize a string with padding -/
def serializeNarString (state : String) : Bytes :=
  let data := state.toUTF8
  let len := data.size
  let padLen := padSize len
  u64le.serialize len.toUInt64 ++ data ++ zeroPad padLen

/-- Serialize NAR node (mutual recursion via fuel) -/
partial
def serializeNarNode : NarNode → Bytes
  | .file exec contents =>
    serializeNarString "(" ++ serializeNarString "type" ++ serializeNarString "regular"
        ++ (if exec then serializeNarString "executable" ++ serializeNarString "" else Bytes.empty)
        ++ serializeNarString "contents"
        ++ (let len := contents.size
        let padLen := padSize len
        u64le.serialize len.toUInt64 ++ contents ++ zeroPad padLen)
        ++ serializeNarString ")"
  | .dir entries =>
    serializeNarString "(" ++ serializeNarString "type" ++ serializeNarString "directory"
        ++ entries.foldl
          (fun result entry =>
            result ++ serializeNarString "entry" ++ serializeNarString "("
                ++ serializeNarString "name"
                ++ serializeNarString entry.name
                ++ serializeNarString "node"
                ++ serializeNarNode entry.node
                ++ serializeNarString ")")
          Bytes.empty
        ++ serializeNarString ")"
  | .link target =>
    serializeNarString "(" ++ serializeNarString "type" ++ serializeNarString "symlink"
        ++ serializeNarString "target"
        ++ serializeNarString target
        ++ serializeNarString ")"

/-- Serialize complete NAR archive -/
def serializeNar (nar : Nar) : Bytes := serializeNarString NAR_MAGIC ++ serializeNarNode nar.root

-- ═══════════════════════════════════════════════════════════════════════════════
-- NAR DETERMINISM THEOREM
-- ═══════════════════════════════════════════════════════════════════════════════

/--
THEOREM: NAR serialization is deterministic.
Same NarNode always produces identical bytes.
-/
theorem nar_serialize_deterministic
        (leftCount rightCount : Nar)
        : leftCount = rightCount → serializeNar leftCount = serializeNar rightCount := by
  intro narEquation
  rw [narEquation]

/--
THEOREM: Wellformed NAR directory entries are sorted.
This follows from the WellFormed predicate - sortedness is part of wellformedness.
-/
theorem nar_entries_sorted_of_wellformed
        (node : NarNode)
        (evidence : node.WellFormed)
        (entries : Array NarEntry)
        (hdir : node = .dir entries)
        (index nextIndex : Nat)
        : index < nextIndex
            → nextIndex < entries.size
            → entries[index]!.name < entries[nextIndex]!.name := by
  intro hij hjsize

  -- Split the remaining proof cases.
  subst hdir

  -- Simplify the remaining goal.
  simp only [NarNode.WellFormed] at evidence

  -- Close the remaining goal.
  exact evidence.1 index nextIndex hij hjsize

end Continuity.Codec.Wire.Nix.Nar
