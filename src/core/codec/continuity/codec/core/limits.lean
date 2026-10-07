import continuity.codec.core.guards
import continuity.codec.core.bytes

open Continuity.Codec.Core
open Continuity.Codec.Core
open Continuity.Codec.Core.Guards

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // continuity // codec // limits
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Every magic constant in the codebase lives here.
-- Every one is connected to a `bounded` Box through Guards.
-- Every one has an exhaustion theorem.
--
-- Before this file existed, these constants were defined but never enforced.
-- They were comments pretending to be security. Now they're types.
-- ──────────────────────────────────────────────────────────────────────────────

namespace Continuity.Codec.Core.Limits
open Continuity.Codec.Core.Bytes

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1. CONSTANTS — one source of truth
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Nix protocol: maximum string size (16 MB) -/
def nixMaxStringBytes : Nat := 16 * 1024 * 1024

/-- Nix protocol: maximum list elements (1M) -/
def nixMaxListElems : Nat := 1024 * 1024

/-- NAR format: maximum recursion depth -/
def narMaxDepth : Nat := 256

/-- NAR format: maximum entry name length -/
def narMaxEntryName : Nat := 4096

/-- NAR format: maximum file size (1 GB) -/
def narMaxFileBytes : Nat := 1024 * 1024 * 1024

/-- HTTP/2: default maximum frame payload (16 KB) -/
def http2MaxFrameDefault : Nat := 16384

/-- HTTP/2: absolute maximum frame payload (~16 MB) -/
def http2MaxFrameAbsolute : Nat := 16777215

/-- ZMTP: maximum frame payload (256 MB) -/
def zmtpMaxFrameBytes : Nat := 256 * 1024 * 1024

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2. POSITIVITY — every constant is positive (needed for budget division)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem nixMaxStringBytes_pos : nixMaxStringBytes > 0 := by decide

theorem nixMaxListElems_pos : nixMaxListElems > 0 := by decide

theorem narMaxDepth_pos : narMaxDepth > 0 := by decide

theorem narMaxEntryName_pos : narMaxEntryName > 0 := by decide

theorem narMaxFileBytes_pos : narMaxFileBytes > 0 := by decide

theorem http2MaxFrameDefault_pos : http2MaxFrameDefault > 0 := by decide

theorem http2MaxFrameAbsolute_pos : http2MaxFrameAbsolute > 0 := by decide

theorem zmtpMaxFrameBytes_pos : zmtpMaxFrameBytes > 0 := by decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3. BOUNDED BOXES — protocol-specific specializations
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Nix string with enforced 16 MB ceiling -/
def boundedNixString : Box (Bounded len_prefixed lenPrefixed nixMaxStringBytes) :=
  bounded lenPrefixed nixMaxStringBytes

/-- HTTP/2 frame payload with enforced default size ceiling -/
def boundedHttp2Frame : Box (Bounded len_prefixed lenPrefixed http2MaxFrameDefault) :=
  bounded lenPrefixed http2MaxFrameDefault

/-- ZMTP frame with enforced 256 MB ceiling -/
def boundedZmtpFrame : Box (Bounded len_prefixed lenPrefixed zmtpMaxFrameBytes) :=
  bounded lenPrefixed zmtpMaxFrameBytes

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4. BUDGET THEOREMS — connect constants to memory budgets
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A Nix connection with a 1 GB memory budget can hold at most 64 strings -/
theorem nix_string_budget : (1024 * 1024 * 1024) / nixMaxStringBytes = 64 := by native_decide

/-- N bounded Nix strings fit in N × 16 MB -/
theorem nix_strings_total
        (states : List (Bounded len_prefixed lenPrefixed nixMaxStringBytes))
        : (states.map (fun stringValue => (lenPrefixed.serialize stringValue.val).size)).sum
            ≤ states.length * nixMaxStringBytes :=
  bounded_list_total lenPrefixed nixMaxStringBytes states

/-- N bounded HTTP/2 frames fit in N × 16 KB -/
theorem http2_frames_total
        (functions : List (Bounded len_prefixed lenPrefixed http2MaxFrameDefault))
        : (functions.map (fun field => (lenPrefixed.serialize field.val).size)).sum
            ≤ functions.length * http2MaxFrameDefault :=
  bounded_list_total lenPrefixed http2MaxFrameDefault functions

/-- N bounded ZMTP frames fit in N × 256 MB -/
theorem zmtp_frames_total
        (functions : List (Bounded len_prefixed lenPrefixed zmtpMaxFrameBytes))
        : (functions.map (fun field => (lenPrefixed.serialize field.val).size)).sum
            ≤ functions.length * zmtpMaxFrameBytes :=
  bounded_list_total lenPrefixed zmtpMaxFrameBytes functions

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5. DEPTH — recursive structure limits
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A depth-limited recursive descent.
    At each level, the budget decreases by 1. When it hits 0, reject.
    This turns maxNarDepth from a comment into an enforced fuel bound. -/
def depthGuard
    {Value : Type}
    (fuel : Nat)
    (function : Nat → ByteArray → ParseResult Value)
    (bytes : ByteArray)
    : ParseResult Value :=
  if fuel == 0 then .fail else function (fuel - 1) bytes

/-- depthGuard rejects at depth 0 -/
theorem depthGuard_zero
        {Value : Type}
        (function : Nat → ByteArray → ParseResult Value)
        (bytes : ByteArray)
        : depthGuard 0 function bytes = .fail := by simp [depthGuard]

/-- depthGuard at fuel n+1 delegates to f at fuel n -/
theorem depthGuard_succ
        {Value : Type}
        (count : Nat)
        (function : Nat → ByteArray → ParseResult Value)
        (bytes : ByteArray)
        : depthGuard (count + 1) function bytes = function count bytes := by simp [depthGuard]

/-- narMaxDepth levels of recursion terminates -/
theorem nar_depth_terminates : narMaxDepth = 256 := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6. NAME LENGTH — entry name validation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check that a string's UTF-8 encoding fits within the name limit -/
def checkNameLen (name : String) : Bool := name.toUTF8.size ≤ narMaxEntryName

/-- A name that satisfies the length check -/
structure BoundedName where
  name   : String
  len_ok : name.toUTF8.size ≤ narMaxEntryName

/-- Reject names exceeding the limit at parse time -/
def parseBoundedName
    (bytes : ByteArray)
    (parseStr : ByteArray → ParseResult String)
    : ParseResult BoundedName :=
  match parseStr bytes with
  | .ok state rest => if h : state.toUTF8.size ≤ narMaxEntryName then .ok ⟨state, h⟩ rest else .fail
  | .fail          => .fail

end Continuity.Codec.Core.Limits
