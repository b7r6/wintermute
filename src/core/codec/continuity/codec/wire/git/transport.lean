/-
  Continuity.Codec.Wire.Git.Transport - Verified Git Smart HTTP Protocol

  Implements the client side of git-upload-pack for clone/fetch.

  Protocol flow:
  1. GET /info/refs?service=git-upload-pack  → ref advertisement
  2. POST /git-upload-pack                    → wants/haves negotiation
  3. Receive packfile (possibly with sideband)

  Uses Continuity.Codec.Core.Framing for pkt-line framing.
  Uses Continuity.Codec.Wire.Git.Pack for packfile parsing.
-/

import continuity.codec.wire.git.framing
import continuity.codec.wire.git.pack

namespace Continuity.Codec.Wire.Git.Transport

open Continuity.Codec.Core Continuity.Codec.Core.Framing Continuity.Codec.Wire.Git.Framing Continuity.Codec.Wire.Git.Pack

-- ═══════════════════════════════════════════════════════════════════════════════
-- REFERENCE ADVERTISEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A git reference (branch, tag, etc.) -/
structure Ref where
  oid  : String -- 40 hex chars (SHA-1) or 64 hex chars (SHA-256)
  name : String -- e.g., "refs/heads/main"
  deriving Repr, DecidableEq

/-- Reference advertisement from server -/
structure RefAdvertisement where
  refs         : List Ref
  capabilities : List Capability
  head         : Option String   -- symref HEAD target
  deriving Repr

/-- Parse reference advertisement line: "<oid> <refname>\0<caps>" or "<oid> <refname>" -/
def parseRefLine (state : String) : Option (Ref × List Capability) :=

  -- First line has capabilities after NUL
  let parts := state.splitOn "\x00"
  let refPart := parts.headD ""
  let caps :=
    match parts.tail? with
    | some (state :: _) => parseCapabilities state
    | _                 => []
  -- Split ref part: "<oid> <refname>"
  match refPart.splitOn " " with
  | [oid, name] => some (⟨oid, name⟩, caps)
  | _           => none

/-- Convert ByteArray to String (UTF-8, unchecked) -/
def bytesToString (bytes : Bytes) : String := String.fromUTF8! bytes

/-- Parse complete reference advertisement from frames -/
def parseRefAdvertisement (frames : List Frame) : Option RefAdvertisement :=
  match frames with
  | [] => some ⟨[], [], none⟩
  | first :: rest =>
    -- First frame might be "# service=git-upload-pack\n" header
    let payloadStr := bytesToString first.payload
    let dataFrames := if payloadStr.startsWith "#" then rest else frames
    -- Parse refs
    let parsed := dataFrames.filterMap fun frame =>
      let payloadText := bytesToString frame.payload
      parseRefLine payloadText.trimAsciiEnd.toString  -- remove trailing newline
    let refs := parsed.map Prod.fst
    let caps := match parsed.head? with
      | some (_, code) => code
      | none => []
    -- Extract HEAD symref from capabilities
    let head := caps.findSome? fun capability =>
      if capability.startsWith "symref=HEAD:" then some (capability.drop 12).toString
      else none
    some ⟨refs, caps, head⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- UPLOAD REQUEST (wants/haves)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Request to upload pack -/
structure UploadRequest where
  wants        : List String     -- OIDs we want
  haves        : List String     -- OIDs we have (for incremental fetch)
  capabilities : List Capability
  shallow      : List String     -- shallow boundaries
  deepen       : Option Nat      -- depth limit
  deriving Repr

/-- Enumerate a list with indices -/
def enumerate {Value : Type} (values : List Value) : List (Nat × Value) :=
  let rec enumerateItems (index : Nat) : List Value → List (Nat × Value)
    | [] => []
    | item :: items => (index, item) :: enumerateItems (index + 1) items
  enumerateItems 0 values

/-- Serialize upload request to pkt-lines -/
def serializeUploadRequest (req : UploadRequest) : List Frame :=
  let wantFrames :=
    (enumerate req.wants).map fun (idx, oid) =>
      let line :=
        if idx == 0 then
          s!"want {oid} {serializeCapabilities req.capabilities}\n"
        else
          s!"want {oid}\n"
      ⟨line.toUTF8⟩
  let haveFrames := req.haves.map fun oid => ⟨s!"have {oid}\n".toUTF8⟩
  let doneFrame : Frame := ⟨"done\n".toUTF8⟩
  wantFrames ++ [Frame.flush] ++ haveFrames ++ [doneFrame]

-- ═══════════════════════════════════════════════════════════════════════════════
-- UPLOAD RESPONSE (NAK/ACK + packfile)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Server response type -/
inductive ServerResponse where
  | nak -- No common commits
  | ack (oid : String) -- Common commit found
  | shallow (oid : String) -- Shallow boundary
  | unshallow (oid : String) -- Unshallow
  deriving Repr, DecidableEq

/-- Parse server response line -/
def parseServerResponse (input : String) : Option ServerResponse :=
  let responseText := input.trimAsciiEnd.toString
  if responseText == "NAK" then
    some .nak
  else if responseText.startsWith "ACK " then
    some (.ack (responseText.drop 4).toString)
  else if responseText.startsWith "shallow " then
    some (.shallow (responseText.drop 8).toString)
  else if responseText.startsWith "unshallow " then
    some (.unshallow (responseText.drop 10).toString)
  else
    none

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOCOL STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Client state for git fetch -/
inductive fetch_state where
  | init -- Initial state
  | awaitingRefs -- Sent info/refs request
  | receivedRefs (adv : RefAdvertisement) -- Got refs, deciding what to fetch
  | awaitingPack -- Sent upload request
  | receivingPack (received : Nat) -- Receiving packfile data
  | done (pack : List UInt8) -- Complete
  | error (msg : String) -- Error occurred
  deriving Repr

/-- Events from network -/
inductive fetch_event where
  | refFrames (frames : List Frame) -- Reference advertisement
  | packFrame (data : Bytes) -- Pack data (sideband channel 1)
  | progress (msg : String) -- Progress message (sideband channel 2)
  | errorMsg (msg : String) -- Error from server (sideband channel 3)
  | serverResponse (resp : ServerResponse) -- NAK/ACK
  | flush -- Flush packet
  | eof -- Connection closed
  deriving Repr

/-- Actions to send -/
inductive fetch_action where
  | httpGet (path : String) -- GET request
  | httpPost (path : String) (body : Bytes) -- POST request
  | close -- Close connection
  deriving Repr

/-- State transition -/
def fetchStep (state : fetch_state) (event : fetch_event) : fetch_state × List fetch_action :=
  match state, event with
  | .init, _ =>
    (.awaitingRefs, [.httpGet "/info/refs?service=git-upload-pack"])

  -- Dispatch the next state transition.
  | .awaitingRefs, .refFrames frames =>
    match parseRefAdvertisement frames with
    | some adv => (.receivedRefs adv, [])
    | none => (.error "Failed to parse ref advertisement", [.close])

  -- Dispatch the next state transition.
  | .receivedRefs adv, _ =>
    -- Caller should examine adv and call fetchStep with wants
    -- For now, auto-fetch HEAD
    match adv.refs.find? (·.name == "HEAD") with
    | some headRef =>
      let req : UploadRequest := {
        wants := [headRef.oid]
        haves := []
        capabilities := ["side-band-64k", "ofs-delta", "thin-pack"]
        shallow := []
        deepen := none
      }
      let frames := serializeUploadRequest req
      let body := serializeWithFlush gitLengthCodec frames
      (.awaitingPack, [.httpPost "/git-upload-pack" body])
    | none => (.error "No HEAD ref", [.close])

  -- Dispatch the next state transition.
  | .awaitingPack, .serverResponse .nak =>
    (.receivingPack 0, [])

  -- Dispatch the next state transition.
  | .awaitingPack, .serverResponse (.ack _) =>
    (.receivingPack 0, [])

  -- Dispatch the next state transition.
  | .receivingPack count, .packFrame data =>
    (.receivingPack (count + data.size), [])

  -- Dispatch the next state transition.
  | .receivingPack _, .eof =>
    (.done [], [.close])

  -- Dispatch the next state transition.
  | .receivingPack _, .progress _ =>
    -- Could log progress
    (state, [])

  -- Dispatch the next state transition.
  | _, .errorMsg msg =>
    (.error msg, [.close])

  -- Dispatch the next state transition.
  | state, _ => (state, [])

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMMON CAPABILITIES FOR CLONE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Default capabilities for efficient clone -/
def defaultCloneCapabilities : List Capability :=
  [
    "multi_ack_detailed",
    "side-band-64k",
    "ofs-delta",
    "thin-pack",
    "no-progress",
    "include-tag",
    "allow-tip-sha1-in-want",
    "allow-reachable-sha1-in-want"
  ]

/-- Capabilities for shallow clone -/
def shallowCloneCapabilities : List Capability :=
  defaultCloneCapabilities ++ ["shallow", "deepen-since", "deepen-not"]

-- ═══════════════════════════════════════════════════════════════════════════════
-- URL PARSING (minimal)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parsed git URL -/
structure GitUrl where
  scheme : String     -- "https" or "http"
  host   : String
  port   : Option Nat
  path   : String     -- e.g., "/owner/repo.git"
  deriving Repr

/-- Parse git URL (simplified) -/
def parseGitUrl (url : String) : Option GitUrl :=

  -- Handle https://host/path or http://host/path
  let parts := url.splitOn "://"
  match parts with
  | [scheme, rest] =>
    if scheme != "https" && scheme != "http" then
      none
    else
      match rest.splitOn "/" with
      | [] => none
      | [_] => none -- no path
      | hostPart :: pathParts =>
        let path := "/" ++ String.intercalate "/" pathParts
        -- Check for port in hostPart
        match hostPart.splitOn ":" with
        | [host] => some ⟨scheme, host, none, path⟩
        | [host, portStr] =>
          match portStr.toNat? with
          | some packet => some ⟨scheme, host, some packet, path⟩
          | none        => none
        | _ => none
  | _ => none

end Continuity.Codec.Wire.Git.Transport
