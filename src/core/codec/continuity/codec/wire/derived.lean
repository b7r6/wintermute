import continuity.codec.core.box
import continuity.codec.core.basic
import continuity.codec.core.bytes
import continuity.codec.core.varint
import continuity.codec.core.u_32_be
import continuity.codec.wire.nix.padded
import continuity.codec.wire.evm
import continuity.codec.core.proto

open Continuity.Codec.Core
open Continuity.Codec.Core
open Continuity.Codec.Core.Varint
open Continuity.Codec.Wire.EVM

namespace Continuity.Codec.Wire.Derived
open Continuity.Codec.Core.Proto
open Continuity.Codec.Core.Bytes
open Continuity.Codec.Wire.Nix.Padded

-- ════════════════════════════════════════════════════════════════════════════
-- CAS BLOB: hash + content
-- The fundamental content-addressed storage unit.
-- ════════════════════════════════════════════════════════════════════════════

structure casblob where
  hash    : fixed_bytes 32 -- SHA-256 of content
  content : len_prefixed -- the actual data

def casBlob : Box casblob :=
  isoBox
    (seq bytes32 lenPrefixed)
    (fun (h, c) => ⟨h, c⟩)
    (fun byte => (byte.hash, byte.content))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- HYBRID SIGNATURE: ed25519 (64B) + ML-DSA (variable)
-- Post-quantum hybrid. Fixed classical + variable PQ.
-- ════════════════════════════════════════════════════════════════════════════

structure hybrid_sig where
  ed25519 : fixed_bytes 64 -- classical signature
  mlDsa   : len_prefixed -- ML-DSA-65 signature (~3309 bytes)

def hybridSig : Box hybrid_sig :=
  isoBox
    (seq bytes64 lenPrefixed)
    (fun (e, m) => ⟨e, m⟩)
    (fun sample => (sample.ed25519, sample.mlDsa))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- VOUCH ENTRY: identity + content + timestamp + signature
-- One link in the vouch chain.
-- ════════════════════════════════════════════════════════════════════════════

structure vouch_entry where
  signerIdentity : fixed_bytes 32 -- hash of signer's hybrid public key
  contentHash    : fixed_bytes 32 -- what's being vouched for
  timestamp      : fixed_bytes 8  -- u64le unix timestamp
  signature      : fixed_bytes 64 -- ed25519 signature of (identity ++ content ++ timestamp)

def vouchEntry : Box vouch_entry :=
  isoBox
    (seq bytes32 (seq bytes32 (seq (fixedBytes 8) bytes64)))
    (fun (id, ch, ts, sig) => ⟨id, ch, ts, sig⟩)
    (fun value => (value.signerIdentity, value.contentHash, value.timestamp, value.signature))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- VOUCH CHAIN: Merkle root + count + entries
-- The full chain is content-addressed. This is the envelope.
-- ════════════════════════════════════════════════════════════════════════════

structure vouch_chain_header where
  merkleRoot : fixed_bytes 32 -- root of Merkle tree over entries
  entryCount : UInt64 -- number of entries (for pre-allocation)

def vouchChainHeader : Box vouch_chain_header :=
  isoBox
    (seq bytes32 u64le)
    (fun (r, n) => ⟨r, n⟩)
    (fun boundProof => (boundProof.merkleRoot, boundProof.entryCount))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- HYBRID PUBLIC KEY: ed25519 (32B) + ML-DSA public key (variable)
-- ════════════════════════════════════════════════════════════════════════════

structure hybrid_pub_key where
  ed25519 : fixed_bytes 32 -- classical public key
  mlDsa   : len_prefixed -- ML-DSA-65 public key (~1952 bytes)

def hybridPubKey : Box hybrid_pub_key :=
  isoBox
    (seq bytes32 lenPrefixed)
    (fun (e, m) => ⟨e, m⟩)
    (fun kdx => (kdx.ed25519, kdx.mlDsa))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- CAPABILITY CERT (full): identity + scope + timestamps + hybrid sig
-- This is the production version of the sketch SSPCert.
-- ════════════════════════════════════════════════════════════════════════════

structure CapabilityCert where
  version     : UInt8          -- protocol version
  identity    : fixed_bytes 32 -- hash of issuer's hybrid public key
  scope       : len_prefixed   -- capability scope (serialized authority)
  issuedAt    : fixed_bytes 8  -- u64le timestamp
  expiresAt   : fixed_bytes 8  -- u64le timestamp
  contentHash : fixed_bytes 32 -- CAS reference to attested content
  vouchRoot   : fixed_bytes 32 -- Merkle root of vouch chain
  signature   : hybrid_sig -- post-quantum hybrid signature

def capabilityCert : Box CapabilityCert :=
  isoBox
    (seq
      u8
      (seq
        bytes32
        (seq
          lenPrefixed
          (seq (fixedBytes 8) (seq (fixedBytes 8) (seq bytes32 (seq bytes32 hybridSig)))))))
    (fun (v, id, scope, iss, exp, ch, vr, sig) => ⟨v, id, scope, iss, exp, ch, vr, sig⟩)
    (fun certificate =>
      ( certificate.version,
        certificate.identity,
        certificate.scope,
        certificate.issuedAt,
        certificate.expiresAt,
        certificate.contentHash,
        certificate.vouchRoot,
        certificate.signature ))
    (fun _ => rfl)
    (fun ⟨_, _, _, _, _, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- PROTOBUF FIELD: tag (varint) + value (wire-type dependent)
-- Wire type 0 = varint, wire type 2 = length-delimited
-- ════════════════════════════════════════════════════════════════════════════

structure proto_field_varint where
  tag   : UInt64 -- (field_number << 3) | wire_type
  value : UInt64

def protoFieldVarint : Box proto_field_varint :=
  isoBox
    (seq varint varint)
    (fun (t, v) => ⟨t, v⟩)
    (fun field => (field.tag, field.value))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

structure proto_field_bytes where
  tag   : UInt64
  value : proto_bytes

def protoFieldBytes : Box proto_field_bytes :=
  isoBox
    (seq varint protoBytes)
    (fun (t, v) => ⟨t, v⟩)
    (fun field => (field.tag, field.value))
    (fun _ => rfl)
    (fun ⟨_, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- NIX STORE PATH INFO: path + deriver + narHash + narSize + refs
-- Simplified — real Nix has more fields but this covers the core.
-- ════════════════════════════════════════════════════════════════════════════

structure nix_path_info where
  storePath : NixString -- /nix/store/hash-name
  deriver   : NixString -- the derivation that built it
  narHash   : NixString -- hash of the NAR archive
  narSize   : UInt64 -- size in bytes

def nixPathInfo : Box nix_path_info :=
  isoBox
    (seq nixString (seq nixString (seq nixString u64le)))
    (fun (p, d, h, s) => ⟨p, d, h, s⟩)
    (fun idx => (idx.storePath, idx.deriver, idx.narHash, idx.narSize))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- EVM EVENT LOG: topics + data
-- Solidity events emit up to 4 indexed topics + unindexed data.
-- ════════════════════════════════════════════════════════════════════════════

-- AttestEvent(bytes32 indexed contentHash, bytes32 indexed signer, uint64 timestamp)
structure attest_event where
  topic0      : Word -- keccak256("Attest(bytes32,bytes32,uint64)")
  contentHash : Word -- indexed
  signer      : Word -- indexed
  timestamp   : Word -- in data section (ABI-encoded)

def attestEvent : Box attest_event :=
  isoBox
    (seq word (seq word (seq word word)))
    (fun (t0, ch, s, ts) => ⟨t0, ch, s, ts⟩)
    (fun entry => (entry.topic0, entry.contentHash, entry.signer, entry.timestamp))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- SSP HANDSHAKE INIT: version + ephemeral key + signature
-- First message in the Straylight Shell Protocol handshake.
-- ════════════════════════════════════════════════════════════════════════════

structure sspinit where
  version      : fixed_bytes 4  -- protocol version bytes
  ephemeralPub : fixed_bytes 32 -- X25519 ephemeral public key
  identitySig  : fixed_bytes 64 -- ed25519 signature over ephemeralPub

def sspInit : Box sspinit :=
  isoBox
    (seq (fixedBytes 4) (seq bytes32 bytes64))
    (fun (v, e, s) => ⟨v, e, s⟩)
    (fun boundProof => (boundProof.version, boundProof.ephemeralPub, boundProof.identitySig))
    (fun _ => rfl)
    (fun ⟨_, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- SSP HANDSHAKE RESPONSE: ephemeral + encrypted payload + tag
-- ════════════════════════════════════════════════════════════════════════════

structure sspresponse where
  ephemeralPub : fixed_bytes 32 -- X25519 ephemeral
  nonce        : fixed_bytes 12 -- ChaCha20-Poly1305 nonce
  encPayload   : len_prefixed   -- encrypted certificate + vouch chain
  tag          : fixed_bytes 16 -- Poly1305 authentication tag

def sspResponse : Box sspresponse :=
  isoBox
    (seq bytes32 (seq (fixedBytes 12) (seq lenPrefixed (fixedBytes 16))))
    (fun (e, n, p, t) => ⟨e, n, p, t⟩)
    (fun request => (request.ephemeralPub, request.nonce, request.encPayload, request.tag))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- SIGIL INFERENCE REQUEST: model hash + input tokens + config
-- TensorRT-LLM inference protocol.
-- ════════════════════════════════════════════════════════════════════════════

structure sigil_request where
  modelHash   : fixed_bytes 32 -- content-addressed model identifier
  maxTokens   : UInt64         -- generation limit
  temperature : UInt64         -- fixed-point temperature (×1000)
  inputTokens : len_prefixed -- serialized token IDs

def sigilRequest : Box sigil_request :=
  isoBox
    (seq bytes32 (seq u64le (seq u64le lenPrefixed)))
    (fun (m, mt, t, inp) => ⟨m, mt, t, inp⟩)
    (fun request => (request.modelHash, request.maxTokens, request.temperature, request.inputTokens))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- SIGIL INFERENCE RESPONSE: output tokens + timing + attestation ref
-- ════════════════════════════════════════════════════════════════════════════

structure sigil_response where
  requestHash  : fixed_bytes 32 -- hash of the request (for correlation)
  outputTokens : len_prefixed   -- generated token IDs
  prefillMs    : UInt64         -- prefill latency
  decodeMs     : UInt64         -- decode latency
  attestRef    : fixed_bytes 32 -- CAS hash of the attestation for this output

def sigilResponse : Box sigil_response :=
  isoBox
    (seq bytes32 (seq lenPrefixed (seq u64le (seq u64le bytes32))))
    (fun (rh, out, pf, dc, att) => ⟨rh, out, pf, dc, att⟩)
    (fun request =>
      (
        request.requestHash,
        request.outputTokens, request.prefillMs, request.decodeMs, request.attestRef
      ))
    (fun _ => rfl)
    (fun ⟨_, _, _, _, _⟩ => rfl)

-- gRPC frame — zero sorry (compositional from u32be + lenPrefixed)
structure GrpcFrame where
  compressed : UInt8
  lengthBE   : BitVec 32
  payload    : len_prefixed

def grpcFrame : Box GrpcFrame :=
  isoBox
    (seq u8 (seq Continuity.Codec.Core.U32BE.u32beBitVec lenPrefixed))
    (fun (c, l, p) => ⟨c, l, p⟩)
    (fun field => (field.compressed, field.lengthBE, field.payload))
    (fun _ => rfl)
    (fun ⟨_, _, _⟩ => rfl)

end Continuity.Codec.Wire.Derived
