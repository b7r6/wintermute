import continuity.codec.core.box
import continuity.codec.core.basic
import continuity.codec.core.bytes

namespace Continuity.Codec.Wire.Sketch
open Continuity.Codec.Core.Bytes

open Continuity.Codec.Core
open Continuity.Codec.Core

-- ════════════════════════════════════════════════════════════════════════════
-- DOOR 1: CREDENTIAL CODEC
-- seq is right-nested: seq A (seq B C) : Box (A × (B × C))
-- ════════════════════════════════════════════════════════════════════════════

structure Credential where
  service  : len_prefixed
  username : len_prefixed
  secret   : len_prefixed

def credential : Box Credential :=
  isoBox
    (seq lenPrefixed (seq lenPrefixed lenPrefixed))
    (fun (s, u, k) => ⟨s, u, k⟩)
    (fun certificate => (certificate.service, certificate.username, certificate.secret))
    (fun _ => rfl)
    (fun ⟨_, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- DOOR 2: EVM ABI STATIC ATTESTATION
-- Four bytes32 words. Pure seq composition.
-- ════════════════════════════════════════════════════════════════════════════

structure abiattestation where
  contentHash : fixed_bytes 32
  signerAddr  : fixed_bytes 32 -- padded to 32 (ABI convention)
  timestamp   : fixed_bytes 32
  vouchRoot   : fixed_bytes 32

def abiAttestation : Box abiattestation :=
  isoBox
    (seq bytes32 (seq bytes32 (seq bytes32 bytes32)))
    (fun (h, a, t, v) => ⟨h, a, t, v⟩)
    (fun certificate =>
      (
        certificate.contentHash,
        certificate.signerAddr, certificate.timestamp, certificate.vouchRoot
      ))
    (fun _ => rfl)
    (fun ⟨_, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- DOOR 5: SSP CAPABILITY CERTIFICATE
-- Mixed fixed + variable fields.
-- ════════════════════════════════════════════════════════════════════════════

structure sspcert where
  identity   : fixed_bytes 32
  scope      : len_prefixed
  issuedAt   : fixed_bytes 8
  expiresAt  : fixed_bytes 8
  sigEd25519 : fixed_bytes 64
  sigMLDSA   : len_prefixed

def sspCert : Box sspcert :=
  isoBox
    (seq
      bytes32
      (seq lenPrefixed (seq (fixedBytes 8) (seq (fixedBytes 8) (seq bytes64 lenPrefixed)))))
    (fun (id, scope, issued, expires, sig1, sig2) => ⟨id, scope, issued, expires, sig1, sig2⟩)
    (fun certificate =>
      (
        certificate.identity,
        certificate.scope, certificate.issuedAt, certificate.expiresAt, certificate.sigEd25519, certificate.sigMLDSA
      ))
    (fun _ => rfl)
    (fun ⟨_, _, _, _, _, _⟩ => rfl)

-- ════════════════════════════════════════════════════════════════════════════
-- SCOREBOARD
-- ════════════════════════════════════════════════════════════════════════════

/-!
| Codec | Lines | Sorry | Status |
|-------|-------|-------|--------|
| credential | 6 | 0 | PROVEN (compositional) |
| abiAttestation | 6 | 0 | PROVEN (compositional) |
| sspCert | 10 | 0 | PROVEN (compositional) |

Three wire formats. All proven by composition from fixedBytes/lenPrefixed/seq/isoBox.
No new proof machinery needed. The combinator algebra does the work.

Remaining doors:
  Nix padded string — needs padding combinator (padSize + expectZeros)
  Protobuf varint   — needs recursive parse with termination bound
-/

end Continuity.Codec.Wire.Sketch
