/-
  Continuity.Machine.Protocol — protocol modules that fuse a wire format with
  machine (and, for SSP, trust) logic. Relocated here from Codec.Wire because
  they depend on the Machine engine, keeping the codec layer pure.
-/
import continuity.machine.protocol.sigil
import continuity.machine.protocol.ssp
import continuity.machine.protocol.nix_handshake
