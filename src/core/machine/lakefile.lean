import Lake
open Lake DSL

package «continuity-machine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «continuity-base» from "../base"
require «continuity-codec» from "../codec"
require «continuity-trust» from "../trust"

@[default_target]
lean_lib «ContinuityMachine» where
  srcDir := "."
  globs := #[
    .one `continuity.machine,
    .one `continuity.machine.abstract,
    .one `continuity.machine.core,
    -- `Continuity.Machine.EVRing.*` + `Continuity.Machine.Grade` (the coeffect
    -- killshots over the EVRing machines) moved to the top-level `evring/`
    -- package as `EVRing.Machine.*` — one io_uring unit, one home.
    .one `continuity.machine.mesh,
    .submodules `continuity.machine.nix,
    .andSubmodules `continuity.machine.protocol,
    .one `continuity.machine.sigil,
    .one `continuity.machine.stack
  ]
