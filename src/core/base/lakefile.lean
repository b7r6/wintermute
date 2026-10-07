import Lake
open Lake DSL

package «continuity-base» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "fa08db58b30eb033edcdab331bba000827f9f785"

@[default_target]
lean_lib «ContinuityBase» where
  srcDir := "."
  globs := #[
    .andSubmodules `continuity.crypto,
    .submodules `continuity.data,
    .andSubmodules `continuity.coeffect,
    .submodules `continuity.verify,
    .one `continuity.witness
  ]
