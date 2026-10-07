import Lake
open Lake DSL

package «continuity-trust» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «continuity-base» from "../base"

@[default_target]
lean_lib «ContinuityTrust» where
  srcDir := "."
  globs := #[.andSubmodules `continuity.trust]
