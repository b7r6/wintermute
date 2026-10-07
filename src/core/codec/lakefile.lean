import Lake
open Lake DSL

package «continuity-codec» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «continuity-base» from "../base"
require «stdlibex» from "../../stdlibex"

@[default_target]
lean_lib «ContinuityCodec» where
  srcDir := "."
  globs := #[
    .one `continuity.codec,
    .andSubmodules `continuity.codec.core,
    .andSubmodules `continuity.codec.wire
  ]
