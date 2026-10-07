import Lake
open Lake DSL

/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               // APPS // WINTERMUTE // LAKEFILE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The hot-reload theme reconciler — desktop theming as a verified control
    loop instead of a rebuild-and-restart cycle.

      Wintermute.*   the library — the ono-sendai palette math (integer HSL,
                     211° hue lock), the two-axis theme vector (luminance ×
                     register), and the reconciler as a `Continuity.Machine`
                     `AbstractMachine` with its invariants PROVEN: generation
                     monotonicity, idempotence, convergence, and predicate
                     preservation (the hue lock survives every transition).
      wintermute     the executable — a stdlib-IO shell around the pure core:
                     state-file control plane (atomic rename), mtime watch
                     loop, live adapters (hyprctl / kitty / emacsclient /
                     nvim --remote) and the durable token-file rewrite that
                     Quickshell watches.

    The IO shell deliberately rides Lean stdlib for now; it ports onto EVRing
    once unix sockets / subprocess / writeFile land in the ring. The pure core
    is executor-agnostic by construction — it is just a Mealy machine.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

package «wintermute» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- The machine calculus: `AbstractMachine` + the Category/Arrow laws the
-- reconciler's stream theorems ride on.
require «continuity-machine» from "../../core/machine"

@[default_target]
lean_lib «Wintermute» where
  globs := #[.andSubmodules `Wintermute]

-- The daemon / CLI.
@[default_target]
lean_exe «wintermute» where
  root := `Main
