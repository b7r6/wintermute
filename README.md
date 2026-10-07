# wintermute

The hot-reload theme reconciler — desktop theming as a verified control
loop. Pure Lean 4 core (a `Continuity.Machine` Mealy machine with proven
invariants) plus a stdlib-IO shell: state-file control plane, mtime watch
loop, and live adapters (hyprctl / kitty / emacsclient / nvim --remote).

## Build

    nix build .#wintermute
    ./result/bin/wintermute

## Provenance

Extracted from the `continuity` Lean 4 monorepo
(branch `b7r6/wintermute-0x01`, mirror `hypermodern-src/orbital-continuity`),
preserving the monorepo's relative layout (`src/apps/wintermute`,
`src/core/{base,codec,trust,machine}`, `src/stdlibex`) so the lakefiles'
relative `require ... from` paths remain intact.
