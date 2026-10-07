{
  description = "// straylight // wintermute — the hot-reload theme reconciler";

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;
      perSystem =
        { system, ... }:
        {
          # The lean toolchain overlay is threaded here (once), so the
          # flake module below sees the pinned `pkgs.lean.*`.
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (inputs.lean4-nix.readToolchainFile ./src/core/base/lean-toolchain)
            ];
          };
        };

      imports = [ ./nix/wintermute.nix ];
    };

  inputs = {
    nixpkgs.url = "github:sensenet-ai/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default-linux";

    # lean4-nix pinned to the manifest/v4.31.0 branch (PR #127), same rev
    # the continuity monorepo pins.
    lean4-nix.url = "github:lenianiva/lean4-nix/1ac326fe8e88796156906b0ad8272364f01a7cdc";
    lean4-nix.inputs.nixpkgs.follows = "nixpkgs";
  };
}
