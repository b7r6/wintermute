# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                            // straylight // wintermute //
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# The wintermute dep cone extracted from the continuity monorepo's
# nix/flake/continuity.nix: base → codec → trust → machine → wintermute,
# plus the stdlibex «straylight-shims» extern_lib the exe link closes over.
{ inputs, ... }:
{
  perSystem =
    {
      pkgs,
      lib,
      ...
    }:
    let
      isLinux = pkgs.stdenv.isLinux;

      lake2nix = pkgs.callPackage inputs.lean4-nix.lake { };

      # ── native deps named by the stdlibex lakefile ─────────────────
      nativeLibs =
        with pkgs;
        [
          cli11
          fmt
          gnutls
          libressl
          nghttp3
          ngtcp2-gnutls
          spdlog
        ]
        ++ lib.optional isLinux liburing;

      alephIncludePath = lib.makeSearchPathOutput "dev" "include" nativeLibs;
      alephLibPath = lib.makeLibraryPath (nativeLibs ++ [ pkgs.stdenv.cc.cc.lib ]);

      # straylight-nix: the sensenet nixpkgs fork ships this; on vanilla
      # nixpkgs the CAS shim simply stays off (the lakefile env-gates it).
      straylightNixEnv = lib.optionalAttrs (pkgs ? straylight-nix) {
        STRAYLIGHT_NIX_PREFIX = "${pkgs.straylight-nix}";
      };

      # batteries (rev-pinned) is required only by base; its :shared facet
      # trips a lake build cycle, so build just the default target.
      coreDeps = lake2nix.buildDeps {
        src = ../src/core/base;
        depOverride = {
          batteries = {
            buildPhase = ''
              runHook preBuild
              lake build batteries
              runHook postBuild
            '';
          };
        };
      };

      continuity-base = lake2nix.mkPackage {
        name = "ContinuityBase";
        src = ../src/core/base;
        lakeDeps = coreDeps;
      };

      # ── the centralized audit floor (stdlibex) ─────────────────────
      # Every hand-written C/C++ shim archived into
      # `extern_lib «straylight-shims»`. No Lean library and no default
      # target, so build the extern_lib by name.
      stdlibex = lake2nix.mkPackage (
        {
          name = "StdlibEx";
          src = ../src/stdlibex;
          lakeDeps = {
            inherit (coreDeps) batteries;
          };
          buildInputs = [
            pkgs.rsync
            pkgs.lean.lean-all
          ]
          ++ nativeLibs;
          buildPhase = ''
            runHook preBuild
            lake build «straylight-shims»
            runHook postBuild
          '';
          ALEPH_INCLUDE_PATH = alephIncludePath;
          ALEPH_LIB_PATH = alephLibPath;
          LEAN_CC = "cc";
        }
        // straylightNixEnv
      );

      continuity-codec = lake2nix.mkPackage {
        name = "ContinuityCodec";
        src = ../src/core/codec;
        lakeDeps = coreDeps // {
          "«continuity-base»" = continuity-base;
          inherit stdlibex;
        };
      };
      continuity-trust = lake2nix.mkPackage {
        name = "ContinuityTrust";
        src = ../src/core/trust;
        lakeDeps = coreDeps // {
          "«continuity-base»" = continuity-base;
        };
      };
      continuity-machine = lake2nix.mkPackage {
        name = "ContinuityMachine";
        src = ../src/core/machine;
        lakeDeps = coreDeps // {
          "«continuity-base»" = continuity-base;
          "«continuity-codec»" = continuity-codec;
          "«continuity-trust»" = continuity-trust;
          inherit stdlibex;
        };
      };

      # ── the hot-reload theme reconciler: apps/wintermute ───────────
      # Pure Lean over the machine calculus, but the EXE link closes over
      # the whole dep graph — codec's stdlibex require drags the
      # «straylight-shims» extern_lib into the link, so the sandbox needs
      # the full header/cc environment even though wintermute itself
      # references none of it.
      wintermute = lake2nix.mkPackage (
        {
          name = "Wintermute";
          src = ../src/apps/wintermute;
          lakeDeps = coreDeps // {
            "«continuity-base»" = continuity-base;
            "«continuity-codec»" = continuity-codec;
            "«continuity-trust»" = continuity-trust;
            "«continuity-machine»" = continuity-machine;
            inherit stdlibex;
          };
          buildInputs = [
            pkgs.rsync
            pkgs.lean.lean-all
          ]
          ++ nativeLibs;
          staticLibDeps = [ pkgs.pkg-config ];
          buildPhase = ''
            runHook preBuild
            lake build
            runHook postBuild
          '';
          installArtifacts = false;
          postInstall = ''
            mkdir -p $out/bin
            cp .lake/build/bin/wintermute $out/bin/
          '';
          ALEPH_INCLUDE_PATH = alephIncludePath;
          ALEPH_LIB_PATH = alephLibPath;
          LEAN_CC = "cc";
        }
        // straylightNixEnv
      );
    in
    {
      packages = {
        inherit
          continuity-base
          continuity-codec
          continuity-trust
          continuity-machine
          stdlibex
          wintermute
          ;
        default = wintermute;
      };

      devShells.default = pkgs.mkShell (
        {
          packages = [
            pkgs.lean.lean-all
            pkgs.pkg-config
          ]
          ++ nativeLibs;

          ALEPH_INCLUDE_PATH = alephIncludePath;
          ALEPH_LIB_PATH = alephLibPath;
          LEAN_CC = "cc";
        }
        // straylightNixEnv
      );
    };
}
