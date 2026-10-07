/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // STDLIBEX // NIX
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Nix store operations: resolve flake references, check store path existence,
    import directories as content-addressed store paths.

    v0: shells out to `nix` CLI (works without straylight-nix linked)
    v1 (future): links straylight-nix directly (zero fork, io_uring store ops)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Nix

/-- Resolve a flake reference to a store path.
    e.g. "nixpkgs#fmt" → "/nix/store/...-fmt-11.0.2" -/
@[extern "nix_resolve"]
opaque resolve (flakeRef : @& String) : IO String

/-- Check if a store path exists. -/
@[extern "nix_has"]
opaque has (storePath : @& String) : IO Bool

/-- Import a directory as a content-addressed store path.
    Returns the store path. -/
@[extern "nix_import"]
opaque import_ (dirPath : @& String) (name : @& String) : IO String

/-- Hash a file path using the Nix hash algorithm. -/
@[extern "nix_hash_path"]
opaque hashPath (path : @& String) : IO String

end StdlibEx.Nix
