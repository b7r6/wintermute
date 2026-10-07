/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // STDLIBEX // NIX // CAS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Content-addressed storage: BLAKE3 hashes, put/get/verify. The digest is the
    authorization — these entry points do no identity work.

    Process-global store rooted at $ALEPH_CAS_ROOT (default ~/.cache/aleph/cas).
    Only available when straylight-nix is linked (STRAYLIGHT_NIX_PREFIX set).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Nix.Cas

/-- Store bytes and return the BLAKE3 hash. -/
@[extern "cas_put"]
opaque put (data : @& ByteArray) : IO String

/-- Retrieve bytes by hash. -/
@[extern "cas_get"]
opaque get (hash : @& String) : IO ByteArray

/-- Check if a hash exists in the store. -/
@[extern "cas_has"]
opaque has (hash : @& String) : IO Bool

/-- Verify that the stored content matches its hash. -/
@[extern "cas_verify"]
opaque verify (hash : @& String) : IO Bool

/-- Hash a file path using BLAKE3 (no store operation). -/
@[extern "cas_hash_file"]
opaque hashFile (path : @& String) : IO String

end StdlibEx.Nix.Cas
