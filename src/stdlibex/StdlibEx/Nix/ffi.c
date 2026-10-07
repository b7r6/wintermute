/*
 * nix_ffi.c — Lean @[extern] bridge to straylight-nix
 *
 * Three operations:
 *   resolve : "nixpkgs#fmt" → "/nix/store/...-fmt-11.0.2"
 *   has     : "/nix/store/..." → Bool
 *   import_ : "/path/to/dir" → "/nix/store/...-name" (CA import)
 *
 * v0: shells out to `nix` CLI (works without straylight-nix linked)
 * v1: links straylight-nix directly (zero fork, io_uring store ops)
 */
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

/* ── resolve: nixpkgs#pkg → /nix/store/...-pkg ── */
LEAN_EXPORT lean_object* nix_resolve(lean_object* flake_ref, lean_object* w) {
  (void)w;
  const char* ref = lean_string_cstr(flake_ref);

  /* v0: shell out to nix build --no-link --print-out-paths */
  char cmd[1024];
  snprintf(cmd, sizeof(cmd),
           "nix build '%s' --no-link --print-out-paths 2>/dev/null | head -1 | tr -d '\\n'", ref);

  FILE* fp = popen(cmd, "r");
  if (!fp) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string("nix build failed to start")));
  }

  char path[4096];
  size_t n = fread(path, 1, sizeof(path) - 1, fp);
  path[n] = '\0';
  int status = pclose(fp);

  if (status != 0 || n == 0) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("nix build failed")));
  }

  return lean_io_result_mk_ok(lean_mk_string(path));
}

/* ── has: check if a store path exists ── */
LEAN_EXPORT lean_object* nix_has(lean_object* store_path, lean_object* w) {
  (void)w;
  struct stat st;
  int exists = stat(lean_string_cstr(store_path), &st) == 0;
  return lean_io_result_mk_ok(lean_box(exists ? 1 : 0));
}

/* ── import: directory → CA store path ── */
LEAN_EXPORT lean_object* nix_import(lean_object* dir_path, lean_object* name, lean_object* w) {
  (void)w;
  const char* dir = lean_string_cstr(dir_path);
  const char* nm = lean_string_cstr(name);

  /* v0: nix store add-path */
  char cmd[4096];
  snprintf(cmd, sizeof(cmd), "nix-store --add '%s' 2>/dev/null | tr -d '\\n'", dir);

  FILE* fp = popen(cmd, "r");
  if (!fp) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("nix-store --add failed")));
  }

  char path[4096];
  size_t n = fread(path, 1, sizeof(path) - 1, fp);
  path[n] = '\0';
  pclose(fp);

  if (n == 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string("nix-store --add returned empty")));
  }

  return lean_io_result_mk_ok(lean_mk_string(path));
}

/* ── hash: content hash of a file (for cache keys) ── */
LEAN_EXPORT lean_object* nix_hash_path(lean_object* file_path, lean_object* w) {
  (void)w;
  const char* path = lean_string_cstr(file_path);

  char cmd[4096];
  snprintf(cmd, sizeof(cmd), "nix-hash --type sha256 --flat '%s' 2>/dev/null | tr -d '\\n'", path);

  FILE* fp = popen(cmd, "r");
  if (!fp) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("nix-hash failed")));
  }

  char hash[128];
  size_t n = fread(hash, 1, sizeof(hash) - 1, fp);
  hash[n] = '\0';
  pclose(fp);

  return lean_io_result_mk_ok(lean_mk_string(hash));
}
