// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // aleph // straylight_cas — CAS shim
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Lean ⇄ straylight::nix::store::ca_store bridge (decision XV). Replaces the
// popen Nix-store shim for the CONTENT layer. The digest is the authorization;
// these entry points do no identity work — they hash, store, and check content.
//
// Process-global store rooted at $ALEPH_CAS_ROOT (default ~/.cache/aleph/cas).

#include <cstdlib>
#include <cstring>
#include <mutex>
#include <span>
#include <string>

#include <lean/lean.h>

#include "straylight/nix/store/ca_store.h"

using namespace straylight::nix::store;

namespace {

ca_store* g_store = nullptr;
std::once_flag g_once;

ca_store* store() {
  std::call_once(g_once, [] {
    const char* env = std::getenv("ALEPH_CAS_ROOT");
    std::string root;
    if (env != nullptr) {
      root = env;
    } else {
      const char* home = std::getenv("HOME");
      root = (home != nullptr ? std::string(home) : std::string("/tmp")) + "/.cache/aleph/cas";
    }
    g_store = new ca_store(root);
    (void)g_store->init();
  });
  return g_store;
}

inline lean_obj_res ok_str(const std::string& s) {
  return lean_io_result_mk_ok(lean_mk_string(s.c_str()));
}

inline lean_obj_res ok_bool(bool b) {
  return lean_io_result_mk_ok(lean_box(b ? 1 : 0));
}

inline lean_obj_res io_err(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

} // namespace

// put : @& ByteArray → IO String
extern "C" LEAN_EXPORT lean_obj_res straylight_cas_put(b_lean_obj_arg data,
                                                       lean_obj_arg /* world */) {
  const std::size_t n = lean_sarray_size(data);
  const auto* p = reinterpret_cast<const std::byte*>(lean_sarray_cptr(data));
  auto h = store()->put(std::span<const std::byte>(p, n));
  if (!h) {
    return io_err("cas: put failed");
  }
  return ok_str(*h);
}

// get : @& String → IO ByteArray
extern "C" LEAN_EXPORT lean_obj_res straylight_cas_get(b_lean_obj_arg hash,
                                                       lean_obj_arg /* world */) {
  auto d = store()->get(lean_string_cstr(hash));
  if (!d) {
    return io_err("cas: not found");
  }
  const std::size_t n = d->size();
  lean_object* arr = lean_alloc_sarray(1, n, n);
  std::memcpy(lean_sarray_cptr(arr), d->data(), n);
  return lean_io_result_mk_ok(arr);
}

// has : @& String → IO Bool
extern "C" LEAN_EXPORT lean_obj_res straylight_cas_has(b_lean_obj_arg hash,
                                                       lean_obj_arg /* world */) {
  return ok_bool(store()->has(lean_string_cstr(hash)));
}

// verify : @& String → IO Bool
extern "C" LEAN_EXPORT lean_obj_res straylight_cas_verify(b_lean_obj_arg hash,
                                                          lean_obj_arg /* world */) {
  auto v = store()->verify(lean_string_cstr(hash));
  return ok_bool(v.has_value() && *v);
}

// hash_file : @& String → IO String  (read file, BLAKE3, return hex; no store)
extern "C" LEAN_EXPORT lean_obj_res straylight_cas_hash_file(b_lean_obj_arg path,
                                                             lean_obj_arg /* world */) {
  const char* p = lean_string_cstr(path);
  std::string content;

  if (FILE* f = std::fopen(p, "rb")) {
    char buf[65536];
    std::size_t r = 0;
    while ((r = std::fread(buf, 1, sizeof(buf), f)) > 0) {
      content.append(buf, r);
    }
    std::fclose(f);
  } else {
    return io_err("cas: hash_file open failed");
  }

  auto h = store()->put(std::span<const std::byte>(
      reinterpret_cast<const std::byte*>(content.data()), content.size()));

  if (!h) {
    return io_err("cas: hash_file failed");
  }

  return ok_str(*h);
}
