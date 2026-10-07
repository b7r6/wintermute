/*
 * straylight_cli.c++ — extern-C shim around CLI11, built to MEASURE the friction
 * of FFI-ing a fluent-typed-builder library, not because it's obviously the right
 * call.
 *
 * CLI11's value is its typed builder: `app.add_option("--jobs", jobs, "desc")`
 * binds a flag to a C++ variable that parse() writes into, with validators,
 * subcommands, and auto-generated help. That model lives in C++. To expose it to
 * Lean across a flat C ABI, the shim must either (a) hardcode the schema in C++
 * and expose per-option getters [this file], or (b) accept a dynamic schema from
 * Lean and re-expose most of CLI11's surface — which erodes the savings.
 *
 * This is option (a): the aleph CLI schema lives HERE, in C++. That's the cost —
 * adding a subcommand or flag is a C++ edit + recompile, not a Lean change. The
 * benefit is real help-text + error handling for free.
 */
#include <string>

#include <lean/lean.h>

#include <CLI/CLI.hpp>

extern "C" {

/* Parsed results, owned C-side, fetched by Lean via getters.
 * Each new flag here is the friction: the schema is C++, not Lean/EDSL. */
struct AlephCli {
  std::string subcommand; // "build" | "query" | "serve" | ""
  std::string target;     // positional //pattern
  int jobs = 0;
  bool verbose = false;
  std::string remote; // --remote host:port
  int exit_code = -1; // -1 = parsed ok; >=0 = CLI11 wants to exit (help/error)
};

LEAN_EXPORT lean_object* straylight_cli_parse(b_lean_obj_arg argv_obj, lean_object* /*w*/) {
  auto* r = new AlephCli();

  CLI::App app{"aleph — a coeffect-graded build tool", "aleph"};
  app.require_subcommand(0, 1);

  auto* build = app.add_subcommand("build", "Build targets matching a pattern");
  build->add_option("pattern", r->target, "//pattern to build")->required();
  build->add_option("-j,--jobs", r->jobs, "Parallel jobs");
  build->add_flag("-v,--verbose", r->verbose, "Verbose output");
  build->add_option("--remote", r->remote, "Remote executor host:port");

  auto* query = app.add_subcommand("query", "Query the build graph");
  query->add_option("pattern", r->target, "//pattern to query")->required();

  auto* serve = app.add_subcommand("serve", "Run the REAPI server");
  serve->add_option("--remote", r->remote, "Bind host:port");

  /* Reconstruct argv from the Lean Array String. */
  size_t n = lean_array_size(argv_obj);
  std::vector<std::string> args;
  for (size_t i = 0; i < n; i++) {
    args.push_back(std::string(lean_string_cstr(lean_array_get_core(argv_obj, i))));
  }

  /* CLI11 wants argv in reverse for its vector overload, or use parse(argc,argv). */
  std::vector<char*> cargv;
  cargv.push_back(const_cast<char*>("aleph"));
  for (auto& s : args) {
    cargv.push_back(const_cast<char*>(s.c_str()));
  }

  try {
    app.parse((int)cargv.size(), cargv.data());
    if (build->parsed()) {
      r->subcommand = "build";
    } else if (query->parsed()) {
      r->subcommand = "query";
    } else if (serve->parsed()) {
      r->subcommand = "serve";
    }
  } catch (const CLI::ParseError& e) {
    /* CLI11 prints help/errors and gives an exit code — real usability for free. */
    r->exit_code = app.exit(e);
  }

  return lean_io_result_mk_ok(lean_alloc_external(
      lean_register_external_class([](void* p) { delete static_cast<AlephCli*>(p); },
                                   [](void*, b_lean_obj_arg) {}),
      r));
}

/* Getters — one per field. THIS is the friction: every flag needs a getter. */
LEAN_EXPORT lean_object* straylight_cli_subcommand(b_lean_obj_arg h, lean_object* /*w*/) {
  auto* r = static_cast<AlephCli*>(lean_get_external_data(h));
  return lean_io_result_mk_ok(lean_mk_string(r->subcommand.c_str()));
}

LEAN_EXPORT lean_object* straylight_cli_target(b_lean_obj_arg h, lean_object* /*w*/) {
  auto* r = static_cast<AlephCli*>(lean_get_external_data(h));
  return lean_io_result_mk_ok(lean_mk_string(r->target.c_str()));
}

LEAN_EXPORT uint32_t straylight_cli_jobs(b_lean_obj_arg h) {
  return (uint32_t)static_cast<AlephCli*>(lean_get_external_data(h))->jobs;
}

LEAN_EXPORT uint8_t straylight_cli_verbose(b_lean_obj_arg h) {
  return static_cast<AlephCli*>(lean_get_external_data(h))->verbose ? 1 : 0;
}

LEAN_EXPORT lean_object* straylight_cli_remote(b_lean_obj_arg h, lean_object* /*w*/) {
  auto* r = static_cast<AlephCli*>(lean_get_external_data(h));
  return lean_io_result_mk_ok(lean_mk_string(r->remote.c_str()));
}

LEAN_EXPORT uint32_t straylight_cli_exit_code(b_lean_obj_arg h) {
  return (uint32_t)(int32_t)static_cast<AlephCli*>(lean_get_external_data(h))->exit_code;
}

} /* extern "C" */
