/*
 * log.cpp — StdlibEx.Logging shim binding spdlog for Lean FFI.
 *
 * Logging is NOT proof surface: there's nothing to verify about emitting a
 * timestamped line to a sink. So we don't reimplement it in Lean — we wire
 * spdlog (levels, colored console, file/rotating sinks, async, thread-safe,
 * microsecond timestamps) behind a flat C ABI and let Lean do the string
 * interpolation, passing the finished message as a plain `const char*`.
 *
 * The shim is deliberately thin: Lean owns formatting (s!"..."), spdlog owns
 * everything that's actually hard about logging (sink fan-out, async queue,
 * rotation, atomic level checks). Exposed as plain C so `@[extern]` can call it.
 */
#include <memory>
#include <string>
#include <vector>

#include <lean/lean.h>
#include <spdlog/sinks/basic_file_sink.h>
#include <spdlog/sinks/rotating_file_sink.h>
#include <spdlog/sinks/stdout_color_sinks.h>
#include <spdlog/spdlog.h>

extern "C" {

/* ── init ──
 * console=1 → colored stderr sink; file != "" → also a basic file sink.
 * pattern "" → spdlog default; level is the spdlog level int (0=trace..6=off). */
LEAN_EXPORT lean_object* stdlibex_log_init(uint8_t console, b_lean_obj_arg file_obj,
                                           b_lean_obj_arg pattern_obj, uint32_t level,
                                           lean_object* /*w*/) {
  try {
    std::vector<spdlog::sink_ptr> sinks;
    if (console) {
      sinks.push_back(std::make_shared<spdlog::sinks::stderr_color_sink_mt>());
    }
    const char* file = lean_string_cstr(file_obj);
    if (file && file[0]) {
      sinks.push_back(std::make_shared<spdlog::sinks::basic_file_sink_mt>(file, false));
    }

    auto logger = std::make_shared<spdlog::logger>("stdlibex", sinks.begin(), sinks.end());
    const char* pat = lean_string_cstr(pattern_obj);
    if (pat && pat[0]) {
      logger->set_pattern(pat);
    }
    logger->set_level(static_cast<spdlog::level::level_enum>(level));
    logger->flush_on(spdlog::level::warn);

    spdlog::set_default_logger(logger);
    return lean_io_result_mk_ok(lean_box(0));
  } catch (const std::exception& e) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(e.what())));
  }
}

/* ── a rotating file sink variant (size-capped, N rotated files) ── */
LEAN_EXPORT lean_object* stdlibex_log_init_rotating(b_lean_obj_arg file_obj, size_t max_size,
                                                    size_t max_files, uint32_t level,
                                                    lean_object* /*w*/) {
  try {
    const char* file = lean_string_cstr(file_obj);
    auto logger = spdlog::rotating_logger_mt("stdlibex", file, max_size, max_files);
    logger->set_level(static_cast<spdlog::level::level_enum>(level));
    spdlog::set_default_logger(logger);
    return lean_io_result_mk_ok(lean_box(0));
  } catch (const std::exception& e) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(e.what())));
  }
}

/* ── log at a level. Lean has already formatted the message. ──
 * We pass it as a runtime string (not a compile-time fmt string) so there's no
 * format-string injection: spdlog treats it as a literal payload. */
LEAN_EXPORT lean_object* stdlibex_log_at(uint32_t level, b_lean_obj_arg msg_obj,
                                         lean_object* /*w*/) {
  const char* msg = lean_string_cstr(msg_obj);
  spdlog::log(static_cast<spdlog::level::level_enum>(level), "{}", msg);
  return lean_io_result_mk_ok(lean_box(0));
}

/* ── set level at runtime ── */
LEAN_EXPORT lean_object* stdlibex_log_set_level(uint32_t level, lean_object* /*w*/) {
  spdlog::set_level(static_cast<spdlog::level::level_enum>(level));
  return lean_io_result_mk_ok(lean_box(0));
}

/* ── flush ── */
LEAN_EXPORT lean_object* stdlibex_log_flush(lean_object* /*w*/) {
  if (auto lg = spdlog::default_logger()) {
    lg->flush();
  }
  return lean_io_result_mk_ok(lean_box(0));
}

} /* extern "C" */
