// s4-runtime // src/exceptions.cpp
#include <s4/core/exceptions.h>

#include <sstream>

#if defined(__GNUC__) || defined(__clang__)
#include <cxxabi.h>
#include <execinfo.h>
#include <cstdlib>
#endif

namespace s4::core {

auto demangle(const char* name) -> std::string {
#if defined(__GNUC__) || defined(__clang__)
  int status = 0;
  char* demangled = abi::__cxa_demangle(name, nullptr, nullptr, &status);
  if (status == 0 && demangled != nullptr) {
    std::string result(demangled);
    std::free(demangled);
    return result;
  }
#endif
  return name;
}

auto get_backtrace(std::size_t frames_to_skip, std::size_t maximum_frames)
    -> std::string {
#if (defined(__GNUC__) || defined(__clang__)) && !defined(__APPLE__)
  std::vector<void*> buffer(maximum_frames);
  int nptrs = ::backtrace(buffer.data(), static_cast<int>(maximum_frames));
  
  if (nptrs <= 0) {
    return "[backtrace unavailable]";
  }
  
  char** symbols = ::backtrace_symbols(buffer.data(), nptrs);
  if (symbols == nullptr) {
    return "[backtrace symbols unavailable]";
  }
  
  std::ostringstream ss;
  for (int i = static_cast<int>(frames_to_skip); i < nptrs; ++i) {
    ss << "  " << symbols[i] << "\n";
  }
  
  std::free(symbols);
  return ss.str();
#else
  return "[backtrace not supported on this platform]";
#endif
}

auto operator<<(std::ostream& out, const source_location& loc) -> std::ostream& {
  out << loc.file << ":" << loc.line << " in " << loc.function;
  return out;
}

s4_error::s4_error(source_location loc, std::string msg)
    : backtrace_(get_backtrace(2, 64)) {
  std::ostringstream ss;
  ss << loc << ": " << msg;
  msg_ = ss.str();  // Store location-prefixed message.
  refresh_what();
}

s4_error::s4_error(std::string msg, std::string backtrace, const void* caller)
    : msg_(std::move(msg)),
      backtrace_(std::move(backtrace)),
      caller_(caller) {
  refresh_what();
}

void s4_error::add_context(std::string msg) {
  context_.push_back(std::move(msg));
  refresh_what();
}

void s4_error::refresh_what() {
  what_without_backtrace_ = compute_what(false);
  what_ = compute_what(true);
}

auto s4_error::compute_what(bool include_backtrace) const -> std::string {
  std::ostringstream ss;
  ss << msg_;
  
  for (const auto& ctx : context_) {
    ss << "\n  Context: " << ctx;
  }
  
  if (include_backtrace && !backtrace_.empty()) {
    ss << "\n\nBacktrace:\n" << backtrace_;
  }
  
  return ss.str();
}

[[noreturn]] void check_fail(
    const char* func, const char* file, std::int64_t line,
    const std::string& msg) {
  throw s4_error({func, file, line}, msg);
}

[[noreturn]] void error_fail(
    const char* func, const char* file, std::int64_t line,
    const char* cond_msg, const std::string& user_msg) {
  std::ostringstream ss;
  ss << cond_msg << user_msg;
  throw s4_error({func, file, line}, ss.str());
}

}  // namespace s4::core
