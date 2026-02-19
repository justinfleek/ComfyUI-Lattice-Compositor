// s4-runtime // core/exceptions.h
// Exception handling and assertion infrastructure.
// Modeled on nvfuser's exception system but framework-independent.
#pragma once

#include <array>
#include <cstdint>
#include <exception>
#include <iosfwd>
#include <optional>
#include <sstream>
#include <source_location>
#include <string>
#include <string_view>
#include <vector>

namespace s4::core {

// Demangle C++ type names for better error messages.
[[nodiscard]] auto demangle(const char* name) -> std::string;

// Capture backtrace (platform-specific implementation).
[[nodiscard]] auto get_backtrace(
    std::size_t frames_to_skip = 0,
    std::size_t maximum_frames = 64) -> std::string;

// Source location for error reporting.
struct source_location final {
  const char* function = "";
  const char* file = "";
  std::int64_t line = 0;
  
  [[nodiscard]] static auto current(
      std::source_location loc = std::source_location::current()) noexcept 
      -> source_location {
    return {loc.function_name(), loc.file_name(), 
            static_cast<std::int64_t>(loc.line())};
  }
};

auto operator<<(std::ostream& out, const source_location& loc) -> std::ostream&;

// Compile-time empty string optimization for zero-cost assertions.
struct compile_time_empty_string final {
  [[nodiscard]] operator const std::string&() const noexcept {
    static const std::string empty;
    return empty;
  }
  [[nodiscard]] operator const char*() const noexcept { return ""; }
};

namespace detail {

inline auto to_str_impl(std::ostream& ss) -> std::ostream& { return ss; }

template <typename T>
auto to_str_impl(std::ostream& ss, const T& t) -> std::ostream& {
  ss << t;
  return ss;
}

template <>
inline auto to_str_impl<compile_time_empty_string>(
    std::ostream& ss, const compile_time_empty_string&) -> std::ostream& {
  return ss;
}

template <typename T, typename... Args>
auto to_str_impl(std::ostream& ss, const T& t, const Args&... args) 
    -> std::ostream& {
  return to_str_impl(to_str_impl(ss, t), args...);
}

template <typename T>
struct canonicalize_str_types { using type = const T&; };

template <std::size_t N>
struct canonicalize_str_types<std::array<char, N>> { using type = const char*; };

template <typename... Args>
struct str_wrapper final {
  [[nodiscard]] static auto call(const Args&... args) -> std::string {
    std::ostringstream ss;
    to_str_impl(ss, args...);
    return ss.str();
  }
};

template <>
struct str_wrapper<std::string> final {
  [[nodiscard]] static auto call(const std::string& str) -> const std::string& {
    return str;
  }
};

template <>
struct str_wrapper<const char*> final {
  [[nodiscard]] static auto call(const char* str) -> const char* { return str; }
};

template <>
struct str_wrapper<> final {
  [[nodiscard]] static auto call() -> compile_time_empty_string {
    return compile_time_empty_string{};
  }
};

}  // namespace detail

// Convert variadic arguments to string with minimal overhead.
template <typename... Args>
[[nodiscard]] inline auto to_str(const Args&... args) -> decltype(auto) {
  return detail::str_wrapper<
      typename detail::canonicalize_str_types<Args>::type...>::call(args...);
}

// The main exception class for s4-runtime.
class s4_error : public std::exception {
public:
  s4_error(source_location loc, std::string msg);
  s4_error(std::string msg, std::string backtrace, const void* caller = nullptr);
  
  void add_context(std::string msg);
  
  [[nodiscard]] auto msg() const noexcept -> const std::string& { return msg_; }
  [[nodiscard]] auto context() const noexcept -> const std::vector<std::string>& {
    return context_;
  }
  [[nodiscard]] auto backtrace() const noexcept -> const std::string& {
    return backtrace_;
  }
  [[nodiscard]] auto what() const noexcept -> const char* override {
    return what_.c_str();
  }
  [[nodiscard]] auto what_without_backtrace() const noexcept -> const char* {
    return what_without_backtrace_.c_str();
  }
  [[nodiscard]] auto caller() const noexcept -> const void* { return caller_; }

private:
  void refresh_what();
  [[nodiscard]] auto compute_what(bool include_backtrace) const -> std::string;

  std::string msg_;
  std::vector<std::string> context_;
  std::string backtrace_;
  std::string what_;
  std::string what_without_backtrace_;
  const void* caller_ = nullptr;
};

[[noreturn]] void check_fail(
    const char* func, const char* file, std::int64_t line,
    const std::string& msg);

[[noreturn]] void error_fail(
    const char* func, const char* file, std::int64_t line,
    const char* cond_msg, const std::string& user_msg);

}  // namespace s4::core

// Core assertion macros.
#define S4_STRINGIZE_IMPL(x) #x
#define S4_STRINGIZE(x) S4_STRINGIZE_IMPL(x)

#define S4_THROW(...)                                                          \
  ::s4::core::error_fail(                                                      \
      __FUNCTION__, __FILE__, __LINE__,                                        \
      " INTERNAL ASSERT FAILED at " __FILE__ ":" S4_STRINGIZE(__LINE__) ". ",  \
      ::s4::core::to_str(__VA_ARGS__))

#define S4_ERROR(cond, ...)                                                    \
  do {                                                                         \
    if (!(cond)) {                                                             \
      S4_THROW("Expected " #cond " . ", ##__VA_ARGS__);                        \
    }                                                                          \
  } while (0)

#define S4_CHECK(cond, ...)                                                    \
  do {                                                                         \
    if (!(cond)) {                                                             \
      ::s4::core::check_fail(                                                  \
          __func__, __FILE__, __LINE__,                                        \
          ::s4::core::to_str("Expected " #cond " . ", ##__VA_ARGS__));         \
    }                                                                          \
  } while (0)

// Comparison assertion macros.
#define S4_COMPARISON_MSG(lhs, op, rhs) "Found ", (lhs), " vs ", (rhs), ". "

#define S4_ERROR_COMPARE(lhs, op, rhs, ...)                                    \
  S4_ERROR((lhs) op (rhs), S4_COMPARISON_MSG(lhs, op, rhs), ##__VA_ARGS__)

#define S4_CHECK_COMPARE(lhs, op, rhs, ...)                                    \
  S4_CHECK((lhs) op (rhs), S4_COMPARISON_MSG(lhs, op, rhs), ##__VA_ARGS__)

#define S4_ERROR_EQ(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, ==, rhs, ##__VA_ARGS__)
#define S4_CHECK_EQ(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, ==, rhs, ##__VA_ARGS__)
#define S4_ERROR_NE(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, !=, rhs, ##__VA_ARGS__)
#define S4_CHECK_NE(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, !=, rhs, ##__VA_ARGS__)
#define S4_ERROR_LT(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, <, rhs, ##__VA_ARGS__)
#define S4_CHECK_LT(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, <, rhs, ##__VA_ARGS__)
#define S4_ERROR_LE(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, <=, rhs, ##__VA_ARGS__)
#define S4_CHECK_LE(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, <=, rhs, ##__VA_ARGS__)
#define S4_ERROR_GT(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, >, rhs, ##__VA_ARGS__)
#define S4_CHECK_GT(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, >, rhs, ##__VA_ARGS__)
#define S4_ERROR_GE(lhs, rhs, ...) S4_ERROR_COMPARE(lhs, >=, rhs, ##__VA_ARGS__)
#define S4_CHECK_GE(lhs, rhs, ...) S4_CHECK_COMPARE(lhs, >=, rhs, ##__VA_ARGS__)

// Debug-only assertions.
#if !defined(NDEBUG) || defined(S4_EXPLICIT_ERROR_CHECK)
#define S4_DEBUG_ERROR(cond, ...) S4_ERROR(cond, ##__VA_ARGS__)
#define S4_DEBUG_CHECK(cond, ...) S4_CHECK(cond, ##__VA_ARGS__)
#else
#define S4_DEBUG_ERROR(cond, ...) ((void)0)
#define S4_DEBUG_CHECK(cond, ...) ((void)0)
#endif
