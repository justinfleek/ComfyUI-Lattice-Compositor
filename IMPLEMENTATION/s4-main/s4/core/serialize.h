// s4-runtime // core/serialize.h
// Binary serialization utilities for configuration and state.
//
// IMPORTANT: Serialization uses host-endian byte order. Data serialized on
// one architecture may not be readable on another with different endianness.
// This is acceptable for GPU inference state which is typically not portable
// across architectures anyway. If cross-platform serialization is needed,
// use explicit little-endian encoding.
#pragma once

#include <s4/core/exceptions.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <type_traits>
#include <vector>

namespace s4::core {

// Magic number for s4 serialized data.
inline constexpr std::uint32_t serialization_magic = 0x53345254;  // "S4RT"

// Simple binary writer for serialization.
class binary_writer final {
public:
  explicit binary_writer(std::size_t reserve_bytes = 256) {
    buffer_.reserve(reserve_bytes);
  }

  // Write raw bytes.
  auto write_bytes(const void* data, std::size_t size) -> binary_writer& {
    const auto* bytes = static_cast<const std::byte*>(data);
    buffer_.insert(buffer_.end(), bytes, bytes + size);
    return *this;
  }

  // Write a trivially copyable value.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  auto write(const T& value) -> binary_writer& {
    return write_bytes(&value, sizeof(T));
  }

  // Write with explicit size check (for fixed-size fields).
  template <typename T, std::size_t ExpectedSize>
    requires std::is_trivially_copyable_v<T>
  auto write_fixed(const T& value) -> binary_writer& {
    static_assert(sizeof(T) == ExpectedSize, "Size mismatch in fixed-size write");
    return write(value);
  }

  // Write a length-prefixed string.
  auto write_string(std::string_view str) -> binary_writer& {
    write(static_cast<std::uint32_t>(str.size()));
    return write_bytes(str.data(), str.size());
  }

  // Write a length-prefixed vector of trivially copyable elements.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  auto write_vector(std::span<const T> vec) -> binary_writer& {
    write(static_cast<std::uint32_t>(vec.size()));
    return write_bytes(vec.data(), vec.size() * sizeof(T));
  }

  // Write an optional value with presence flag.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  auto write_optional(const std::optional<T>& opt) -> binary_writer& {
    write(static_cast<std::uint8_t>(opt.has_value() ? 1 : 0));
    if (opt.has_value()) {
      write(*opt);
    }
    return *this;
  }

  // Write a float as uint32 bits (portable).
  auto write_float_bits(float value) -> binary_writer& {
    std::uint32_t bits;
    std::memcpy(&bits, &value, sizeof(float));
    return write(bits);
  }

  // Write a double as uint64 bits (portable).
  auto write_double_bits(double value) -> binary_writer& {
    std::uint64_t bits;
    std::memcpy(&bits, &value, sizeof(double));
    return write(bits);
  }

  // Get the serialized data.
  [[nodiscard]] auto data() const noexcept -> const std::byte* {
    return buffer_.data();
  }

  [[nodiscard]] auto size() const noexcept -> std::size_t {
    return buffer_.size();
  }

  [[nodiscard]] auto bytes() const noexcept -> std::span<const std::byte> {
    return buffer_;
  }

  // Move out the buffer.
  [[nodiscard]] auto take_buffer() -> std::vector<std::byte> {
    return std::move(buffer_);
  }

private:
  std::vector<std::byte> buffer_;
};

// Simple binary reader for deserialization.
class binary_reader final {
public:
  explicit binary_reader(std::span<const std::byte> data) noexcept
      : data_(data), pos_(0) {}

  binary_reader(const void* data, std::size_t size) noexcept
      : data_(static_cast<const std::byte*>(data), size), pos_(0) {}

  // Check if there are enough bytes remaining.
  [[nodiscard]] auto can_read(std::size_t bytes) const noexcept -> bool {
    return pos_ + bytes <= data_.size();
  }

  [[nodiscard]] auto remaining() const noexcept -> std::size_t {
    return data_.size() - pos_;
  }

  [[nodiscard]] auto position() const noexcept -> std::size_t {
    return pos_;
  }

  [[nodiscard]] auto at_end() const noexcept -> bool {
    return pos_ >= data_.size();
  }

  // Read raw bytes.
  [[nodiscard]] auto try_read_bytes(void* out, std::size_t size) noexcept -> bool {
    if (!can_read(size)) return false;
    std::memcpy(out, data_.data() + pos_, size);
    pos_ += size;
    return true;
  }

  // Read a trivially copyable value.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto try_read(T& out) noexcept -> bool {
    return try_read_bytes(&out, sizeof(T));
  }

  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto read() -> T {
    T value{};
    S4_CHECK(try_read(value), "Failed to read value from binary stream");
    return value;
  }

  // Read with explicit size check.
  template <typename T, std::size_t ExpectedSize>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto read_fixed() -> T {
    static_assert(sizeof(T) == ExpectedSize, "Size mismatch in fixed-size read");
    return read<T>();
  }

  // Read a length-prefixed string.
  [[nodiscard]] auto try_read_string(std::string& out) -> bool {
    std::uint32_t length = 0;
    if (!try_read(length)) return false;
    if (!can_read(length)) return false;
    
    out.assign(reinterpret_cast<const char*>(data_.data() + pos_), length);
    pos_ += length;
    return true;
  }

  [[nodiscard]] auto read_string() -> std::string {
    std::string result;
    S4_CHECK(try_read_string(result), "Failed to read string from binary stream");
    return result;
  }

  // Read a length-prefixed vector.
  // Guards against overflow when computing byte count.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto try_read_vector(std::vector<T>& out) -> bool {
    std::uint32_t count = 0;
    if (!try_read(count)) return false;
    
    // Guard against overflow: count * sizeof(T) must fit in size_t.
    constexpr std::size_t max_elements = 
        std::numeric_limits<std::size_t>::max() / sizeof(T);
    if (count > max_elements) return false;
    
    const std::size_t byte_count = static_cast<std::size_t>(count) * sizeof(T);
    if (!can_read(byte_count)) return false;
    
    out.resize(count);
    std::memcpy(out.data(), data_.data() + pos_, byte_count);
    pos_ += byte_count;
    return true;
  }

  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto read_vector() -> std::vector<T> {
    std::vector<T> result;
    S4_CHECK(try_read_vector(result), "Failed to read vector from binary stream");
    return result;
  }

  // Read an optional value.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto try_read_optional(std::optional<T>& out) -> bool {
    std::uint8_t present = 0;
    if (!try_read(present)) return false;
    
    if (present != 0) {
      T value{};
      if (!try_read(value)) return false;
      out = value;
    } else {
      out = std::nullopt;
    }
    return true;
  }

  // Read float from uint32 bits.
  [[nodiscard]] auto read_float_bits() -> float {
    std::uint32_t bits = read<std::uint32_t>();
    float value;
    std::memcpy(&value, &bits, sizeof(float));
    return value;
  }

  // Read double from uint64 bits.
  [[nodiscard]] auto read_double_bits() -> double {
    std::uint64_t bits = read<std::uint64_t>();
    double value;
    std::memcpy(&value, &bits, sizeof(double));
    return value;
  }

  // Skip bytes.
  [[nodiscard]] auto try_skip(std::size_t bytes) noexcept -> bool {
    if (!can_read(bytes)) return false;
    pos_ += bytes;
    return true;
  }

  // Peek without advancing.
  template <typename T>
    requires std::is_trivially_copyable_v<T>
  [[nodiscard]] auto try_peek(T& out) const noexcept -> bool {
    if (!can_read(sizeof(T))) return false;
    std::memcpy(&out, data_.data() + pos_, sizeof(T));
    return true;
  }

private:
  std::span<const std::byte> data_;
  std::size_t pos_;
};

// Helper to create versioned serialized data.
struct versioned_header final {
  std::uint32_t magic = serialization_magic;
  std::uint32_t version = 0;
  std::uint32_t payload_size = 0;
  std::uint32_t reserved = 0;
};

static_assert(sizeof(versioned_header) == 16, "Header must be 16 bytes");

inline auto write_versioned_header(
    binary_writer& writer, std::uint32_t version, std::uint32_t payload_size) 
    -> void {
  writer.write(versioned_header{
    .magic = serialization_magic,
    .version = version,
    .payload_size = payload_size,
    .reserved = 0,
  });
}

[[nodiscard]] inline auto read_versioned_header(binary_reader& reader)
    -> std::optional<versioned_header> {
  versioned_header header{};
  if (!reader.try_read(header)) return std::nullopt;
  if (header.magic != serialization_magic) return std::nullopt;
  return header;
}

}  // namespace s4::core
