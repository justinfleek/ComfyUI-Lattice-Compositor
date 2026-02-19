// s4-runtime // tensor/view.h
// Non-owning tensor views for GPU data.
// Framework-independent view types for interoperability.
#pragma once

#include <s4/dtypes/dtype.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace s4::tensor {

// Maximum supported tensor rank.
inline constexpr std::size_t max_rank = 8;

// 1D tensor view (contiguous or strided).
struct view_1d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t count = 0;
  std::int64_t stride = 0;  // In elements, not bytes.

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           count >= 0 && stride >= 0;
  }

  [[nodiscard]] constexpr auto is_contiguous() const noexcept -> bool {
    return stride == 1;
  }

  [[nodiscard]] constexpr auto size_bytes() const noexcept -> std::size_t {
    std::size_t bytes = 0;
    dtypes::try_compute_storage_bytes(dtype, static_cast<std::size_t>(count), &bytes);
    return bytes;
  }
};

// Mutable 1D tensor view.
struct mutable_view_1d final {
  void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t count = 0;
  std::int64_t stride = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           count >= 0 && stride >= 0;
  }

  [[nodiscard]] constexpr auto is_contiguous() const noexcept -> bool {
    return stride == 1;
  }

  [[nodiscard]] constexpr auto as_const() const noexcept -> view_1d {
    return {data, dtype, count, stride};
  }
};

// 2D tensor view (row-major layout).
struct view_2d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t rows = 0;
  std::int64_t cols = 0;
  std::int64_t row_stride = 0;  // In elements.

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           rows >= 0 && cols >= 0 && row_stride >= 0;
  }

  [[nodiscard]] constexpr auto is_contiguous() const noexcept -> bool {
    return row_stride == cols;
  }

  [[nodiscard]] constexpr auto element_count() const noexcept -> std::int64_t {
    return rows * cols;
  }

  [[nodiscard]] constexpr auto size_bytes() const noexcept -> std::size_t {
    std::size_t bytes = 0;
    dtypes::try_compute_storage_bytes(
        dtype, static_cast<std::size_t>(rows * row_stride), &bytes);
    return bytes;
  }
};

// Mutable 2D tensor view.
struct mutable_view_2d final {
  void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t rows = 0;
  std::int64_t cols = 0;
  std::int64_t row_stride = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           rows >= 0 && cols >= 0 && row_stride >= 0;
  }

  [[nodiscard]] constexpr auto is_contiguous() const noexcept -> bool {
    return row_stride == cols;
  }

  [[nodiscard]] constexpr auto as_const() const noexcept -> view_2d {
    return {data, dtype, rows, cols, row_stride};
  }
};

// Packed 2D tensor view (for sub-byte types like FP4).
// Uses byte strides since element stride doesn't apply cleanly.
struct packed_view_2d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t rows = 0;
  std::int64_t logical_cols = 0;  // Number of logical elements per row.
  std::int64_t row_stride_bytes = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           dtypes::is_packed(dtype) &&
           rows >= 0 && logical_cols >= 0 && row_stride_bytes >= 0;
  }
};

// Mutable packed 2D tensor view.
struct mutable_packed_view_2d final {
  void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::int64_t rows = 0;
  std::int64_t logical_cols = 0;
  std::int64_t row_stride_bytes = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype != dtypes::dtype_code::invalid &&
           dtypes::is_packed(dtype) &&
           rows >= 0 && logical_cols >= 0 && row_stride_bytes >= 0;
  }

  [[nodiscard]] constexpr auto as_const() const noexcept -> packed_view_2d {
    return {data, dtype, rows, logical_cols, row_stride_bytes};
  }
};

// N-dimensional tensor view with dynamic rank.
struct view_nd final {
  const void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::size_t rank = 0;
  std::array<std::int64_t, max_rank> shape{};
  std::array<std::int64_t, max_rank> strides{};  // In elements.

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    if (data == nullptr || dtype == dtypes::dtype_code::invalid) return false;
    if (rank > max_rank) return false;
    for (std::size_t i = 0; i < rank; ++i) {
      if (shape[i] < 0 || strides[i] < 0) return false;
    }
    return true;
  }

  [[nodiscard]] constexpr auto element_count() const noexcept -> std::int64_t {
    std::int64_t count = 1;
    for (std::size_t i = 0; i < rank; ++i) {
      count *= shape[i];
    }
    return count;
  }

  // Create a 1D view if rank == 1.
  [[nodiscard]] constexpr auto as_1d() const noexcept -> view_1d {
    if (rank != 1) return {};
    return {data, dtype, shape[0], strides[0]};
  }

  // Create a 2D view if rank == 2.
  [[nodiscard]] constexpr auto as_2d() const noexcept -> view_2d {
    if (rank != 2) return {};
    return {data, dtype, shape[0], shape[1], strides[0]};
  }
};

// Mutable N-dimensional tensor view.
struct mutable_view_nd final {
  void* data = nullptr;
  dtypes::dtype_code dtype = dtypes::dtype_code::invalid;
  std::size_t rank = 0;
  std::array<std::int64_t, max_rank> shape{};
  std::array<std::int64_t, max_rank> strides{};

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    if (data == nullptr || dtype == dtypes::dtype_code::invalid) return false;
    if (rank > max_rank) return false;
    for (std::size_t i = 0; i < rank; ++i) {
      if (shape[i] < 0 || strides[i] < 0) return false;
    }
    return true;
  }

  [[nodiscard]] constexpr auto as_const() const noexcept -> view_nd {
    view_nd result{data, dtype, rank, {}, {}};
    result.shape = shape;
    result.strides = strides;
    return result;
  }
};

// Helper to compute row-major strides from shape.
constexpr auto compute_row_major_strides(
    std::span<const std::int64_t> shape,
    std::span<std::int64_t> strides) noexcept -> void {
  if (shape.empty()) return;
  
  std::int64_t running = 1;
  for (std::size_t i = shape.size(); i-- > 0;) {
    strides[i] = running;
    running *= shape[i];
  }
}

// Helper to compute column-major strides from shape.
constexpr auto compute_column_major_strides(
    std::span<const std::int64_t> shape,
    std::span<std::int64_t> strides) noexcept -> void {
  if (shape.empty()) return;
  
  std::int64_t running = 1;
  for (std::size_t i = 0; i < shape.size(); ++i) {
    strides[i] = running;
    running *= shape[i];
  }
}

// Helper to check if strides represent contiguous row-major layout.
[[nodiscard]] constexpr auto is_row_major_contiguous(
    std::span<const std::int64_t> shape,
    std::span<const std::int64_t> strides) noexcept -> bool {
  if (shape.size() != strides.size()) return false;
  if (shape.empty()) return true;
  
  std::int64_t expected = 1;
  for (std::size_t i = shape.size(); i-- > 0;) {
    if (strides[i] != expected) return false;
    expected *= shape[i];
  }
  return true;
}

// Backwards-compatible aliases for s4-tensorrt tensor view types.
// These use the original naming conventions.
struct tensor_view_1d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t element_count = 0;
  std::int64_t stride_elements = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           element_count >= 0 && stride_elements >= 0;
  }
};

struct mutable_tensor_view_1d final {
  void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t element_count = 0;
  std::int64_t stride_elements = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           element_count >= 0 && stride_elements >= 0;
  }
};

struct tensor_view_2d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t row_count = 0;
  std::int64_t column_count_elements = 0;
  std::int64_t row_stride_elements = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           row_count >= 0 && column_count_elements >= 0 &&
           row_stride_elements >= 0;
  }
};

struct mutable_tensor_view_2d final {
  void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t row_count = 0;
  std::int64_t column_count_elements = 0;
  std::int64_t row_stride_elements = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           row_count >= 0 && column_count_elements >= 0 &&
           row_stride_elements >= 0;
  }
};

struct packed_tensor_view_2d final {
  void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t row_count = 0;
  std::int64_t column_count_logical_elements = 0;
  std::int64_t row_stride_storage_bytes = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           row_count >= 0 && column_count_logical_elements >= 0 &&
           row_stride_storage_bytes >= 0;
  }
};

struct const_packed_tensor_view_2d final {
  const void* data = nullptr;
  dtypes::dtype_code dtype_code = dtypes::dtype_code::invalid;
  std::int64_t row_count = 0;
  std::int64_t column_count_logical_elements = 0;
  std::int64_t row_stride_storage_bytes = 0;

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return data != nullptr && dtype_code != dtypes::dtype_code::invalid &&
           row_count >= 0 && column_count_logical_elements >= 0 &&
           row_stride_storage_bytes >= 0;
  }
};

}  // namespace s4::tensor
