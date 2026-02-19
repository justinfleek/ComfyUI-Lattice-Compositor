// s4 // trt/trt_dtypes.h
#pragma once

#include <s4/dtypes/dtype.h>

#include <NvInferRuntimeBase.h>

#include <cstddef>
#include <cstdint>

namespace s4::trt {

[[nodiscard]] inline auto
try_get_dtype_code_from_trt(nvinfer1::DataType trt_dtype,
                            s4::dtypes::dtype_code *out_dtype_code) noexcept
    -> bool {
  if (out_dtype_code == nullptr) {
    return false;
  }

  switch (trt_dtype) {
  case nvinfer1::DataType::kFLOAT:
    *out_dtype_code = s4::dtypes::dtype_code::float32;
    return true;

  case nvinfer1::DataType::kHALF:
    *out_dtype_code = s4::dtypes::dtype_code::float16;
    return true;

  case nvinfer1::DataType::kBF16:
    *out_dtype_code = s4::dtypes::dtype_code::bfloat16;
    return true;

  default:
    *out_dtype_code = s4::dtypes::dtype_code::invalid;
    return false;
  }
}

[[nodiscard]] inline auto try_get_element_size_bytes_from_trt(
    nvinfer1::DataType trt_dtype, std::size_t *out_element_size_bytes) noexcept
    -> bool {

  if (out_element_size_bytes == nullptr) {
    return false;
  }

  s4::dtypes::dtype_code dtype_code = s4::dtypes::dtype_code::invalid;
  if (!try_get_dtype_code_from_trt(trt_dtype, &dtype_code)) {
    return false;
  }

  const std::size_t element_size_bytes =
      s4::dtypes::dtype_storage_size_bytes(dtype_code);
  if (element_size_bytes == 0) {
    return false;
  }

  *out_element_size_bytes = element_size_bytes;
  return true;
}

[[nodiscard]] inline auto
try_compute_volume_elements(const nvinfer1::Dims &dims,
                            std::size_t *out_volume_elements) noexcept -> bool {

  if (out_volume_elements == nullptr) {
    return false;
  }

  std::size_t volume = 1;

  for (int axis = 0; axis < dims.nbDims; ++axis) {
    const int dim_value = dims.d[axis];
    if (dim_value < 0) {
      return false;
    }

    const std::size_t dim_value_size = static_cast<std::size_t>(dim_value);
    if (dim_value_size == 0) {
      volume = 0;
      break;
    }

    const std::size_t max_safe = static_cast<std::size_t>(-1) / dim_value_size;
    if (volume > max_safe) {
      return false;
    }

    volume *= dim_value_size;
  }

  *out_volume_elements = volume;
  return true;
}

} // namespace s4::trt
