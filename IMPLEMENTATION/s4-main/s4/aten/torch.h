// s4 // aten/torch.h
#pragma once

#include <ATen/cuda/CUDAContext.h>
#include <torch/extension.h>

#include <cuda_runtime.h>

#include <s4/dtypes/cuda_data_type.h>
#include <s4/dtypes/dtype.h>

namespace s4::aten {

inline auto require_cuda(const at::Tensor &tensor, const char *tensor_name)
    -> void {
  TORCH_CHECK(tensor.is_cuda(), tensor_name, " must be a CUDA tensor");
}

inline auto require_contiguous_last_dim(const at::Tensor &tensor,
                                        const char *tensor_name) -> void {
  TORCH_CHECK(tensor.stride(-1) == 1, tensor_name,
              " must be contiguous in the last dimension");
}

inline auto dtype_code_from_scalar_type(at::ScalarType scalar_type)
    -> s4::dtypes::dtype_code {
  switch (scalar_type) {
  case at::ScalarType::Half:
    return s4::dtypes::dtype_code::float16;
  case at::ScalarType::BFloat16:
    return s4::dtypes::dtype_code::bfloat16;
  case at::ScalarType::Float:
    return s4::dtypes::dtype_code::float32;
  case at::ScalarType::Float8_e4m3fn:
    return s4::dtypes::dtype_code::float8_e4m3;
  default:
    break;
  }
  TORCH_CHECK(false, "Unsupported dtype for s4::dtypes dispatch: ",
              static_cast<int>(scalar_type));
  return s4::dtypes::dtype_code::invalid;
}

inline auto to_cuda_data_type(at::ScalarType scalar_type) -> cudaDataType {
  const s4::dtypes::dtype_code code = dtype_code_from_scalar_type(scalar_type);
  cudaDataType cuda_type = CUDA_R_32F;

  const bool ok =
      s4::dtypes::try_get_cuda_data_type_from_dtype_code(code, &cuda_type);
  TORCH_CHECK(ok, "Unsupported dtype for cudaDataType dispatch: ",
              static_cast<int>(scalar_type));
  return cuda_type;
}

inline auto current_stream_for_tensor(const at::Tensor &tensor)
    -> cudaStream_t {
  return at::cuda::getDefaultCUDAStream(tensor.get_device());
}

} // namespace s4::aten
