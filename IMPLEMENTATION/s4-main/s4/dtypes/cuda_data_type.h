// s4 // dtypes/cuda_data_type.h
#pragma once

#include <s4/dtypes/dtype.h>

#include <cuda_runtime.h>

namespace s4::dtypes {

// Conversion between dtype_code and cudaDataType is a *leaf* concern.
// It should not appear in quantization problem structs or generic tensor views.

[[nodiscard]] inline auto try_get_cuda_data_type_from_dtype_code(
    dtype_code code,
    cudaDataType* out_cuda_data_type) noexcept -> bool
{
    if (out_cuda_data_type == nullptr) {
        return false;
    }

    switch (code) {
        case dtype_code::float16:
            *out_cuda_data_type = CUDA_R_16F;
            return true;

        case dtype_code::bfloat16:
            *out_cuda_data_type = CUDA_R_16BF;
            return true;

        case dtype_code::float32:
            *out_cuda_data_type = CUDA_R_32F;
            return true;

        default:
            return false;
    }
}

}  // namespace s4::dtypes
