// s4 // dtypes/cuda_types.h
#pragma once

#include <cuda_bf16.h>
#include <cuda_fp16.h>

namespace s4::dtypes {

// Explicit CUDA type aliases.
// Keep these “leaf-level” and avoid leaking CUDA types into higher-level APIs.

using float16 = __half;
using bfloat16 = __nv_bfloat16;

}  // namespace s4::dtypes
