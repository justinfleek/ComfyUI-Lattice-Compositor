// s4 // cuda/cccl_standard.h
#pragma once

#include <cuda/std/array>
#include <cuda/std/bit>
#include <cuda/std/cstddef>
#include <cuda/std/cstdint>
#include <cuda/std/mdspan>
#include <cuda/std/span>
#include <cuda/std/type_traits>

namespace s4::cccl {

// Alias “standards-track” CCCL facilities behind a stable include path.

namespace stdgpu = cuda::std;

template <typename element_type, int rank>
using dextents = cuda::std::dextents<int, rank>;

template <typename element_type>
using mdspan_2d = cuda::std::mdspan<element_type, dextents<element_type, 2>,
                                    cuda::std::layout_right>;

template <typename element_type>
using mdspan_3d = cuda::std::mdspan<element_type, dextents<element_type, 3>,
                                    cuda::std::layout_right>;

template <typename element_type>
using mdspan_4d = cuda::std::mdspan<element_type, dextents<element_type, 4>,
                                    cuda::std::layout_right>;

} // namespace s4::cccl
