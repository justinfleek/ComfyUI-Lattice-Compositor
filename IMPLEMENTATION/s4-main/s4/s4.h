// s4 // s4.h
// Main include header for s4 library (core components only).
// CUDA components require separate includes: <s4/cuda/nvfp4/nvfp4.h>, etc.
#pragma once

// Core utilities.
#include <s4/core/exceptions.h>
#include <s4/core/generator.h>
#include <s4/core/hash.h>
#include <s4/core/serialize.h>
#include <s4/core/workspace.h>

// Type system.
#include <s4/dtypes/dtype.h>
#include <s4/dtypes/dispatch.h>

// Container types.
#include <s4/containers/unique_vector.h>
#include <s4/containers/disjoint_sets.h>

// Tensor views.
#include <s4/tensor/view.h>

// Type traits and concepts.
#include <s4/traits/traits.h>

// Library version.
namespace s4 {

inline constexpr int version_major = 0;
inline constexpr int version_minor = 1;
inline constexpr int version_patch = 0;

[[nodiscard]] inline constexpr auto version_string() noexcept -> const char* {
  return "0.1.0";
}

}  // namespace s4
