"""CUDA build macros for s4 with C++23 support.

Provides macros for building CUDA libraries with consistent compiler flags
for both host and device code. Targets Ampere through Blackwell architectures.
"""

load("@rules_cuda//cuda:defs.bzl", "cuda_library")

# Default CUDA compilation options for C++23.
S4_CUDA_COMPILER_OPTIONS = [
    "-std=c++23",
    "--expt-relaxed-constexpr",
    "--extended-lambda",
    "-Xcompiler=-std=c++23",
]

# Optimized CUDA options for release builds.
S4_CUDA_RELEASE_COMPILER_OPTIONS = S4_CUDA_COMPILER_OPTIONS + [
    "-O3",
    "--use_fast_math",
    "-lineinfo",
    "-Xptxas=-v",  # Show register usage.
]

# Debug CUDA options with device debug info.
S4_CUDA_DEBUG_COMPILER_OPTIONS = S4_CUDA_COMPILER_OPTIONS + [
    "-O0",
    "-g",
    "-G",  # Device debug info.
]

# Target architectures: Ampere, Ada, Hopper.
# Blackwell (SM100) requires --config=blackwell.
S4_CUDA_TARGET_ARCHITECTURES = [
    "sm_80",   # Ampere (A100).
    "sm_86",   # Ampere (RTX 3090).
    "sm_89",   # Ada Lovelace (RTX 4090).
    "sm_90",   # Hopper (H100).
]

def s4_cuda_library(
        name,
        source_files = [],
        header_files = [],
        dependencies = [],
        compiler_options = [],
        linker_options = [],
        **additional_arguments):
    """CUDA library with s4 defaults for C++23.

    Wraps cuda_library with standard compiler flags for host and device code.

    Args:
        name: Target name.
        source_files: CUDA source files (.cu).
        header_files: Header files (.h, .cuh).
        dependencies: Library dependencies.
        compiler_options: Additional compiler options.
        linker_options: Additional linker options.
        **additional_arguments: Additional arguments passed to cuda_library.
    """
    cuda_library(
        name = name,
        srcs = source_files,
        hdrs = header_files,
        deps = dependencies,
        copts = S4_CUDA_COMPILER_OPTIONS + compiler_options,
        linkopts = linker_options,
        **additional_arguments
    )

def s4_cuda_kernel_library(
        name,
        source_files = [],
        header_files = [],
        dependencies = [],
        compiler_options = [],
        **additional_arguments):
    """CUDA kernel library optimized for maximum performance.

    Use this for performance-critical kernels (NVFP4 quantization, attention).
    Includes aggressive optimization flags and fast math.

    Args:
        name: Target name.
        source_files: CUDA source files (.cu).
        header_files: Header files (.h, .cuh).
        dependencies: Library dependencies.
        compiler_options: Additional compiler options.
        **additional_arguments: Additional arguments passed to cuda_library.
    """
    cuda_library(
        name = name,
        srcs = source_files,
        hdrs = header_files,
        deps = dependencies,
        copts = S4_CUDA_RELEASE_COMPILER_OPTIONS + compiler_options,
        **additional_arguments
    )

def s4_cuda_test(
        name,
        source_files,
        dependencies = [],
        **additional_arguments):
    """CUDA test with s4 defaults.

    Creates a cuda_library for the test code and links it with Catch2.

    Args:
        name: Target name.
        source_files: Test source files.
        dependencies: Library dependencies.
        **additional_arguments: Additional arguments.
    """
    cuda_library(
        name = name + "_library",
        srcs = source_files,
        deps = dependencies,
        copts = S4_CUDA_COMPILER_OPTIONS,
        testonly = True,
    )

    native.cc_test(
        name = name,
        deps = [
            ":" + name + "_library",
            "@catch2//:catch2_main",
        ],
        **additional_arguments
    )

