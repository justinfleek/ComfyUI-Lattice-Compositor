"""Common build definitions for s4.

Provides macros for building C++ libraries and tests with consistent
compiler flags and dependency patterns across the codebase.
"""

load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")

# C++23 compilation options for host code.
S4_HOST_COMPILER_OPTIONS = [
    "-std=c++23",
    "-Wall",
    "-Wextra",
    "-Wpedantic",
    "-Wno-unused-parameter",
]

# Release-optimized compilation options.
S4_RELEASE_COMPILER_OPTIONS = S4_HOST_COMPILER_OPTIONS + [
    "-O3",
    "-DNDEBUG",
    "-march=native",
]

# Debug compilation options with full symbols.
S4_DEBUG_COMPILER_OPTIONS = S4_HOST_COMPILER_OPTIONS + [
    "-O0",
    "-g",
    "-fno-omit-frame-pointer",
]

def s4_cc_library(
        name,
        source_files = [],
        header_files = [],
        dependencies = [],
        compiler_options = [],
        **additional_arguments):
    """C++ library with s4 defaults for C++23.

    Wraps cc_library with standard compiler flags and naming conventions.

    Args:
        name: Target name.
        source_files: Source files (.cpp).
        header_files: Header files (.h).
        dependencies: Library dependencies.
        compiler_options: Additional compiler options.
        **additional_arguments: Additional arguments passed to cc_library.
    """
    cc_library(
        name = name,
        srcs = source_files,
        hdrs = header_files,
        deps = dependencies,
        copts = S4_HOST_COMPILER_OPTIONS + compiler_options,
        **additional_arguments
    )

def s4_cc_test(
        name,
        source_files,
        dependencies = [],
        compiler_options = [],
        **additional_arguments):
    """C++ unit test with s4 defaults.

    Automatically links Catch2 test framework.

    Args:
        name: Target name.
        source_files: Test source files.
        dependencies: Library dependencies.
        compiler_options: Additional compiler options.
        **additional_arguments: Additional arguments.
    """
    cc_test(
        name = name,
        srcs = source_files,
        deps = dependencies + ["@catch2//:catch2_main"],
        copts = S4_HOST_COMPILER_OPTIONS + compiler_options,
        **additional_arguments
    )

def s4_property_test(
        name,
        source_files,
        dependencies = [],
        **additional_arguments):
    """Property-based test with RapidCheck.

    Automatically links Catch2 and RapidCheck frameworks.

    Args:
        name: Target name.
        source_files: Test source files.
        dependencies: Library dependencies.
        **additional_arguments: Additional arguments.
    """
    cc_test(
        name = name,
        srcs = source_files,
        deps = dependencies + [
            "@catch2//:catch2_main",
            "@rapidcheck",
        ],
        copts = S4_HOST_COMPILER_OPTIONS,
        **additional_arguments
    )

def s4_benchmark(
        name,
        source_files,
        dependencies = [],
        **additional_arguments):
    """Benchmark target with release optimizations.

    Tagged as "benchmark" for selective execution.

    Args:
        name: Target name.
        source_files: Benchmark source files.
        dependencies: Library dependencies.
        **additional_arguments: Additional arguments.
    """
    cc_test(
        name = name,
        srcs = source_files,
        deps = dependencies,
        copts = S4_RELEASE_COMPILER_OPTIONS,
        tags = ["benchmark"],
        **additional_arguments
    )

