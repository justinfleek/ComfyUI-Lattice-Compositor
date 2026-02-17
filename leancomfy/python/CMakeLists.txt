cmake_minimum_required(VERSION 3.18)
project(tensor_core_py)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find nanobind
find_package(Python COMPONENTS Interpreter Development.Module REQUIRED)
execute_process(
    COMMAND ${Python_EXECUTABLE} -m nanobind --cmake_dir
    OUTPUT_VARIABLE nanobind_DIR
    OUTPUT_STRIP_TRAILING_WHITESPACE
)
find_package(nanobind CONFIG REQUIRED)

# C library paths - can be overridden for Nix builds
set(C_SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../c" CACHE PATH "Path to C source directory")
set(C_INCLUDE_DIR "${C_SRC_DIR}/include" CACHE PATH "Path to C headers")

# Build the C library
add_library(tensor_core_c STATIC
    ${C_SRC_DIR}/src/tensor_core.c
)
target_include_directories(tensor_core_c PUBLIC
    ${C_INCLUDE_DIR}
)

# Build Python module
nanobind_add_module(tensor_core
    tensor_core_py.cpp
)
target_link_libraries(tensor_core PRIVATE tensor_core_c)
target_include_directories(tensor_core PRIVATE
    ${C_INCLUDE_DIR}
)

# Install
install(TARGETS tensor_core LIBRARY DESTINATION .)
