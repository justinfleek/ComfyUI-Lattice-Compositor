# s4: GPU inference runtime.
# CMake build for Python wheel (scikit-build-core).
# Primary build system is Bazel; CMake is for pip install only.
cmake_minimum_required(VERSION 3.21)
project(s4 VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Options.
option(S4_BUILD_TESTS "Build C++ tests" OFF)
option(S4_BUILD_PYTHON "Build Python bindings" ON)

# Core library (implementation).
add_library(s4_implementation STATIC
    src/exceptions.cpp
)
target_include_directories(s4_implementation PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)
target_compile_features(s4_implementation PUBLIC cxx_std_23)

# Python bindings.
if(S4_BUILD_PYTHON)
    find_package(Python3 COMPONENTS Interpreter Development REQUIRED)
    find_package(pybind11 CONFIG REQUIRED)

    pybind11_add_module(_s4_runtime
        bindings/python/module.cpp
        bindings/python/dtype_bindings.cpp
        bindings/python/containers_bindings.cpp
        bindings/python/core_bindings.cpp
    )
    target_link_libraries(_s4_runtime PRIVATE s4_implementation)
    target_compile_features(_s4_runtime PRIVATE cxx_std_23)

    # Install into Python package directory.
    install(TARGETS _s4_runtime
        LIBRARY DESTINATION s4_runtime
    )
endif()

# Tests (off by default for wheel builds).
if(S4_BUILD_TESTS)
    enable_testing()
    include(FetchContent)

    FetchContent_Declare(
        Catch2
        GIT_REPOSITORY https://github.com/catchorg/Catch2.git
        GIT_TAG v3.5.4
    )
    FetchContent_MakeAvailable(Catch2)

    add_executable(test_dtypes tests/unit/test_dtype.cpp)
    target_link_libraries(test_dtypes PRIVATE s4_implementation Catch2::Catch2WithMain)
    add_test(NAME test_dtypes COMMAND test_dtypes)

    add_executable(test_containers tests/unit/test_containers.cpp)
    target_link_libraries(test_containers PRIVATE s4_implementation Catch2::Catch2WithMain)
    add_test(NAME test_containers COMMAND test_containers)

    add_executable(test_core tests/unit/test_core.cpp)
    target_link_libraries(test_core PRIVATE s4_implementation Catch2::Catch2WithMain)
    add_test(NAME test_core COMMAND test_core)

    add_executable(test_generator tests/unit/test_generator.cpp)
    target_link_libraries(test_generator PRIVATE s4_implementation Catch2::Catch2WithMain)
    add_test(NAME test_generator COMMAND test_generator)
endif()
