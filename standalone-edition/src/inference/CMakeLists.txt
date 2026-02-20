cmake_minimum_required(VERSION 3.26)
project(lattice-inference LANGUAGES CXX CUDA)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CUDA_STANDARD 17)
set(CMAKE_CUDA_STANDARD_REQUIRED ON)

# Find packages
find_package(CUDAToolkit 12.0 REQUIRED)
find_package(TensorRT REQUIRED)

# Sources
set(INFERENCE_SOURCES
    src/safetensors.cpp
    src/tensorrt_engine.cpp
    src/scheduler.cpp
    src/server.cpp
    src/ffi_glue.cpp
)

# Library
add_library(lattice-inference STATIC ${INFERENCE_SOURCES})

target_include_directories(lattice-inference PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CUDAToolkit_INCLUDE_DIRS}
    ${TensorRT_INCLUDE_DIRS}
)

target_link_libraries(lattice-inference PUBLIC
    CUDA::cudart
    CUDA::cublas
    ${TensorRT_LIBRARIES}
    nvinfer
    nvinfer_plugin
    nvonnxparser
)

# Executable
add_executable(diffusion-server src/main.cpp)
target_link_libraries(diffusion-server PRIVATE lattice-inference)
