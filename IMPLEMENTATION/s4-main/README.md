# s4

GPU inference runtime for NVFP4 quantization and SageAttention.

C++23 for host and device code. Bazel build system.

## Features

### Core (Header-only)

- **Type System** (`s4::dtypes`): Stable, serializable dtype vocabulary with packed formats (NVFP4, FP8).
- **Containers** (`s4::containers`): `unique_vector` (set-backed, O(1) lookup), `disjoint_sets`.
- **Utilities** (`s4::core`): Exception handling with backtrace, workspace allocators, binary serialization, generators.
- **Tensor Views** (`s4::tensor`): Non-owning tensor views for framework-independent data access.
- **Type Traits** (`s4::traits`): Concepts and traits for GPU-safe types.

### CUDA Components

- **NVFP4 Quantization** (`s4::cuda::nvfp4`): Hardware-accelerated FP4 quantization with E2M1 format (Blackwell SM100+).
- **Attention Kernels** (`s4::attention`): Mean centering, score correction for SageAttention.
- **TensorRT Plugins**: SageAttention FP4 plugin.

## Building

Requires Bazel 7.0+ and CUDA 12.4+ for device code.

### Core Library (Host-only)

```bash
bazel build //:s4_core
bazel test //...
```

### With CUDA Components

```bash
bazel build //src/cuda:nvfp4 --config=release
bazel build //src/attention:attention --config=release
```

### Build Configurations

| Configuration | Description |
|---------------|-------------|
| `--config=release` | Optimized build (-O3, fast math) |
| `--config=debug` | Debug symbols, no optimization |
| `--config=asan` | AddressSanitizer enabled |
| `--config=tsan` | ThreadSanitizer enabled |
| `--config=blackwell` | Blackwell SM100 only |
| `--config=fast` | Fast iteration (SM89 only) |

### Target Architectures

Default: SM80 (Ampere), SM86, SM89 (Ada), SM90 (Hopper), SM100 (Blackwell).

## Quick Example

### C++

```cpp
#include <s4/s4.h>
#include <iostream>

int main() {
    // Dtype system.
    s4::dtypes::dtype_descriptor const descriptor = 
        s4::dtypes::describe(s4::dtypes::dtype_code::float16);
    std::cout << "float16: " << descriptor.storage_size_bytes << " bytes\n";
    
    // Unique vector: set-backed, maintains insertion order.
    s4::containers::unique_vector<int> unique_integers;
    unique_integers.push_back(1);
    unique_integers.push_back(2);
    unique_integers.push_back(1);  // Ignored: already exists.
    std::cout << "Size: " << unique_integers.size() << "\n";  // 2
    
    // Disjoint sets.
    s4::containers::disjoint_sets<int> equivalence_classes;
    equivalence_classes.map_entries(1, 2);  // 1 and 2 are equivalent.
    equivalence_classes.map_entries(2, 3);  // 1, 2, 3 are equivalent.
    std::cout << "1~3: " << equivalence_classes.permissive_are_mapped(1, 3) << "\n";
    
    // Generator: lazy iteration.
    for (std::int64_t index : s4::core::iota(5)) {
        std::cout << index << " ";
    }
    std::cout << "\n";  // 0 1 2 3 4
    
    return 0;
}
```

### CUDA (NVFP4 Quantization)

```cpp
#include <s4/cuda/nvfp4/nvfp4.h>

// Quantize attention tensors to FP4.
s4_launch_fp4_quantize_query(
    query_input,
    query_packed_output,
    query_scale_factors,
    batch_size,
    head_count,
    sequence_length,
    head_dimension,
    cuda_stream);
```

## Directory Structure

```
s4/
├── BUILD.bazel             # Root build file
├── MODULE.bazel            # Bzlmod dependencies
├── .bazelrc                # Build configuration
├── bazel/
│   ├── defs.bzl            # Host code macros
│   └── cuda.bzl            # CUDA code macros
├── include/s4/
│   ├── core/               # exceptions, generator, serialize, workspace
│   ├── dtypes/             # dtype vocabulary
│   ├── containers/         # unique_vector, disjoint_sets
│   ├── tensor/             # tensor views
│   ├── traits/             # type traits
│   ├── cuda/nvfp4/         # NVFP4 quantization
│   └── attention/          # SageAttention kernels
├── src/
│   ├── exceptions.cpp
│   ├── cuda/               # NVFP4 kernels
│   └── attention/          # Attention kernels
├── tests/
│   ├── unit/               # Catch2 tests
│   ├── property/           # RapidCheck property tests
│   └── python/             # Hypothesis tests
└── bindings/python/        # pybind11 bindings
```

## Testing

### C++ Tests

```bash
bazel test //...
bazel test //:test_dtypes //:test_containers //:test_core
bazel test //:test_properties  # Property-based tests
```

### Python Tests

```bash
pip install pytest hypothesis
pip install -e .  # Build and install wheel via CMake/scikit-build
pytest tests/python -v
```

## Design Principles

1. **Explicit types over auto**: Disambiguation beats brevity.
2. **Fully qualified names**: No `using namespace`, absolute clarity.
3. **C++23 maximally**: Modern constructs throughout.
4. **Framework independence**: No PyTorch/TensorFlow dependencies in core.
5. **Serialization stability**: Explicit `dtype_code` values for cross-version compatibility.

## License

MIT License
