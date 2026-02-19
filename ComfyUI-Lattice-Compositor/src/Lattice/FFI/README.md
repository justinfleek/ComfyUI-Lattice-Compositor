# Lattice FFI - Python-Haskell Interop

Python bindings for Haskell pure functions via C FFI.

## Overview

This module provides Python wrappers for Haskell functions migrated from Python code. Functions are called via C FFI bindings to a shared Haskell library (`liblattice-ffi.so`).

## Quick Start

```python
from lattice.ffi import frame_interpolation

# Simple function call
factor = frame_interpolation.slowdown_to_factor(2.5)
print(factor)  # Output: 2

# Complex function with validation
result = frame_interpolation.validate_interpolation_params(
    model_name="rife-v4.6",
    factor=2,
    ensemble=False,
    slowdown=2.0
)

if result["status"] == "success":
    params = result["params"]
    print(f"Validated: {params}")
else:
    print(f"Error: {result['message']}")
```

## Installation

### Prerequisites

1. **Nix** (for building the shared library)
2. **Python 3.8+**

### Building the Shared Library

```bash
# Build with Nix
nix build .#lattice-ffi

# The library will be at:
# result/lib/liblattice-ffi.so
# result/include/lattice-ffi.h
```

### Setting Library Path

The Python wrapper automatically searches for the library in:

1. `LATTICE_FFI_LIB` environment variable
2. `result/lib/liblattice-ffi.so` (Nix build result)
3. System library path (`liblattice-ffi.so`)

**Option 1: Environment Variable**
```bash
export LATTICE_FFI_LIB=/path/to/liblattice-ffi.so
python your_script.py
```

**Option 2: Nix Result (Automatic)**
```bash
# After building with Nix, the wrapper automatically finds:
# result/lib/liblattice-ffi.so
python your_script.py
```

**Option 3: System Installation**
```bash
# Install to system library directory
cp result/lib/liblattice-ffi.so /usr/local/lib/
python your_script.py
```

## Modules

### Frame Interpolation (`frame_interpolation.py`)

```python
from lattice.ffi import frame_interpolation

# Convert slowdown to factor
factor = frame_interpolation.slowdown_to_factor(2.5)  # Returns: 2

# Validate interpolation parameters
result = frame_interpolation.validate_interpolation_params(
    model_name="rife-v4.6",
    factor=2,
    ensemble=False,
    slowdown=2.0
)
```

### Model Integrity (`model_integrity.py`)

```python
from lattice.ffi import model_integrity

# Compute SHA256 hash
hash_value = model_integrity.compute_hash(b"some bytes")
print(hash_value)  # Hex digest

# Verify hash
is_valid = model_integrity.verify_hash(computed_hash, expected_hash)

# Validate decomposition parameters
result = model_integrity.validate_decomposition_params(
    num_layers=5,
    cfg_scale=4.0,
    steps=50,
    resolution=640,
    seed=42
)
```

### Audio Stem Separation (`audio_stem_separation.py`)

```python
from lattice.ffi import audio_stem_separation

# Get model configuration
config = audio_stem_separation.get_model_config("htdemucs")
if config["status"] == "success":
    model = config["model"]
    print(f"Model: {model['displayName']}")

# Get all available models
models = audio_stem_separation.get_available_models()

# Get attribution info
attribution = audio_stem_separation.get_attribution_info()

# Validate parameters
result = audio_stem_separation.validate_stem_separation_params(
    model_name="htdemucs",
    segment_length=10.0,
    overlap=0.1,
    stems=["vocals", "drums"]
)
```

### Project Validation (`project_validation.py`)

```python
from lattice.ffi import project_validation

# Calculate max depth
result = project_validation.calculate_max_depth(json_data, current_depth=0)
max_depth = result["result"]

# Validate expressions
result = project_validation.validate_expressions(json_data, path="")
errors = result["errors"]

# Validate single expression
result = project_validation.validate_single_expression(
    "Math.sin(time)",
    path="layers[0].expressions.rotation"
)

# Count layers
result = project_validation.count_layers(json_data)
layer_count = result["result"]

# Validate project ID
is_valid = project_validation.validate_project_id("my-project-123")
```

### SVG Path Parsing (`svg_path_parsing.py`)

```python
from lattice.ffi import svg_path_parsing

# Parse SVG string
svg_string = '<svg><path d="M 10 20 L 30 40"/></svg>'
result = svg_path_parsing.parse_svg_to_paths(
    svg_string,
    img_width=1920,
    img_height=1080
)
paths = result["paths"]

# Parse path data
path_data = "M 10 20 L 30 40 C 50 60 70 80 90 100"
result = svg_path_parsing.parse_path_data(path_data, path_idx=0)
control_points = result["controlPoints"]
is_closed = result["closed"]
```

## Error Handling

All functions return structured responses:

**Success Response:**
```python
{
    "status": "success",
    "params": { ... }  # or "result", "paths", "errors", etc.
}
```

**Error Response:**
```python
{
    "status": "error",
    "message": "Error description"
}
```

**Example:**
```python
result = frame_interpolation.validate_interpolation_params(...)

if result["status"] == "success":
    # Use validated parameters
    params = result["params"]
    model_name = params["modelName"]
    factor = params["factor"]
else:
    # Handle error
    error_msg = result["message"]
    logger.error(f"Validation failed: {error_msg")
```

## Memory Management

The Python wrapper automatically handles memory management:

- **Python → Haskell:** Strings are converted to CStrings (temporary, no free needed)
- **Haskell → Python:** CStrings are converted to Python strings and freed automatically

**No manual memory management required** - the wrapper handles everything.

## RTS Initialization

The Haskell Runtime System (RTS) is automatically initialized when you import the module:

```python
from lattice.ffi import frame_interpolation  # RTS initialized here
```

If initialization fails, a warning is issued and functions will raise `RuntimeError` when called.

## Troubleshooting

### Library Not Found

**Error:** `RuntimeError: FFI function not available`

**Solutions:**
1. Set `LATTICE_FFI_LIB` environment variable
2. Build with Nix: `nix build .#lattice-ffi`
3. Install to system library path

### RTS Initialization Failed

**Error:** Warning about RTS initialization

**Solutions:**
1. Ensure the shared library is built correctly
2. Check that `hs_init` symbol is exported
3. Verify library dependencies are available

### Function Returns NULL

**Error:** `RuntimeError: No result from Haskell function`

**Solutions:**
1. Check function arguments (JSON format, types)
2. Verify Haskell function implementation
3. Check Haskell logs for errors

## Integration Example

Here's how to integrate FFI functions into existing Python code:

```python
# Before (Python implementation)
def validate_params(model_name, factor, ensemble, slowdown):
    if model_name not in RIFE_MODELS:
        raise ValueError(f"Unknown model: {model_name}")
    if factor not in [2, 4, 8]:
        raise ValueError(f"Invalid factor: {factor}")
    # ... more validation
    return {"model": model_name, "factor": factor, ...}

# After (Using FFI)
from lattice.ffi import frame_interpolation

def validate_params(model_name, factor, ensemble, slowdown):
    result = frame_interpolation.validate_interpolation_params(
        model_name=model_name,
        factor=factor,
        ensemble=ensemble,
        slowdown=slowdown
    )
    
    if result["status"] == "error":
        raise ValueError(result["message"])
    
    return result["params"]
```

## Performance Notes

- **FFI Overhead:** Minimal (~microseconds per call)
- **JSON Parsing:** Small overhead for complex types
- **Memory:** Automatic management, no leaks
- **Thread Safety:** RTS initialization is thread-safe

## API Reference

See individual module docstrings for detailed API documentation:

- `frame_interpolation.py` - Frame interpolation functions
- `model_integrity.py` - Hash computation and validation
- `audio_stem_separation.py` - Audio model configuration
- `project_validation.py` - Project validation functions
- `svg_path_parsing.py` - SVG path parsing

## Development

### Building from Source

```bash
# Build shared library
nix build .#lattice-ffi

# Test Python wrapper
python -c "from lattice.ffi import frame_interpolation; print(frame_interpolation.slowdown_to_factor(2.5))"
```

### Adding New Functions

1. Add FFI export to Haskell module (`src/lattice/FFI/*.hs`)
2. Update Nix build if needed
3. Add Python wrapper function (`src/lattice/ffi/*.py`)
4. Update documentation

## License

Same as main project (MIT)
