# HaskTorch Diffusion Inference - Roadmap

## Goal
Port RES4LYF's advanced sampler/scheduler math to HaskTorch with CUDA 13+ and TensorRT for NVFP4 quantized inference.

## Current Status

### Completed
- [x] **CUDA 13+ HaskTorch Setup** - `flake.nix` now uses `nvidia-sdk` overlay with CUDA 13.1
- [x] **TensorRT in devShell** - Available via `$TENSORRT_HOME` in `nix develop`
- [x] **pkgsCuda pattern** - CUDA-enabled hasktorch on x86_64-linux, CPU fallback elsewhere
- [x] **~30 RK tableaux** in `RKCoefficients.hs`
- [x] **φ functions** with Torch tensor versions in `Phi.hs`
- [x] **Exponential RK coefficients** in `RKExponential.hs`

### In Progress
- [ ] **Test CUDA tensor operations** - Verify hasktorch CUDA backend works
- [ ] **Build TensorRT C++ FFI** - Compile `CMakeLists.txt` with TensorRT

## Next Steps

### 1. Test CUDA Tensors
```bash
cd standalone-edition
nix develop .#cuda
ghci -isrc/inference/hasktorch <<< 'import Torch; t = zeros [3,3] (withDevice (Device CUDA 0) defaultOpts); print t'
```

### 2. Build TensorRT FFI
```bash
cd standalone-edition/src/inference
mkdir build && cd build
cmake .. -DCMAKE_PREFIX_PATH="$TENSORRT_HOME;$CUDA_PATH"
ninja
```

### 3. Wire FFI to Haskell
Update `TensorRT/FFI.hs` to call the compiled C library.

### 2. Landauer Precision Framework Integration
The thermodynamic precision model is in `Precision/Landauer.hs`. Key insight: FP4 is optimal for latent space because VAE already paid Landauer cost.

**Action:** Wire `LandauerPrecision` into the sampler pipeline to select NVFP4 quantization.

### 3. TensorRT Engine Integration
C++ glue exists at `src/inference/src/ffi_glue.cpp`. FFI bindings at `TensorRT/FFI.hs`.

**Action:** 
1. Build the C++ lib via `src/inference/CMakeLists.txt`
2. Link against TensorRT from nvidia-sdk
3. Test FFI calls from Haskell

### 4. Complete RK Tableaux
`RKCoefficients.hs` has ~30 tableaux. Reference has 100+.

**Missing (high priority):**
- Radau IIA 5s/7s/9s/11s (from reference lines 657-709)
- Lobatto IIIA/IIIB/IIIC 4s variants
- All exponential methods (RES variants, ETDRK, Lawson)

**Reference:** `src/inference/reference/RES4LYF/beta/rk_coefficients_beta.py`

### 5. DEIS Coefficient Generation
DEIS computes coefficients dynamically based on sigma schedule, not static tableaux.

**Reference:** `src/inference/reference/RES4LYF/beta/deis_coefficients.py`

## File Locations

```
standalone-edition/
├── flake.nix                    # UPDATE for CUDA 13+
├── lattice.cabal                # Has hasktorch dep, needs libtorch-ffi
├── src/inference/
│   ├── ROADMAP.md               # This file
│   ├── hasktorch/Lattice/Diffusion/
│   │   ├── Phi.hs               # φ functions (has Torch tensor versions)
│   │   ├── RKCoefficients.hs    # Butcher tableaux (scalar)
│   │   ├── RKExponential.hs     # Dynamic exponential RK coeffs
│   │   ├── Schedulers.hs        # Sigma schedules
│   │   ├── Noise.hs             # Noise types/SDE
│   │   ├── Workflows.hs         # Model presets (Flux, SDXL, WAN, etc.)
│   │   ├── Precision/Landauer.hs # Thermodynamic precision
│   │   ├── Samplers/Exponential.hs # RES/DPM++ samplers
│   │   └── TensorRT/
│   │       ├── FFI.hs           # C FFI bindings
│   │       ├── Engine.hs        # Safe wrapper
│   │       └── Pipeline.hs      # End-to-end generation
│   ├── src/
│   │   ├── ffi_glue.cpp         # extern "C" bridge
│   │   ├── tensorrt_engine.cpp  # TRT engine wrapper
│   │   └── scheduler.cpp        # C++ schedulers
│   ├── include/                 # C++ headers
│   ├── CMakeLists.txt           # C++ build
│   └── reference/RES4LYF/       # Python reference (DO NOT DELETE)
│       └── beta/
│           ├── rk_coefficients_beta.py  # 100+ tableaux
│           ├── phi_functions.py
│           └── deis_coefficients.py
```

## External Resources

| Resource | URL | Purpose |
|----------|-----|---------|
| Model-Optimizer | github:weyl-ai/Model-Optimizer | NVFP4/FP8 quantization patterns |
| nixos-dgx-spark | github:weyl-ai/nixos-dgx-spark | CUDA 13 overlay, DGX config |
| nvidia-sdk | `IMPLEMENTATION/nvidia-sdk-main/` | TensorRT nix packaging |
| hasktorch | github:hasktorch/hasktorch | Haskell libtorch bindings |
| RES4LYF | reference/RES4LYF/ | Original Python implementation |

## Quantization Path (from Model-Optimizer)

Key file: `modelopt/torch/quantization/tensor_quant.py`

```python
mx_format_map = {
    (4, 3): "E4M3",   # FP8
    (5, 2): "E5M2",   # FP8
    (2, 1): "E2M1",   # FP4 (NVFP4)
    (1, 2): "E1M2",   # FP4 variant
}
```

For NVFP4: use E2M1 format with block scaling (MX format).
