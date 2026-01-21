# Nix Dev Shell Setup

This document describes the Nix development environment configuration for the Lattice Compositor project.

## Overview

The Nix dev shell provides an isolated, reproducible development environment with:
- Python 3.13 with comprehensive package set
- PyTorch with CUDA support (CUDA 12.8)
- All development dependencies from `requirements-dev.txt`
- Tools: `uv`, `bun`, `git`

## Configuration Files

### `flake.nix`
Main flake configuration that:
- Enables CUDA support (`cudaSupport = true`)
- Allows unfree packages (`allowUnfree = true`) for CUDA
- Imports the flake module

### `nix/flake-module.nix`
Defines the dev shell with:
- Python environment with packages from nixpkgs
- Automatic package installation via `shellHook`
- User site-packages installation to `~/.local`

### `requirements-dev.txt`
Contains 170+ Python packages that are:
- Not available in nixpkgs, OR
- Need specific versions
- Installed automatically when entering the dev shell

## Usage

### Enter the dev shell
```bash
nix develop
```

### First-time setup
On first entry, the shell will:
1. Build/download Python packages from nixpkgs (including PyTorch with CUDA)
2. Install packages from `requirements-dev.txt` via `uv` to `~/.local`
3. Create installation marker at `~/.local/.lattice-packages-installed`

### Subsequent entries
- Packages are cached, so entry is fast
- Re-installs only if `requirements-dev.txt` is newer than the marker

### Verify setup
```bash
./verify-nix-setup.sh
```

## Package Installation Strategy

### From nixpkgs (installed immediately)
- `torch`, `torchvision`, `torchaudio` (with CUDA support)
- `numpy`, `scipy`, `sympy`
- `fastapi`, `starlette`
- `pytest`, `hypothesis`, `coverage`
- `ruff`, `gitpython`
- `opencv4`, `soundfile`, `sounddevice`
- `transformers`, `huggingface-hub`
- And many more...

### From requirements-dev.txt (installed via uv)
- Packages not in nixpkgs
- Packages needing specific versions
- Installed to `~/.local` (user site-packages)

## Troubleshooting

### Reinstall packages
```bash
rm ~/.local/.lattice-packages-installed
nix develop  # Will reinstall on next entry
```

### Check what's installed
```bash
python -m pip list --user
```

### Verify CUDA
```bash
python -c "import torch; print(torch.cuda.is_available())"
```

### Clear Nix cache (if builds fail)
```bash
nix-collect-garbage
```

## Notes

- Packages are installed to `~/.local`, not system Python
- Installation is cached for performance
- CUDA support requires NVIDIA drivers and CUDA toolkit
- The dev shell is isolated from your system Python
