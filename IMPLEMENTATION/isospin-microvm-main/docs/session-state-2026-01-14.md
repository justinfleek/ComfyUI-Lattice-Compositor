# Isospin Session State - 2026-01-14 (Updated)

## Summary

Successfully implemented **VFIO GPU passthrough for Firecracker** with an NVIDIA RTX PRO 6000 Blackwell GPU (128GB VRAM). The GPU is now fully visible inside a Firecracker microVM with nvidia.ko and nvidia-modeset.ko modules loading successfully.

**Packaged as `nix run .#fc-gpu`** - a single command to build and boot a GPU-enabled Firecracker VM.

## Quick Start

```bash
# Boot GPU VM (GPU must be bound to vfio-pci)
nix run .#fc-gpu

# With options
nix run .#fc-gpu -- --pci 0000:01:00.0 --mem 32768 --cpus 8

# Show help
nix run .#fc-gpu -- --help
```

## Key Files

### Nix Flake Module
- `nix/flake-modules/main.nix` - Contains:
  - `fc-gpu` package (lines 1279-1491) - Main GPU VM launcher
  - `create-gpu-assets` package (lines 1494-1615) - Asset creation helper
  - `boot-vm-gpu` package (legacy script)

### Firecracker VFIO Implementation
- `firecracker/src/vmm/src/pci/vfio/device.rs` - VFIO device handling, BAR allocation, MSI-X setup
- `firecracker/src/vmm/src/pci/vfio/error.rs` - Error variants for VFIO
- `firecracker/src/vmm/src/pci/vfio/container.rs` - VfioContainer for IOMMU domain/DMA mapping
- `firecracker/src/vmm/src/pci/vfio/msix.rs` - MSI-X interrupt handling
- `firecracker/src/vmm/src/pci/vfio/proptests.rs` - Property-based tests (41 properties)
- `firecracker/src/device_manager/pci_mngr.rs` - PCI device manager with VFIO support
- `firecracker/src/firecracker/src/main.rs` - Updated with `pci_enabled` logic

### VM Assets (`.vm-assets/`)
- `vmlinux-6.12.63.bin` - Kernel extracted from host's bzImage (matches NVIDIA modules)
- `initramfs.cpio.gz` - Initramfs with virtio + ext4 modules
- `gpu-rootfs.ext4` - 4GB rootfs with NVIDIA modules + nvidia-smi closure
- `vm-config-gpu-612.json` - VM config for GPU passthrough
- `create-gpu-rootfs.sh` - Script to build GPU rootfs
- `create-initramfs.sh` - Script to build initramfs

## Current Working State

The VM boots successfully with:
```
- GPU visible as PCI device 10de:2bb1 (NVIDIA RTX PRO 6000 Blackwell)
- BAR0: 64MB at 0xc4000000 (32-bit)
- BAR1: 128GB VRAM at 0x6000000000 (64-bit prefetchable)
- BAR3: 32MB at 0x4002000000 (64-bit prefetchable)
- nvidia.ko and nvidia-modeset.ko load successfully
- Device nodes created: /dev/nvidia0, /dev/nvidiactl, /dev/nvidia-modeset
```

## Hardware Context

- Host: NixOS with kernel 6.12.63, IOMMU enabled
- GPU: NVIDIA RTX PRO 6000 Blackwell at `0000:01:00.0` (IOMMU group 13)
- GPU bound to vfio-pci driver via NixOS config

## Nix Store Paths (Host-Specific)

```
NVIDIA modules: /nix/store/rwfsyfyi8mrzdp4brm618r2jz0nlx5wy-nvidia-open-6.12.63-580.95.05
NVIDIA bin:     /nix/store/gnzdlz9m5nlv5cr3203lbc0kgpiwhsn5-nvidia-x11-580.95.05-6.12.63-bin
NVIDIA lib:     /nix/store/iqvqw3q2k0fj6s0jndi70ahh09b833z9-nvidia-x11-580.95.05-6.12.63
Kernel modules: /nix/store/n8rq5y12z8amfiyqldyvc8q5rq6jmr4a-linux-6.12.63-modules
```

## Key Commits

- `9ba1dc6` - tmp testing
- `716656c` - docs: Add live GPU passthrough test plan
- `5aef2db` - docs: Add property test execution report
- `f924c07` - vfio: Fix property test compilation errors
- `eb95a6f` - vfio: Add comprehensive property-based tests (41 properties)
- `05b7563` - mock config space, BAR alloc, MSI-X parsing tests
- `ce00140` - safe vfio bind with display check
- `00c3551` - vfio property tests (28 passing)
- `c38474f` - vfio scaffolding

## Available Commands

```bash
# GPU passthrough
nix run .#fc-gpu              # Boot GPU VM
nix run .#create-gpu-assets   # Create VM assets

# Standard VM boot
nix run .#boot-vm             # Boot basic VM
nix run .#boot-vm-net         # Boot VM with networking
nix run .#boot-ch             # Boot Cloud Hypervisor VM

# Build
nix run .#build-fc            # Build Firecracker
nix run .#build-ch            # Build Cloud Hypervisor
nix run .#rebuild             # Full rebuild

# Networking
nix run .#setup-network       # Setup TAP device
nix run .#teardown-network    # Remove TAP device

# Direct binaries
nix run .#firecracker -- --help
nix run .#cloud-hypervisor -- --help
```

## Next Steps

1. **nvidia-smi inside VM** - Currently loads modules but nvidia-smi has issues
2. **Add networking to GPU VM** - TAP device for SSH access
3. **Performance testing** - CUDA workloads in VM
4. **Snapshot support** - Save/restore VM state with GPU
