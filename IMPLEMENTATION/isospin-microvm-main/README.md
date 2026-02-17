# Isospin

**GPU passthrough and multiplexing for Firecracker VMs.**

Isospin eliminates the ~20 second GPU cold boot penalty by keeping a "GPU VM" with the real NVIDIA driver running, while lightweight worker VMs connect instantly via the gpu-broker.

## Quick Start

```bash
# Enter development shell
nix develop

# Run the full GPU broker demo (requires VFIO-bound GPU)
sudo nix run .#demo-broker

# Or run broker unit tests (no GPU required)
nix run .#broker-test
```

## Architecture

```
┌────────────────────────────────────────────────────────────────────────┐
│ GPU VM (Cloud Hypervisor + VFIO)                                       │
│   nvidia.ko (580.95.05) → NVIDIA RTX PRO 6000 Blackwell (128GB)       │
│   gpu-broker (real ioctl forwarding) on vsock:9999                     │
└──────────────────────────────────┬─────────────────────────────────────┘
                                   │ Cloud Hypervisor vsock
                                   ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ HOST: vsock-bridge                                                       │
│   Bridges CH vsock ↔ Firecracker vsock                                   │
└──────────────────────────────────┬───────────────────────────────────────┘
                                   │ Firecracker vsock
                                   ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Worker VM (Firecracker, boots in <1s)                                    │
│   nvidia-shim.ko → /dev/nvidiactl, /dev/nvidia0 (proxied to broker)     │
│   Applications use GPU instantly, no driver initialization               │
└──────────────────────────────────────────────────────────────────────────┘
```

## Commands

### Container Runner

| Command | Description |
|---------|-------------|
| `nix run .#gpu-run -- <cmd> <image>` | Run commands in NGC containers with GPU passthrough |

**Examples:**
```bash
# Interactive shell in tritonserver
nix run .#gpu-run -- /bin/bash nvcr.io/nvidia/tritonserver:25.11-py3

# Run nvidia-smi in a CUDA container
nix run .#gpu-run -- nvidia-smi nvcr.io/nvidia/cuda:12.4.0-base-ubuntu22.04

# Test PyTorch CUDA availability
nix run .#gpu-run -- python -c 'import torch; print(torch.cuda.is_available())' nvcr.io/nvidia/pytorch:25.04-py3
```

**Environment variables:**
- `GPU_RUN_KEEP_ROOTFS=1` - Keep extracted rootfs after exit
- `GPU_RUN_ROOTFS=<path>` - Use existing rootfs instead of extracting

### GPU Broker Demo

| Command | Description |
|---------|-------------|
| `nix run .#demo-broker` | **Full demo** - GPU VM + bridge + worker in tmux |
| `nix run .#gpu-vm` | Boot GPU VM with NVIDIA driver and broker |
| `nix run .#vsock-bridge` | Start vsock bridge (FC ↔ CH) |
| `nix run .#worker-vm` | Boot worker VM with nvidia-shim |
| `nix run .#kill-vms` | Stop all VMs and cleanup |
| `nix run .#vfio-status` | Show GPU and IOMMU binding status |
| `nix run .#broker-test` | Run gpu-broker unit tests |

### Development

| Command | Description |
|---------|-------------|
| `nix develop` | Enter full development environment |
| `nix develop .#broker` | Minimal broker development shell |
| `nix build .#gpu-broker` | Build broker binary |
| `nix build .#gpu-broker-static` | Build static broker for VMs |
| `nix build .#nvidia-shim` | Build nvidia-shim.ko kernel module |
| `nix build .#fc-gpu-kernel` | Build Firecracker kernel (6.12.10) |
| `nix build .#fc-rootfs` | Build worker VM rootfs |

### VFIO Setup

```bash
# Check current status
nix run .#vfio-status

# Bind GPU to vfio-pci (required before running demo)
sudo ./scripts/vfio-bind.sh 0000:01:00.0

# Unbind (return to nvidia driver)
sudo ./scripts/vfio-unbind.sh 0000:01:00.0
```

## Running the Demo

### Prerequisites

1. **GPU bound to vfio-pci:**
   ```bash
   sudo ./scripts/vfio-bind.sh 0000:01:00.0
   ```

2. **GPU VM assets in `.vm-assets/`:**
   - `vmlinux-6.12.63.bin` - GPU VM kernel
   - `initramfs-6.12.63-pci.cpio.gz` - GPU VM initramfs  
   - `gpu-rootfs.ext4` - GPU VM rootfs with NVIDIA modules

### Full Demo (Recommended)

```bash
sudo nix run .#demo-broker
```

This starts a tmux session with 4 windows:
- `gpu-vm` - GPU VM booting (watch NVIDIA driver load in ~20s)
- `bridge` - Vsock bridge (shows client connections)
- `worker` - Worker VM (nvidia-shim connects to broker)
- `log` - GPU VM serial log

### Manual Step-by-Step

```bash
# Terminal 1: Start GPU VM
sudo nix run .#gpu-vm

# Wait for "Broker running" in log (~25 seconds)
tail -f /tmp/gpu-vm.log

# Terminal 2: Start vsock bridge
sudo nix run .#vsock-bridge

# Terminal 3: Start worker VM  
sudo nix run .#worker-vm

# Cleanup
sudo nix run .#kill-vms
```

## Package Reference

### Core Packages

| Package | Description |
|---------|-------------|
| `gpu-broker` | GPU broker binary (dynamically linked) |
| `gpu-broker-static` | GPU broker binary (static, for VMs) |
| `nvidia-shim` | nvidia-shim.ko kernel module for guest VMs |
| `fc-gpu-kernel` | Linux 6.12.10 kernel for Firecracker |
| `fc-rootfs` | Minimal rootfs with nvidia-shim + busybox |
| `fc-initramfs` | Initramfs for Firecracker boot |

### GPU VM Packages

| Package | Description |
|---------|-------------|
| `gpu-vm-kernel` | Linux 6.12.64 kernel (nixpkgs) |
| `gpu-vm-initramfs` | Initramfs with virtio-pci modules |

### Build Tools

| Package | Description |
|---------|-------------|
| `rustVendor` | Vendored Rust crates for Buck2 |
| `vendor-link` | Symlink vendor directory |
| `buckify` | Run reindeer to generate BUCK files |

## Documentation

- [docs/vfio-gpu-passthrough-book.md](docs/vfio-gpu-passthrough-book.md) - **The Book** - Complete GPU passthrough guide
- [docs/nixos-vfio-setup.md](docs/nixos-vfio-setup.md) - NixOS VFIO configuration
- [docs/firecracker-gpu-passthrough.md](docs/firecracker-gpu-passthrough.md) - Firecracker GPU guide

## Project Structure

```
isospin/
├── gpu-broker/           # GPU broker (Rust)
│   ├── src/              # Broker source
│   ├── kernel/           # nvidia-shim.ko source
│   └── Cargo.toml
├── firecracker/          # Firecracker VMM (Buck2)
├── cloud-hypervisor/     # Cloud Hypervisor VMM
├── scripts/              # Helper scripts
│   ├── vfio-bind.sh      # Bind GPU to vfio-pci
│   ├── vfio-unbind.sh    # Unbind GPU
│   └── vfio-status.sh    # Show IOMMU status
├── nix/
│   └── flake-modules/    # Nix derivations
│       ├── gpu-broker.nix    # Broker packages
│       ├── kernel.nix        # Kernel + nvidia-shim
│       ├── vm-images.nix     # VM rootfs/initramfs
│       ├── vm-runners.nix    # Demo apps
│       └── devshell.nix      # Dev environment
├── docs/                 # Documentation
│   └── vfio-gpu-passthrough-book.md
└── .vm-assets/           # VM assets (not in git)
    ├── vmlinux-6.12.63.bin
    ├── initramfs-6.12.63-pci.cpio.gz
    └── gpu-rootfs.ext4
```

## Hardware Tested

| Component | Specification |
|-----------|---------------|
| GPU | NVIDIA RTX PRO 6000 Blackwell Workstation Edition |
| VRAM | 128GB |
| PCI Address | 0000:01:00.0 |
| Driver | NVIDIA 580.95.05 Open Kernel Module |
| Host Kernel | 6.12.63 |

## Key Results

```
GPU VM boot to broker ready:     ~25 seconds (one-time)
Worker VM boot:                  <1 second
Worker VM GPU access:            Instant (via broker)
Cold boot penalty eliminated:    YES
```

## License

MIT
