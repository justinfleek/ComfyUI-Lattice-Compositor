# GPU Passthrough Setup Guide

## Prerequisites

1. **IOMMU enabled** in BIOS/UEFI (VT-d for Intel, AMD-Vi for AMD)
2. **Kernel parameters**: `intel_iommu=on` or `amd_iommu=on`
3. **vfio-pci module** loaded

## Display Options for GPU Passthrough Testing

When you pass your GPU to a VM, it's no longer available for host display. You have three options:

### Option 1: Second GPU (Recommended)
Keep one GPU for host display, pass the other to VM.
```bash
# Example: Keep GPU at 00:02.0 for display, pass 01:00.0 to VM
lspci | grep VGA  # List all GPUs
```

### Option 2: Integrated Graphics (iGPU)
Use Intel/AMD integrated graphics for host display.

**Check for iGPU:**
```bash
lspci | grep -i "vga\|display"
# Look for Intel UHD/Iris or AMD Radeon integrated
```

**NixOS configuration to prefer iGPU:**
```nix
# configuration.nix
boot.kernelParams = [ "intel_iommu=on" ];

# Force X to use Intel iGPU
services.xserver.videoDrivers = [ "modesetting" ];  # or "intel"

# Blacklist nvidia from grabbing the GPU on boot (optional)
boot.blacklistedKernelModules = [ "nvidia" "nouveau" ];
```

### Option 3: Headless / SSH Only
Work entirely over SSH, no host display needed.

```bash
# From another machine:
ssh user@host

# Bind GPU to vfio-pci
sudo ./scripts/vfio-bind.sh 0000:01:00.0 0000:01:00.1

# Boot VM with GPU
sudo ./scripts/boot-ch-gpu.sh
```

## Quick Start

### 1. Check IOMMU Groups
```bash
./scripts/vfio-status.sh
```

### 2. Bind GPU to vfio-pci
```bash
# Both GPU and HDMI audio must be bound (same IOMMU group)
sudo ./scripts/vfio-bind.sh 0000:01:00.0 0000:01:00.1
```

### 3. Create VM Image (first time only)
```bash
./scripts/create-gpu-image.sh
```

### 4. Boot VM with GPU
```bash
sudo ./scripts/boot-ch-gpu.sh 0000:01:00.0
```

### 5. SSH into VM
```bash
ssh -i .vm-assets/vm_key root@172.16.0.2
# Or use password: gpu
```

### 6. Verify GPU in VM
```bash
# In the VM:
lspci | grep -i nvidia
nvidia-smi  # After driver installs
```

### 7. Restore GPU to Host (when done)
```bash
sudo ./scripts/vfio-unbind.sh 0000:01:00.0 0000:01:00.1
# Then restart display manager if needed
sudo systemctl restart display-manager
```

## Troubleshooting

### "GPU stuck after unbind"
The nvidia driver can get wedged. Safest fix is reboot.

### "IOMMU group has other devices"
All devices in an IOMMU group must be bound to vfio-pci or the passthrough will fail.
```bash
# Check what's in the group
ls /sys/kernel/iommu_groups/13/devices/
```

### "No /dev/vfio/"
Load the vfio modules:
```bash
sudo modprobe vfio-pci
```

### "Permission denied on /dev/vfio/N"
Either run as root or add your user to the appropriate group:
```bash
sudo chmod 666 /dev/vfio/13  # Quick fix
# Or add udev rules for persistent access
```

## NixOS-Specific Setup

Add to `configuration.nix`:
```nix
{
  boot.kernelParams = [ "intel_iommu=on" "iommu=pt" ];
  
  boot.kernelModules = [ "vfio-pci" ];
  
  # Optional: bind GPU to vfio-pci at boot
  boot.extraModprobeConfig = ''
    options vfio-pci ids=10de:2bb1,10de:22e8
  '';
}
```

Get your GPU's vendor:device IDs:
```bash
lspci -nn | grep -i nvidia
# 01:00.0 ... [10de:2bb1]  <- this is the ID
```
