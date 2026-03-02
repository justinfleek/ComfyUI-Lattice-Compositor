#!/usr/bin/env bash
# ISOSPIN GPU Demo - Firecracker cold boot to nvidia-smi
set -euo pipefail
cd "$(dirname "$0")/.."

GPU_ADDR="${GPU_ADDR:-0000:01:00.0}"
FC="./buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"

# Use firmware-preloaded initramfs if FW_PRELOAD=1 is set
if [[ "${FW_PRELOAD:-0}" == "1" ]] && [[ -f ".vm-assets/initramfs-with-fw.cpio.gz" ]]; then
	INITRAMFS=".vm-assets/initramfs-with-fw.cpio.gz"
	echo "Using firmware-preloaded initramfs (62MB, ~1s faster)"
else
	INITRAMFS=".vm-assets/initramfs.cpio.gz"
fi

# Check prerequisites
if [[ ! -x "$FC" ]]; then
	echo "ERROR: Firecracker binary not found: $FC"
	echo "Build first: nix develop -c buck2 build //firecracker/src/firecracker:firecracker"
	exit 1
fi

if [[ ! -f ".vm-assets/vmlinux-6.12.63.bin" ]]; then
	echo "ERROR: Kernel not found: .vm-assets/vmlinux-6.12.63.bin"
	exit 1
fi

if [[ ! -f ".vm-assets/gpu-rootfs.ext4" ]]; then
	echo "ERROR: Rootfs not found: .vm-assets/gpu-rootfs.ext4"
	exit 1
fi

if [[ ! -f "$INITRAMFS" ]]; then
	echo "ERROR: Initramfs not found: $INITRAMFS"
	exit 1
fi

# Check GPU binding
if [[ -L "/sys/bus/pci/devices/$GPU_ADDR/driver" ]]; then
	driver=$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/driver")")
	if [[ "$driver" != "vfio-pci" ]]; then
		echo "ERROR: GPU $GPU_ADDR bound to $driver, not vfio-pci"
		exit 1
	fi
else
	echo "ERROR: GPU $GPU_ADDR has no driver"
	exit 1
fi

# Check device permissions
IOMMU_GROUP=$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/iommu_group")")
if [[ ! -r "/dev/vfio/$IOMMU_GROUP" ]] || [[ ! -w "/dev/vfio/$IOMMU_GROUP" ]]; then
	echo "ERROR: No access to /dev/vfio/$IOMMU_GROUP"
	echo "  Fix: sudo usermod -aG kvm $USER && newgrp kvm"
	echo "  Or:  sudo chmod 666 /dev/vfio/$IOMMU_GROUP"
	exit 1
fi

if [[ ! -r "/dev/kvm" ]] || [[ ! -w "/dev/kvm" ]]; then
	echo "ERROR: No access to /dev/kvm"
	echo "  Fix: sudo usermod -aG kvm $USER && newgrp kvm"
	exit 1
fi

# Check memlock limit - GPU passthrough needs lots of locked memory for DMA
MEMLOCK=$(ulimit -l)
if [[ "$MEMLOCK" != "unlimited" ]] && [[ "$MEMLOCK" -lt 100000000 ]]; then
	echo "WARNING: memlock limit is ${MEMLOCK}KB, GPU passthrough needs unlimited"
	echo "  Running with sudo, or add to /etc/security/limits.conf:"
	echo "    @kvm  hard  memlock  unlimited"
	echo "    @kvm  soft  memlock  unlimited"
fi

GPU_INFO=$(lspci -s "$GPU_ADDR" 2>/dev/null | cut -d: -f3- || echo "Unknown")

CONFIG="/tmp/fc-gpu-$$.json"
cat >"$CONFIG" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$PWD/.vm-assets/vmlinux-6.12.63.bin",
    "initrd_path": "$PWD/$INITRAMFS",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=realloc pcie_aspm=off init=/init"
  },
  "drives": [{"drive_id": "rootfs", "path_on_host": "$PWD/.vm-assets/gpu-rootfs.ext4", "is_root_device": true, "is_read_only": false}],
  "machine-config": {"vcpu_count": 4, "mem_size_mib": 8192},
  "vfio": [{"id": "gpu0", "pci_address": "$GPU_ADDR"}]
}
EOF
trap 'rm -f "$CONFIG"' EXIT

echo "════════════════════════════════════════════════════════════════════════"
echo " ISOSPIN: Firecracker GPU Passthrough Demo"
echo "════════════════════════════════════════════════════════════════════════"
echo ""
echo " GPU: $GPU_INFO"
echo " PCI: $GPU_ADDR (vfio-pci)"
echo ""

# Show full output with color highlighting for important lines
# Green: LTR masking, success
# Cyan: nvidia-smi output
# Yellow: LTR status messages
# Magenta: GPU PCI enumeration
# Blue: driver loading
timeout 30 "$FC" --no-api --config-file "$CONFIG" 2>&1 |
	sed -E \
		-e "s/(Masked DevCap2.*)/\x1b[1;32m\1\x1b[0m/" \
		-e "s/(NVIDIA-SMI.*)/\x1b[1;36m\1\x1b[0m/" \
		-e "s/(NVRM:.*LTR.*)/\x1b[1;33m\1\x1b[0m/" \
		-e "s/(nvidia-smi exit.*)/\x1b[1;32m\1\x1b[0m/" \
		-e "s/(pci 0000:00:02\.0.*10de.*)/\x1b[1;35m\1\x1b[0m/" \
		-e "s/(insmod nvidia.*)/\x1b[1;34m\1\x1b[0m/" \
		-e "s/(nvidia\.ko done)/\x1b[1;34m\1\x1b[0m/"
