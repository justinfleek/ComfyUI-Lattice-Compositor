#!/usr/bin/env bash
# Boot Cloud Hypervisor with GPU passthrough
# Usage: sudo ./boot-ch-gpu.sh [pci-address]
# Default: 0000:01:00.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

GPU_ADDR="${1:-0000:01:00.0}"
GPU_PATH="/sys/bus/pci/devices/$GPU_ADDR"

# Verify GPU exists and is bound to vfio-pci
if [[ ! -d "$GPU_PATH" ]]; then
	echo "ERROR: GPU $GPU_ADDR not found"
	exit 1
fi

if [[ -L "$GPU_PATH/driver" ]]; then
	driver=$(basename "$(readlink "$GPU_PATH/driver")")
	if [[ "$driver" != "vfio-pci" ]]; then
		echo "ERROR: GPU $GPU_ADDR is bound to $driver, not vfio-pci"
		echo "Run: sudo $SCRIPT_DIR/vfio-bind.sh $GPU_ADDR"
		exit 1
	fi
else
	echo "ERROR: GPU $GPU_ADDR has no driver"
	exit 1
fi

# Check IOMMU group - all devices must be bound to vfio-pci
iommu_group=$(basename "$(readlink "$GPU_PATH/iommu_group")")
echo "GPU $GPU_ADDR in IOMMU group $iommu_group"

for dev_path in /sys/kernel/iommu_groups/$iommu_group/devices/*; do
	dev=$(basename "$dev_path")
	if [[ -L "/sys/bus/pci/devices/$dev/driver" ]]; then
		dev_driver=$(basename "$(readlink "/sys/bus/pci/devices/$dev/driver")")
		if [[ "$dev_driver" != "vfio-pci" ]]; then
			echo "WARNING: $dev in same IOMMU group bound to $dev_driver"
			echo "You may need to also bind: sudo $SCRIPT_DIR/vfio-bind.sh $dev"
		fi
	fi
done

# Assets
KERNEL="$REPO_ROOT/.vm-assets/vmlinux.bin"
DISK="$REPO_ROOT/.vm-assets/ubuntu-gpu.raw"

if [[ ! -f "$KERNEL" ]]; then
	echo "ERROR: Kernel not found: $KERNEL"
	exit 1
fi

if [[ ! -f "$DISK" ]]; then
	echo "ERROR: Disk image not found: $DISK"
	echo "Create with: $SCRIPT_DIR/create-gpu-image.sh"
	exit 1
fi

# Network setup (tap0)
TAP_DEV="tap0"
if ! ip link show "$TAP_DEV" &>/dev/null; then
	echo "Creating tap device $TAP_DEV"
	ip tuntap add dev "$TAP_DEV" mode tap
	ip addr add 172.16.0.1/24 dev "$TAP_DEV"
	ip link set "$TAP_DEV" up
fi

echo ""
echo "=== Booting Cloud Hypervisor with GPU ==="
echo "GPU:    $GPU_ADDR"
echo "Kernel: $KERNEL"
echo "Disk:   $DISK"
echo "Net:    $TAP_DEV (172.16.0.1/24)"
echo ""
echo "SSH into VM: ssh -i $REPO_ROOT/.vm-assets/vm_key root@172.16.0.2"
echo ""

# Find cloud-hypervisor binary
CH_BIN="$REPO_ROOT/buck-out/v2/gen/root/*/cloud-hypervisor/cloud-hypervisor/__cloud-hypervisor__/cloud-hypervisor"
CH_BIN=$(ls $CH_BIN 2>/dev/null | head -1 || true)

if [[ -z "$CH_BIN" || ! -x "$CH_BIN" ]]; then
	echo "Cloud Hypervisor binary not found in buck-out"
	echo "Build with: nix develop --command buck2 build //cloud-hypervisor/cloud-hypervisor:cloud-hypervisor"
	exit 1
fi

exec "$CH_BIN" \
	--kernel "$KERNEL" \
	--disk path="$DISK" \
	--cmdline "console=ttyS0 root=/dev/vda1 rw pci=realloc" \
	--cpus boot=4 \
	--memory size=8G \
	--serial tty \
	--console off \
	--net tap="$TAP_DEV",mac=52:54:00:12:34:56 \
	--device path="$GPU_PATH"
