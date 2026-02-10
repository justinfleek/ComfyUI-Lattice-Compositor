#!/usr/bin/env bash
# broker-test.sh - Test GPU broker with two VMs
#
# Architecture:
#   Host: GPU bound to vfio-pci
#   GPU VM (CID=3): VFIO passthrough, nvidia.ko, gpu-broker on vsock:9999
#   Client VM 1 (CID=4): nvidia-shim.ko connects to CID=3:9999
#   Client VM 2 (CID=5): nvidia-shim.ko connects to CID=3:9999
#
# Usage:
#   sudo ./broker-test.sh gpu      # Boot GPU VM
#   sudo ./broker-test.sh client1  # Boot Client VM 1
#   sudo ./broker-test.sh client2  # Boot Client VM 2

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

# Assets
KERNEL="$REPO_ROOT/.vm-assets/vmlinux-6.12.63.bin"
ROOTFS="$REPO_ROOT/.vm-assets/gpu-rootfs.ext4"

# GPU address
GPU_ADDR="0000:01:00.0"
GPU_AUDIO_ADDR="0000:01:00.1"

# VM CIDs
GPU_VM_CID=3
CLIENT1_CID=4
CLIENT2_CID=5

# Broker port
BROKER_PORT=9999

check_assets() {
	if [[ ! -f "$KERNEL" ]]; then
		echo "ERROR: Kernel not found: $KERNEL"
		exit 1
	fi
	if [[ ! -f "$ROOTFS" ]]; then
		echo "ERROR: Rootfs not found: $ROOTFS"
		exit 1
	fi
}

bind_vfio() {
	echo "=== Binding GPU to vfio-pci ==="
	"$SCRIPT_DIR/vfio-bind-safe.sh" "$GPU_ADDR" "$GPU_AUDIO_ADDR"
	"$SCRIPT_DIR/vfio-status.sh"
}

boot_gpu_vm() {
	echo "=== Booting GPU VM (CID=$GPU_VM_CID) ==="

	# Check VFIO binding
	if [[ ! -e "/sys/bus/pci/devices/$GPU_ADDR/driver" ]] ||
		[[ "$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/driver")")" != "vfio-pci" ]]; then
		echo "GPU not bound to vfio-pci, binding now..."
		bind_vfio
	fi

	# Create a copy of rootfs for this VM
	ROOTFS_GPU="/tmp/gpu-vm-rootfs.ext4"
	cp "$ROOTFS" "$ROOTFS_GPU"

	echo ""
	echo "Starting QEMU with GPU passthrough..."
	echo "Inside VM, run:"
	echo "  modprobe nvidia NVreg_OpenRmEnableUnsupportedGpus=1"
	echo "  gpu-broker --vsock-port $BROKER_PORT -v"
	echo ""

	qemu-system-x86_64 \
		-enable-kvm \
		-cpu host \
		-m 8G \
		-smp 4 \
		-kernel "$KERNEL" \
		-append "console=ttyS0 root=/dev/vda rw init=/init" \
		-drive file="$ROOTFS_GPU",format=raw,if=virtio \
		-device vfio-pci,host="$GPU_ADDR" \
		-device vhost-vsock-pci,guest-cid=$GPU_VM_CID \
		-nographic \
		-serial mon:stdio
}

boot_client_vm() {
	local cid=$1
	local name=$2

	echo "=== Booting $name (CID=$cid) ==="

	# Create a copy of rootfs for this VM
	ROOTFS_CLIENT="/tmp/${name}-rootfs.ext4"
	cp "$ROOTFS" "$ROOTFS_CLIENT"

	echo ""
	echo "Starting QEMU..."
	echo "Inside VM, run:"
	echo "  insmod /lib/modules/6.12.63/kernel/drivers/video/nvidia-shim.ko broker_cid=$GPU_VM_CID broker_port=$BROKER_PORT"
	echo "  nvidia-smi"
	echo ""

	qemu-system-x86_64 \
		-enable-kvm \
		-cpu host \
		-m 2G \
		-smp 2 \
		-kernel "$KERNEL" \
		-append "console=ttyS0 root=/dev/vda rw init=/init" \
		-drive file="$ROOTFS_CLIENT",format=raw,if=virtio \
		-device vhost-vsock-pci,guest-cid=$cid \
		-nographic \
		-serial mon:stdio
}

usage() {
	echo "Usage: $0 {gpu|client1|client2|bind}"
	echo ""
	echo "  gpu      - Boot GPU VM with VFIO passthrough (run first)"
	echo "  client1  - Boot Client VM 1"
	echo "  client2  - Boot Client VM 2"
	echo "  bind     - Bind GPU to vfio-pci"
	exit 1
}

check_assets

case "${1:-}" in
gpu)
	boot_gpu_vm
	;;
client1)
	boot_client_vm $CLIENT1_CID "client1"
	;;
client2)
	boot_client_vm $CLIENT2_CID "client2"
	;;
bind)
	bind_vfio
	;;
*)
	usage
	;;
esac
