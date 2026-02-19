#!/usr/bin/env bash
# Test broker loopback: single VM with vsock to host mock broker
#
# Usage: sudo ./scripts/test-broker-loopback.sh
#
# This script:
#   1. Prepares rootfs with nvidia-shim.ko
#   2. Starts mock broker listening on the Firecracker vsock socket
#   3. Prints instructions to start VM in another terminal
#
set -euo pipefail

if [[ $EUID -ne 0 ]]; then
	echo "Must run as root: sudo $0"
	exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Build paths - use nix store outputs
echo "Building components..."
KERNEL=$(nix build "${PROJECT_ROOT}#fc-gpu-kernel" --print-out-paths 2>/dev/null)/vmlinux
INITRAMFS=$(nix build "${PROJECT_ROOT}#fc-initramfs" --print-out-paths 2>/dev/null)/initrd
ROOTFS_SRC=$(nix build "${PROJECT_ROOT}#fc-rootfs" --print-out-paths 2>/dev/null)/rootfs.ext4
BROKER=$(nix build "${PROJECT_ROOT}#gpu-broker" --print-out-paths 2>/dev/null)/bin/gpu-broker
# Note: nvidia-shim.ko is already included in fc-rootfs at /lib/modules/6.12.10/extra/

echo ""
echo "=== Broker Loopback Test ==="
echo "Kernel:    $KERNEL"
echo "Initramfs: $INITRAMFS"
echo "Rootfs:    $ROOTFS_SRC"
echo "Broker:    $BROKER"
echo ""

# Create writable rootfs (already has nvidia-shim.ko built in)
ROOTFS="/tmp/broker-test-rootfs.ext4"
echo "Creating writable rootfs copy..."
cp "$ROOTFS_SRC" "$ROOTFS"
chmod 644 "$ROOTFS"
echo "Rootfs ready at $ROOTFS"

# The vsock UDS path base (Firecracker creates this)
VSOCK_BASE="/tmp/fc-broker-test.sock"
# Broker will listen on ${VSOCK_BASE}_9999 for guest connections to port 9999
BROKER_SOCKET="${VSOCK_BASE}_9999"

# Clean up stale sockets
rm -f "$VSOCK_BASE" "$BROKER_SOCKET"

# Create VM config with vsock
cat >/tmp/fc-broker-test.json <<EOF
{
  "boot-source": {
    "kernel_image_path": "$KERNEL",
    "initrd_path": "$INITRAMFS",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=off init=/init"
  },
  "drives": [{
    "drive_id": "rootfs",
    "path_on_host": "$ROOTFS",
    "is_root_device": true,
    "is_read_only": false
  }],
  "machine-config": {
    "vcpu_count": 2,
    "mem_size_mib": 512
  },
  "vsock": {
    "guest_cid": 3,
    "uds_path": "$VSOCK_BASE"
  }
}
EOF

echo "Created VM config: /tmp/fc-broker-test.json"
echo "  vsock base path: $VSOCK_BASE"
echo "  broker will listen on: $BROKER_SOCKET"
echo ""
echo "============================================================"
echo "STEP 1: This terminal runs the broker"
echo "============================================================"
echo ""
echo "Starting mock broker on $BROKER_SOCKET..."
echo "The broker handles guest vsock connections to port 9999."
echo ""
echo "Press Ctrl+C to stop the broker when done."
echo ""
echo "============================================================"
echo "STEP 2: In another terminal, start the VM:"
echo "============================================================"
echo ""
echo "  sudo firecracker --no-api --config-file /tmp/fc-broker-test.json"
echo ""
echo "============================================================"
echo "STEP 3: Inside the VM shell, test the shim:"
echo "============================================================"
echo ""
echo "  # Load the shim module (CID 2 = host)"
echo "  insmod /lib/modules/6.12.10/extra/nvidia-shim.ko broker_cid=2 broker_port=9999"
echo ""
echo "  # Check devices were created"
echo "  ls -la /dev/nvidia*"
echo ""
echo "  # Check kernel logs"
echo "  dmesg | tail -20"
echo ""
echo "============================================================"
echo ""

# Start broker with Firecracker vsock path
# --firecracker-vsock takes the BASE path, broker appends _<port>
exec "$BROKER" --mock -v --vsock-port 9999 --firecracker-vsock "$VSOCK_BASE"
