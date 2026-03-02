#!/usr/bin/env bash
# GPU VM Boot Script
#
# Boots the complete GPU broker stack:
# 1. GPU VM (Cloud Hypervisor with VFIO GPU passthrough)
# 2. Socat proxy for vsock bridging
# 3. Optionally, worker VM (Firecracker with nvidia-shim)
#
# Prerequisites:
# - NVIDIA GPU bound to vfio-pci (use scripts/vfio-bind.sh)
# - Root privileges for Cloud Hypervisor
#
# Usage:
#   ./scripts/gpu-vm-boot.sh                    # Boot GPU VM only
#   ./scripts/gpu-vm-boot.sh --with-worker      # Boot GPU VM + worker VM
#   ./scripts/gpu-vm-boot.sh --kill             # Kill all VMs and proxies

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Configuration
GPU_PCI_ADDR="${GPU_PCI_ADDR:-0000:01:00.0}"
GPU_VM_CID=3
WORKER_VM_CID=5
VSOCK_PORT=9999

# Asset paths - use existing 6.12.63 assets (kernel + modules must match)
GPU_KERNEL="${PROJECT_DIR}/.vm-assets/vmlinux-6.12.63.bin"
GPU_INITRAMFS="${PROJECT_DIR}/.vm-assets/initramfs-6.12.63-pci.cpio.gz"
GPU_ROOTFS="${PROJECT_DIR}/.vm-assets/gpu-rootfs.ext4"

# Worker VM assets - use Nix-built kernel that matches nvidia-shim
WORKER_KERNEL="" # Will be set from Nix
WORKER_ROOTFS="" # Will be copied from Nix (needs to be writable)

# Socket paths
GPU_VM_VSOCK_SOCK="/tmp/gpu-vm-vsock.sock"
FC_WORKER_SOCK="/tmp/fc-worker.sock"
FC_WORKER_PROXY_SOCK="/tmp/fc-worker.sock_${VSOCK_PORT}"
GPU_VM_LOG="/tmp/gpu-vm.log"
WORKER_VM_LOG="/tmp/worker-vm.log"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

log_info() { echo -e "${BLUE}[INFO]${NC} $*"; }
log_ok() { echo -e "${GREEN}[OK]${NC} $*"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $*"; }
log_error() { echo -e "${RED}[ERROR]${NC} $*"; }

# Get paths from Nix
get_nix_paths() {
	log_info "Resolving Nix package paths..."

	CH_BIN=$(nix build nixpkgs#cloud-hypervisor --no-link --print-out-paths 2>/dev/null)/bin/cloud-hypervisor
	FC_BIN=$(nix build nixpkgs#firecracker --no-link --print-out-paths 2>/dev/null)/bin/firecracker

	# Worker kernel and rootfs from our flake
	WORKER_KERNEL=$(nix build "${PROJECT_DIR}#fc-gpu-kernel" --no-link --print-out-paths 2>/dev/null)/vmlinux
	FC_ROOTFS_SRC=$(nix build "${PROJECT_DIR}#fc-rootfs" --no-link --print-out-paths 2>/dev/null)/rootfs.ext4

	log_ok "Cloud Hypervisor: $CH_BIN"
	log_ok "Firecracker: $FC_BIN"
	log_ok "Worker kernel: $WORKER_KERNEL"
}

# Kill all running VMs and proxies
kill_all() {
	log_info "Killing all GPU broker components..."

	sudo pkill -9 cloud-hyperviso 2>/dev/null || true
	sudo pkill -9 firecracker 2>/dev/null || true
	sudo pkill -9 socat 2>/dev/null || true

	sudo rm -f "$GPU_VM_VSOCK_SOCK" "$FC_WORKER_SOCK" "$FC_WORKER_PROXY_SOCK" 2>/dev/null || true
	sudo rm -f "${FC_WORKER_SOCK}_"* 2>/dev/null || true

	sleep 1
	log_ok "All components killed"
}

# Check prerequisites
check_prerequisites() {
	log_info "Checking prerequisites..."

	# Check if GPU is bound to vfio-pci
	if [ ! -d "/sys/bus/pci/devices/${GPU_PCI_ADDR}/driver" ]; then
		log_error "GPU ${GPU_PCI_ADDR} not found"
		exit 1
	fi

	local driver=$(basename $(readlink "/sys/bus/pci/devices/${GPU_PCI_ADDR}/driver" 2>/dev/null) 2>/dev/null)
	if [ "$driver" != "vfio-pci" ]; then
		log_error "GPU ${GPU_PCI_ADDR} is bound to '$driver', not 'vfio-pci'"
		log_info "Run: sudo ./scripts/vfio-bind.sh ${GPU_PCI_ADDR}"
		exit 1
	fi

	# Check required files
	for f in "$GPU_KERNEL" "$GPU_ROOTFS"; do
		if [ ! -f "$f" ]; then
			log_error "Required file not found: $f"
			exit 1
		fi
	done

	# Check initramfs
	if [ ! -f "$GPU_INITRAMFS" ]; then
		log_warn "GPU initramfs not found at $GPU_INITRAMFS"
		log_info "Creating initramfs from manual steps (one-time)..."
		# Would need to create this - for now, error out
		log_error "Please create initramfs first (see docs/session-state-*.md)"
		exit 1
	fi

	log_ok "All prerequisites met"
}

# Start GPU VM
start_gpu_vm() {
	log_info "Starting GPU VM (Cloud Hypervisor + VFIO)..."

	# Clean up old sockets
	sudo rm -f "$GPU_VM_VSOCK_SOCK" "$GPU_VM_LOG" 2>/dev/null || true

	sudo "$CH_BIN" \
		--kernel "$GPU_KERNEL" \
		--initramfs "$GPU_INITRAMFS" \
		--disk path="$GPU_ROOTFS" \
		--cmdline "console=ttyS0 root=/dev/vda rw init=/init" \
		--cpus boot=2 --memory size=8G \
		--vsock cid=${GPU_VM_CID},socket="$GPU_VM_VSOCK_SOCK" \
		--device path=/sys/bus/pci/devices/${GPU_PCI_ADDR} \
		--serial file="$GPU_VM_LOG" --console off &

	GPU_VM_PID=$!
	log_info "GPU VM starting (PID: $GPU_VM_PID)..."

	# Wait for vsock socket
	local timeout=30
	while [ $timeout -gt 0 ]; do
		if [ -S "$GPU_VM_VSOCK_SOCK" ]; then
			log_ok "GPU VM vsock socket ready"
			break
		fi
		sleep 1
		((timeout--))
	done

	if [ ! -S "$GPU_VM_VSOCK_SOCK" ]; then
		log_error "GPU VM failed to create vsock socket"
		log_info "Check log: $GPU_VM_LOG"
		exit 1
	fi

	# Wait for broker to start (NVIDIA driver takes ~15-20 seconds to load)
	log_info "Waiting for GPU broker to start (this may take 20-30 seconds)..."
	timeout=60
	while [ $timeout -gt 0 ]; do
		if grep -q "Broker running" "$GPU_VM_LOG" 2>/dev/null; then
			log_ok "GPU broker is running"
			break
		fi
		if grep -q "Broker failed" "$GPU_VM_LOG" 2>/dev/null; then
			log_error "GPU broker failed to start"
			tail -20 "$GPU_VM_LOG"
			exit 1
		fi
		sleep 1
		((timeout--))
	done

	# Show GPU info
	if grep -q "GPU 0:" "$GPU_VM_LOG" 2>/dev/null; then
		grep "GPU 0:" "$GPU_VM_LOG"
	fi
}

# Start socat proxy
start_vsock_proxy() {
	log_info "Starting vsock proxy..."

	sudo rm -f "$FC_WORKER_PROXY_SOCK" 2>/dev/null || true

	sudo socat UNIX-LISTEN:${FC_WORKER_PROXY_SOCK},fork,mode=777 \
		UNIX-CONNECT:${GPU_VM_VSOCK_SOCK} &

	sleep 1

	if [ -S "$FC_WORKER_PROXY_SOCK" ]; then
		log_ok "Vsock proxy ready at $FC_WORKER_PROXY_SOCK"
	else
		log_error "Failed to create vsock proxy"
		exit 1
	fi
}

# Start worker VM
start_worker_vm() {
	log_info "Starting worker VM (Firecracker)..."

	# Copy rootfs to writable location
	WORKER_ROOTFS="/tmp/fc-worker-rootfs.ext4"
	cp "$FC_ROOTFS_SRC" "$WORKER_ROOTFS"
	chmod 644 "$WORKER_ROOTFS"

	# Clean up old socket
	sudo rm -f "$FC_WORKER_SOCK" 2>/dev/null || true

	# Create config
	cat >/tmp/fc-worker-config.json <<EOF
{
    "boot-source": {
        "kernel_image_path": "$WORKER_KERNEL",
        "boot_args": "console=ttyS0 reboot=k panic=1 pci=off"
    },
    "drives": [{
        "drive_id": "rootfs",
        "path_on_host": "$WORKER_ROOTFS",
        "is_root_device": true,
        "is_read_only": false
    }],
    "machine-config": {
        "vcpu_count": 1,
        "mem_size_mib": 512
    },
    "vsock": {
        "guest_cid": ${WORKER_VM_CID},
        "uds_path": "$FC_WORKER_SOCK"
    }
}
EOF

	log_info "Starting Firecracker with serial output to terminal..."
	sudo "$FC_BIN" --no-api --config-file /tmp/fc-worker-config.json &

	WORKER_VM_PID=$!
	log_ok "Worker VM started (PID: $WORKER_VM_PID)"
}

# Main
main() {
	cd "$PROJECT_DIR"

	case "${1:-}" in
	--kill | -k)
		kill_all
		exit 0
		;;
	--help | -h)
		echo "GPU VM Boot Script"
		echo ""
		echo "Usage:"
		echo "  $0                  Boot GPU VM only"
		echo "  $0 --with-worker    Boot GPU VM and worker VM"
		echo "  $0 --kill           Kill all VMs and proxies"
		echo ""
		echo "Environment variables:"
		echo "  GPU_PCI_ADDR        PCI address of GPU (default: 0000:01:00.0)"
		exit 0
		;;
	esac

	get_nix_paths
	check_prerequisites
	kill_all # Clean slate

	start_gpu_vm
	start_vsock_proxy

	if [ "${1:-}" = "--with-worker" ]; then
		start_worker_vm
		log_ok "Full stack running!"
		log_info "Worker VM output shown below. Press Ctrl+C to stop."
		wait
	else
		log_ok "GPU VM running!"
		echo ""
		echo "To start a worker VM:"
		echo "  $0 --with-worker"
		echo ""
		echo "Or manually connect via vsock from any VM:"
		echo "  vsock CID=${GPU_VM_CID} port=${VSOCK_PORT}"
		echo ""
		echo "GPU VM log: $GPU_VM_LOG"
		echo "  tail -f $GPU_VM_LOG"
		echo ""
		log_info "Press Ctrl+C to stop GPU VM"
		wait
	fi
}

main "$@"
