#!/usr/bin/env bash
# GPU Passthrough Timing Test
# Compares Cloud Hypervisor vs Firecracker VFIO performance
#
# Usage: sudo ./scripts/gpu-timing-test.sh [ch|fc|both]
#
# This test measures:
# - PCI BAR enumeration time
# - NVIDIA driver module load time
# - nvidia-smi initialization time (first call vs subsequent)
# - Total boot-to-GPU-ready time

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

# Configuration
GPU_ADDR="${GPU_ADDR:-0000:01:00.0}"
KERNEL_6_12="$REPO_ROOT/.vm-assets/vmlinux-6.12.63.bin"
INITRAMFS="$REPO_ROOT/.vm-assets/initramfs.cpio.gz"
ROOTFS="$REPO_ROOT/.vm-assets/gpu-rootfs.ext4"
RESULTS_DIR="$REPO_ROOT/.vm-assets/timing-results"
TIMEOUT=120

# Binaries
CH_BIN="$REPO_ROOT/buck-out/v2/gen/root/b42aeba648b8c415/cloud-hypervisor/cloud-hypervisor/__cloud-hypervisor__/cloud_hypervisor_bin"
FC_BIN="$REPO_ROOT/buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"

mkdir -p "$RESULTS_DIR"

log() {
	echo "[$(date '+%H:%M:%S')] $*" >&2
}

check_prerequisites() {
	log "Checking prerequisites..."

	if [[ $EUID -ne 0 ]]; then
		echo "ERROR: Must run as root" >&2
		exit 1
	fi

	if [[ ! -d "/sys/bus/pci/devices/$GPU_ADDR" ]]; then
		echo "ERROR: GPU $GPU_ADDR not found" >&2
		exit 1
	fi

	# Check driver binding
	if [[ -L "/sys/bus/pci/devices/$GPU_ADDR/driver" ]]; then
		local driver=$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/driver")")
		if [[ "$driver" != "vfio-pci" ]]; then
			echo "ERROR: GPU bound to $driver, not vfio-pci" >&2
			echo "Run: sudo $SCRIPT_DIR/vfio-bind.sh $GPU_ADDR" >&2
			exit 1
		fi
		log "GPU $GPU_ADDR bound to vfio-pci"
	fi

	# Check IOMMU group
	local iommu_group=$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/iommu_group")")
	log "IOMMU group: $iommu_group"

	# Check rootfs
	if [[ ! -f "$ROOTFS" ]]; then
		echo "ERROR: Rootfs not found: $ROOTFS" >&2
		exit 1
	fi

	log "Rootfs: $ROOTFS ($(du -h "$ROOTFS" | cut -f1))"
}

run_cloud_hypervisor_test() {
	log "=========================================="
	log "CLOUD HYPERVISOR TEST"
	log "=========================================="

	local test_rootfs="$RESULTS_DIR/ch-test-rootfs.ext4"
	local output_file="$RESULTS_DIR/ch-output-$(date +%Y%m%d-%H%M%S).log"
	local kernel="$KERNEL_6_12"

	if [[ ! -x "$CH_BIN" ]]; then
		log "ERROR: Cloud Hypervisor binary not found: $CH_BIN"
		return 1
	fi

	log "Creating test rootfs copy..."
	cp "$ROOTFS" "$test_rootfs"

	log "Kernel: $kernel"
	log "Rootfs: $test_rootfs"
	log "Output: $output_file"
	log "Starting Cloud Hypervisor..."

	local start_time=$(date +%s)

	# Get all devices in the same IOMMU group
	local iommu_group=$(basename "$(readlink "/sys/bus/pci/devices/$GPU_ADDR/iommu_group")")
	local device_args=()
	for dev in /sys/kernel/iommu_groups/$iommu_group/devices/*; do
		local dev_addr=$(basename "$dev")
		device_args+=("path=/sys/bus/pci/devices/$dev_addr")
		log "Adding device: $dev_addr"
	done

	# Run with timeout, capture output
	# Use initramfs if available (needed for virtio-blk module loading)
	local initramfs_arg=""
	if [[ -f "$INITRAMFS" ]]; then
		initramfs_arg="--initramfs $INITRAMFS"
		log "Using initramfs: $INITRAMFS"
	fi

	timeout "$TIMEOUT" "$CH_BIN" \
		--kernel "$kernel" \
		$initramfs_arg \
		--disk path="$test_rootfs" \
		--cmdline "console=ttyS0 root=/dev/vda rw init=/init pci=realloc pcie_aspm=off firmware_class.path=/lib/firmware" \
		--cpus boot=4 \
		--memory size=8G,shared=on \
		--serial tty \
		--console off \
		--device "${device_args[@]}" \
		2>&1 | tee "$output_file" || true

	local end_time=$(date +%s)
	local total_time=$((end_time - start_time))

	log "Cloud Hypervisor test completed in ${total_time}s"
	log "Output saved to: $output_file"

	# Extract timing info
	analyze_output "$output_file" "CH"

	rm -f "$test_rootfs"
}

run_firecracker_test() {
	log "=========================================="
	log "FIRECRACKER TEST"
	log "=========================================="

	local fc_bin="$FC_BIN"
	if [[ ! -x "$fc_bin" ]]; then
		log "ERROR: Firecracker binary not found: $fc_bin"
		log "Build with: nix develop --command buck2 build //firecracker/src/firecracker:firecracker"
		return 1
	fi

	local test_rootfs="$RESULTS_DIR/fc-test-rootfs.ext4"
	local output_file="$RESULTS_DIR/fc-output-$(date +%Y%m%d-%H%M%S).log"
	local config_file="$RESULTS_DIR/fc-config.json"

	log "Creating test rootfs copy..."
	cp "$ROOTFS" "$test_rootfs"

	log "Binary: $fc_bin"
	log "Kernel: $KERNEL_6_12"
	log "Rootfs: $test_rootfs"
	log "Output: $output_file"

	# Create config - use printf to avoid heredoc issues
	# Include initramfs if available for virtio module loading
	local initrd_line=""
	if [[ -f "$INITRAMFS" ]]; then
		initrd_line=',"initrd_path": "'"$INITRAMFS"'"'
		log "Using initramfs: $INITRAMFS"
	fi

	printf '%s\n' '{
  "boot-source": {
    "kernel_image_path": "'"$KERNEL_6_12"'"'"$initrd_line"',
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=realloc pcie_aspm=off firmware_class.path=/lib/firmware init=/init"
  },
  "drives": [{
    "drive_id": "rootfs",
    "path_on_host": "'"$test_rootfs"'",
    "is_root_device": true,
    "is_read_only": false
  }],
  "machine-config": {
    "vcpu_count": 4,
    "mem_size_mib": 8192
  },
  "vfio": [{
    "id": "gpu0",
    "pci_address": "'"$GPU_ADDR"'"
  }]
}' >"$config_file"

	log "Config file:"
	cat "$config_file" >&2

	log "Starting Firecracker..."
	local start_time=$(date +%s)

	# Run with timeout, capture output
	timeout "$TIMEOUT" "$fc_bin" \
		--no-api \
		--config-file "$config_file" \
		2>&1 | tee "$output_file" || true

	local end_time=$(date +%s)
	local total_time=$((end_time - start_time))

	log "Firecracker test completed in ${total_time}s"
	log "Output saved to: $output_file"

	# Extract timing info
	analyze_output "$output_file" "FC"

	rm -f "$test_rootfs" "$config_file"
}

analyze_output() {
	local output_file="$1"
	local prefix="$2"

	log ""
	log "=== TIMING ANALYSIS ($prefix) ==="

	echo ""
	echo "PCI Enumeration:"
	# Extract key timestamps from kernel log
	grep -E "pci 0000:.*\[10de" "$output_file" | head -3 | sed 's/^/  /' || echo "  N/A"

	echo ""
	echo "LTR/Timeout messages:"
	grep -iE "LTR|Timed out|pcie_capability" "$output_file" | head -5 | sed 's/^/  /' || echo "  None found"

	echo ""
	echo "NVIDIA Driver Load:"
	grep -E "nvidia|NVIDIA|Loading.*\.ko" "$output_file" | head -10 | sed 's/^/  /' || echo "  N/A"

	echo ""
	echo "nvidia-smi Timing (from init script):"
	grep -A4 "nvidia-smi" "$output_file" | grep -E "Kernel time|nvidia-smi" | sed 's/^/  /' || echo "  N/A"

	echo ""
	echo "Delay patterns found:"
	grep -E "(took [0-9]+ [um]?secs|Timed out|delay|waiting)" "$output_file" | head -10 | sed 's/^/  /' || echo "  None"

	echo ""
	echo "Full dmesg GPU section:"
	grep -E "pci 0000:00:0[23]|nvidia|NVIDIA|vfio|VFIO" "$output_file" | head -30 | sed 's/^/  /' || echo "  N/A"

	log ""
}

usage() {
	echo "Usage: $0 [ch|fc|both]"
	echo ""
	echo "  ch    - Run Cloud Hypervisor test only"
	echo "  fc    - Run Firecracker test only"
	echo "  both  - Run both tests (default)"
	echo ""
	echo "Environment variables:"
	echo "  GPU_ADDR  - PCI address of GPU (default: 0000:01:00.0)"
	echo ""
	exit 1
}

main() {
	local mode="${1:-both}"

	case "$mode" in
	ch | cloud-hypervisor)
		check_prerequisites
		run_cloud_hypervisor_test
		;;
	fc | firecracker)
		check_prerequisites
		run_firecracker_test
		;;
	both)
		check_prerequisites
		run_cloud_hypervisor_test
		echo ""
		echo ""
		run_firecracker_test
		;;
	-h | --help | help)
		usage
		;;
	*)
		echo "Unknown mode: $mode"
		usage
		;;
	esac

	log ""
	log "Results saved to: $RESULTS_DIR"
}

main "$@"
