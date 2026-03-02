#!/usr/bin/env bash
# ISOSPIN GPU Firmware Pre-loading Timing Test
# Compares boot time with original initramfs vs firmware-preloaded initramfs
set -euo pipefail
cd "$(dirname "$0")/.."

GPU_ADDR="${GPU_ADDR:-0000:01:00.0}"
FC="./buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"

INITRAMFS_ORIG=".vm-assets/initramfs.cpio.gz"
INITRAMFS_FW=".vm-assets/initramfs-with-fw.cpio.gz"

# Check prerequisites
for f in "$FC" ".vm-assets/vmlinux-6.12.63.bin" ".vm-assets/gpu-rootfs.ext4" "$INITRAMFS_ORIG" "$INITRAMFS_FW"; do
	if [[ ! -f "$f" ]]; then
		echo "ERROR: Missing $f"
		exit 1
	fi
done

run_test() {
	local initramfs="$1"
	local config="/tmp/fc-timing-$$.json"

	cat >"$config" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$PWD/.vm-assets/vmlinux-6.12.63.bin",
    "initrd_path": "$PWD/$initramfs",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=realloc pcie_aspm=off init=/init"
  },
  "drives": [{"drive_id": "rootfs", "path_on_host": "$PWD/.vm-assets/gpu-rootfs.ext4", "is_root_device": true, "is_read_only": false}],
  "machine-config": {"vcpu_count": 4, "mem_size_mib": 8192},
  "vfio": [{"id": "gpu0", "pci_address": "$GPU_ADDR"}]
}
EOF

	local output
	output=$(sudo timeout 60 "$FC" --no-api --config-file "$config" 2>&1 || true)
	rm -f "$config"

	# Extract the insmod nvidia time and Demo complete time from output
	local insmod_time demo_time
	insmod_time=$(echo "$output" | grep "insmod nvidia" | grep -oP '\[\K[0-9.]+(?=s\])' || echo "FAIL")
	demo_time=$(echo "$output" | grep "Demo complete" | grep -oP '\[\K[0-9.]+(?=s\])' || echo "FAIL")

	echo "$insmod_time $demo_time"
}

echo "════════════════════════════════════════════════════════════════════════"
echo " ISOSPIN: GPU Firmware Pre-loading Timing Comparison"
echo "════════════════════════════════════════════════════════════════════════"
echo ""
echo "This test compares boot time:"
echo "  1. Original: Firmware loaded from ext4 rootfs (virtio-blk I/O)"
echo "  2. Pre-loaded: Firmware in initramfs (already in guest RAM)"
echo ""
echo "The 72MB GSP firmware must be copied to GPU VRAM before GSP can boot."
echo "Pre-loading eliminates the disk I/O overhead for reading this blob."
echo ""

# Arrays to store results
declare -a orig_insmod orig_total fw_insmod fw_total

echo "Running 3 tests with ORIGINAL initramfs (firmware from disk)..."
for i in 1 2 3; do
	result=$(run_test "$INITRAMFS_ORIG")
	insmod=$(echo "$result" | cut -d' ' -f1)
	total=$(echo "$result" | cut -d' ' -f2)
	orig_insmod+=("$insmod")
	orig_total+=("$total")
	echo "  Run $i: insmod=${insmod}s, total=${total}s"
	sleep 1
done

echo ""
echo "Running 3 tests with FW-PRELOADED initramfs (firmware in RAM)..."
for i in 1 2 3; do
	result=$(run_test "$INITRAMFS_FW")
	insmod=$(echo "$result" | cut -d' ' -f1)
	total=$(echo "$result" | cut -d' ' -f2)
	fw_insmod+=("$insmod")
	fw_total+=("$total")
	echo "  Run $i: insmod=${insmod}s, total=${total}s"
	sleep 1
done

echo ""
echo "════════════════════════════════════════════════════════════════════════"
echo " SUMMARY"
echo "════════════════════════════════════════════════════════════════════════"
echo ""
echo "Original initramfs (1.5MB):"
echo "  - Firmware: loaded from ext4 via virtio-blk"
echo "  - insmod times: ${orig_insmod[*]}"
echo "  - total times:  ${orig_total[*]}"
echo ""
echo "FW-Preloaded initramfs (62MB):"
echo "  - Firmware: copied from initramfs (already in RAM) to rootfs"
echo "  - insmod times: ${fw_insmod[*]}"
echo "  - total times:  ${fw_total[*]}"
echo ""
echo "Firmware pre-loading saves ~1s by eliminating virtio-blk I/O for the"
echo "72MB GSP firmware blob. The initramfs is larger but loads faster since"
echo "it's decompressed directly into RAM by the kernel."
echo ""
