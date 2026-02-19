#!/usr/bin/env bash
# Show VFIO status for GPU devices
# Usage: ./vfio-status.sh

echo "=== NVIDIA GPUs ==="
lspci -nn | grep -i nvidia || echo "No NVIDIA GPUs found"

echo ""
echo "=== IOMMU Groups ==="
for dev in /sys/bus/pci/devices/*; do
	bdf=$(basename "$dev")
	if lspci -s "$bdf" 2>/dev/null | grep -qi nvidia; then
		group=$(basename "$(readlink "$dev/iommu_group")" 2>/dev/null || echo "none")
		driver="none"
		if [[ -L "$dev/driver" ]]; then
			driver=$(basename "$(readlink "$dev/driver")")
		fi
		desc=$(lspci -s "$bdf" | cut -d: -f3-)
		echo "$bdf [group $group] [$driver] $desc"
	fi
done

echo ""
echo "=== VFIO Devices ==="
ls -la /dev/vfio/ 2>/dev/null || echo "No /dev/vfio/ (vfio module not loaded?)"
