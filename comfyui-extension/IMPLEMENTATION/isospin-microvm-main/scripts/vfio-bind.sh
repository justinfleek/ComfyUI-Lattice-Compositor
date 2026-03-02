#!/usr/bin/env bash
# Bind PCI device(s) to vfio-pci driver
# Usage: sudo ./vfio-bind.sh 0000:01:00.0 [0000:01:00.1 ...]

set -euo pipefail

if [[ $EUID -ne 0 ]]; then
	echo "Must run as root"
	exit 1
fi

if [[ $# -eq 0 ]]; then
	echo "Usage: $0 <pci-address> [<pci-address> ...]"
	echo "Example: $0 0000:01:00.0 0000:01:00.1"
	exit 1
fi

# Ensure vfio-pci module is loaded
modprobe vfio-pci

for dev in "$@"; do
	dev_path="/sys/bus/pci/devices/$dev"

	if [[ ! -d "$dev_path" ]]; then
		echo "Device $dev not found"
		exit 1
	fi

	# Get current driver
	if [[ -L "$dev_path/driver" ]]; then
		current_driver=$(basename "$(readlink "$dev_path/driver")")
		echo "Unbinding $dev from $current_driver"
		echo "$dev" >"/sys/bus/pci/drivers/$current_driver/unbind" 2>/dev/null || true
	fi

	# Set driver override and bind
	echo "Binding $dev to vfio-pci"
	echo "vfio-pci" >"$dev_path/driver_override"
	echo "$dev" >/sys/bus/pci/drivers/vfio-pci/bind

	echo "Done: $dev -> vfio-pci"
done

echo ""
echo "Verify with: ls -la /sys/bus/pci/devices/*/driver"
