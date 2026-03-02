#!/usr/bin/env bash
# Unbind PCI device(s) from vfio-pci and let them re-probe to native drivers
# Usage: sudo ./vfio-unbind.sh 0000:01:00.0 [0000:01:00.1 ...]

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

for dev in "$@"; do
	dev_path="/sys/bus/pci/devices/$dev"

	if [[ ! -d "$dev_path" ]]; then
		echo "Device $dev not found"
		exit 1
	fi

	# Unbind from vfio-pci if bound
	if [[ -L "$dev_path/driver" ]]; then
		current_driver=$(basename "$(readlink "$dev_path/driver")")
		if [[ "$current_driver" == "vfio-pci" ]]; then
			echo "Unbinding $dev from vfio-pci"
			echo "$dev" >/sys/bus/pci/drivers/vfio-pci/unbind 2>/dev/null || true
		fi
	fi

	# Clear driver override
	echo "" >"$dev_path/driver_override"

	# Re-probe to let kernel find native driver
	echo "Re-probing $dev"
	echo "$dev" >/sys/bus/pci/drivers_probe

	# Show what driver picked it up
	sleep 0.5
	if [[ -L "$dev_path/driver" ]]; then
		new_driver=$(basename "$(readlink "$dev_path/driver")")
		echo "Done: $dev -> $new_driver"
	else
		echo "Done: $dev (no driver bound)"
	fi
done
