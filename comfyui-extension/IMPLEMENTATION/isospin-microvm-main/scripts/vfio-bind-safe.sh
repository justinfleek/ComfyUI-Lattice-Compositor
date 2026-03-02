#!/usr/bin/env bash
# Safely bind PCI device(s) to vfio-pci driver
# CHECKS if GPU is in use for display before unbinding
# Usage: sudo ./vfio-bind-safe.sh 0000:01:00.0 [0000:01:00.1 ...]

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

if [[ $EUID -ne 0 ]]; then
	echo -e "${RED}Must run as root${NC}"
	exit 1
fi

if [[ $# -eq 0 ]]; then
	echo "Usage: $0 <pci-address> [<pci-address> ...]"
	echo "Example: $0 0000:01:00.0 0000:01:00.1"
	exit 1
fi

# Check if any GPU is being used for active display
check_gpu_in_use() {
	local dev=$1
	local dev_path="/sys/bus/pci/devices/$dev"

	# Check if this is a VGA/display device
	local class=$(cat "$dev_path/class" 2>/dev/null || echo "")
	if [[ ! "$class" =~ ^0x03 ]]; then
		# Not a display device, safe to unbind
		return 1
	fi

	# Check if drm is using this device
	if [[ -d "$dev_path/drm" ]]; then
		local cards=$(ls "$dev_path/drm" 2>/dev/null | grep "^card" || true)
		for card in $cards; do
			# Check if this card has active framebuffer
			if [[ -e "/dev/dri/$card" ]]; then
				# Check if X or Wayland is using this card
				if lsof "/dev/dri/$card" 2>/dev/null | grep -qE "Xorg|Xwayland|gnome-shell|kwin|sway|weston"; then
					return 0 # In use!
				fi
				# Check for render nodes too
				local render="${card/card/renderD}"
				render="renderD$((128 + ${card#card}))"
				if [[ -e "/dev/dri/$render" ]]; then
					if lsof "/dev/dri/$render" 2>/dev/null | grep -q .; then
						return 0 # In use!
					fi
				fi
			fi
		done
	fi

	# Check if nvidia-drm is loaded and this is an nvidia GPU
	if [[ -L "$dev_path/driver" ]]; then
		local driver=$(basename "$(readlink "$dev_path/driver")")
		if [[ "$driver" == "nvidia" ]]; then
			# Check if nvidia-drm modeset is active
			if lsmod | grep -q nvidia_drm; then
				# Check if any console is using this
				if [[ -e "$dev_path/drm" ]]; then
					return 0 # Assume in use if nvidia_drm loaded
				fi
			fi
		fi
	fi

	return 1 # Not in use
}

# Check for alternative display
check_alternative_display() {
	local exclude_dev=$1

	# Look for other VGA devices
	for dev_path in /sys/bus/pci/devices/*; do
		local dev=$(basename "$dev_path")
		[[ "$dev" == "$exclude_dev" ]] && continue

		local class=$(cat "$dev_path/class" 2>/dev/null || echo "")
		if [[ "$class" =~ ^0x03 ]]; then
			# Found another display device
			local vendor=$(cat "$dev_path/vendor" 2>/dev/null || echo "")
			local device=$(cat "$dev_path/device" 2>/dev/null || echo "")
			echo "$dev ($vendor:$device)"
			return 0
		fi
	done

	return 1
}

# Ensure vfio-pci module is loaded
modprobe vfio-pci

echo -e "${YELLOW}=== VFIO Safe Bind ===${NC}"
echo ""

# First pass: safety checks
for dev in "$@"; do
	dev_path="/sys/bus/pci/devices/$dev"

	if [[ ! -d "$dev_path" ]]; then
		echo -e "${RED}ERROR: Device $dev not found${NC}"
		exit 1
	fi

	# Check if GPU is in use for display
	if check_gpu_in_use "$dev"; then
		echo -e "${RED}WARNING: $dev appears to be in use for display!${NC}"

		alt=$(check_alternative_display "$dev" || echo "none")
		if [[ "$alt" != "none" ]]; then
			echo -e "${YELLOW}Alternative display device found: $alt${NC}"
			echo ""
			echo "Options:"
			echo "  1. Switch your display to the other GPU first"
			echo "  2. SSH in and run this script headless"
			echo "  3. Use --force to unbind anyway (will lose display!)"
		else
			echo -e "${RED}No alternative display device found!${NC}"
			echo ""
			echo "Options:"
			echo "  1. SSH in and run this script headless"
			echo "  2. Use --force to unbind anyway (will lose display!)"
		fi
		echo ""
		read -p "Continue anyway? [y/N] " -n 1 -r
		echo
		if [[ ! $REPLY =~ ^[Yy]$ ]]; then
			echo "Aborted."
			exit 1
		fi
	fi
done

# Second pass: check IOMMU groups
echo "Checking IOMMU groups..."
declare -A groups_to_bind

for dev in "$@"; do
	dev_path="/sys/bus/pci/devices/$dev"

	if [[ ! -L "$dev_path/iommu_group" ]]; then
		echo -e "${RED}ERROR: $dev has no IOMMU group. Is IOMMU enabled?${NC}"
		echo "Add intel_iommu=on or amd_iommu=on to kernel cmdline"
		exit 1
	fi

	group=$(basename "$(readlink "$dev_path/iommu_group")")
	groups_to_bind[$group]=1

	echo "  $dev -> IOMMU group $group"
done

# Check if all devices in each group will be bound
echo ""
echo "Verifying IOMMU group completeness..."
for group in "${!groups_to_bind[@]}"; do
	group_devs=$(ls "/sys/kernel/iommu_groups/$group/devices/")
	for gdev in $group_devs; do
		found=0
		for dev in "$@"; do
			if [[ "$dev" == "$gdev" ]]; then
				found=1
				break
			fi
		done
		if [[ $found -eq 0 ]]; then
			# Check if it's already bound to vfio-pci
			gdev_path="/sys/bus/pci/devices/$gdev"
			if [[ -L "$gdev_path/driver" ]]; then
				driver=$(basename "$(readlink "$gdev_path/driver")")
				if [[ "$driver" != "vfio-pci" ]]; then
					echo -e "${YELLOW}WARNING: $gdev is in IOMMU group $group but not in bind list${NC}"
					echo "  Currently bound to: $driver"
					echo "  You should also bind this device for proper isolation"
					echo ""
					read -p "Add $gdev to bind list? [Y/n] " -n 1 -r
					echo
					if [[ ! $REPLY =~ ^[Nn]$ ]]; then
						set -- "$@" "$gdev"
						echo "  Added $gdev"
					fi
				fi
			fi
		fi
	done
done

# Third pass: do the actual binding
echo ""
echo -e "${GREEN}Binding devices to vfio-pci...${NC}"

for dev in "$@"; do
	dev_path="/sys/bus/pci/devices/$dev"

	# Get current driver
	if [[ -L "$dev_path/driver" ]]; then
		current_driver=$(basename "$(readlink "$dev_path/driver")")
		if [[ "$current_driver" == "vfio-pci" ]]; then
			echo "  $dev: already bound to vfio-pci"
			continue
		fi
		echo "  $dev: unbinding from $current_driver"
		echo "$dev" >"/sys/bus/pci/drivers/$current_driver/unbind" 2>/dev/null || true
		sleep 0.5
	fi

	# Set driver override and bind
	echo "  $dev: binding to vfio-pci"
	echo "vfio-pci" >"$dev_path/driver_override"
	echo "$dev" >/sys/bus/pci/drivers/vfio-pci/bind

	echo -e "  ${GREEN}$dev -> vfio-pci${NC}"
done

echo ""
echo -e "${GREEN}=== Done ===${NC}"
echo ""
echo "VFIO devices:"
ls -la /dev/vfio/ 2>/dev/null || echo "  (none)"
echo ""
echo "To use with Cloud Hypervisor:"
echo "  sudo ./scripts/boot-ch-gpu.sh ${1:-0000:01:00.0}"
