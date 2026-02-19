#!/usr/bin/env bash
# run-firecracker.sh - Download test resources and boot a Firecracker microVM
#
# Usage:
#   ./scripts/run-firecracker.sh [setup|run|clean]
#
# Commands:
#   setup  - Download kernel and rootfs (run once)
#   run    - Start Firecracker microVM
#   clean  - Remove downloaded resources
#
# Prerequisites:
#   - KVM access: /dev/kvm must be readable/writable
#   - Built Firecracker: buck2 build //firecracker/src/firecracker:firecracker

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESOURCES_DIR="$REPO_ROOT/.firecracker-resources"
API_SOCKET="$RESOURCES_DIR/firecracker.sock"

ARCH="$(uname -m)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

info() { echo -e "${GREEN}[INFO]${NC} $*"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $*"; }
error() { echo -e "${RED}[ERROR]${NC} $*" >&2; }

check_kvm() {
	if [[ ! -r /dev/kvm ]] || [[ ! -w /dev/kvm ]]; then
		error "No access to /dev/kvm"
		echo "Try one of:"
		echo "  sudo setfacl -m u:\${USER}:rw /dev/kvm"
		echo "  sudo usermod -aG kvm \${USER}  # then re-login"
		exit 1
	fi
	info "KVM access: OK"
}

check_firecracker() {
	local fc_bin="$REPO_ROOT/buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"
	if [[ ! -x "$fc_bin" ]]; then
		error "Firecracker binary not found. Build it first:"
		echo "  buck2 build //firecracker/src/firecracker:firecracker"
		exit 1
	fi
	echo "$fc_bin"
}

setup() {
	info "Setting up Firecracker test resources in $RESOURCES_DIR"
	mkdir -p "$RESOURCES_DIR"
	cd "$RESOURCES_DIR"

	# Get latest CI version for kernel/rootfs
	local release_url="https://github.com/firecracker-microvm/firecracker/releases"
	local latest_version
	latest_version=$(basename "$(curl -fsSLI -o /dev/null -w '%{url_effective}' "${release_url}/latest")")
	local CI_VERSION="${latest_version%.*}"
	info "Using CI version: $CI_VERSION"

	# Download kernel
	if ! ls vmlinux-* 1>/dev/null 2>&1; then
		info "Downloading kernel for $ARCH..."
		local latest_kernel_key
		latest_kernel_key=$(curl -s "http://spec.ccfc.min.s3.amazonaws.com/?prefix=firecracker-ci/$CI_VERSION/$ARCH/vmlinux-&list-type=2" |
			grep -oP "(?<=<Key>)(firecracker-ci/$CI_VERSION/$ARCH/vmlinux-[0-9]+\.[0-9]+\.[0-9]{1,3})(?=</Key>)" |
			sort -V | tail -1)

		if [[ -z "$latest_kernel_key" ]]; then
			error "Failed to find kernel in S3"
			exit 1
		fi

		wget -q --show-progress "https://s3.amazonaws.com/spec.ccfc.min/${latest_kernel_key}"
		info "Downloaded kernel: $(ls vmlinux-*)"
	else
		info "Kernel already exists: $(ls vmlinux-*)"
	fi

	# Download and prepare rootfs
	if ! ls *.ext4 1>/dev/null 2>&1; then
		info "Downloading rootfs for $ARCH..."
		local latest_ubuntu_key
		latest_ubuntu_key=$(curl -s "http://spec.ccfc.min.s3.amazonaws.com/?prefix=firecracker-ci/$CI_VERSION/$ARCH/ubuntu-&list-type=2" |
			grep -oP "(?<=<Key>)(firecracker-ci/$CI_VERSION/$ARCH/ubuntu-[0-9]+\.[0-9]+\.squashfs)(?=</Key>)" |
			sort -V | tail -1)

		if [[ -z "$latest_ubuntu_key" ]]; then
			error "Failed to find rootfs in S3"
			exit 1
		fi

		local ubuntu_version
		ubuntu_version=$(basename "$latest_ubuntu_key" .squashfs | grep -oE '[0-9]+\.[0-9]+')

		wget -q --show-progress -O "ubuntu-$ubuntu_version.squashfs" "https://s3.amazonaws.com/spec.ccfc.min/$latest_ubuntu_key"

		info "Converting squashfs to ext4..."
		unsquashfs -d squashfs-root "ubuntu-$ubuntu_version.squashfs"

		# Generate SSH key for access
		if [[ ! -f id_rsa ]]; then
			ssh-keygen -f id_rsa -N "" -q
		fi
		mkdir -p squashfs-root/root/.ssh
		cp id_rsa.pub squashfs-root/root/.ssh/authorized_keys

		# Create ext4 image
		truncate -s 1G "ubuntu-$ubuntu_version.ext4"
		# Note: mkfs.ext4 -d requires root to preserve ownership
		# For non-root, we'll use a simpler approach
		if [[ $EUID -eq 0 ]]; then
			chown -R root:root squashfs-root
			mkfs.ext4 -d squashfs-root -F "ubuntu-$ubuntu_version.ext4"
		else
			warn "Not running as root - rootfs may have wrong permissions"
			warn "For proper rootfs, run: sudo $0 setup"
			mkfs.ext4 -F "ubuntu-$ubuntu_version.ext4"
			# Mount and copy (requires sudo for mount)
			local mnt_dir="$RESOURCES_DIR/mnt"
			mkdir -p "$mnt_dir"
			sudo mount "ubuntu-$ubuntu_version.ext4" "$mnt_dir"
			sudo cp -a squashfs-root/* "$mnt_dir/"
			sudo umount "$mnt_dir"
			rmdir "$mnt_dir"
		fi

		# Cleanup
		rm -rf squashfs-root "ubuntu-$ubuntu_version.squashfs"

		info "Created rootfs: ubuntu-$ubuntu_version.ext4"
		info "SSH key: id_rsa (use with: ssh -i $RESOURCES_DIR/id_rsa root@<vm-ip>)"
	else
		info "Rootfs already exists: $(ls *.ext4)"
	fi

	info "Setup complete!"
	echo ""
	echo "Resources in $RESOURCES_DIR:"
	ls -lh "$RESOURCES_DIR"
}

run() {
	check_kvm
	local fc_bin
	fc_bin=$(check_firecracker)

	if [[ ! -d "$RESOURCES_DIR" ]]; then
		error "Resources directory not found. Run setup first:"
		echo "  $0 setup"
		exit 1
	fi

	cd "$RESOURCES_DIR"

	local kernel rootfs
	kernel=$(ls vmlinux-* 2>/dev/null | head -1)
	rootfs=$(ls *.ext4 2>/dev/null | head -1)

	if [[ -z "$kernel" ]] || [[ -z "$rootfs" ]]; then
		error "Missing kernel or rootfs. Run setup first:"
		echo "  $0 setup"
		exit 1
	fi

	# Remove old socket
	rm -f "$API_SOCKET"

	# Check for network config
	local net_config="$RESOURCES_DIR/network-tap0.env"
	local has_network=false
	local guest_mac=""
	local tap_name=""
	local tap_ip=""
	local guest_ip=""

	if [[ -f "$net_config" ]]; then
		# shellcheck source=/dev/null
		source "$net_config"
		has_network=true
		guest_mac="$GUEST_MAC"
		tap_name="$TAP_NAME"
		tap_ip="$TAP_IP"
		guest_ip="$GUEST_IP"
	fi

	info "Starting Firecracker..."
	info "  Kernel: $kernel"
	info "  Rootfs: $rootfs"
	info "  Socket: $API_SOCKET"
	if [[ "$has_network" == "true" ]]; then
		info "  Network: $tap_name ($guest_ip)"
	else
		warn "  Network: disabled (run 'sudo ./scripts/setup-network.sh setup' first)"
	fi
	echo ""

	# Create config file
	local config_file="$RESOURCES_DIR/vm-config.json"

	if [[ "$has_network" == "true" ]]; then
		cat >"$config_file" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$RESOURCES_DIR/$kernel",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=off"
  },
  "drives": [
    {
      "drive_id": "rootfs",
      "path_on_host": "$RESOURCES_DIR/$rootfs",
      "is_root_device": true,
      "is_read_only": false
    }
  ],
  "network-interfaces": [
    {
      "iface_id": "eth0",
      "guest_mac": "$guest_mac",
      "host_dev_name": "$tap_name"
    }
  ],
  "machine-config": {
    "vcpu_count": 2,
    "mem_size_mib": 1024
  }
}
EOF
	else
		cat >"$config_file" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$RESOURCES_DIR/$kernel",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=off"
  },
  "drives": [
    {
      "drive_id": "rootfs",
      "path_on_host": "$RESOURCES_DIR/$rootfs",
      "is_root_device": true,
      "is_read_only": false
    }
  ],
  "machine-config": {
    "vcpu_count": 2,
    "mem_size_mib": 1024
  }
}
EOF
	fi

	info "Config written to: $config_file"
	echo ""
	warn "Press Ctrl+C to stop the VM"
	echo ""

	# Run Firecracker
	exec "$fc_bin" \
		--api-sock "$API_SOCKET" \
		--config-file "$config_file"
}

run_interactive() {
	# Alternative: start FC and use API to configure
	check_kvm
	local fc_bin
	fc_bin=$(check_firecracker)

	rm -f "$API_SOCKET"

	info "Starting Firecracker in API mode..."
	info "Socket: $API_SOCKET"
	echo ""
	echo "In another terminal, configure the VM with:"
	echo ""
	echo "  # Set kernel"
	echo "  curl --unix-socket $API_SOCKET -X PUT http://localhost/boot-source \\"
	echo "    -H 'Content-Type: application/json' \\"
	echo "    -d '{\"kernel_image_path\": \"$RESOURCES_DIR/\$(ls $RESOURCES_DIR/vmlinux-*)\", \"boot_args\": \"console=ttyS0 reboot=k panic=1 pci=off\"}'"
	echo ""
	echo "  # Set rootfs"
	echo "  curl --unix-socket $API_SOCKET -X PUT http://localhost/drives/rootfs \\"
	echo "    -H 'Content-Type: application/json' \\"
	echo "    -d '{\"drive_id\": \"rootfs\", \"path_on_host\": \"$RESOURCES_DIR/\$(ls $RESOURCES_DIR/*.ext4)\", \"is_root_device\": true, \"is_read_only\": false}'"
	echo ""
	echo "  # Start VM"
	echo "  curl --unix-socket $API_SOCKET -X PUT http://localhost/actions \\"
	echo "    -H 'Content-Type: application/json' \\"
	echo "    -d '{\"action_type\": \"InstanceStart\"}'"
	echo ""

	exec "$fc_bin" --api-sock "$API_SOCKET"
}

clean() {
	info "Cleaning up resources..."
	rm -rf "$RESOURCES_DIR"
	info "Done"
}

usage() {
	echo "Usage: $0 [setup|run|api|clean]"
	echo ""
	echo "Commands:"
	echo "  setup  - Download kernel and rootfs from Firecracker CI"
	echo "  run    - Start Firecracker microVM with config file"
	echo "  api    - Start Firecracker in API mode (manual configuration)"
	echo "  clean  - Remove downloaded resources"
	echo ""
	echo "Example:"
	echo "  $0 setup   # Download resources (once)"
	echo "  $0 run     # Boot the VM"
}

case "${1:-}" in
setup)
	setup
	;;
run)
	run
	;;
api)
	run_interactive
	;;
clean)
	clean
	;;
*)
	usage
	exit 1
	;;
esac
