#!/usr/bin/env bash
# setup-network.sh - Configure TAP networking for Firecracker VMs
#
# Usage:
#   sudo ./scripts/setup-network.sh setup [tap_name] [guest_ip]
#   sudo ./scripts/setup-network.sh teardown [tap_name]
#   sudo ./scripts/setup-network.sh status
#
# Examples:
#   sudo ./scripts/setup-network.sh setup           # Creates tap0 with 172.16.0.2
#   sudo ./scripts/setup-network.sh setup tap1 172.16.1.2  # Creates tap1 with custom IP
#   sudo ./scripts/setup-network.sh teardown tap0   # Removes tap0
#
# This script sets up NAT-based routing for Firecracker VMs.

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

info() { echo -e "${GREEN}[INFO]${NC} $*"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $*"; }
error() { echo -e "${RED}[ERROR]${NC} $*" >&2; }
debug() { echo -e "${BLUE}[DEBUG]${NC} $*"; }

# Find nft binary - check PATH first, then Nix store
find_nft() {
	if command -v nft &>/dev/null; then
		echo "nft"
		return 0
	fi
	# Search Nix store for nftables
	local nft_path
	nft_path=$(find /nix/store -maxdepth 3 -type f -name 'nft' 2>/dev/null | sort -V | tail -1)
	if [[ -n "$nft_path" && -x "$nft_path" ]]; then
		echo "$nft_path"
		return 0
	fi
	return 1
}

# Find iptables binary
find_iptables() {
	if command -v iptables &>/dev/null; then
		echo "iptables"
		return 0
	fi
	local ipt_path
	ipt_path=$(find /nix/store -maxdepth 3 -type f -name 'iptables' 2>/dev/null | head -1)
	if [[ -n "$ipt_path" && -x "$ipt_path" ]]; then
		echo "$ipt_path"
		return 0
	fi
	return 1
}

NFT=""
IPTABLES=""
USE_NFT=true

init_firewall_tool() {
	NFT=$(find_nft) || true
	if [[ -n "$NFT" ]]; then
		USE_NFT=true
		debug "Using nftables: $NFT"
	else
		IPTABLES=$(find_iptables) || true
		if [[ -n "$IPTABLES" ]]; then
			USE_NFT=false
			debug "Using iptables: $IPTABLES"
		else
			error "Neither nftables nor iptables found!"
			error "On NixOS, add nftables to environment.systemPackages or use nix-shell -p nftables"
			exit 1
		fi
	fi
}

# Detect the main network interface
detect_interface() {
	# Try to find the default route interface
	local iface
	iface=$(ip route | grep '^default' | awk '{print $5}' | head -1)
	if [[ -z "$iface" ]]; then
		# Fallback: find first non-loopback interface that's up
		iface=$(ip -o link show | grep -v 'lo:' | grep 'state UP' | awk -F': ' '{print $2}' | head -1)
	fi
	echo "$iface"
}

# Check if running as root
check_root() {
	if [[ $EUID -ne 0 ]]; then
		error "This script must be run as root (use sudo)"
		exit 1
	fi
	init_firewall_tool
}

# Calculate TAP IP from guest IP (guest IP - 1)
calc_tap_ip() {
	local guest_ip="$1"
	local IFS='.'
	read -r a b c d <<<"$guest_ip"
	echo "$a.$b.$c.$((d - 1))"
}

# Calculate MAC from IP (06:00:XX:XX:XX:XX where XX is hex of IP octets)
calc_mac() {
	local ip="$1"
	local IFS='.'
	read -r a b c d <<<"$ip"
	printf "06:00:%02X:%02X:%02X:%02X" "$a" "$b" "$c" "$d"
}

setup_tap() {
	local tap_name="${1:-tap0}"
	local guest_ip="${2:-172.16.0.2}"
	local tap_ip
	tap_ip=$(calc_tap_ip "$guest_ip")
	local guest_mac
	guest_mac=$(calc_mac "$guest_ip")
	local host_iface
	host_iface=$(detect_interface)

	if [[ -z "$host_iface" ]]; then
		error "Could not detect host network interface"
		exit 1
	fi

	info "Setting up TAP device: $tap_name"
	debug "  Host interface: $host_iface"
	debug "  TAP IP: $tap_ip/30"
	debug "  Guest IP: $guest_ip"
	debug "  Guest MAC: $guest_mac"

	# Check if TAP already exists
	if ip link show "$tap_name" &>/dev/null; then
		warn "TAP device $tap_name already exists, removing first..."
		ip link del "$tap_name" 2>/dev/null || true
	fi

	# Create TAP device
	info "Creating TAP device..."
	ip tuntap add "$tap_name" mode tap
	ip addr add "$tap_ip/30" dev "$tap_name"
	ip link set "$tap_name" up

	# Enable IP forwarding
	info "Enabling IP forwarding..."
	echo 1 >/proc/sys/net/ipv4/ip_forward

	# Setup NAT rules
	info "Configuring NAT rules..."

	if [[ "$USE_NFT" == "true" ]]; then
		# Create table if not exists
		"$NFT" list table inet firecracker &>/dev/null || "$NFT" add table inet firecracker

		# Create chains if not exist
		"$NFT" list chain inet firecracker postrouting &>/dev/null ||
			"$NFT" 'add chain inet firecracker postrouting { type nat hook postrouting priority srcnat; policy accept; }'
		"$NFT" list chain inet firecracker forward &>/dev/null ||
			"$NFT" 'add chain inet firecracker forward { type filter hook forward priority filter; policy accept; }'

		# Add rules (with comments for identification)
		# Masquerade outgoing traffic from guest
		"$NFT" add rule inet firecracker postrouting ip saddr "$guest_ip" oifname "$host_iface" counter masquerade comment "\"fc-$tap_name-masq\""

		# Allow forwarding from TAP to host interface
		"$NFT" add rule inet firecracker forward iifname "$tap_name" oifname "$host_iface" counter accept comment "\"fc-$tap_name-fwd\""

		# Allow return traffic
		"$NFT" add rule inet firecracker forward iifname "$host_iface" oifname "$tap_name" ct state established,related counter accept comment "\"fc-$tap_name-ret\""
	else
		# iptables fallback
		"$IPTABLES" -t nat -A POSTROUTING -s "$guest_ip" -o "$host_iface" -j MASQUERADE -m comment --comment "fc-$tap_name-masq"
		"$IPTABLES" -A FORWARD -i "$tap_name" -o "$host_iface" -j ACCEPT -m comment --comment "fc-$tap_name-fwd"
		"$IPTABLES" -A FORWARD -i "$host_iface" -o "$tap_name" -m state --state ESTABLISHED,RELATED -j ACCEPT -m comment --comment "fc-$tap_name-ret"
	fi

	info "Network setup complete!"
	echo ""
	echo "TAP device '$tap_name' is ready."
	echo ""
	echo "Add this to your Firecracker config:"
	echo ""
	echo "  \"network-interfaces\": ["
	echo "    {"
	echo "      \"iface_id\": \"eth0\","
	echo "      \"guest_mac\": \"$guest_mac\","
	echo "      \"host_dev_name\": \"$tap_name\""
	echo "    }"
	echo "  ]"
	echo ""
	echo "Inside the guest, configure networking:"
	echo "  ip addr add $guest_ip/30 dev eth0"
	echo "  ip link set eth0 up"
	echo "  ip route add default via $tap_ip"
	echo ""
	echo "Or the guest may auto-configure if using the FC CI rootfs."
	echo ""

	# Save config for the run script
	local config_dir
	config_dir="$(dirname "$0")/../.firecracker-resources"
	mkdir -p "$config_dir"
	cat >"$config_dir/network-$tap_name.env" <<EOF
TAP_NAME=$tap_name
TAP_IP=$tap_ip
GUEST_IP=$guest_ip
GUEST_MAC=$guest_mac
HOST_IFACE=$host_iface
USE_NFT=$USE_NFT
EOF
	info "Saved network config to $config_dir/network-$tap_name.env"
}

teardown_tap() {
	local tap_name="${1:-tap0}"

	info "Tearing down TAP device: $tap_name"

	# Load saved config to get firewall type
	local config_file
	config_file="$(dirname "$0")/../.firecracker-resources/network-$tap_name.env"
	if [[ -f "$config_file" ]]; then
		# shellcheck source=/dev/null
		source "$config_file"
	fi

	# Remove TAP device
	if ip link show "$tap_name" &>/dev/null; then
		ip link del "$tap_name"
		info "Removed TAP device $tap_name"
	else
		warn "TAP device $tap_name does not exist"
	fi

	# Remove associated firewall rules
	if [[ "$USE_NFT" == "true" ]]; then
		if "$NFT" list table inet firecracker &>/dev/null; then
			info "Removing NAT rules for $tap_name..."
			# Delete rules with matching comments
			"$NFT" -a list chain inet firecracker postrouting 2>/dev/null |
				grep "fc-$tap_name" |
				grep -oP 'handle \d+' |
				while read -r handle; do
					"$NFT" delete rule inet firecracker postrouting $handle 2>/dev/null || true
				done

			"$NFT" -a list chain inet firecracker forward 2>/dev/null |
				grep "fc-$tap_name" |
				grep -oP 'handle \d+' |
				while read -r handle; do
					"$NFT" delete rule inet firecracker forward $handle 2>/dev/null || true
				done
		fi
	else
		# iptables cleanup
		info "Removing iptables rules for $tap_name..."
		"$IPTABLES" -t nat -S | grep "fc-$tap_name" | sed 's/-A/-D/' | while read -r rule; do
			"$IPTABLES" -t nat $rule 2>/dev/null || true
		done
		"$IPTABLES" -S FORWARD | grep "fc-$tap_name" | sed 's/-A/-D/' | while read -r rule; do
			"$IPTABLES" $rule 2>/dev/null || true
		done
	fi

	# Remove saved config
	local config_file
	config_file="$(dirname "$0")/../.firecracker-resources/network-$tap_name.env"
	if [[ -f "$config_file" ]]; then
		rm -f "$config_file"
	fi

	info "Teardown complete"
}

status() {
	# Initialize firewall tool for status check (doesn't require root)
	NFT=$(find_nft) || true
	IPTABLES=$(find_iptables) || true

	echo "=== TAP Devices ==="
	ip -br link show type tun 2>/dev/null || echo "No TAP devices found"
	echo ""

	echo "=== IP Forwarding ==="
	cat /proc/sys/net/ipv4/ip_forward
	echo ""

	echo "=== Firewall Rules ==="
	if [[ -n "$NFT" ]]; then
		if "$NFT" list table inet firecracker &>/dev/null 2>&1; then
			"$NFT" list table inet firecracker
		else
			echo "No firecracker nftables table found"
		fi
	elif [[ -n "$IPTABLES" ]]; then
		echo "iptables NAT rules:"
		"$IPTABLES" -t nat -S 2>/dev/null | grep "fc-" || echo "  (none)"
		echo "iptables FORWARD rules:"
		"$IPTABLES" -S FORWARD 2>/dev/null | grep "fc-" || echo "  (none)"
	else
		echo "No firewall tool found"
	fi
	echo ""

	echo "=== Saved Configs ==="
	local config_dir
	config_dir="$(dirname "$0")/../.firecracker-resources"
	if ls "$config_dir"/network-*.env &>/dev/null; then
		for f in "$config_dir"/network-*.env; do
			echo "--- $f ---"
			cat "$f"
			echo ""
		done
	else
		echo "No saved network configs"
	fi
}

usage() {
	echo "Usage: $0 <command> [options]"
	echo ""
	echo "Commands:"
	echo "  setup [tap_name] [guest_ip]  - Create TAP device and configure NAT"
	echo "  teardown [tap_name]          - Remove TAP device and NAT rules"
	echo "  status                       - Show current network status"
	echo ""
	echo "Defaults:"
	echo "  tap_name: tap0"
	echo "  guest_ip: 172.16.0.2"
	echo ""
	echo "Examples:"
	echo "  sudo $0 setup                    # Create tap0 for 172.16.0.2"
	echo "  sudo $0 setup tap1 172.16.1.2    # Create tap1 for 172.16.1.2"
	echo "  sudo $0 teardown tap0            # Remove tap0"
	echo "  $0 status                        # Show status (no root needed)"
}

case "${1:-}" in
setup)
	check_root
	setup_tap "${2:-}" "${3:-}"
	;;
teardown)
	check_root
	teardown_tap "${2:-}"
	;;
status)
	status
	;;
*)
	usage
	exit 1
	;;
esac
