#!/usr/bin/env bash
# demo-broker.sh - GPU Broker Multi-VM Demo
#
# Architecture:
#   Host (gpu-broker) ◄──vsock──► VM 1 (nvidia-shim.ko)
#        │            ◄──vsock──► VM 2 (nvidia-shim.ko)
#        └──► /dev/nvidiactl (real GPU) or mock mode
#
# Usage: sudo ./scripts/demo-broker.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

info() { echo -e "${GREEN}[INFO]${NC} $*"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $*"; }
error() { echo -e "\033[0;31m[ERROR]\033[0m $*" >&2; }

# Check root
if [[ $EUID -ne 0 ]]; then
	error "Must run as root: sudo $0"
	exit 1
fi

# Check tmux
if ! command -v tmux &>/dev/null; then
	error "tmux required. Install with: nix-shell -p tmux"
	exit 1
fi

# Find Firecracker binary
FC="$REPO_ROOT/buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"
if [[ ! -x "$FC" ]]; then
	error "Firecracker not found: $FC"
	echo "Build with: nix develop -c buck2 build //firecracker/src/firecracker:firecracker"
	exit 1
fi

# Find gpu-broker binary
BROKER="$REPO_ROOT/gpu-broker/target/release/gpu-broker"
if [[ ! -x "$BROKER" ]]; then
	warn "gpu-broker not found, building..."
	cd "$REPO_ROOT/gpu-broker"
	cargo build --release
	cd "$REPO_ROOT"
fi

# Assets - use new 6.12.10 kernel with VIRTIO_MMIO_CMDLINE_DEVICES=y
KERNEL="$REPO_ROOT/.vm-assets/vmlinux-6.12.10.bin"
ROOTFS="$REPO_ROOT/.vm-assets/gpu-rootfs.ext4"
INITRAMFS="$REPO_ROOT/.vm-assets/initramfs.cpio.gz"

# Verify assets
for f in "$KERNEL" "$ROOTFS" "$INITRAMFS"; do
	if [[ ! -f "$f" ]]; then
		error "Missing: $f"
		if [[ "$f" == *"6.12.10"* ]]; then
			echo "Build kernel with: nix build .#fc-gpu-kernel && cp result/vmlinux .vm-assets/vmlinux-6.12.10.bin"
		fi
		exit 1
	fi
done

# Create VM disk copies
info "Preparing VM disks..."
cp "$ROOTFS" /tmp/vm1-rootfs.ext4
cp "$ROOTFS" /tmp/vm2-rootfs.ext4

# Create vsock UDS paths
VSOCK_UDS_1="/tmp/fc-vsock-vm1.sock"
VSOCK_UDS_2="/tmp/fc-vsock-vm2.sock"
rm -f "$VSOCK_UDS_1" "$VSOCK_UDS_2"

# Create Firecracker configs
create_fc_config() {
	local name=$1
	local cid=$2
	local rootfs=$3
	local vsock_uds=$4
	local config="/tmp/fc-config-$name.json"

	cat >"$config" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$KERNEL",
    "initrd_path": "$INITRAMFS",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=off init=/init"
  },
  "drives": [{
    "drive_id": "rootfs",
    "path_on_host": "$rootfs",
    "is_root_device": true,
    "is_read_only": false
  }],
  "machine-config": {
    "vcpu_count": 2,
    "mem_size_mib": 512
  },
  "vsock": {
    "guest_cid": $cid,
    "uds_path": "$vsock_uds"
  }
}
EOF
	echo "$config"
}

CONFIG_1=$(create_fc_config "vm1" 3 "/tmp/vm1-rootfs.ext4" "$VSOCK_UDS_1")
CONFIG_2=$(create_fc_config "vm2" 4 "/tmp/vm2-rootfs.ext4" "$VSOCK_UDS_2")

# Kill existing session
tmux kill-session -t broker-demo 2>/dev/null || true

info "Launching demo..."

# Create tmux session with 3 panes
tmux new-session -d -s broker-demo -x 200 -y 50

# Pane 0: GPU Broker on HOST
tmux send-keys -t broker-demo "echo -e '${CYAN}=== GPU BROKER (Host) ===${NC}' && echo 'Starting broker with mock driver...' && sleep 1 && $BROKER --vsock-port 9999 --mock -v" Enter

# Split for VM 1
tmux split-window -h -t broker-demo

# Pane 1: VM 1
tmux send-keys -t broker-demo "echo -e '${CYAN}=== VM 1 (CID=3) ===${NC}' && echo 'Waiting 2s for broker...' && sleep 2 && $FC --no-api --config-file $CONFIG_1" Enter

# Split for VM 2
tmux split-window -v -t broker-demo

# Pane 2: VM 2
tmux send-keys -t broker-demo "echo -e '${CYAN}=== VM 2 (CID=4) ===${NC}' && echo 'Waiting 3s for broker...' && sleep 3 && $FC --no-api --config-file $CONFIG_2" Enter

# Select first pane
tmux select-pane -t broker-demo:0.0

cat <<'BANNER'

╔══════════════════════════════════════════════════════════════════════╗
║                    GPU BROKER MULTI-VM DEMO                          ║
╠══════════════════════════════════════════════════════════════════════╣
║                                                                      ║
║  Architecture:                                                       ║
║    Host (gpu-broker) ◄──vsock──► VM 1 (nvidia-shim.ko)               ║
║         │            ◄──vsock──► VM 2 (nvidia-shim.ko)               ║
║         └──► /dev/nvidiactl (real or mock GPU)                       ║
║                                                                      ║
║  Panes:                                                              ║
║    Left:         GPU broker running on host (mock mode)              ║
║    Top-right:    VM 1 (Firecracker, CID=3)                           ║
║    Bottom-right: VM 2 (Firecracker, CID=4)                           ║
║                                                                      ║
║  IN VMs (when booted to shell):                                      ║
║    # Load shim module to intercept nvidia ioctls                     ║
║    insmod /lib/modules/*/kernel/drivers/video/nvidia-shim.ko \       ║
║           broker_cid=2 broker_port=9999                              ║
║                                                                      ║
║    # Run nvidia-smi (goes through broker)                            ║
║    nvidia-smi                                                        ║
║                                                                      ║
║  Note: broker_cid=2 is VMADDR_CID_HOST (the host)                    ║
║                                                                      ║
║  Controls:                                                           ║
║    Switch panes: Ctrl-b + arrow keys                                 ║
║    Kill demo:    tmux kill-session -t broker-demo                    ║
╚══════════════════════════════════════════════════════════════════════╝

BANNER

# Attach
exec tmux attach -t broker-demo
