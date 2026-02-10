#!/usr/bin/env bash
# Create Ubuntu VM image with NVIDIA drivers for GPU passthrough testing
# Usage: ./create-gpu-image.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
ASSETS_DIR="$REPO_ROOT/.vm-assets"

OUTPUT="$ASSETS_DIR/ubuntu-gpu.raw"
SIZE="20G"

# Cloud image URL
CLOUD_IMG_URL="https://cloud-images.ubuntu.com/noble/current/noble-server-cloudimg-amd64.img"
CLOUD_IMG="$ASSETS_DIR/noble-server-cloudimg-amd64.img"

echo "=== Creating GPU-enabled VM image ==="

# Download cloud image if needed
if [[ ! -f "$CLOUD_IMG" ]]; then
	echo "Downloading Ubuntu 24.04 cloud image..."
	curl -L -o "$CLOUD_IMG" "$CLOUD_IMG_URL"
fi

# Convert to raw and resize
echo "Converting to raw format ($SIZE)..."
qemu-img convert -f qcow2 -O raw "$CLOUD_IMG" "$OUTPUT"
qemu-img resize "$OUTPUT" "$SIZE"

# Create cloud-init config
CLOUD_INIT_DIR=$(mktemp -d)
trap "rm -rf $CLOUD_INIT_DIR" EXIT

# Get SSH public key
SSH_PUBKEY=""
if [[ -f "$ASSETS_DIR/vm_key.pub" ]]; then
	SSH_PUBKEY=$(cat "$ASSETS_DIR/vm_key.pub")
fi

cat >"$CLOUD_INIT_DIR/meta-data" <<EOF
instance-id: gpu-vm
local-hostname: gpu-vm
EOF

cat >"$CLOUD_INIT_DIR/user-data" <<EOF
#cloud-config
hostname: gpu-vm
users:
  - name: root
    lock_passwd: false
    ssh_authorized_keys:
      - $SSH_PUBKEY

# Set root password for console access
chpasswd:
  list: |
    root:gpu
  expire: false

# Network config
write_files:
  - path: /etc/netplan/99-static.yaml
    content: |
      network:
        version: 2
        ethernets:
          enp0s3:
            addresses: [172.16.0.2/24]
            routes:
              - to: default
                via: 172.16.0.1

# Install NVIDIA drivers on first boot
package_update: true
packages:
  - linux-headers-generic
  - build-essential
  - pciutils
  - curl

runcmd:
  - netplan apply
  # Add NVIDIA driver repo and install
  - |
    curl -fsSL https://nvidia.github.io/libnvidia-container/gpgkey | gpg --dearmor -o /usr/share/keyrings/nvidia-container-toolkit-keyring.gpg
    curl -s -L https://nvidia.github.io/libnvidia-container/stable/deb/nvidia-container-toolkit.list | \
      sed 's#deb https://#deb [signed-by=/usr/share/keyrings/nvidia-container-toolkit-keyring.gpg] https://#g' | \
      tee /etc/apt/sources.list.d/nvidia-container-toolkit.list
  - apt-get update
  - DEBIAN_FRONTEND=noninteractive apt-get install -y nvidia-driver-565 nvidia-utils-565 || true
  - echo "NVIDIA driver installation attempted - reboot may be required"
EOF

# Create cloud-init ISO
echo "Creating cloud-init ISO..."
CLOUD_INIT_ISO="$ASSETS_DIR/cloud-init-gpu.iso"
genisoimage -output "$CLOUD_INIT_ISO" -volid cidata -joliet -rock \
	"$CLOUD_INIT_DIR/user-data" "$CLOUD_INIT_DIR/meta-data" 2>/dev/null ||
	mkisofs -output "$CLOUD_INIT_ISO" -volid cidata -joliet -rock \
		"$CLOUD_INIT_DIR/user-data" "$CLOUD_INIT_DIR/meta-data" 2>/dev/null ||
	xorriso -as mkisofs -output "$CLOUD_INIT_ISO" -volid cidata -joliet -rock \
		"$CLOUD_INIT_DIR/user-data" "$CLOUD_INIT_DIR/meta-data"

echo ""
echo "=== Created ==="
echo "Disk image:     $OUTPUT"
echo "Cloud-init ISO: $CLOUD_INIT_ISO"
echo ""
echo "To boot with cloud-init (first boot):"
echo "  Add --disk path=$CLOUD_INIT_ISO,readonly=on to cloud-hypervisor"
echo ""
echo "After first boot, cloud-init will:"
echo "  - Set root password to 'gpu'"
echo "  - Configure static IP 172.16.0.2"
echo "  - Install NVIDIA driver 565"
