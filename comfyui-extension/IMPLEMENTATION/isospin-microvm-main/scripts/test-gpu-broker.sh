#!/usr/bin/env bash
# test-gpu-broker.sh - Test GPU broker in a Firecracker VM
#
# Boots a minimal VM with gpu-broker and guest-shim, runs the live wire test.
#
# Usage:
#   ./scripts/test-gpu-broker.sh build   # Build binaries, create rootfs
#   ./scripts/test-gpu-broker.sh run     # Boot VM and run test

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
GPU_BROKER_DIR="$REPO_ROOT/gpu-broker"
RESOURCES_DIR="$REPO_ROOT/.gpu-broker-test"

info() { echo -e "\033[0;32m[INFO]\033[0m $*"; }
error() { echo -e "\033[0;31m[ERROR]\033[0m $*" >&2; }

build_broker() {
	info "Building gpu-broker..."
	cd "$GPU_BROKER_DIR"
	cargo build --release
	info "Built binaries"
}

download_kernel() {
	mkdir -p "$RESOURCES_DIR"

	if ls "$RESOURCES_DIR"/vmlinux-* 1>/dev/null 2>&1; then
		info "Kernel exists: $(ls "$RESOURCES_DIR"/vmlinux-*)"
		return
	fi

	info "Downloading kernel..."
	local arch="x86_64"
	local latest_version
	latest_version=$(curl -fsSL "https://api.github.com/repos/firecracker-microvm/firecracker/releases/latest" | grep -oP '"tag_name": "\K[^"]+')
	local ci_version="${latest_version%.*}"

	local kernel_key
	kernel_key=$(curl -s "http://spec.ccfc.min.s3.amazonaws.com/?prefix=firecracker-ci/$ci_version/$arch/vmlinux-&list-type=2" |
		grep -oP "(?<=<Key>)(firecracker-ci/$ci_version/$arch/vmlinux-[0-9]+\.[0-9]+\.[0-9]{1,3})(?=</Key>)" |
		sort -V | tail -1)

	wget -q --show-progress -O "$RESOURCES_DIR/$(basename "$kernel_key")" \
		"https://s3.amazonaws.com/spec.ccfc.min/$kernel_key"
	info "Downloaded kernel"
}

create_rootfs() {
	local include_nvidia_smi="${1:-}"
	info "Creating rootfs..."

	local rootfs="$RESOURCES_DIR/rootfs.ext4"
	local tmpdir=$(mktemp -d)

	mkdir -p "$tmpdir"/{bin,lib,lib64,tmp,dev,proc,sys}

	# Download static busybox
	if [[ ! -f "$RESOURCES_DIR/busybox" ]]; then
		info "Downloading busybox..."
		wget -q -O "$RESOURCES_DIR/busybox" \
			"https://busybox.net/downloads/binaries/1.35.0-x86_64-linux-musl/busybox"
		chmod +x "$RESOURCES_DIR/busybox"
	fi

	cp "$RESOURCES_DIR/busybox" "$tmpdir/bin/"

	# Create busybox symlinks
	for cmd in sh mount umount sleep echo cat ls mknod; do
		ln -sf busybox "$tmpdir/bin/$cmd"
	done

	# Copy our binaries
	local broker="$GPU_BROKER_DIR/target/release/gpu-broker"
	local shim="$GPU_BROKER_DIR/target/release/guest-shim"

	cp "$broker" "$tmpdir/bin/"
	cp "$shim" "$tmpdir/bin/"

	# Optionally include nvidia-smi
	if [[ "$include_nvidia_smi" == "nvidia-smi" ]]; then
		local nvidia_smi="$RESOURCES_DIR/nvidia-extract/nvidia-smi"
		if [[ -f "$nvidia_smi" ]]; then
			info "Including nvidia-smi in rootfs"
			cp "$nvidia_smi" "$tmpdir/bin/"

			# Use our stub NVML library instead of real one
			local nvml_stub="$GPU_BROKER_DIR/nvml-stub/libnvidia-ml.so.1"
			if [[ -f "$nvml_stub" ]]; then
				info "Including NVML stub library"
				cp "$nvml_stub" "$tmpdir/lib/"
				ln -sf "libnvidia-ml.so.1" "$tmpdir/lib/libnvidia-ml.so"
			else
				error "NVML stub not built. Run: cd gpu-broker/nvml-stub && gcc -shared -fPIC -o libnvidia-ml.so.1 nvml_stub.c"
				exit 1
			fi

			# Download static strace for tracing
			if [[ ! -f "$RESOURCES_DIR/strace" ]]; then
				info "Downloading static strace..."
				wget -q -O "$RESOURCES_DIR/strace" \
					"https://github.com/andrew-d/static-binaries/raw/master/binaries/linux/x86_64/strace" || true
				chmod +x "$RESOURCES_DIR/strace" 2>/dev/null || true
			fi
			if [[ -f "$RESOURCES_DIR/strace" ]]; then
				cp "$RESOURCES_DIR/strace" "$tmpdir/bin/"
			fi
		else
			error "nvidia-smi not found. Run extraction first."
			exit 1
		fi
	fi

	# Find glibc path from Nix store
	local glibc_path=$(dirname $(ldd "$broker" 2>/dev/null | grep libc.so | awk '{print $3}'))

	info "Using glibc from: $glibc_path"

	# Copy glibc libraries to standard locations
	mkdir -p "$tmpdir/lib/x86_64-linux-gnu" "$tmpdir/lib64"

	# Copy the actual libraries
	for lib in libc.so.6 libm.so.6 libpthread.so.0 libdl.so.2 librt.so.1; do
		if [[ -f "$glibc_path/$lib" ]]; then
			cp -L "$glibc_path/$lib" "$tmpdir/lib/x86_64-linux-gnu/"
			# Also copy to /lib for fallback
			cp -L "$glibc_path/$lib" "$tmpdir/lib/"
		fi
	done

	# Copy ld-linux
	local ld_path=$(dirname "$glibc_path")/lib64/ld-linux-x86-64.so.2
	if [[ -f "$ld_path" ]]; then
		cp -L "$ld_path" "$tmpdir/lib64/"
	else
		# Try alternate location
		cp -L "$glibc_path/../lib64/ld-linux-x86-64.so.2" "$tmpdir/lib64/" 2>/dev/null ||
			cp -L "$glibc_path/ld-linux-x86-64.so.2" "$tmpdir/lib64/" 2>/dev/null || true
	fi

	cat >"$tmpdir/init" <<'EOF'
#!/bin/sh
/bin/busybox mount -t proc proc /proc
/bin/busybox mount -t sysfs sys /sys
/bin/busybox mount -t devtmpfs dev /dev

echo "=== GPU Broker Test ==="

# Check if nvidia-smi test mode
if [ -x /bin/nvidia-smi ]; then
    echo "=== nvidia-smi trace mode ==="
    
    # Set library path
    export LD_LIBRARY_PATH=/lib:/lib/x86_64-linux-gnu
    
    # Create fake NVIDIA devices
    /bin/busybox mknod /dev/nvidiactl c 195 255
    /bin/busybox mknod /dev/nvidia0 c 195 0
    
    echo "Created /dev/nvidia* devices"
    /bin/busybox ls -la /dev/nvidia*
    
    # Check libraries
    echo "Libraries in /lib:"
    /bin/busybox ls /lib/*.so* 2>/dev/null | /bin/busybox head -5
    
    # Run nvidia-smi 
    echo "--- nvidia-smi -L ---"
    /bin/nvidia-smi -L 2>&1
    echo ""
    echo "--- nvidia-smi ---"
    /bin/nvidia-smi 2>&1
    echo ""
    echo "Exit code: $?"
else
    # Regular broker test
    /bin/gpu-broker --mock --socket /tmp/broker.sock &
    /bin/busybox sleep 1

    /bin/guest-shim --broker-socket /tmp/broker.sock --live-test -v
    result=$?

    echo ""
    if [ $result -eq 0 ]; then
        echo "=== TEST PASSED ==="
    else
        echo "=== TEST FAILED (exit $result) ==="
    fi
fi

# Shutdown
echo o > /proc/sysrq-trigger
EOF
	chmod +x "$tmpdir/init"

	# Create ext4 (64MB for libs)
	dd if=/dev/zero of="$rootfs" bs=1M count=64 2>/dev/null
	mkfs.ext4 -F -d "$tmpdir" "$rootfs" 2>/dev/null || {
		mkfs.ext4 -F "$rootfs" 2>/dev/null
		local mnt=$(mktemp -d)
		sudo mount "$rootfs" "$mnt"
		sudo cp -a "$tmpdir"/* "$mnt/"
		sudo umount "$mnt"
		rmdir "$mnt"
	}

	rm -rf "$tmpdir"
	info "Created rootfs: $rootfs"
}

find_firecracker() {
	local fc="$REPO_ROOT/buck-out/v2/gen/root/b42aeba648b8c415/firecracker/src/firecracker/__firecracker__/firecracker"
	[[ -x "$fc" ]] && echo "$fc" && return

	fc="$REPO_ROOT/firecracker/target/release/firecracker"
	[[ -x "$fc" ]] && echo "$fc" && return

	error "Firecracker not found. Build with: buck2 build //firecracker/src/firecracker:firecracker"
	exit 1
}

run_vm() {
	[[ -r /dev/kvm ]] || {
		error "No KVM access"
		exit 1
	}

	local fc=$(find_firecracker)
	local kernel=$(ls "$RESOURCES_DIR"/vmlinux-* 2>/dev/null | head -1)
	local rootfs="$RESOURCES_DIR/rootfs.ext4"
	local socket="$RESOURCES_DIR/fc.sock"

	[[ -f "$kernel" ]] || {
		error "No kernel. Run: $0 build"
		exit 1
	}
	[[ -f "$rootfs" ]] || {
		error "No rootfs. Run: $0 build"
		exit 1
	}

	rm -f "$socket"

	info "Booting VM..."
	info "  Kernel: $kernel"
	info "  Rootfs: $rootfs"
	echo ""

	local config=$(mktemp)
	cat >"$config" <<EOF
{
  "boot-source": {
    "kernel_image_path": "$kernel",
    "boot_args": "console=ttyS0 reboot=k panic=1 pci=off init=/init"
  },
  "drives": [{
    "drive_id": "root",
    "path_on_host": "$rootfs",
    "is_root_device": true,
    "is_read_only": false
  }],
  "machine-config": {
    "vcpu_count": 1,
    "mem_size_mib": 128
  }
}
EOF

	"$fc" --api-sock "$socket" --config-file "$config"
	rm -f "$config"
}

build() {
	build_broker
	download_kernel
	create_rootfs
	echo ""
	info "Build complete. Run: $0 run"
}

build_nvidia_smi() {
	build_broker
	download_kernel
	create_rootfs "nvidia-smi"
	echo ""
	info "Build complete with nvidia-smi. Run: $0 run"
}

case "${1:-}" in
build) build ;;
build-nvidia-smi) build_nvidia_smi ;;
run) run_vm ;;
clean)
	rm -rf "$RESOURCES_DIR"
	info "Cleaned"
	;;
*) echo "Usage: $0 [build|build-nvidia-smi|run|clean]" ;;
esac
