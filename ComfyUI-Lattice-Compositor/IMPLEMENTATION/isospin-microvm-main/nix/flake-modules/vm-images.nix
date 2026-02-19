# nix/flake-modules/vm-images.nix
#
# VM images for GPU broker testing
#
# Provides:
#   packages.fc-initramfs    - Minimal initramfs for Firecracker (kernel 6.12.10)
#   packages.fc-rootfs       - Root filesystem with nvidia-shim for Firecracker
#   packages.gpu-vm-initramfs - Initramfs for Cloud Hypervisor GPU VM (kernel 6.12.63)
#
# Usage:
#   nix build .#fc-initramfs
#   nix build .#fc-rootfs
#   nix build .#gpu-vm-initramfs
#
{ inputs, ... }:
{
  _class = "flake";

  config.perSystem =
    {
      pkgs,
      lib,
      config,
      ...
    }:
    let
      # Get our custom kernel
      fc-gpu-kernel = config.packages.fc-gpu-kernel;
      nvidia-shim = config.packages.nvidia-shim;
      gpu-broker = config.packages.gpu-broker;
      kernelVersion = "6.12.10";

      # Static busybox - MUST be statically linked for initramfs!
      # Dynamic busybox fails after switch_root because glibc paths don't exist
      staticBusybox = pkgs.pkgsStatic.busybox;

      # ════════════════════════════════════════════════════════════════════════
      # Initramfs - Minimal boot image
      # ════════════════════════════════════════════════════════════════════════
      fc-initramfs = pkgs.makeInitrdNG {
        compressor = "gzip";
        contents = [
          # Busybox binaries - MUST use static busybox!
          {
            source = "${staticBusybox}/bin";
            target = "/bin";
          }

          # Init script
          {
            source = pkgs.writeScript "init" ''
              #!/bin/sh
              export PATH=/bin

              # Mount essential filesystems
              mount -t proc proc /proc
              mount -t sysfs sys /sys
              mount -t devtmpfs dev /dev

              # Create device nodes if devtmpfs didn't
              [ -e /dev/console ] || mknod /dev/console c 5 1
              [ -e /dev/null ] || mknod /dev/null c 1 3
              [ -e /dev/tty ] || mknod /dev/tty c 5 0

              # Mount root filesystem
              echo "Mounting root filesystem..."
              mkdir -p /newroot
              mount -t ext4 /dev/vda /newroot

              # Switch root
              exec switch_root /newroot /sbin/init
            '';
            target = "/init";
          }
        ];
      };

      # ════════════════════════════════════════════════════════════════════════
      # Rootfs - Full root filesystem
      # ════════════════════════════════════════════════════════════════════════
      #
      # Contains:
      #   - busybox for basic utilities
      #   - nvidia-shim.ko kernel module
      #   - gpu-broker binary
      #   - Basic init system
      #
      fc-rootfs = pkgs.stdenv.mkDerivation {
        name = "fc-rootfs";

        # No source, we're building from scratch
        dontUnpack = true;

        # Don't patch shebangs - the init script needs #!/bin/sh for VM busybox
        dontPatchShebangs = true;

        nativeBuildInputs = with pkgs; [
          e2fsprogs
          util-linux
        ];

        buildPhase = ''
                              # Create rootfs directory structure
                              mkdir -p rootfs/{bin,sbin,lib,lib64,usr/{bin,sbin,lib},etc,proc,sys,dev,run,tmp,root,var/{log,run}}
                              mkdir -p rootfs/lib/modules/${kernelVersion}/extra

                              # Install busybox binary (static for no glibc dependency)
                              cp ${staticBusybox}/bin/busybox rootfs/bin/

                              # Create busybox symlinks
                              for cmd in sh ash cat ls cp mv rm mkdir mount umount mknod ln echo sleep \
                                         dmesg insmod rmmod lsmod modprobe ip ifconfig route ping hostname \
                                         ps top kill killall free df du stat head tail grep sed awk \
                                         vi less more tar gzip gunzip find xargs sort uniq wc cut \
                                         tr tee chown chmod touch date; do
                                ln -sf busybox rootfs/bin/$cmd 2>/dev/null || true
                              done

                              # Install nvidia-shim kernel module
                              cp ${nvidia-shim}/nvidia-shim.ko rootfs/lib/modules/${kernelVersion}/extra/

                              # Install gpu-broker
                              mkdir -p rootfs/usr/bin
                              cp ${gpu-broker}/bin/gpu-broker rootfs/usr/bin/
                              cp ${gpu-broker}/bin/guest-shim rootfs/usr/bin/ 2>/dev/null || true

                    # Create init script using printf to prevent shebang patching
                    # The shebang must be exactly "#!/bin/sh" for the VM's busybox
                    printf '%s\n' '#!'"/bin/sh" > rootfs/sbin/init
                    cat >> rootfs/sbin/init << 'INIT_BODY'
          export PATH=/bin:/sbin:/usr/bin:/usr/sbin

          # Mount filesystems
          mount -t proc proc /proc
          mount -t sysfs sys /sys
          mount -t devtmpfs dev /dev
          mkdir -p /dev/pts /dev/shm
          mount -t devpts devpts /dev/pts
          mount -t tmpfs tmpfs /dev/shm
          mount -t tmpfs tmpfs /run
          mount -t tmpfs tmpfs /tmp

          # Set hostname
          hostname broker-vm

          # Create vsock device if needed
          if [ ! -e /dev/vsock ]; then
            mknod /dev/vsock c 10 $(cat /proc/misc | grep vsock | cut -d' ' -f2) 2>/dev/null || true
          fi

          # Print welcome message
          echo ""
          echo "=========================================="
          echo "  Isospin Broker Test VM"  
          echo "=========================================="
          echo ""

          # Test nvidia-shim module loading
          echo "[TEST] Loading nvidia-shim kernel module..."
          if insmod /lib/modules/6.12.10/extra/nvidia-shim.ko; then
            echo "[PASS] nvidia-shim loaded successfully!"
            lsmod | grep nvidia
            echo ""
            echo "[TEST] Checking /dev/nvidia* devices..."
            ls -la /dev/nvidia* 2>/dev/null || echo "  (no devices yet - needs broker connection)"
          else
            echo "[FAIL] nvidia-shim failed to load"
          fi
          echo ""

          echo "Available commands:"
          echo "  insmod /lib/modules/6.12.10/extra/nvidia-shim.ko"
          echo "  gpu-broker --mock -v"
          echo ""

          # Start shell
          exec /bin/sh
          INIT_BODY
                    chmod +x rootfs/sbin/init

                              # Create /etc files
                              echo "root:x:0:0:root:/root:/bin/sh" > rootfs/etc/passwd
                              echo "root:x:0:" > rootfs/etc/group
                              echo "broker-vm" > rootfs/etc/hostname

                              # Create modules.dep for modprobe
                              mkdir -p rootfs/lib/modules/${kernelVersion}
                              touch rootfs/lib/modules/${kernelVersion}/modules.dep
                              echo "extra/nvidia-shim.ko:" >> rootfs/lib/modules/${kernelVersion}/modules.dep
        '';

        installPhase = ''
          # Calculate size needed (add 50MB buffer)
          SIZE_KB=$(du -sk rootfs | cut -f1)
          SIZE_KB=$((SIZE_KB + 51200))

          # Create ext4 filesystem
          mkdir -p $out
          dd if=/dev/zero of=$out/rootfs.ext4 bs=1K count=$SIZE_KB
          mkfs.ext4 -F -d rootfs $out/rootfs.ext4

          # Also output the raw directory for inspection
          cp -r rootfs $out/rootfs-contents
        '';
      };

      # ════════════════════════════════════════════════════════════════════════
      # GPU VM Initramfs - For Cloud Hypervisor with VFIO GPU passthrough
      # ════════════════════════════════════════════════════════════════════════
      #
      # This initramfs is for the GPU VM running Cloud Hypervisor with:
      #   - Kernel 6.12.63 (matches NVIDIA modules in gpu-rootfs.ext4)
      #   - virtio-pci drivers (Cloud Hypervisor uses PCI, not MMIO)
      #   - ext4 for rootfs
      #
      # The GPU VM boots this initramfs, mounts the rootfs, then runs the
      # real NVIDIA driver and gpu-broker.
      #
      gpu-vm-initramfs =
        let
          # IMPORTANT: This must match the kernel version in .vm-assets/vmlinux-6.12.63.bin
          # and the NVIDIA modules compiled in gpu-rootfs.ext4
          linuxKernel = pkgs.linuxPackages_6_12.kernel;
          linuxModules = linuxKernel.modules;
          # Use the actual kernel version from nixpkgs (modules must match kernel)
          gpuKernelVersion = linuxKernel.modDirVersion;
        in
        pkgs.stdenv.mkDerivation {
          name = "gpu-vm-initramfs";
          dontUnpack = true;
          dontPatchShebangs = true;

          nativeBuildInputs = with pkgs; [
            cpio
            gzip
            xz
          ];

          buildPhase = ''
                        echo "Building initramfs for kernel version: ${gpuKernelVersion}"
                        
                        mkdir -p initramfs/{bin,sbin,lib/modules/${gpuKernelVersion},dev,proc,sys,mnt/root,lib64}
                        MODDIR=initramfs/lib/modules/${gpuKernelVersion}
                        SRCBASE="${linuxModules}/lib/modules/${gpuKernelVersion}/kernel"

                        # Busybox
                        cp ${staticBusybox}/bin/busybox initramfs/bin/
                        for cmd in sh mount umount mkdir switch_root mdev cat ls ln chmod sleep echo insmod modprobe awk; do
                          ln -sf busybox initramfs/bin/$cmd
                        done
                        ln -sf ../bin/insmod initramfs/sbin/insmod
                        ln -sf ../bin/modprobe initramfs/sbin/modprobe

                        # Copy and decompress virtio modules for Cloud Hypervisor (uses virtio-pci)
                        # All virtio modules are in drivers/virtio/
                        for mod in virtio virtio_ring virtio_pci_modern_dev virtio_pci_legacy_dev virtio_pci virtio_mmio; do
                          src="$SRCBASE/drivers/virtio/$mod.ko.xz"
                          if [ -f "$src" ]; then
                            xz -dc "$src" > $MODDIR/$mod.ko
                            echo "Copied $mod.ko"
                          else
                            echo "WARNING: $src not found"
                          fi
                        done
                        
                        # virtio_blk is in drivers/block/
                        src="$SRCBASE/drivers/block/virtio_blk.ko.xz"
                        if [ -f "$src" ]; then
                          xz -dc "$src" > $MODDIR/virtio_blk.ko
                          echo "Copied virtio_blk.ko"
                        fi

                        # ext4 dependencies - crc modules
                        for mod in crc16 libcrc32c; do
                          src="$SRCBASE/lib/$mod.ko.xz"
                          [ -f "$src" ] && xz -dc "$src" > $MODDIR/$mod.ko && echo "Copied $mod.ko"
                        done
                        src="$SRCBASE/crypto/crc32c_generic.ko.xz"
                        [ -f "$src" ] && xz -dc "$src" > $MODDIR/crc32c_generic.ko && echo "Copied crc32c_generic.ko"
                        
                        # ext4 dependencies - mbcache and jbd2 are directly in fs/
                        src="$SRCBASE/fs/mbcache.ko.xz"
                        [ -f "$src" ] && xz -dc "$src" > $MODDIR/mbcache.ko && echo "Copied mbcache.ko"
                        src="$SRCBASE/fs/jbd2/jbd2.ko.xz"
                        [ -f "$src" ] && xz -dc "$src" > $MODDIR/jbd2.ko && echo "Copied jbd2.ko"
                        
                        # ext4 itself is in fs/ext4/
                        src="$SRCBASE/fs/ext4/ext4.ko.xz"
                        [ -f "$src" ] && xz -dc "$src" > $MODDIR/ext4.ko && echo "Copied ext4.ko"

                        echo "=== Modules copied ==="
                        ls -la $MODDIR/

                        # Init script - using double-quoted heredoc for variable substitution
                        # Note: We escape $ for variables that should be evaluated at runtime
                        cat > initramfs/init << INITSCRIPT
            #!/bin/sh
            export PATH=/bin:/sbin

            mount -t proc proc /proc
            mount -t sysfs sys /sys
            mount -t devtmpfs dev /dev

            echo "=== Initramfs: Loading virtio modules ==="
            cd /lib/modules/${gpuKernelVersion}
            for mod in virtio virtio_ring virtio_pci_modern_dev virtio_pci_legacy_dev virtio_pci virtio_mmio virtio_blk; do
              [ -f \$mod.ko ] && { echo "  Loading \$mod"; insmod \$mod.ko 2>/dev/null || true; }
            done

            echo "=== Loading ext4 modules ==="
            for mod in crc16 libcrc32c crc32c_generic mbcache jbd2 ext4; do
              [ -f \$mod.ko ] && insmod \$mod.ko 2>/dev/null || true
            done

            echo "=== Waiting for /dev/vda ==="
            for i in 1 2 3 4 5; do
              [ -b /dev/vda ] && break
              sleep 0.5
            done
            ls -la /dev/vda 2>/dev/null || { echo "ERROR: /dev/vda not found"; exec /bin/sh; }

            mkdir -p /mnt/root
            mount -t ext4 /dev/vda /mnt/root || { echo "ERROR: mount failed"; exec /bin/sh; }

            echo "=== Mounted /dev/vda, switching root ==="
            exec switch_root /mnt/root /init
            INITSCRIPT
                        chmod +x initramfs/init
          '';

          installPhase = ''
            mkdir -p $out
            cd initramfs
            find . | cpio -o -H newc | gzip -9 > $out/initramfs.cpio.gz

            # Record the kernel version for reference
            echo "${gpuKernelVersion}" > $out/kernel-version
          '';
        };

      # GPU VM kernel - must match initramfs modules
      gpu-vm-kernel = pkgs.linuxPackages_6_12.kernel;

    in
    {
      packages = {
        inherit
          fc-initramfs
          fc-rootfs
          gpu-vm-initramfs
          gpu-vm-kernel
          ;
      };
    };
}
