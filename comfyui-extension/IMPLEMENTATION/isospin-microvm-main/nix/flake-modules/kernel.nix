# nix/flake-modules/kernel.nix
#
# Kernel and kernel module builds for Firecracker GPU passthrough
#
# Provides:
#   packages.fc-gpu-kernel - Linux kernel configured for FC + GPU
#   packages.nvidia-shim - GPU broker kernel module
#
# Usage:
#   nix build .#fc-gpu-kernel
#   nix build .#nvidia-shim
#
{ ... }:
{
  _class = "flake";

  config.perSystem =
    { pkgs, lib, ... }:
    let
      kernelVersion = "6.12.10";
      kernelMajor = "6";

      # Kernel config for Firecracker with GPU passthrough
      kernelConfig = pkgs.writeText "fc-gpu-kernel-config" ''
        # Base Firecracker requirements
        CONFIG_VIRTIO_MMIO=y
        CONFIG_VIRTIO_MMIO_CMDLINE_DEVICES=y
        CONFIG_VIRTIO_BLK=y
        CONFIG_VIRTIO_NET=y
        CONFIG_VIRTIO_CONSOLE=y
        CONFIG_HW_RANDOM_VIRTIO=y
        CONFIG_NET_9P=y
        CONFIG_NET_9P_VIRTIO=y
        CONFIG_9P_FS=y
        CONFIG_EXT4_FS=y
        CONFIG_SERIAL_8250=y
        CONFIG_SERIAL_8250_CONSOLE=y

        # Networking (required for kernel socket API)
        CONFIG_NET=y
        CONFIG_INET=y
        CONFIG_UNIX=y
        CONFIG_PACKET=y

        # PCI and IOMMU for GPU passthrough
        CONFIG_PCI=y
        CONFIG_PCI_HOST_GENERIC=y
        CONFIG_PCIEPORTBUS=y
        CONFIG_PCIEAER=y
        CONFIG_PCIEASPM=y
        CONFIG_HOTPLUG_PCI=y
        CONFIG_HOTPLUG_PCI_PCIE=y

        # IOMMU
        CONFIG_IOMMU_SUPPORT=y
        CONFIG_IOMMU_API=y
        CONFIG_AMD_IOMMU=y
        CONFIG_INTEL_IOMMU=y
        CONFIG_INTEL_IOMMU_SVM=y

        # VFIO
        CONFIG_VFIO=y
        CONFIG_VFIO_PCI=y
        CONFIG_VFIO_IOMMU_TYPE1=y
        CONFIG_VFIO_VIRQFD=y

        # Kernel modules support
        CONFIG_MODULES=y
        CONFIG_MODULE_UNLOAD=y

        # vsock for GPU broker communication
        CONFIG_VSOCKETS=y
        CONFIG_VIRTIO_VSOCKETS=y

        # Memory
        CONFIG_MEMORY_HOTPLUG=y
        CONFIG_MEMORY_HOTREMOVE=y

        # Debug
        CONFIG_PRINTK=y
        CONFIG_EARLY_PRINTK=y
      '';

      fc-gpu-kernel = pkgs.stdenv.mkDerivation {
        pname = "fc-gpu-kernel";
        version = kernelVersion;

        src = pkgs.fetchurl {
          url = "https://cdn.kernel.org/pub/linux/kernel/v${kernelMajor}.x/linux-${kernelVersion}.tar.xz";
          sha256 = "sha256-SlFuXtdIU3pzy0LsR/u+tt+LEpjoiSwpwOkd55CVspc=";
        };

        nativeBuildInputs = with pkgs; [
          bc
          bison
          flex
          openssl
          perl
          elfutils
          ncurses
          pkg-config
          python3
          zstd
          cpio
          # Use GCC 13 - kernel 6.12 doesn't build with GCC 15
          gcc13
        ];

        # Force use of GCC 13
        CC = "${pkgs.gcc13}/bin/gcc";
        HOSTCC = "${pkgs.gcc13}/bin/gcc";

        buildInputs = with pkgs; [
          elfutils
          openssl
          zlib
        ];

        postPatch = ''
          patchShebangs scripts/
        '';

        configurePhase = ''
          runHook preConfigure

          # Start with defconfig for a working base, then apply our customizations
          make ARCH=x86_64 defconfig

          # Apply our required options
          cat ${kernelConfig} >> .config

          # Resolve dependencies - run olddefconfig twice to stabilize
          make ARCH=x86_64 olddefconfig
          make ARCH=x86_64 olddefconfig

          # Verify critical options are set
          echo "Verifying kernel config..."
          grep -E "^CONFIG_VIRTIO_BLK=|^CONFIG_SERIAL_8250=|^CONFIG_EXT4_FS=" .config

          runHook postConfigure
        '';

        buildPhase = ''
          runHook preBuild
          make ARCH=x86_64 CC=${pkgs.gcc13}/bin/gcc HOSTCC=${pkgs.gcc13}/bin/gcc -j$NIX_BUILD_CORES vmlinux modules
          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall

          mkdir -p $out
          cp vmlinux $out/vmlinux
          cp .config $out/config

          # Install modules
          make ARCH=x86_64 INSTALL_MOD_PATH=$out modules_install

          # Setup build directory for out-of-tree modules
          rm -f $out/lib/modules/${kernelVersion}/build
          rm -f $out/lib/modules/${kernelVersion}/source
          buildDir=$out/lib/modules/${kernelVersion}/build
          mkdir -p $buildDir

          cp .config $buildDir/
          cp Makefile $buildDir/
          cp Module.symvers $buildDir/
          cp -r scripts $buildDir/
          cp -r include $buildDir/
          mkdir -p $buildDir/arch/x86
          cp -r arch/x86/include $buildDir/arch/x86/
          cp arch/x86/Makefile $buildDir/arch/x86/
          mkdir -p $buildDir/tools/objtool
          cp tools/objtool/objtool $buildDir/tools/objtool/ 2>/dev/null || true
          mkdir -p $buildDir/arch/x86/kernel
          cp arch/x86/kernel/asm-offsets.s $buildDir/arch/x86/kernel/ 2>/dev/null || true

          ln -sf build $out/lib/modules/${kernelVersion}/source
          ln -s vmlinux $out/vmlinux-${kernelVersion}.bin

          runHook postInstall
        '';

        dontCheckForBrokenSymlinks = true;

        meta = {
          description = "Linux kernel configured for Firecracker with GPU passthrough";
          license = lib.licenses.gpl2Only;
          platforms = [ "x86_64-linux" ];
        };
      };

      # nvidia-shim kernel module for GPU broker
      nvidia-shim = pkgs.stdenv.mkDerivation {
        pname = "nvidia-shim";
        version = "0.1.0";

        src = ../../gpu-broker/kernel;

        nativeBuildInputs = with pkgs; [ gnumake ];

        KDIR = "${fc-gpu-kernel}/lib/modules/${kernelVersion}/build";

        buildPhase = ''
          runHook preBuild
          make KDIR=$KDIR
          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          mkdir -p $out/lib/modules/${kernelVersion}/extra
          cp nvidia-shim.ko $out/lib/modules/${kernelVersion}/extra/
          cp nvidia-shim.ko $out/
          runHook postInstall
        '';

        meta = {
          description = "NVIDIA GPU broker shim kernel module";
          license = lib.licenses.mit;
          platforms = [ "x86_64-linux" ];
        };
      };
    in
    {
      packages = {
        inherit fc-gpu-kernel nvidia-shim;
      };
    };
}
