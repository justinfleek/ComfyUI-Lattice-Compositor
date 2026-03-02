# nix/flake-modules/rust-vendor.nix
#
# Rust crate vendoring for Buck2
#
# Provides:
#   packages.rustVendor - Patched vendor directory
#
# Usage:
#   nix build .#rustVendor
#   ln -sf $(nix build .#rustVendor --print-out-paths) third-party/rust/vendor
#
{ inputs, ... }:
let
  # vm-memory 0.18 compatibility patches
  vendorPatchScript = ''
    # Add acpi_tables from rust-vmm git
    mkdir -p $out/acpi_tables-0.1.0
    cp -r $acpiTablesSrc/* $out/acpi_tables-0.1.0/
    chmod -R u+w $out/acpi_tables-0.1.0
    echo '{"files":{},"package":"acpi_tables_from_rust_vmm_git"}' > $out/acpi_tables-0.1.0/.cargo-checksum.json

    # Cargo.toml version constraint patches
    if [ -d $out/linux-loader-0.13.2 ]; then
      $sed -i 's/<=0.17.1/<=0.18.0/g' $out/linux-loader-0.13.2/Cargo.toml
    fi

    for crate in virtio-queue-0.16.0 vhost-user-backend-0.20.0 vfio-ioctls-0.5.2 vfio_user-0.1.2; do
      if [ -d $out/$crate ]; then
        $sed -i 's/"0.16"/">=0.16, <=0.18"/g' $out/$crate/Cargo.toml
      fi
    done

    # rustix extern crate errno fix
    if [ -d $out/rustix-1.1.3 ]; then
      for file in io/errno.rs fs/dir.rs event/syscalls.rs fs/syscalls.rs process/syscalls.rs; do
        filepath="$out/rustix-1.1.3/src/backend/libc/$file"
        if [ -f "$filepath" ]; then
          $sed -i '0,/^use /{s/^use /extern crate errno as libc_errno;\n\nuse /}' "$filepath"
        fi
      done
    fi

    # linux-loader vm-memory 0.18 GuestMemoryBackend bounds
    if [ -d $out/linux-loader-0.13.2 ]; then
      for file in \
        $out/linux-loader-0.13.2/src/configurator/fdt.rs \
        $out/linux-loader-0.13.2/src/configurator/mod.rs \
        $out/linux-loader-0.13.2/src/configurator/x86_64/linux.rs \
        $out/linux-loader-0.13.2/src/configurator/x86_64/pvh.rs \
        $out/linux-loader-0.13.2/src/loader/bzimage/mod.rs \
        $out/linux-loader-0.13.2/src/loader/elf/mod.rs \
        $out/linux-loader-0.13.2/src/loader/mod.rs \
        $out/linux-loader-0.13.2/src/loader/pe/mod.rs
      do
        if [ -f "$file" ]; then
          $sed -i 's/M: GuestMemory,$/M: GuestMemory + GuestMemoryBackend,/g' "$file"
          $sed -i 's/M: GuestMemory;$/M: GuestMemory + GuestMemoryBackend;/g' "$file"
          $sed -i 's/<F, M: GuestMemory>/<F, M: GuestMemory + GuestMemoryBackend>/g' "$file"
          $sed -i 's/<M: GuestMemory>/<M: GuestMemory + GuestMemoryBackend>/g' "$file"
        fi
      done

      $sed -i 's/use vm_memory::{Bytes, GuestMemory};/use vm_memory::{Bytes, GuestMemory, GuestMemoryBackend};/g' \
        $out/linux-loader-0.13.2/src/configurator/fdt.rs
      $sed -i 's/use vm_memory::{Address, ByteValued, GuestAddress, GuestMemory};/use vm_memory::{Address, ByteValued, GuestAddress, GuestMemory, GuestMemoryBackend};/g' \
        $out/linux-loader-0.13.2/src/configurator/mod.rs
      $sed -i 's/use vm_memory::{Bytes, GuestMemory};/use vm_memory::{Bytes, GuestMemory, GuestMemoryBackend};/g' \
        $out/linux-loader-0.13.2/src/configurator/x86_64/linux.rs
      $sed -i 's/use vm_memory::{ByteValued, Bytes, GuestMemory};/use vm_memory::{ByteValued, Bytes, GuestMemory, GuestMemoryBackend};/g' \
        $out/linux-loader-0.13.2/src/configurator/x86_64/pvh.rs
      $sed -i 's/GuestMemory, GuestUsize, ReadVolatile};/GuestMemory, GuestMemoryBackend, GuestUsize, ReadVolatile};/g' \
        $out/linux-loader-0.13.2/src/loader/bzimage/mod.rs \
        $out/linux-loader-0.13.2/src/loader/elf/mod.rs \
        $out/linux-loader-0.13.2/src/loader/mod.rs \
        $out/linux-loader-0.13.2/src/loader/pe/mod.rs
    fi

    # virtio-queue vm-memory 0.18 patches
    if [ -d $out/virtio-queue-0.16.0 ]; then
      for file in \
        $out/virtio-queue-0.16.0/src/chain.rs \
        $out/virtio-queue-0.16.0/src/lib.rs \
        $out/virtio-queue-0.16.0/src/queue.rs \
        $out/virtio-queue-0.16.0/src/queue_sync.rs \
        $out/virtio-queue-0.16.0/src/descriptor_utils.rs
      do
        if [ -f "$file" ]; then
          $sed -i 's/as GuestMemory>::R/as GuestMemoryBackend>::R/g' "$file"
          $sed -i 's/M::Target: GuestMemory,$/M::Target: GuestMemory + GuestMemoryBackend,/g' "$file"
          $sed -i 's/M::Target: GuestMemory$/M::Target: GuestMemory + GuestMemoryBackend/g' "$file"
          $sed -i 's/M::Target: GuestMemory + Sized,$/M::Target: GuestMemory + GuestMemoryBackend + Sized,/g' "$file"
          $sed -i 's/M::Target: GuestMemory + Sized$/M::Target: GuestMemory + GuestMemoryBackend + Sized/g' "$file"
          $sed -i 's/T::Target: GuestMemory + Sized,$/T::Target: GuestMemory + GuestMemoryBackend + Sized,/g' "$file"
          $sed -i 's/T::Target: GuestMemory + Sized$/T::Target: GuestMemory + GuestMemoryBackend + Sized/g' "$file"
          $sed -i 's/<M: GuestMemory>(&self/<M: GuestMemory + GuestMemoryBackend>(\&self/g' "$file"
          $sed -i 's/<M: GuestMemory>(&mut self/<M: GuestMemory + GuestMemoryBackend>(\&mut self/g' "$file"
          $sed -i 's/<M: GuestMemory>($/\<M: GuestMemory + GuestMemoryBackend>(/g' "$file"
          $sed -i 's/M: GuestMemory,$/M: GuestMemory + GuestMemoryBackend,/g' "$file"
          $sed -i 's/M: GuestMemory;$/M: GuestMemory + GuestMemoryBackend;/g' "$file"
          $sed -i 's/M: GuestMemory + ?Sized;/M: GuestMemory + GuestMemoryBackend + ?Sized;/g' "$file"
          $sed -i 's/M: GuestMemory + ?Sized,/M: GuestMemory + GuestMemoryBackend + ?Sized,/g' "$file"
        fi
      done

      $sed -i 's/use vm_memory::{Address, Bytes, GuestAddress, GuestMemory, GuestMemoryRegion};/use vm_memory::{Address, Bytes, GuestAddress, GuestMemory, GuestMemoryBackend, GuestMemoryRegion};/g' \
        $out/virtio-queue-0.16.0/src/chain.rs
      $sed -i 's/use vm_memory::{GuestMemory, GuestMemoryError/use vm_memory::{GuestMemory, GuestMemoryBackend, GuestMemoryError/g' \
        $out/virtio-queue-0.16.0/src/lib.rs
      $sed -i 's/M::Target: GuestMemory;$/M::Target: GuestMemory + GuestMemoryBackend;/g' \
        $out/virtio-queue-0.16.0/src/lib.rs
      $sed -i 's/use vm_memory::{Address, Bytes, GuestAddress, GuestMemory};/use vm_memory::{Address, Bytes, GuestAddress, GuestMemory, GuestMemoryBackend};/g' \
        $out/virtio-queue-0.16.0/src/queue.rs
      $sed -i 's/use vm_memory::GuestMemory;/use vm_memory::{GuestMemory, GuestMemoryBackend};/g' \
        $out/virtio-queue-0.16.0/src/queue_sync.rs
      $sed -i 's/Address, ByteValued, GuestMemory, GuestMemoryRegion, MemoryRegionAddress/Address, ByteValued, GuestMemory, GuestMemoryBackend, GuestMemoryRegion, MemoryRegionAddress/g' \
        $out/virtio-queue-0.16.0/src/descriptor_utils.rs
    fi

    # vfio-ioctls vm-memory 0.18 patches
    if [ -d $out/vfio-ioctls-0.5.2 ]; then
      $sed -i 's/<M: GuestMemory>(&self, mem: &M)/<M: GuestMemory + GuestMemoryBackend>(\&self, mem: \&M)/g' \
        $out/vfio-ioctls-0.5.2/src/vfio_device.rs
      $sed -i 's/use vm_memory::{Address, GuestMemory, GuestMemoryRegion/use vm_memory::{Address, GuestMemory, GuestMemoryBackend, GuestMemoryRegion/g' \
        $out/vfio-ioctls-0.5.2/src/vfio_device.rs
    fi

    # vhost-0.14.0 patches
    if [ -d $out/vhost-0.14.0 ]; then
      $sed -i 's/use vm_memory::{mmap::NewBitmap, ByteValued, Error as MmapError, FileOffset, MmapRegion};/use vm_memory::{mmap::NewBitmap, ByteValued, FileOffset, MmapRegion};/g' \
        $out/vhost-0.14.0/src/vhost_user/message.rs
      $sed -i '/\.map_err(MmapError::MmapRegion)/d' \
        $out/vhost-0.14.0/src/vhost_user/message.rs
    fi

    # vhost-0.15.0 patches
    if [ -d $out/vhost-0.15.0 ]; then
      $sed -i 's/use vm_memory::{Address, GuestAddress, GuestAddressSpace, GuestMemory, GuestUsize};/use vm_memory::{Address, GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryBackend, GuestUsize};/g' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs
      $sed -i 's/fn is_valid(\&self, config_data: \&VringConfigData) -> bool {/fn is_valid(\&self, config_data: \&VringConfigData) -> bool where <Self::AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs
      $sed -i 's/impl<T: VhostKernBackend> VhostBackend for T {/impl<T: VhostKernBackend> VhostBackend for T where <<T as VhostKernBackend>::AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs
      $sed -i 's/impl<I: VhostKernBackend + VhostKernFeatures> VhostIotlbBackend for I {/impl<I: VhostKernBackend + VhostKernFeatures> VhostIotlbBackend for I where <<I as VhostKernBackend>::AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs
      $sed -i 's/pub fn to_vhost_vring_addr<AS: GuestAddressSpace>(/pub fn to_vhost_vring_addr<AS: GuestAddressSpace + Clone>(/g' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs
      $perl -i -0pe 's/(pub fn to_vhost_vring_addr<AS: GuestAddressSpace \+ Clone>\(\s*\&self,\s*queue_index: usize,\s*mem: \&AS,\s*\) -> Result<vhost_vring_addr>) \{/$1\n    where\n        <AS as GuestAddressSpace>::M: GuestMemoryBackend,\n    {/s' \
        $out/vhost-0.15.0/src/vhost_kern/mod.rs

      for vhostFile in vdpa.rs net.rs vsock.rs; do
        $sed -i 's/use vm_memory::GuestAddressSpace;/use vm_memory::{GuestAddressSpace, GuestMemoryBackend};/' \
          $out/vhost-0.15.0/src/vhost_kern/$vhostFile 2>/dev/null || true
      done
      $sed -i 's/impl<AS: GuestAddressSpace> VhostKernVdpa<AS> {/impl<AS: GuestAddressSpace> VhostKernVdpa<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vdpa.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> VhostKernBackend for VhostKernVdpa<AS> {/impl<AS: GuestAddressSpace> VhostKernBackend for VhostKernVdpa<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vdpa.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> VhostVdpa for VhostKernVdpa<AS> {/impl<AS: GuestAddressSpace> VhostVdpa for VhostKernVdpa<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vdpa.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> VhostKernFeatures for VhostKernVdpa<AS> {/impl<AS: GuestAddressSpace> VhostKernFeatures for VhostKernVdpa<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vdpa.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> AsRawFd for VhostKernVdpa<AS> {/impl<AS: GuestAddressSpace> AsRawFd for VhostKernVdpa<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vdpa.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> VhostKernBackend for Net<AS> {/impl<AS: GuestAddressSpace> VhostKernBackend for Net<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/net.rs 2>/dev/null || true
      $sed -i 's/impl<AS: GuestAddressSpace> VhostKernBackend for Vsock<AS> {/impl<AS: GuestAddressSpace> VhostKernBackend for Vsock<AS> where <AS as GuestAddressSpace>::M: GuestMemoryBackend {/' \
        $out/vhost-0.15.0/src/vhost_kern/vsock.rs 2>/dev/null || true
    fi

    # vhost-user-backend patches
    if [ -d $out/vhost-user-backend-0.20.0 ]; then
      $sed -i 's/use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryMmap};/use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryBackend, GuestMemoryMmap};/g' \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i 's/impl<M: GuestAddressSpace> VringState<M> {/impl<M: GuestAddressSpace> VringState<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g' \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i 's/impl<M: GuestAddressSpace> VringMutex<M> {/impl<M: GuestAddressSpace> VringMutex<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g' \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i 's/impl<M: GuestAddressSpace> VringRwLock<M> {/impl<M: GuestAddressSpace> VringRwLock<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g' \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<'a, M: 'a + GuestAddressSpace> VringStateGuard<'a, M> for VringMutex<M> {/impl<'a, M: 'a + GuestAddressSpace> VringStateGuard<'a, M> for VringMutex<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<'a, M: 'a + GuestAddressSpace> VringStateMutGuard<'a, M> for VringMutex<M> {/impl<'a, M: 'a + GuestAddressSpace> VringStateMutGuard<'a, M> for VringMutex<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<'a, M: 'a + GuestAddressSpace> VringStateGuard<'a, M> for VringRwLock<M> {/impl<'a, M: 'a + GuestAddressSpace> VringStateGuard<'a, M> for VringRwLock<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<'a, M: 'a + GuestAddressSpace> VringStateMutGuard<'a, M> for VringRwLock<M> {/impl<'a, M: 'a + GuestAddressSpace> VringStateMutGuard<'a, M> for VringRwLock<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<M: 'static + GuestAddressSpace> VringT<M> for VringMutex<M> {/impl<M: 'static + GuestAddressSpace> VringT<M> for VringMutex<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs
      $sed -i "s/impl<M: 'static + GuestAddressSpace> VringT<M> for VringRwLock<M> {/impl<M: 'static + GuestAddressSpace> VringT<M> for VringRwLock<M> where <M as GuestAddressSpace>::M: GuestMemoryBackend {/g" \
        $out/vhost-user-backend-0.20.0/src/vring.rs

      $sed -i 's/use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryMmap, GuestRegionMmap};/use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryBackend, GuestMemoryMmap, GuestRegionMmap};/g' \
        $out/vhost-user-backend-0.20.0/src/handler.rs

      $awk '
        /GuestRegionMmap::new\(/ { in_grm = 1 }
        in_grm && /\.map_err\(\|e\| \{/ {
          gsub(/\.map_err\(\|e\| \{/, ".ok_or_else(|| {")
          in_grm = 0
          next_replace = 1
        }
        next_replace && /VhostUserError::ReqHandlerError\(io::Error::new\(io::ErrorKind::Other, e\)\)/ {
          gsub(/, e\)/, ", \"GuestRegionMmap overflow\")")
          next_replace = 0
        }
        { print }
      ' $out/vhost-user-backend-0.20.0/src/handler.rs > $out/vhost-user-backend-0.20.0/src/handler.rs.tmp && \
        mv $out/vhost-user-backend-0.20.0/src/handler.rs.tmp $out/vhost-user-backend-0.20.0/src/handler.rs
    fi

    # Apply overlay files from fixups
    for fixup in $fixupsDir/*/overlay; do
      if [ -d "$fixup" ]; then
        crate=$(basename $(dirname $fixup))
        for vendor_crate in $out/$crate-*; do
          if [ -d "$vendor_crate" ]; then
            mkdir -p "$vendor_crate/out"
            cp -r "$fixup"/* "$vendor_crate/out/" 2>/dev/null || true
          fi
        done
      fi
    done
  '';
in
{
  _class = "flake";

  config.perSystem =
    { pkgs, isospinConfig, ... }:
    let
      cfg = isospinConfig.vendor;

      vendorBase = pkgs.rustPlatform.importCargoLock {
        inherit (cfg) lockFile outputHashes;
      };

      acpiTablesSrc = pkgs.fetchFromGitHub {
        owner = "rust-vmm";
        repo = "acpi_tables";
        rev = "e08a3f0b0a59b98859dbf59f5aa7fd4d2eb4018a";
        hash = "sha256-ykg3UFX/8r8uYlbBxHfRHElH7qGHQIfCJ8VTjxOD+Hk=";
      };

      rustVendor =
        pkgs.runCommand "rust-vendor-patched"
          {
            inherit (cfg) fixupsDir;
            inherit acpiTablesSrc;
            nativeBuildInputs = [
              pkgs.perl
              pkgs.gawk
            ];
            sed = "${pkgs.gnused}/bin/sed";
            perl = "${pkgs.perl}/bin/perl";
            awk = "${pkgs.gawk}/bin/awk";
          }
          ''
            mkdir -p $out
            cp -rL ${vendorBase}/* $out/
            chmod -R u+w $out
            ${vendorPatchScript}
          '';
    in
    {
      _module.args.rustVendor = rustVendor;
      packages.rustVendor = rustVendor;
    };
}
