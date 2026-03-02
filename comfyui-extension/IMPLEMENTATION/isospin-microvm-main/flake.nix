# ════════════════════════════════════════════════════════════════════════════════
# Isospin - GPU Passthrough for Firecracker VMs
# ════════════════════════════════════════════════════════════════════════════════
#
# This flake provides:
#   - GPU broker for eliminating GPU cold-boot latency
#   - Custom kernel with VFIO/IOMMU support
#   - nvidia-shim kernel module for ioctl proxying
#   - Development environment with all tools
#
# ────────────────────────────────────────────────────────────────────────────────
# Quick Start
# ────────────────────────────────────────────────────────────────────────────────
#
#   # Build packages
#   nix build .#gpu-broker               # Build broker binary
#   nix build .#nvidia-shim              # Build kernel module
#   nix build .#fc-gpu-kernel            # Build custom kernel
#
#   # Enter development shell
#   nix develop                          # Full dev environment
#   nix develop .#broker                 # Minimal broker dev shell
#
#   # For Buck2 builds
#   nix develop --command buck2 build //firecracker/...
#
# ────────────────────────────────────────────────────────────────────────────────
# Troubleshooting: ca-derivations Error
# ────────────────────────────────────────────────────────────────────────────────
#
# If you see: "experimental Nix feature 'ca-derivations' is disabled"
#
# This is because the Nix daemon doesn't have ca-derivations enabled.
# Fix by adding to /etc/nix/nix.conf:
#
#   experimental-features = nix-command flakes ca-derivations
#
# Then restart the daemon:
#   sudo systemctl restart nix-daemon
#
# Alternative: Use --option flag:
#   nix develop --option extra-experimental-features ca-derivations
#
# Or run builds directly (which work without ca-derivations):
#   nix build .#gpu-broker
#   ./result/bin/gpu-broker --help
#
# ════════════════════════════════════════════════════════════════════════════════
{
  description = "Isospin - GPU passthrough and multiplexing for Firecracker VMs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ./nix/flake-modules/main.nix ];

      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      # ══════════════════════════════════════════════════════════════════════
      # Isospin Configuration
      # ══════════════════════════════════════════════════════════════════════
      isospin = {
        # Rust toolchain version and targets
        rust = {
          version = "1.89.0";
          targets = [
            "x86_64-unknown-linux-gnu"
            "aarch64-unknown-linux-gnu"
          ];
        };

        # Cargo vendor configuration for Buck2
        vendor = {
          lockFile = ./third-party/rust/Cargo.lock;
          fixupsDir = ./third-party/rust/fixups;
          outputHashes = {
            "micro_http-0.1.0" = "sha256-XemdzwS25yKWEXJcRX2l6QzD7lrtroMeJNOUEWGR7WQ=";
          };
        };

        # Static library configuration
        static-libs = {
          aws-lc-prefix-headers = ./third-party/rust/aws-lc-sys-headers;
        };
      };

      # ══════════════════════════════════════════════════════════════════════
      # Per-System Outputs
      # ══════════════════════════════════════════════════════════════════════
      perSystem =
        {
          config,
          pkgs,
          rustVendor,
          awsLcStatic,
          libseccompStatic,
          zstdStatic,
          ...
        }:
        {
          packages = {
            # Default: vendor directory for Buck2
            default = rustVendor;

            # ────────────────────────────────────────────────────────────────
            # Helper Scripts
            # ────────────────────────────────────────────────────────────────

            # Link vendor directory for Buck2 builds
            vendor-link = pkgs.writeShellScriptBin "vendor-link" ''
              rm -f third-party/rust/vendor
              ln -sf "${rustVendor}" third-party/rust/vendor
              echo "Linked vendor -> ${rustVendor}"
            '';

            # Run reindeer to generate Buck2 BUCK files
            buckify = pkgs.writeShellScriptBin "buckify" ''
              export AWS_LC_LIB_DIR="${awsLcStatic}/lib"
              export LIBSECCOMP_LIB_DIR="${libseccompStatic.lib}/lib"
              export ZSTD_LIB_DIR="${zstdStatic}/lib"
              if [ ! -e third-party/rust/vendor ]; then
                ln -sf "${rustVendor}" third-party/rust/vendor
              fi
              ${pkgs.reindeer}/bin/reindeer --third-party-dir third-party/rust buckify
            '';

          };
        };
    };
}
