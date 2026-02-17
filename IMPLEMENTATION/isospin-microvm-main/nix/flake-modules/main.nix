# nix/flake-modules/main.nix
#
# Isospin flake-parts configuration
#
# ════════════════════════════════════════════════════════════════════════════════
# Module Structure
# ════════════════════════════════════════════════════════════════════════════════
#
#   main.nix         - Options definitions + imports submodules
#   rust-vendor.nix  - Rust crate vendoring for Buck2
#   static-libs.nix  - Static library builds (aws-lc, libseccomp, zstd)
#   kernel.nix       - Linux kernel and nvidia-shim kernel module
#   gpu-broker.nix   - GPU broker Rust package
#   devshell.nix     - Development environment
#
# ════════════════════════════════════════════════════════════════════════════════
# Flake Outputs
# ════════════════════════════════════════════════════════════════════════════════
#
# Packages:
#   default              - Alias for rustVendor
#   rustVendor           - Patched vendor directory for Buck2
#   gpu-broker           - GPU broker binary (Rust)
#   nvidia-shim          - GPU broker kernel module
#   fc-gpu-kernel        - Linux kernel for Firecracker + GPU passthrough
#   awsLcStatic          - Static aws-lc with prefixed symbols
#   libseccompStatic     - Static libseccomp
#   zstdStatic           - Static zstd
#   vendor-link          - Helper to symlink vendor directory
#   buckify              - Helper to run reindeer buckify
#
# Development:
#   devShells.default    - Full development environment
#
# ════════════════════════════════════════════════════════════════════════════════
# Quick Start
# ════════════════════════════════════════════════════════════════════════════════
#
#   # Enter development shell
#   nix develop
#
#   # Build GPU broker
#   nix build .#gpu-broker
#
#   # Build kernel module
#   nix build .#nvidia-shim
#
#   # Build custom kernel
#   nix build .#fc-gpu-kernel
#
#   # Run broker tests
#   nix develop --command bash -c "cd gpu-broker && cargo test"
#
# ════════════════════════════════════════════════════════════════════════════════
# Troubleshooting
# ════════════════════════════════════════════════════════════════════════════════
#
# If you see "ca-derivations" errors:
#   Add to /etc/nix/nix.conf:
#     experimental-features = nix-command flakes ca-derivations
#   Then restart the nix-daemon:
#     sudo systemctl restart nix-daemon
#
# Or use the --option flag:
#   nix develop --option extra-experimental-features ca-derivations
#
{
  inputs,
  lib,
  config,
  ...
}:
{
  imports = [
    ./rust-vendor.nix
    ./static-libs.nix
    ./kernel.nix
    ./gpu-broker.nix
    ./vm-images.nix
    ./vm-runners.nix
    ./devshell.nix
  ];

  # ════════════════════════════════════════════════════════════════════════════
  # Options definitions (used by all submodules)
  # ════════════════════════════════════════════════════════════════════════════

  options.isospin = {
    rust = {
      version = lib.mkOption {
        type = lib.types.str;
        default = "1.89.0";
        description = "Rust toolchain version";
      };

      targets = lib.mkOption {
        type = lib.types.listOf lib.types.str;
        default = [
          "x86_64-unknown-linux-gnu"
          "aarch64-unknown-linux-gnu"
        ];
        description = "Rust compilation targets";
      };
    };

    vendor = {
      lockFile = lib.mkOption {
        type = lib.types.path;
        description = "Path to Cargo.lock";
      };

      fixupsDir = lib.mkOption {
        type = lib.types.path;
        description = "Path to fixups directory";
      };

      outputHashes = lib.mkOption {
        type = lib.types.attrsOf lib.types.str;
        default = { };
        description = "Output hashes for git dependencies";
      };
    };

    static-libs = {
      aws-lc-prefix-headers = lib.mkOption {
        type = lib.types.path;
        description = "Path to aws-lc prefix headers";
      };
    };
  };

  # Pass top-level config to perSystem via _module.args
  config.perSystem =
    { ... }:
    {
      _module.args.isospinConfig = config.isospin;
    };
}
