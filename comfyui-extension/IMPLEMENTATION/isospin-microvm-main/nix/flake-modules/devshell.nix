# nix/flake-modules/devshell.nix
#
# Development shell for Isospin
#
# ════════════════════════════════════════════════════════════════════════════════
# Features
# ════════════════════════════════════════════════════════════════════════════════
#
#   - Rust toolchain with rust-analyzer, clippy, rustfmt
#   - Buck2 build system + reindeer
#   - Kernel headers for building nvidia-shim.ko
#   - QEMU and Firecracker for VM testing
#   - All static libraries pre-linked
#
# ════════════════════════════════════════════════════════════════════════════════
# Usage
# ════════════════════════════════════════════════════════════════════════════════
#
#   nix develop                    # Enter shell
#   cargo test --manifest-path gpu-broker/Cargo.toml  # Run broker tests
#   buck2 build //firecracker/...  # Build firecracker
#
{ inputs, ... }:
{
  _class = "flake";

  config.perSystem =
    {
      pkgs,
      config,
      isospinConfig,
      rustVendor,
      libseccompStatic,
      awsLcStatic,
      zstdStatic,
      ...
    }:
    let
      rustCfg = isospinConfig.rust;

      overlays = [ (import inputs.rust-overlay) ];
      pkgsWithRust = import inputs.nixpkgs {
        system = pkgs.stdenv.hostPlatform.system;
        inherit overlays;
      };

      rustToolchain = pkgsWithRust.rust-bin.stable.${rustCfg.version}.default.override {
        extensions = [
          "rust-src"
          "rust-analyzer"
          "rustfmt"
          "clippy"
        ];
        targets = rustCfg.targets;
      };

      # Kernel headers for building out-of-tree modules
      linuxPackages = pkgs.linuxPackages_latest;
    in
    {
      devShells.default = pkgs.mkShell {
        name = "isospin-dev";

        buildInputs =
          (with pkgs; [
            # Build Tools
            buck2
            reindeer
            rustToolchain
            cargo
            gnumake

            # Compilers & Linkers
            pkg-config
            clang
            llvm
            lld
            gcc

            # Kernel Development
            linuxHeaders
            linuxPackages.kernel.dev

            # Python
            python3

            # Rust Dev Tools
            cargo-edit
            cargo-watch
            rust-analyzer

            # CLI Tools
            ripgrep
            fd
            jq
            tree

            # Security Libraries
            libseccomp
            libseccomp.dev

            # Virtualization
            qemu
            firecracker

            # Build Dependencies
            protobuf
            zlib
            zlib.dev
            openssl
            openssl.dev

            # Kernel Module Build Dependencies
            kmod
            elfutils
            bc
            bison
            flex
            ncurses
          ])
          ++ [
            awsLcStatic
            libseccompStatic
            zstdStatic
          ];

        shellHook = ''
          export RUST_BACKTRACE=1
          export AWS_LC_LIB_DIR="${awsLcStatic}/lib"
          export LIBSECCOMP_LIB_DIR="${libseccompStatic.lib}/lib"
          export LIBSECCOMP_INCLUDE_DIR="${pkgs.libseccomp.dev}/include"
          export ZSTD_LIB_DIR="${zstdStatic}/lib"
          export RUST_VENDOR_DIR="${rustVendor}"
          export LIBRARY_PATH="${libseccompStatic.lib}/lib:${zstdStatic}/lib:$LIBRARY_PATH"
          export KDIR="${linuxPackages.kernel.dev}/lib/modules/${linuxPackages.kernel.modDirVersion}/build"

          if [ ! -e third-party/rust/vendor ] || [ -L third-party/rust/vendor ]; then
            rm -f third-party/rust/vendor
            ln -sf "${rustVendor}" third-party/rust/vendor
          fi

          echo ""
          echo "╔══════════════════════════════════════════════════════════════╗"
          echo "║              Isospin Development Environment                 ║"
          echo "╚══════════════════════════════════════════════════════════════╝"
          echo ""
          echo "  Rust:   $(rustc --version 2>/dev/null | cut -d' ' -f2)"
          echo "  Buck2:  $(buck2 --version 2>/dev/null | head -1 || echo 'not found')"
          echo "  Kernel: ${linuxPackages.kernel.version} (headers available)"
          echo ""
          echo "  Quick commands:"
          echo "    cargo test -p gpu-broker           # Run broker tests"
          echo "    buck2 build //firecracker/...      # Build firecracker"
          echo "    cd gpu-broker/kernel && make       # Build nvidia-shim.ko"
          echo "    sudo ./scripts/test-broker-loopback.sh  # Test VM loopback"
          echo ""
        '';
      };

      # Minimal broker development shell
      devShells.broker = pkgs.mkShell {
        name = "gpu-broker-dev";

        buildInputs = with pkgs; [
          rustToolchain
          cargo
          pkg-config
          openssl
          openssl.dev
        ];

        shellHook = ''
          echo "GPU Broker Development Shell"
          echo "  Run: cargo test"
        '';
      };

      # ══════════════════════════════════════════════════════════════════════
      # Standalone devshell script (workaround for ca-derivations)
      # ══════════════════════════════════════════════════════════════════════
      packages.devshell =
        let
          tools = with pkgs; [
            buck2
            reindeer
            rustToolchain
            cargo
            gnumake
            pkg-config
            clang
            llvm
            lld
            gcc
            linuxHeaders
            linuxPackages.kernel.dev
            python3
            cargo-edit
            cargo-watch
            rust-analyzer
            ripgrep
            fd
            jq
            tree
            libseccomp
            libseccomp.dev
            qemu
            firecracker
            protobuf
            zlib
            zlib.dev
            openssl
            openssl.dev
            kmod
            elfutils
            bc
            bison
            flex
            ncurses
            coreutils
            gnused
            gnugrep
            gnutar
            gzip
            findutils
            diffutils
            gawk
            patch
            bash
          ];
          toolPaths = pkgs.lib.makeBinPath tools;
        in
        pkgs.writeShellScriptBin "devshell" ''
          export PATH="${toolPaths}:$PATH"
          export RUST_BACKTRACE=1
          export AWS_LC_LIB_DIR="${awsLcStatic}/lib"
          export LIBSECCOMP_LIB_DIR="${libseccompStatic.lib}/lib"
          export LIBSECCOMP_INCLUDE_DIR="${pkgs.libseccomp.dev}/include"
          export ZSTD_LIB_DIR="${zstdStatic}/lib"
          export RUST_VENDOR_DIR="${rustVendor}"
          export LIBRARY_PATH="${libseccompStatic.lib}/lib:${zstdStatic}/lib:''${LIBRARY_PATH:-}"
          export KDIR="${linuxPackages.kernel.dev}/lib/modules/${linuxPackages.kernel.modDirVersion}/build"
          export CC="${pkgs.gcc}/bin/gcc"
          export CXX="${pkgs.gcc}/bin/g++"

          if [ -d "third-party/rust" ]; then
            if [ ! -e third-party/rust/vendor ] || [ -L third-party/rust/vendor ]; then
              rm -f third-party/rust/vendor
              ln -sf "${rustVendor}" third-party/rust/vendor
            fi
          fi

          echo ""
          echo "╔══════════════════════════════════════════════════════════════╗"
          echo "║              Isospin Development Environment                 ║"
          echo "╚══════════════════════════════════════════════════════════════╝"
          echo ""
          echo "  Rust:   $(${rustToolchain}/bin/rustc --version 2>/dev/null | cut -d' ' -f2)"
          echo "  Buck2:  $(${pkgs.buck2}/bin/buck2 --version 2>/dev/null | head -1 || echo 'available')"
          echo "  Kernel: ${linuxPackages.kernel.version} (headers at \$KDIR)"
          echo ""
          echo "  Commands:"
          echo "    cargo test -p gpu-broker           # Run broker tests"
          echo "    buck2 build //firecracker/...      # Build firecracker"
          echo "    cd gpu-broker/kernel && make       # Build nvidia-shim.ko"
          echo "    sudo ./scripts/test-broker-loopback.sh  # Test VM loopback"
          echo ""

          if [ $# -gt 0 ]; then
            exec ${pkgs.bash}/bin/bash "$@"
          else
            exec ${pkgs.bash}/bin/bash
          fi
        '';
    };
}
