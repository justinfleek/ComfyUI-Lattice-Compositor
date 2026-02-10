{
  description = "Isospin - Buck2 monorepo for Firecracker and Cloud Hypervisor";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      rust-overlay,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        # Rust toolchain matching both hypervisors
        rustToolchain = pkgs.rust-bin.stable."1.89.0".default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "rustfmt"
            "clippy"
          ];
          targets = [
            "x86_64-unknown-linux-gnu"
            "aarch64-unknown-linux-gnu"
          ];
        };

        devPackages = with pkgs; [
          # Build tools
          rustToolchain
          cargo

          # System dependencies
          pkg-config
          clang
          llvm
          linuxHeaders

          # Python for integration tests
          python3
          python3Packages.pytest

          # Development tools
          cargo-edit
          cargo-watch
          rust-analyzer
          ripgrep
          fd

          # Security tools
          libseccomp
          libseccomp.dev

          # Network tools
          iperf3
          netcat

          # VM management
          qemu

          # Build dependencies
          protobuf

          # System libraries
          zlib
          zlib.dev
          openssl
          openssl.dev

          # Cross-compilation (optional)
          # pkgsCross.aarch64-multiplatform.stdenv.cc
        ];

      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = devPackages;

          shellHook = ''
            export RUST_BACKTRACE=1
            export RUST_LOG=debug
            export BUCK2_VERSION="8.0.0"

            echo "🚀 Isospin Development Environment Ready!"
            echo "🔧 Buck2: $(buck2 --version 2>/dev/null || echo 'Buck2 not found')"
            echo "🦀 Rust: $(rustc --version)"
            echo "🐧 Kernel Headers: ${pkgs.linuxHeaders.version}"
          '';
        };
      }
    );
}
