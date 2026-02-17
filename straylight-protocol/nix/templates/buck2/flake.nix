{
  description = "Buck2 project with hermetic Nix toolchains";

  inputs = {
    straylight.url = "github:straylight-software/straylight";
    nixpkgs.follows = "straylight/nixpkgs";
    flake-parts.follows = "straylight/flake-parts";
    systems.url = "github:nix-systems/default-linux";

    # Buck2 prelude (straylight fork with NVIDIA support)
    buck2-prelude = {
      url = "github:weyl-ai/straylight-buck2-prelude";
      flake = false;
    };
  };

  outputs =
    inputs@{ flake-parts, straylight, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Import the build module for Buck2 integration
      imports = [
        straylight.modules.flake.build
        straylight.modules.flake.nixpkgs
        straylight.modules.flake.formatter
      ];

      systems = import inputs.systems;

      # ════════════════════════════════════════════════════════════════════════
      # Buck2 Build Configuration
      # ════════════════════════════════════════════════════════════════════════
      straylight-naught.build = {
        enable = true;

        # Auto-generate .buckconfig, .buckroot, none/BUCK if missing
        generate-buckconfig-main = true;

        # Enable the toolchains you need
        toolchain = {
          cxx.enable = true; # LLVM 22 C++ (required)
          nv.enable = true; # NVIDIA (clang + nvidia-sdk)
          rust.enable = true; # Rust
          haskell.enable = false; # GHC (disable if not needed)
          lean.enable = false; # Lean 4
          python.enable = false; # Python/nanobind
        };
      };

      # Enable LLVM and NVIDIA overlays
      straylight-naught.nixpkgs.nv.enable = true;

      perSystem =
        { pkgs, config, ... }:
        {
          # Development shell with Buck2 and toolchains
          # Uses packages from the build module (includes llvm-git, nvidia-sdk, etc.)
          devShells.default = pkgs.mkShell {
            packages = [ pkgs.buck2 ] ++ config.straylight.build.packages;

            # Shell hook from build module links prelude, toolchains,
            # and generates .buckconfig.local with Nix store paths
            inherit (config.straylight.build) shellHook;
          };

          packages.default = pkgs.hello;
        };
    };
}
