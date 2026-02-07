# nix/_main.nix
#
# FREESIDEフリーサイド — WHY WAIT?
#
# The directory is the kind signature.
#
{ inputs, lib, ... }:
let
  # Import module indices by kind
  flakeModules = import ./modules/flake/_index.nix { inherit inputs lib; };
  nixosModules = import ./modules/nixos/_index.nix;
  homeModules = import ./modules/home/_index.nix;
in
{
  _class = "flake";

  # Required by flake-parts for perSystem
  systems = import inputs.systems;

  # ════════════════════════════════════════════════════════════════════════════
  # MODULES BY KIND
  #
  # flake.modules.<kind>.<name> for automatic _class validation
  # ════════════════════════════════════════════════════════════════════════════

  flake.modules = {
    flake = {
      inherit (flakeModules)
        build
        buck2
        build-standalone
        default
        default-with-demos
        devshell
        docs
        formatter
        full
        lint
        lre
        nativelink
        nix-conf
        nixpkgs
        nv-sdk
        container
        prelude
        prelude-demos
        typed-build
        shortlist
        shortlist-standalone
        std
        options-only
        ;
    };

    nixos = nixosModules;

    home = homeModules;
  };

  # ════════════════════════════════════════════════════════════════════════════
  # OVERLAYS
  #
  # A pure function from the world as it is to the world as it ought to be.
  # ════════════════════════════════════════════════════════════════════════════

  flake.overlays = (import ./overlays inputs).flake.overlays;

  # ════════════════════════════════════════════════════════════════════════════
  # LIB
  #
  # Pure functions. No pkgs, no system.
  # ════════════════════════════════════════════════════════════════════════════

  flake.lib = import ./lib { inherit lib; } // {
    # Buck2 builder - use from downstream flakes:
    #   packages.myapp = straylight.lib.buck2.build pkgs { target = "//src:myapp"; };
    buck2 = import ./lib/buck2.nix { inherit inputs lib; };
  };

  # ════════════════════════════════════════════════════════════════════════════
  # TEMPLATES
  # ════════════════════════════════════════════════════════════════════════════

  flake.templates = {
    default = {
      path = ./templates/default;
      description = "Standard project";
    };

    nv = {
      path = ./templates/nv;
      description = "NVIDIA/ML project";
    };

    buck2 = {
      path = ./templates/buck2;
      description = "Buck2 build system with hermetic Nix toolchains";
    };

    minimal = {
      path = ./templates/minimal;
      description = "Minimal flake";
    };

    dhall-configured = {
      path = ./templates/dhall-configured;
      description = "Dhall-typed configuration";
    };

    nickel-configured = {
      path = ./templates/nickel-configured;
      description = "Nickel-typed configuration";
    };
  };

  # ════════════════════════════════════════════════════════════════════════════
  # INTERNAL: straylight-naught's own development
  # ════════════════════════════════════════════════════════════════════════════

  imports = [
    flakeModules.formatter
    flakeModules.lint
    flakeModules.docs
    flakeModules.std
    flakeModules.devshell
    flakeModules.prelude
    flakeModules.prelude-demos
    flakeModules.container
    flakeModules.build
    flakeModules.buck2
    flakeModules.shortlist
    flakeModules.lre
    # nix2gpu.flakeModule must be imported before nativelink module
    # (provides perSystem.nix2gpu options)
    inputs.nix2gpu.flakeModule
    flakeModules.nativelink
  ];

  # Enable shortlist, LRE, and NativeLink containers for straylight itself
  straylight-naught.shortlist.enable = true;
  straylight-naught.lre.enable = true;
  straylight-naught.nativelink.enable = true;

  perSystem =
    {
      pkgs,
      system,
      config,
      ...
    }:
    let
      # WASM infrastructure (internal)
      wasm-infra = import ./prelude/wasm-plugin.nix {
        inherit lib;
        inherit (pkgs) stdenv runCommand;
        inherit (inputs) ghc-wasm-meta;
      };

      # GHC WASM toolchain for compiling .hs packages
      ghc-wasm = inputs.ghc-wasm-meta.packages.${system}.all_9_12 or null;

      # The straylight interface
      # Usage: straylight.eval "Straylight.Packages.Nvidia.nccl" {}
      straylight = import ./prelude/straylight.nix {
        inherit lib pkgs;
        wasmFile = wasm-infra.straylightWasm;
      };

      # ────────────────────────────────────────────────────────────────────────
      # // call-package for typed .hs files //
      # ────────────────────────────────────────────────────────────────────────
      # This is the local version for internal use. The prelude exports
      # a version that's available to downstream consumers.
      #
      # User files just need:
      #   module Pkg where
      #   import Straylight.Nix.Package
      #   pkg = mkDerivation [ ... ]
      #
      # The FFI boilerplate is generated automatically.
      #
      # IFD AVOIDANCE: If a pre-built .wasm file exists alongside the .hs file,
      # we use it directly instead of building at evaluation time. This avoids
      # the "import from derivation" warning in `nix flake show`.
      #
      # To pre-build all .wasm files:
      #   nix build .#wasm-packages -o result-wasm
      #   cp result-wasm/*.wasm nix/packages/
      #
      call-package =
        path: args:
        let
          pathStr = toString path;
          ext = lib.last (lib.splitString "." pathStr);
          straylightModules = ../src/tools/scripts;

          # Check for pre-built WASM file (avoids IFD)
          baseName = lib.removeSuffix ".hs" (baseNameOf pathStr);
          prebuiltWasm = ./packages + "/${baseName}.wasm";
          hasPrebuiltWasm = builtins.pathExists prebuiltWasm;

          # Generated Main.hs that wraps the user's package module
          wrapperMain = pkgs.writeText "Main.hs" ''
            {-# LANGUAGE ForeignFunctionInterface #-}
            module Main where

            import Straylight.Nix.Value (Value(..))
            import Straylight.Nix.Derivation (drvToNixAttrs)
            import Straylight.Nix (nixWasmInit)
            import qualified Pkg (pkg)

            main :: IO ()
            main = pure ()

            foreign export ccall "nix_wasm_init_v1" initPlugin :: IO ()
            initPlugin :: IO ()
            initPlugin = nixWasmInit

            foreign export ccall "pkg" pkgExport :: Value -> IO Value
            pkgExport :: Value -> IO Value
            pkgExport _args = drvToNixAttrs Pkg.pkg
          '';

          # Build single-file Haskell to WASM
          buildHsWasm =
            hsPath:
            let
              name = lib.removeSuffix ".hs" (baseNameOf (toString hsPath));
            in
            pkgs.runCommand "${name}.wasm"
              {
                src = hsPath;
                nativeBuildInputs = [ ghc-wasm ];
              }
              ''
                mkdir -p build
                cd build
                cp -r ${straylightModules}/Straylight Straylight
                chmod -R u+w Straylight
                cp $src Pkg.hs
                cp ${wrapperMain} Main.hs
                wasm32-wasi-ghc \
                  -optl-mexec-model=reactor \
                  -optl-Wl,--allow-undefined \
                  -optl-Wl,--export=hs_init \
                  -optl-Wl,--export=nix_wasm_init_v1 \
                  -optl-Wl,--export=pkg \
                  -O2 \
                  Main.hs \
                  -o plugin.wasm
                wasm-opt -O3 plugin.wasm -o $out
              '';

          # Build single-file PureScript to WASM
          # Uses pure-sarcasm (Wasm-GC backend) if available, otherwise provides helpful error.
          # NOTE: pure-sarcasm is experimental and targets Wasm-GC (not standard WASM).
          buildPursWasm =
            pursPath:
            let
              name = lib.removeSuffix ".purs" (baseNameOf (toString pursPath));
              # Check if pure-sarcasm is available (experimental Wasm-GC backend)
              # This is a community project: https://github.com/ajnsit/pure-sarcasm
              pureSarcasm = pkgs.pure-sarcasm or null;
            in
            if pureSarcasm == null then
              throw ''
                ════════════════════════════════════════════════════════════════════════════════
                PureScript WASM Backend Not Available
                ════════════════════════════════════════════════════════════════════════════════

                PureScript WASM compilation requires pure-sarcasm (Wasm-GC backend), which is
                not currently available in your nixpkgs.

                Current Status:
                  ✅ Infrastructure: Ready (buildPursWasm function exists)
                  ✅ Integration: Ready (call-package supports .purs files)
                  ❌ pure-sarcasm: Not available in nixpkgs

                Available Options:
                  1. Use Haskell (.hs) files instead (same type system, same API)
                  2. Add pure-sarcasm to nixpkgs overlay (experimental Wasm-GC backend)
                  3. Wait for official PureScript WASM support

                PureScript WASM Backends:
                  - pure-sarcasm: Experimental Wasm-GC backend (https://github.com/ajnsit/pure-sarcasm)
                  - Official: Not yet available (PureScript currently targets JavaScript)

                Example (using Haskell instead):
                  # Instead of: call-package ./my-package.purs {}
                  # Use:        call-package ./my-package.hs {}

                The Haskell and PureScript APIs are identical - just change the file extension.

                ════════════════════════════════════════════════════════════════════════════════
              ''
            else
              let
                # PureScript wrapper module (equivalent to Main.hs for Haskell)
                # PureScript functions are exported by default when compiled to WASM
                wrapperMain = pkgs.writeText "Main.purs" ''
                  module Main where

                  import Pkg (pkg)
                  import Straylight.Nix.Derivation (drvToNixAttrs)
                  import Straylight.Nix (nixWasmInit)

                  -- Initialize the WASM plugin
                  -- Exported as "nix_wasm_init_v1" by the WASM backend
                  initPlugin :: Effect Unit
                  initPlugin = nixWasmInit

                  -- Export the package specification
                  -- Exported as "pkg" by the WASM backend
                  pkgExport :: Value -> Effect Value
                  pkgExport _args = drvToNixAttrs pkg
                '';

                # Straylight.Nix PureScript modules path
                straylightPursModules = ../src/purescript;
              in
              pkgs.runCommand "${name}.wasm"
                {
                  src = pursPath;
                  nativeBuildInputs = [ pureSarcasm pkgs.purescript ];
                }
                ''
                  set -euo pipefail
                  
                  mkdir -p build
                  cd build
                  
                  # Copy Straylight.Nix PureScript modules
                  if [ -d "${straylightPursModules}" ]; then
                    cp -r ${straylightPursModules}/Straylight Straylight
                    chmod -R u+w Straylight
                  fi
                  
                  # Copy user's package as Pkg.purs, wrapper as Main.purs
                  cp $src Pkg.purs
                  cp ${wrapperMain} Main.purs
                  
                  # Compile PureScript to Wasm-GC using pure-sarcasm
                  # NOTE: pure-sarcasm is experimental and may have different CLI
                  # This implementation attempts compilation and handles errors gracefully
                  
                  # Check if purs-sarcasm is available
                  if ! command -v purs-sarcasm >/dev/null 2>&1; then
                    echo "pure-sarcasm compiler not found in PATH"
                    echo ""
                    echo "To enable PureScript WASM support:"
                    echo "  1. Add pure-sarcasm overlay to your flake"
                    echo "  2. Import straylight.modules.flake.default (includes pure-sarcasm overlay)"
                    echo ""
                    echo "For now, use Haskell (.hs) files instead - same API, fully working."
                    exit 1
                  fi
                  
                  # Compile PureScript to Wasm-GC
                  # pure-sarcasm CLI may vary - try common patterns
                  echo "Compiling PureScript to WASM using pure-sarcasm..."
                  
                  # Try compilation with pure-sarcasm
                  # The exact command depends on pure-sarcasm's actual API
                  # Common patterns: purs-sarcasm compile, purs compile --backend wasm-gc, etc.
                  if purs-sarcasm compile --output-dir output Main.purs Pkg.purs 2>&1; then
                    # Success - find the output WASM file
                    if [ -f "output/Main.wasm" ]; then
                      cp output/Main.wasm $out
                    elif [ -f "output/main.wasm" ]; then
                      cp output/main.wasm $out
                    elif [ -f "output/index.wasm" ]; then
                      cp output/index.wasm $out
                    else
                      echo "pure-sarcasm compilation succeeded but no WASM output found"
                      echo "Searched for: output/Main.wasm, output/main.wasm, output/index.wasm"
                      echo "Output directory contents:"
                      ls -la output/ || true
                      exit 1
                    fi
                  else
                    echo "PureScript WASM compilation failed"
                    echo ""
                    echo "This may be due to:"
                    echo "  1. Missing Straylight.Nix PureScript bindings"
                    echo "  2. PureScript FFI syntax differences"
                    echo "  3. pure-sarcasm CLI changes"
                    echo ""
                    echo "Current status:"
                    echo "  ✅ Infrastructure: Ready"
                    echo "  ✅ pure-sarcasm: Available"
                    echo "  ⚠️  PureScript bindings: Need implementation"
                    echo ""
                    echo "Workaround: Use Haskell (.hs) files instead - same API, fully working."
                    echo "See: https://github.com/ajnsit/pure-sarcasm"
                    exit 1
                  fi
                '';
        in
        # Check if language backend is enabled (if config is available)
        # Default to enabled if config is not available (backward compatibility)
        let
          buildConfig = config.straylight.build.config or null;
          haskellEnabled = buildConfig == null || buildConfig.haskell.enable;
          purescriptEnabled = buildConfig == null || buildConfig.purescript.enable;
          nixEnabled = buildConfig == null || buildConfig.nix.enable;
        in
        if ext == "hs" then
          if !haskellEnabled then
            throw "call-package: Haskell backend (.hs files) is disabled. Enable it with: straylight.build.languages.haskell.enable = true;"
          else if !(builtins ? wasm) then
            throw "call-package for .hs files requires straylight-nix with builtins.wasm"
          # Use pre-built WASM if available (no IFD)
          else if hasPrebuiltWasm then
            wasm-infra.buildFromSpec {
              spec = builtins.wasm prebuiltWasm "pkg" args;
              inherit pkgs;
            }
          # Fall back to building at eval time (causes IFD warning)
          else if ghc-wasm == null then
            throw "call-package for .hs files requires ghc-wasm-meta input (or pre-built ${baseName}.wasm)"
          else
            let
              wasmDrv = buildHsWasm path;
              spec = builtins.wasm wasmDrv "pkg" args;
            in
            wasm-infra.buildFromSpec { inherit spec pkgs; }
        else if ext == "purs" then
          if !purescriptEnabled then
            throw "call-package: PureScript backend (.purs files) is disabled. Enable it with: straylight.build.languages.purescript.enable = true;"
          else if !(builtins ? wasm) then
            throw "call-package for .purs files requires straylight-nix with builtins.wasm"
          else
            let
              # Build PureScript to WASM
              # NOTE: This will fail until PureScript WASM backend is available
              wasmDrv = buildPursWasm path;
              spec = builtins.wasm wasmDrv "pkg" args;
            in
            wasm-infra.buildFromSpec { inherit spec pkgs; }
        else if ext == "wasm" then
          if !(builtins ? wasm) then
            throw "call-package for .wasm files requires straylight-nix"
          else
            wasm-infra.buildFromSpec {
              spec = builtins.wasm path "pkg" args;
              inherit pkgs;
            }
        else if ext == "nix" then
          if !nixEnabled then
            throw "call-package: Nix backend (.nix files) is disabled. Enable it with: straylight.build.languages.nix.enable = true;"
          else
            pkgs.callPackage path args
        else
          throw "call-package: unsupported extension .${ext} (expected .hs, .purs, .wasm, or .nix)";

      # ────────────────────────────────────────────────────────────────────────
      # // typed packages //
      # ────────────────────────────────────────────────────────────────────────
      # Packages defined in Haskell via call-package.
      # Only available when using straylight-nix (builtins.wasm).
      #
      # List of all .hs package files (used for both building and pre-building WASM)
      hsPackageFiles = [
        "test-hello"
        "test-zlib-ng"
        "test-tool-deps"
        "test-typed-tools"
        "catch2"
        "fmt"
        "mdspan"
        "nlohmann-json"
        "rapidjson"
        "spdlog"
        "zlib-ng"
        "nvidia-nccl"
        "nvidia-cudnn"
        "nvidia-tensorrt"
        "nvidia-cutensor"
        "nvidia-cusparselt"
        "nvidia-cutlass"
      ];

      # Build WASM from a single .hs file (for pre-building)
      buildHsWasmStandalone =
        name:
        let
          hsPath = ./packages + "/${name}.hs";
          wrapperMain = pkgs.writeText "Main.hs" ''
            {-# LANGUAGE ForeignFunctionInterface #-}
            module Main where

            import Straylight.Nix.Value (Value(..))
            import Straylight.Nix.Derivation (drvToNixAttrs)
            import Straylight.Nix (nixWasmInit)
            import qualified Pkg (pkg)

            main :: IO ()
            main = pure ()

            foreign export ccall "nix_wasm_init_v1" initPlugin :: IO ()
            initPlugin :: IO ()
            initPlugin = nixWasmInit

            foreign export ccall "pkg" pkgExport :: Value -> IO Value
            pkgExport :: Value -> IO Value
            pkgExport _args = drvToNixAttrs Pkg.pkg
          '';
        in
        pkgs.runCommand "${name}.wasm"
          {
            src = hsPath;
            nativeBuildInputs = [ ghc-wasm ];
          }
          ''
            mkdir -p build
            cd build
            cp -r ${../src/tools/scripts}/Straylight Straylight
            chmod -R u+w Straylight
            cp $src Pkg.hs
            cp ${wrapperMain} Main.hs
            wasm32-wasi-ghc \
              -optl-mexec-model=reactor \
              -optl-Wl,--allow-undefined \
              -optl-Wl,--export=hs_init \
              -optl-Wl,--export=nix_wasm_init_v1 \
              -optl-Wl,--export=pkg \
              -O2 \
              Main.hs \
              -o plugin.wasm
            wasm-opt -O3 plugin.wasm -o $out
          '';

      # All WASM files bundled together (for easy copying to repo)
      wasmPackagesBundle = lib.optionalAttrs (ghc-wasm != null) {
        wasm-packages = pkgs.runCommand "wasm-packages" { } ''
          mkdir -p $out
          ${lib.concatMapStringsSep "\n" (name: ''
            cp ${buildHsWasmStandalone name} $out/${name}.wasm
          '') hsPackageFiles}
        '';
      };

      typedPackages = lib.optionalAttrs (builtins ? wasm) (
        lib.listToAttrs (
          map (name: {
            inherit name;
            value = call-package (./packages + "/${name}.hs") { };
          }) hsPackageFiles
        )
      );

      # NativeLink from inputs (for LRE)
      nativelink =
        if inputs ? nativelink then
          inputs.nativelink.packages.${system}.default or inputs.nativelink.packages.${system}.nativelink
            or null
        else
          null;
    in
    {
      # Make straylight available to other modules via _module.args
      _module.args = {
        inherit straylight call-package;
      };

      # Wire up shortlist paths to buck2 config
      buck2.shortlist = {
        fmt = "${pkgs.fmt}";
        fmt_dev = "${pkgs.fmt.dev}";
        zlib_ng = "${pkgs.zlib-ng}";
        catch2 = "${pkgs.catch2_3}";
        catch2_dev = "${pkgs.catch2_3.dev or pkgs.catch2_3}";
        spdlog = "${pkgs.spdlog}";
        spdlog_dev = "${pkgs.spdlog.dev or pkgs.spdlog}";
        mdspan = "${pkgs.mdspan}";
        rapidjson = "${pkgs.rapidjson}";
        nlohmann_json = "${pkgs.nlohmann_json}";
        libsodium = "${pkgs.libsodium}";
        libsodium_dev = "${pkgs.libsodium.dev or pkgs.libsodium}";
      };

      packages = {
        mdspan = pkgs.mdspan or null;
        wsn-lint = pkgs.callPackage ./packages/wsn-lint.nix { };

        # Buck2 built packages - these can be used in NixOS, containers, etc.
        # fmt-test = config.buck2.build { target = "//examples/cxx:fmt_test"; };
      }
      // lib.optionalAttrs (system == "x86_64-linux" || system == "aarch64-linux") {
        llvm-git = pkgs.llvm-git or null;
        nvidia-sdk = pkgs.nvidia-sdk or null;
      }
      // lib.optionalAttrs (nativelink != null) {
        inherit nativelink;
      }
      // wasmPackagesBundle
      // typedPackages;

      checks = import ./checks/default.nix { inherit pkgs system lib; };

      # nix2gpu requires explicit empty default (upstream bug - no default in option)
      nix2gpu = { };
    };

  straylight-naught.devshell = {
    enable = true;
    nv.enable = true;
    straylight-nix.enable = true;
  };

  straylight-naught.nixpkgs.nv.enable = true;

  # Buck2 build system integration
  straylight-naught.build = {
    enable = true;
    prelude.enable = true;
    toolchain = {
      cxx.enable = true;
      nv.enable = true;
      haskell = {
        enable = true;
        # Core packages for Buck2 haskell_binary rules
        # Includes Straylight.Script dependencies for typed CLI tools
        packages =
          hp:
          builtins.filter (p: p != null) [
            # Core
            hp.text or null
            hp.bytestring or null
            hp.containers or null
            hp.directory or null
            hp.filepath or null
            hp.process or null
            hp.time or null

            # CLI / scripting
            hp.aeson or null
            hp.aeson-pretty or null
            hp.optparse-applicative or null
            hp.megaparsec or null
            hp.prettyprinter or null

            # Straylight.Script dependencies
            hp.shelly or null
            hp.foldl or null
            hp.dhall or null
            hp.crypton or null
            hp.memory or null
            hp.unordered-containers or null
            hp.vector or null
            hp.unix or null
            hp.async or null
            hp.transformers or null
            hp.mtl or null
          ];
      };
      rust.enable = true;
      lean.enable = true;
      python.enable = true;
    };
  };

  straylight-naught.docs = {
    enable = true;
    title = "Weyl Standard Nix";
    description = "A specification for reproducible, composable infrastructure on Nix";
    theme = "ono-sendai";

    # Document all straylight-naught modules
    modules = [ flakeModules.options-only ];
  };
}
