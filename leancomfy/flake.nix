{
  description = "Bulletproof types - everything from Lean proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4.url = "github:leanprover/lean4/v4.15.0";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];

      perSystem =
        {
          config,
          self',
          inputs',
          pkgs,
          system,
          lib,
          ...
        }:
        let
          # The lean4 flake's Nix build is deprecated but still works
          # Use lean-all which includes both lean and lake
          lean4-pkg = inputs.lean4.packages.${system}.deprecated;

          # Build script for Elm (replaces heredoc)
          build-elm-script = pkgs.writeShellScript "build-elm" ''
            set -e
            cd "$(dirname "$0")/.."
            elm make src/Main.elm --optimize --output=elm.js
            echo "Built elm.js"
          '';

          # =================================================================
          # LEAN CORE - builds the prover and extractor
          # =================================================================
          tensor-core-lean = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-lean";
            version = "0.1.0";
            src = ./lean;

            nativeBuildInputs = [
              lean4-pkg.lean-all
            ];

            buildPhase = ''
              export HOME=$(mktemp -d)
              lake build
            '';

            installPhase = ''
              mkdir -p $out/bin $out/lib
              cp .lake/build/bin/* $out/bin/ || true
              cp -r .lake/build/lib/* $out/lib/ || true
            '';

            meta = {
              description = "Lean4 tensor core with formal proofs";
              license = lib.licenses.mit;
              platforms = lib.platforms.all;
              mainProgram = "tensor-core";
            };
          });

          # =================================================================
          # EXTRACTION - runs Lean to emit verified Elm/Python/C
          # This is a PURE derivation - deterministic, cacheable, read-only
          # =================================================================
          extracted-types = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-extracted";
            version = "0.1.0";
            src = ./lean;

            nativeBuildInputs = [
              lean4-pkg.lean-all
            ];

            buildPhase = ''
              export HOME=$(mktemp -d)
              lake build extract
              lake exe extract all
            '';

            installPhase = ''
              mkdir -p $out/elm $out/python $out/c
              cp -r extracted/elm/* $out/elm/ || true
              cp -r extracted/python/* $out/python/ || true
              cp -r extracted/c/* $out/c/ || true
            '';

            meta = {
              description = "Extracted types from Lean4 proofs";
              license = lib.licenses.mit;
              platforms = lib.platforms.all;
              # No executables - data package
            };
          });

          # =================================================================
          # PYTHON - uses extracted types as READ-ONLY input
          # Uses meson instead of cmake (cmake is banned per STRAYLIGHT-003)
          # =================================================================
          python-env = pkgs.python311.withPackages (
            ps: with ps; [
              nanobind
              numpy
              pytest
            ]
          );

          python-with-nanobind = pkgs.python311.withPackages (ps: [ ps.nanobind ]);

          tensor-core-python = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-python";
            version = "0.1.0";

            # Use the whole repo as source so we have access to both python/ and c/
            src = ./.;

            nativeBuildInputs = [
              pkgs.meson
              pkgs.ninja
              pkgs.pkg-config
              python-with-nanobind
            ];

            buildInputs = [
              extracted-types
              pkgs.python311Packages.nanobind
            ];

            # Meson build configuration
            mesonFlags = [
              "-Dpython_bindings=true"
            ];

            preConfigure = ''
              # Copy extracted types
              cp ${extracted-types}/python/types.py python/tensor_core_types.py || true

              # Copy extracted C header (add to existing include dir)
              cp ${extracted-types}/c/tensor_core_types.h c/include/ || true
            '';

            installPhase = ''
              mkdir -p $out/${python-with-nanobind.sitePackages}
              find . -name "*.so" -exec cp {} $out/${python-with-nanobind.sitePackages}/ \; || true
              cp python/tensor_core_types.py $out/${python-with-nanobind.sitePackages}/ || true
            '';

            meta = {
              description = "Python bindings for tensor core with verified types";
              license = lib.licenses.mit;
              platforms = lib.platforms.all;
            };
          });

          # =================================================================
          # ELM - uses extracted types as READ-ONLY input
          # NOTE: Elm build requires network access for dependencies.
          # For CI/production, use elm2nix to pre-fetch deps.
          # This derivation packages source + extracted types.
          # Use `make elm` in dev shell for actual Elm compilation.
          # =================================================================
          tensor-core-elm = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-elm";
            version = "0.1.0";
            src = ./elm;

            nativeBuildInputs = [ ];

            buildInputs = [ extracted-types ];

            # Skip Elm compilation in Nix (needs network for deps)
            # Instead, just package the source and extracted types
            buildPhase = ''
              mkdir -p src/TensorCore
              cp ${extracted-types}/elm/TensorCore/Types.elm src/TensorCore/ || true
            '';

            installPhase = ''
              mkdir -p $out/src/TensorCore $out/bin
              cp -r src/* $out/src/
              cp index.html $out/
              cp elm.json $out/
              cp ${build-elm-script} $out/bin/build-elm.sh
            '';

            meta = {
              description = "Elm frontend with verified tensor types";
              license = lib.licenses.mit;
              platforms = lib.platforms.all;
              mainProgram = "build-elm.sh";
            };
          });

        in
        {
          # =================================================================
          # PACKAGES - each is a pure, cacheable derivation
          # =================================================================
          packages = {
            default = extracted-types;
            lean = tensor-core-lean;
            extracted = extracted-types;
            python = tensor-core-python;
            elm = tensor-core-elm;
          };

          # =================================================================
          # DEV SHELL
          # =================================================================
          devShells.default = pkgs.mkShell {
            packages = [
              lean4-pkg.lean-all
              python-env
              pkgs.meson
              pkgs.ninja
              pkgs.pkg-config
              pkgs.elmPackages.elm
              pkgs.elmPackages.elm-format
              pkgs.nodejs
              pkgs.gnumake
            ];

            # Mount extracted types read-only in the shell
            EXTRACTED_TYPES = extracted-types;

            shellHook = ''
              echo ""
              echo "typed-comfy: Bulletproof Types"
              echo "Everything from Lean proofs. Extracted types immutable."
              echo ""
              echo "Extracted types (READ-ONLY):"
              echo "  $EXTRACTED_TYPES/elm/TensorCore/Types.elm"
              echo "  $EXTRACTED_TYPES/python/types.py"
              echo "  $EXTRACTED_TYPES/c/tensor_core_types.h"
              echo ""
              echo "Commands:"
              echo "  nix build .#extracted   # Build verified types"
              echo "  nix build .#elm         # Package Elm source"
              echo "  nix build .#python      # Build Python bindings"
              echo "  make extract            # Re-extract (dev mode)"
              echo "  make elm                # Build Elm app (dev mode)"
              echo "  make serve              # Run scene editor"
              echo ""
            '';
          };
        };
    };
}
