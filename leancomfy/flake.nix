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
          ...
        }:
        let
          # The lean4 flake's Nix build is deprecated but still works
          # Use lean-all which includes both lean and lake
          lean4Pkg = inputs.lean4.packages.${system}.deprecated;

          # =================================================================
          # LEAN CORE - builds the prover and extractor
          # =================================================================
          tensorCoreLean = pkgs.stdenv.mkDerivation {
            pname = "tensor-core-lean";
            version = "0.1.0";
            src = ./lean;

            nativeBuildInputs = [
              lean4Pkg.lean-all
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
          };

          # =================================================================
          # EXTRACTION - runs Lean to emit verified Elm/Python/C
          # This is a PURE derivation - deterministic, cacheable, read-only
          # =================================================================
          extractedTypes = pkgs.stdenv.mkDerivation {
            pname = "tensor-core-extracted";
            version = "0.1.0";
            src = ./lean;

            nativeBuildInputs = [
              lean4Pkg.lean-all
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

            # This is the key: the output is content-addressed and immutable
            # Once built, it's read-only forever
          };

          # =================================================================
          # PYTHON - uses extracted types as READ-ONLY input
          # =================================================================
          python = pkgs.python311.withPackages (
            ps: with ps; [
              nanobind
              numpy
              pytest
            ]
          );

          # Python with nanobind for building
          pythonWithNanobind = pkgs.python311.withPackages (ps: [ ps.nanobind ]);

          tensorCorePython = pkgs.stdenv.mkDerivation {
            pname = "tensor-core-python";
            version = "0.1.0";

            # Use the whole repo as source so we have access to both python/ and c/
            src = ./.;

            nativeBuildInputs = with pkgs; [
              cmake
              ninja
              pythonWithNanobind
            ];

            buildInputs = [
              extractedTypes
              pkgs.python311Packages.nanobind
            ];

            # Disable default cmake configure phase
            dontConfigure = true;

            buildPhase = ''
              # Copy extracted types
              cp ${extractedTypes}/python/types.py python/tensor_core_types.py

              # Copy extracted C header (add to existing include dir)
              cp ${extractedTypes}/c/tensor_core_types.h c/include/

              cd python
              cmake -B build -G Ninja \
                -DCMAKE_BUILD_TYPE=Release \
                -DPython_EXECUTABLE=${pythonWithNanobind}/bin/python3 \
                -DC_SRC_DIR=$PWD/../c
              cmake --build build
              cd ..
            '';

            installPhase = ''
              mkdir -p $out/${pythonWithNanobind.sitePackages}
              find . -name "*.so" -exec cp {} $out/${pythonWithNanobind.sitePackages}/ \;
              cp python/tensor_core_types.py $out/${pythonWithNanobind.sitePackages}/
            '';
          };

          # =================================================================
          # ELM - uses extracted types as READ-ONLY input
          # NOTE: Elm build requires network access for dependencies.
          # For CI/production, use elm2nix to pre-fetch deps.
          # This derivation is a placeholder that copies static assets.
          # Use `make elm` in dev shell for actual Elm compilation.
          # =================================================================
          tensorCoreElm = pkgs.stdenv.mkDerivation {
            pname = "tensor-core-elm";
            version = "0.1.0";
            src = ./elm;

            nativeBuildInputs = [ ];

            buildInputs = [ extractedTypes ];

            # Skip Elm compilation in Nix (needs network for deps)
            # Instead, just package the source and extracted types
            buildPhase = ''
              mkdir -p src/TensorCore
              cp ${extractedTypes}/elm/TensorCore/Types.elm src/TensorCore/
            '';

            installPhase = ''
              mkdir -p $out/src/TensorCore
              cp -r src/* $out/src/
              cp index.html $out/
              cp elm.json $out/

              # Create a helper script to build Elm (run in dev shell)
              mkdir -p $out/bin
              cat > $out/bin/build-elm.sh << 'EOF'
              #!/usr/bin/env bash
              # Run this script in the nix develop shell to build Elm
              set -e
              cd "$(dirname "$0")/.."
              elm make src/Main.elm --optimize --output=elm.js
              echo "Built elm.js"
              EOF
              chmod +x $out/bin/build-elm.sh
            '';
          };

        in
        {
          # =================================================================
          # PACKAGES - each is a pure, cacheable derivation
          # =================================================================
          packages = {
            default = extractedTypes; # Changed: extracted types are the main output
            lean = tensorCoreLean;
            extracted = extractedTypes; # The verified types
            python = tensorCorePython;
            elm = tensorCoreElm; # Source + extracted types (build in dev shell)
          };

          # =================================================================
          # DEV SHELL
          # =================================================================
          devShells.default = pkgs.mkShell {
            packages = [
              lean4Pkg.lean-all
              python
              pkgs.cmake
              pkgs.ninja
              pkgs.elmPackages.elm
              pkgs.elmPackages.elm-format
              pkgs.nodejs
              pkgs.gnumake
            ];

            # Mount extracted types read-only in the shell
            EXTRACTED_TYPES = extractedTypes;

            shellHook = ''
              echo ""
              echo "╔══════════════════════════════════════════════════════════╗"
              echo "║  typed-comfy: Bulletproof Types                          ║"
              echo "║  Everything from Lean proofs. Extracted types immutable. ║"
              echo "╚══════════════════════════════════════════════════════════╝"
              echo ""
              echo "Extracted types (READ-ONLY):"
              echo "  \$EXTRACTED_TYPES/elm/TensorCore/Types.elm"
              echo "  \$EXTRACTED_TYPES/python/types.py"
              echo "  \$EXTRACTED_TYPES/c/tensor_core_types.h"
              echo ""
              echo "Commands:"
              echo "  nix build .#extracted   # Build verified types"
              echo "  nix build .#elm         # Package Elm source"
              echo "  nix build .#python      # Build Python bindings"
              echo "  make extract            # Re-extract (dev mode)"
              echo "  make elm                # Build Elm app (dev mode)"
              echo "  make serve              # Run scene editor"
              echo ""
              echo "The extracted types are content-addressed and immutable."
              echo "Droids can't modify them - they're in the Nix store."
              echo ""
            '';
          };
        };
    };
}
