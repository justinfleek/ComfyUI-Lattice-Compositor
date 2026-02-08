{
  description = "Bulletproof types - everything from Lean proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
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
          # Use elan to manage Lean toolchain - it handles version matching
          elan = pkgs.elan;

          # Build script for Elm (replaces heredoc)
          build-elm-script = pkgs.writeShellScript "build-elm" ''
            set -e
            cd "$(dirname "$0")/.."
            elm make src/Main.elm --optimize --output=elm.js
            echo "Built elm.js"
          '';

          # =================================================================
          # LAKE DEPENDENCIES - Fixed-Output Derivation with network access
          # This fetches mathlib, scilean, batteries from GitHub
          # Run `nix build .#lake-deps` first to get the correct hash
          # =================================================================
          lean-src = lib.cleanSourceWith {
            src = ./lean;
            filter = path: type:
              # Exclude patched-deps (now fetched from git) and .lake cache
              !(lib.hasInfix "patched-deps" path) && !(lib.hasInfix ".lake" path);
          };

          lake-deps = pkgs.stdenvNoCC.mkDerivation {
            name = "tensor-core-lake-deps";
            src = lean-src;

            nativeBuildInputs = [
              elan
              pkgs.git
              pkgs.cacert
              pkgs.curl
            ];

            # Fixed-output derivation - allows network access
            outputHashAlgo = "sha256";
            outputHashMode = "recursive";
            # To get this hash: run `nix build .#lake-deps` with lib.fakeHash,
            # then copy the "got:" hash from the error message
            outputHash = "sha256-1OCk7b5ft5IxAa68kKKoRe80Q3g6SypbbGJBbgVu0+4=";

            buildPhase = ''
              export HOME=$TMPDIR
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export GIT_SSL_CAINFO=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export ELAN_HOME=$TMPDIR/.elan
              export PATH=$ELAN_HOME/bin:$PATH

              # Configure git for HTTPS
              git config --global http.sslCAInfo $SSL_CERT_FILE

              # Let elan install the correct toolchain from lean-toolchain file
              elan default leanprover/lean4:v4.26.0

              # Fetch all Lake dependencies
              lake update

              # Build dependencies (but not our code) to populate .lake/build
              lake build Batteries Qq Aesop || true
            '';

            installPhase = ''
              mkdir -p $out
              cp -r .lake/* $out/
              cp lake-manifest.json $out/ || true
            '';
          };

          # =================================================================
          # LEAN CORE - builds the prover and extractor
          # Uses pre-fetched dependencies from lake-deps
          # =================================================================
          tensor-core-lean = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-lean";
            version = "0.1.0";
            src = lean-src;

            nativeBuildInputs = [
              elan
              pkgs.git
              pkgs.cacert
            ];

            buildPhase = ''
              export HOME=$(mktemp -d)
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export ELAN_HOME=$HOME/.elan
              export PATH=$ELAN_HOME/bin:$PATH

              # Install the correct toolchain
              elan default leanprover/lean4:v4.26.0

              # Use pre-fetched dependencies
              mkdir -p .lake
              cp -r ${lake-deps}/* .lake/
              chmod -R u+w .lake

              # Build with cached deps (no network needed)
              lake build --no-build-deps
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
          # Uses pre-fetched dependencies from lake-deps
          # =================================================================
          extracted-types = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "tensor-core-extracted";
            version = "0.1.0";
            src = lean-src;

            nativeBuildInputs = [
              elan
              pkgs.git
              pkgs.cacert
            ];

            buildPhase = ''
              export HOME=$(mktemp -d)
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export ELAN_HOME=$HOME/.elan
              export PATH=$ELAN_HOME/bin:$PATH

              # Install the correct toolchain
              elan default leanprover/lean4:v4.26.0

              # Use pre-fetched dependencies
              mkdir -p .lake
              cp -r ${lake-deps}/* .lake/
              chmod -R u+w .lake

              # Build extraction tool with cached deps
              lake build extract --no-build-deps
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
            lake-deps = lake-deps;
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
              elan
              pkgs.git
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
