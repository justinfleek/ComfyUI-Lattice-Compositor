{
  description = "Hydrogen - PureScript/Halogen web framework with Lean4 proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    purescript-overlay.url = "github:thomashoneyman/purescript-overlay";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      purescript-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ purescript-overlay.overlays.default ];
        };

        # Common build inputs
        buildInputs = [
          pkgs.nodejs_22
          pkgs.purs
          pkgs.spago-unstable
          pkgs.esbuild
          pkgs.elan
        ];

      in
      {
        # Development shell
        devShells.default = pkgs.mkShell {
          inherit buildInputs;

          shellHook = ''
            echo ""
            echo "  HYDROGEN // dev shell"
            echo ""
            echo "  PureScript: $(purs --version)"
            echo "  Lean4: via elan (see lean-toolchain)"
            echo ""
          '';
        };

        # Runnable apps
        apps = {
          # Run test suite
          test = {
            type = "app";
            program = toString (
              pkgs.writeShellScript "hydrogen-test" ''
                export PATH="${pkgs.lib.makeBinPath buildInputs}:$PATH"
                # Must run from project directory with write access
                if [ ! -f "spago.yaml" ] || [ ! -d "src/Hydrogen" ]; then
                  echo "Error: Run this from the hydrogen project directory"
                  exit 1
                fi
                echo ""
                echo "  HYDROGEN // test suite"
                echo ""
                spago test
              ''
            );
          };

          # Build and check
          build = {
            type = "app";
            program = toString (
              pkgs.writeShellScript "hydrogen-build" ''
                export PATH="${pkgs.lib.makeBinPath buildInputs}:$PATH"
                # Must run from project directory with write access
                if [ ! -f "spago.yaml" ] || [ ! -d "src/Hydrogen" ]; then
                  echo "Error: Run this from the hydrogen project directory"
                  exit 1
                fi
                echo ""
                echo "  HYDROGEN // build"
                echo ""
                spago build
              ''
            );
          };

          # Show project status
          status = {
            type = "app";
            program = toString (
              pkgs.writeShellScript "hydrogen-status" ''
                export PATH="${pkgs.lib.makeBinPath buildInputs}:$PATH"
                # Use current directory if it looks like hydrogen, otherwise use flake source
                if [ -f "spago.yaml" ] && [ -d "src/Hydrogen" ]; then
                  PROJECT_DIR="$PWD"
                else
                  PROJECT_DIR="${self}"
                fi
                cd "$PROJECT_DIR"
                echo ""
                  echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
                  echo "                              HYDROGEN // status"
                  echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
                  echo ""
                  echo "  The purest web design language ever created."
                  echo "  UI as data, not framework-specific code."
                  echo ""
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo "  Schema Pillars"
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo ""

                  # Count files per pillar
                  for pillar in Color Dimension Geometry Typography Material Elevation Temporal Reactive Gestural Haptic Audio Spatial Brand Attestation Scheduling Sensation Epistemic Accessibility; do
                    dir="src/Hydrogen/Schema/$pillar"
                    if [ -d "$dir" ]; then
                      count=$(find "$dir" -name "*.purs" | wc -l)
                      printf "    %-15s %3d files\n" "$pillar" "$count"
                    fi
                  done

                  echo ""
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo "  GPU Pipeline"
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo ""

                  for module in ComputeKernel Diffusion DrawCommand RenderEffect FrameState; do
                    file="src/Hydrogen/GPU/$module.purs"
                    if [ -f "$file" ]; then
                      lines=$(wc -l < "$file")
                      printf "    %-20s %4d lines\n" "$module.purs" "$lines"
                    fi
                  done

                  # Kernel directory
                  kernel_count=$(find src/Hydrogen/GPU/Kernel -name "*.purs" 2>/dev/null | wc -l)
                  echo "    Kernel/              $kernel_count files"

                  echo ""
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo "  Distributed Systems"
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo ""

                  for file in src/Hydrogen/Distributed/*.purs; do
                    if [ -f "$file" ]; then
                      name=$(basename "$file")
                      lines=$(wc -l < "$file")
                      printf "    %-25s %4d lines\n" "$name" "$lines"
                    fi
                  done

                  echo ""
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo "  Totals"
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo ""

                  purs_count=$(find src -name "*.purs" | wc -l)
                  test_count=$(find test -name "*.purs" | wc -l)
                  lean_count=$(find proofs -name "*.lean" 2>/dev/null | wc -l)

                  echo "    PureScript (src):    $purs_count files"
                  echo "    PureScript (test):   $test_count files"
                  echo "    Lean4 (proofs):      $lean_count files"
                  echo ""
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo "  Commands"
                  echo "  ─────────────────────────────────────────────────────────────"
                  echo ""
                  echo "    nix run .#build   — Build PureScript"
                  echo "    nix run .#test    — Run test suite"
                  echo "    nix run .#status  — Show this status"
                  echo "    nix develop       — Enter dev shell"
                  echo ""
                  echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
                  echo ""
              ''
            );
          };

          # Default app is status
          default = self.apps.${system}.status;
        };
      }
    );
}
