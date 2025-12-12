{
  description = "Weyl Motion Graphics Compositor for ComfyUI";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        # Base Python WITHOUT torch - we'll pip install the ML stack
        pythonBase = pkgs.python311.withPackages (ps: with ps; [
          pip
          virtualenv
          numpy
          pillow
          aiohttp
          websockets
        ]);

      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pythonBase
            pkgs.nodejs_20
            pkgs.nodePackages.npm
            
            # Build tools for pip packages that need compilation
            pkgs.gcc
            pkgs.stdenv.cc.cc.lib
            pkgs.zlib
            pkgs.libGL
            pkgs.glib
          ];

          # Make sure CUDA libs are findable if present
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
            pkgs.stdenv.cc.cc.lib
            pkgs.zlib
            pkgs.libGL
            pkgs.glib
          ];

          shellHook = ''
            echo "═══════════════════════════════════════════════════════"
            echo "  Weyl Compositor Dev Environment"
            echo "═══════════════════════════════════════════════════════"
            echo ""
            echo "Node: $(node --version)"
            echo "Python: $(python --version)"
            echo ""
            echo "SETUP (first time only):"
            echo "  1. cd ui && npm install"
            echo "  2. python -m venv .venv"
            echo "  3. source .venv/bin/activate"
            echo "  4. pip install torch torchvision --index-url https://download.pytorch.org/whl/cu124"
            echo "  5. pip install opencv-python aiohttp"
            echo ""
            echo "RUN:"
            echo "  Frontend: cd ui && npm run dev"
            echo "  Backend:  source .venv/bin/activate && python -m comfyui"
            echo "═══════════════════════════════════════════════════════"
          '';
        };
      }
    );
}
