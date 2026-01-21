{ inputs, ... }:
{
  # Expose overlays via flake-parts
  flake.overlays.default = import ./overlays/default.nix;

  # Configure nixpkgs with CUDA support
  perSystem =
    {
      system,
      ...
    }:
    let
      # Import nixpkgs with CUDA support enabled
      pkgs = import inputs.nixpkgs {
        inherit system;
        config = {
          allowUnfree = true;
          cudaSupport = true;
        };
      };
      
      # Python environment with packages available in nixpkgs
      pythonEnv = pkgs.python3.withPackages (ps: with ps; [
        pytest
        pytest-cov
        pytest-asyncio
        aiohttp
        torch  # PyTorch with CUDA support (when cudaSupport = true)
        torchvision
        torchaudio
        # Core scientific computing
        numpy
        pillow
        scipy
        sympy
        # Web frameworks
        fastapi
        starlette
        # Utilities
        click
        pyyaml
        requests
        httpx
        # Testing
        hypothesis
        coverage
        # Code quality
        ruff
        # Git
        gitpython
        # Other common packages
        pydantic
        python-dateutil
        python-dotenv
        tqdm
        rich
        # Audio/video
        soundfile
        sounddevice
        # OpenCV (python3Packages.opencv4)
        opencv4
        # Additional packages
        beautifulsoup4
        lxml
        # Network/async
        anyio
        # ML/AI
        transformers
        huggingface-hub
        # Monitoring
        psutil
        # Build tools
        setuptools
        pip
        wheel
        # Note: 'build' package might conflict, install via pip if needed
      ]);
    in
    {
      # Dev shell: Python + uv, Bun with comprehensive package set
      # Note: CUDA support enabled via flake.nix nixpkgs.config
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [
          pythonEnv
          uv
          bun
          git
          # System tools
          which
          curl
          wget
        ];

        # Install remaining packages via uv (faster than pip)
        shellHook = ''
          echo "🐍 Python environment ready"
          
          # Fix terminal size for WSL/Playwright (prevents "bogus screen size" warnings)
          if [ -z "$COLUMNS" ] || [ "$COLUMNS" -gt 1000 ] || [ "$COLUMNS" -lt 10 ]; then
            export COLUMNS=120
          fi
          if [ -z "$LINES" ] || [ "$LINES" -lt 2 ] || [ "$LINES" -gt 1000 ]; then
            export LINES=30
          fi
          # Set stty if available (for proper terminal size detection)
          if command -v stty >/dev/null 2>&1; then
            stty cols $COLUMNS rows $LINES 2>/dev/null || true
          fi
          
          # Set up Python path to include user site-packages
          export PYTHONUSERBASE="$HOME/.local"
          export PATH="$PYTHONUSERBASE/bin:$PATH"
          
          # Get the project root (handle WSL paths)
          PROJECT_ROOT="$(pwd)"
          if [[ "$PROJECT_ROOT" == /mnt/* ]]; then
            # We're in WSL, ensure we're in the right directory
            echo "📍 WSL environment detected"
          fi
          
          # Check if packages need to be installed
          INSTALL_MARKER="$HOME/.local/.lattice-packages-installed"
          REQ_FILE="$PROJECT_ROOT/requirements-dev.txt"
          
          if [ ! -f "$INSTALL_MARKER" ] || [ "$REQ_FILE" -nt "$INSTALL_MARKER" ]; then
            echo "📦 Installing packages via uv..."
            
            # Use uv to install packages (faster and more reliable)
            if [ -f "$REQ_FILE" ]; then
              echo "   Found requirements-dev.txt at: $REQ_FILE"
              uv pip install --user -r "$REQ_FILE" || {
                echo "⚠️  Some packages failed to install via uv, trying pip..."
                ${pythonEnv}/bin/pip install --user -r "$REQ_FILE" || echo "⚠️  Some packages may have failed to install"
              }
              touch "$INSTALL_MARKER"
              echo "✅ Packages installed!"
            else
              echo "⚠️  requirements-dev.txt not found at: $REQ_FILE"
              echo "   Current directory: $(pwd)"
              echo "   Skipping package installation"
            fi
          else
            echo "✅ Packages already installed (use 'rm ~/.local/.lattice-packages-installed' to reinstall)"
          fi
          
          echo "💡 Tip: Packages are installed in ~/.local (user site-packages)"
          
          # Check for local ComfyUI setup
          if [ -d "$PROJECT_ROOT/ComfyUI" ]; then
            echo ""
            echo "✅ Local ComfyUI detected"
            echo "   Start with: bash scripts/start-comfyui-test.sh"
          else
            echo ""
            echo "💡 Tip: Set up ComfyUI locally for E2E testing:"
            echo "   bash scripts/setup-comfyui-local.sh"
          fi
          
          echo "🚀 Dev shell ready!"
        '';
      };

      # UI package built with bun2nix v2
      # bun2nix v2: use packages.${system}.default instead of lib
      packages.ui = pkgs.callPackage ./packages/ui.nix {
        bun2nix = inputs.bun2nix.packages.${system}.default;
        inherit (pkgs) bun;
        inherit (pkgs) nodejs_20;
      };

      # treefmt: always on (nixfmt, statix, deadnix, ruff)
      # Note: biome disabled in treefmt due to treefmt-nix validation issue
      # that strips out our "off" linting settings. Use biome directly for formatting.
      treefmt = {
        projectRootFile = "flake.nix";
        programs = {
          nixfmt.enable = true;
          statix.enable = true;
          deadnix.enable = true;
          ruff.enable = true;
        };
      };
    };
}
