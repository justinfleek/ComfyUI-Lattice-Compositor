#!/bin/bash
# Setup ComfyUI locally for testing and E2E tests
# This installs ComfyUI in the repo (gitignored) for development/testing

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

echo "=========================================="
echo "Setting up ComfyUI for Local Testing"
echo "=========================================="
echo ""

# Check if ComfyUI already exists
if [ -d "$COMFYUI_DIR" ]; then
    echo "✅ ComfyUI already exists at: $COMFYUI_DIR"
    echo ""
    read -p "Reinstall? (y/N): " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Skipping installation."
        exit 0
    fi
    echo "Removing existing ComfyUI..."
    rm -rf "$COMFYUI_DIR"
fi

# Clone ComfyUI
echo "Cloning ComfyUI..."
git clone https://github.com/comfyanonymous/ComfyUI.git "$COMFYUI_DIR"

cd "$COMFYUI_DIR"

# Install ComfyUI dependencies
echo ""
echo "Installing ComfyUI dependencies..."

# Check if we're in Nix shell (externally-managed Python)
if [ -n "$NIX_SHELL" ] || [ -n "$IN_NIX_SHELL" ]; then
    echo "⚠️  Detected Nix shell - using virtual environment"
    python -m venv venv
    source venv/bin/activate
    pip install --upgrade pip
fi

if [ -f "requirements.txt" ]; then
    pip install -r requirements.txt || {
        echo "⚠️  Some dependencies may have failed (this is OK if ComfyUI already has them)"
    }
else
    echo "⚠️  No requirements.txt found in ComfyUI"
fi

# Create symlink to Lattice Compositor
echo ""
echo "Linking Lattice Compositor as custom node..."
CUSTOM_NODES_DIR="$COMFYUI_DIR/custom_nodes"
mkdir -p "$CUSTOM_NODES_DIR"

LATTICE_LINK="$CUSTOM_NODES_DIR/ComfyUI-Lattice-Compositor"
if [ -L "$LATTICE_LINK" ]; then
    echo "✅ Symlink already exists"
elif [ -d "$LATTICE_LINK" ]; then
    echo "⚠️  Directory exists (not a symlink), removing..."
    rm -rf "$LATTICE_LINK"
    ln -s "$PROJECT_ROOT" "$LATTICE_LINK"
    echo "✅ Created symlink"
else
    ln -s "$PROJECT_ROOT" "$LATTICE_LINK"
    echo "✅ Created symlink: $LATTICE_LINK -> $PROJECT_ROOT"
fi

# Install Lattice Compositor Python dependencies
echo ""
echo "Installing Lattice Compositor dependencies..."
cd "$PROJECT_ROOT"
if [ -f "requirements.txt" ]; then
    # Use same Python environment (venv if in Nix, system otherwise)
    if [ -f "$COMFYUI_DIR/venv/bin/activate" ]; then
        source "$COMFYUI_DIR/venv/bin/activate"
    fi
    pip install -r requirements.txt || {
        echo "⚠️  Some dependencies may have failed (check if already installed)"
    }
    echo "✅ Dependencies installed"
else
    echo "⚠️  No requirements.txt found"
fi

# Install ComfyUI Manager and Lattice Compositor
echo ""
echo "Installing custom nodes..."

cd "$COMFYUI_DIR/custom_nodes"

# ComfyUI Manager
if [ ! -d "ComfyUI-Manager" ]; then
    echo "Cloning ComfyUI-Manager..."
    git clone https://github.com/ltdrdata/ComfyUI-Manager.git
    echo "✅ ComfyUI Manager installed"
else
    echo "✅ ComfyUI Manager already exists"
fi

# Lattice Compositor (from weyl-compositor repo)
if [ ! -d "ComfyUI-Lattice-Compositor" ]; then
    echo "Cloning Lattice Compositor..."
    git clone https://github.com/justinfleek/weyl-compositor.git ComfyUI-Lattice-Compositor
    echo "✅ Lattice Compositor installed"
else
    echo "✅ Lattice Compositor already exists"
fi

echo ""
echo "=========================================="
echo "✅ ComfyUI setup complete!"
echo "=========================================="
echo ""
echo "ComfyUI location: $COMFYUI_DIR"
if [ -f "$COMFYUI_DIR/venv/bin/activate" ]; then
    echo ""
    echo "⚠️  Virtual environment created (Nix shell detected)"
    echo "   To start ComfyUI, use:"
    echo "   cd $COMFYUI_DIR"
    echo "   source venv/bin/activate"
    echo "   python main.py --port 8188"
else
    echo ""
    echo "To start ComfyUI for testing:"
    echo "  cd $COMFYUI_DIR"
    echo "  python main.py --port 8188"
fi
echo ""
echo "Then run E2E tests:"
echo "  cd $PROJECT_ROOT/ui"
echo "  npm run test:playwright"
echo ""
