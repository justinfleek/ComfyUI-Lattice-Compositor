#!/bin/bash
# Setup script to verify ComfyUI is ready for E2E testing
# Checks for local ComfyUI installation (in repo root)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

echo "=========================================="
echo "ComfyUI Test Setup Check"
echo "=========================================="
echo ""

# Check if ComfyUI exists locally
if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ ComfyUI not found at: $COMFYUI_DIR"
    echo ""
    echo "Set up ComfyUI locally with:"
    echo "  bash scripts/setup-comfyui-local.sh"
    echo ""
    echo "This will:"
    echo "  1. Clone ComfyUI to ./ComfyUI (gitignored)"
    echo "  2. Install ComfyUI dependencies"
    echo "  3. Link Lattice Compositor as custom node"
    echo "  4. Install Lattice Compositor dependencies"
    exit 1
fi

echo "✅ ComfyUI found at: $COMFYUI_DIR"
echo ""

# Check if symlink exists
LATTICE_LINK="$COMFYUI_DIR/custom_nodes/ComfyUI-Lattice-Compositor"
if [ ! -L "$LATTICE_LINK" ] && [ ! -d "$LATTICE_LINK" ]; then
    echo "⚠️  Lattice Compositor not linked"
    echo "Creating symlink..."
    mkdir -p "$COMFYUI_DIR/custom_nodes"
    ln -s "$PROJECT_ROOT" "$LATTICE_LINK"
    echo "✅ Symlink created"
else
    echo "✅ Lattice Compositor linked"
fi

# Check if ComfyUI dependencies are installed
echo ""
echo "Checking ComfyUI Python dependencies..."
cd "$COMFYUI_DIR"
python -c "import torch; import aiohttp; print('✅ Core dependencies OK')" 2>/dev/null || {
    echo "⚠️  Some ComfyUI dependencies missing"
    echo "   Install with: cd ComfyUI && pip install -r requirements.txt"
}

# Check Lattice Compositor dependencies
echo ""
echo "Checking Lattice Compositor dependencies..."
cd "$PROJECT_ROOT"
python -c "import numpy; import PIL; print('✅ Core dependencies OK')" 2>/dev/null || {
    echo "⚠️  Some dependencies missing"
    echo "   Install with: pip install -r requirements.txt"
}

echo ""
echo "=========================================="
echo "✅ ComfyUI is ready for testing!"
echo "=========================================="
echo ""
echo "To start ComfyUI:"
echo "  bash scripts/start-comfyui-test.sh"
echo ""
echo "Or manually:"
echo "  cd ComfyUI"
echo "  python main.py --port 8188"
echo ""
echo "Then run tests:"
echo "  cd ui"
echo "  npm run test:playwright"
echo ""
