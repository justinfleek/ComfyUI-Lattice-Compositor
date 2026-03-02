#!/bin/bash
# Start ComfyUI for E2E testing
# This script starts ComfyUI with the Lattice Compositor custom node

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

# Check if ComfyUI exists
if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ ComfyUI not found at: $COMFYUI_DIR"
    echo ""
    echo "Run setup first:"
    echo "  bash scripts/setup-comfyui-local.sh"
    exit 1
fi

# Check if symlink exists
LATTICE_LINK="$COMFYUI_DIR/custom_nodes/ComfyUI-Lattice-Compositor"
if [ ! -L "$LATTICE_LINK" ] && [ ! -d "$LATTICE_LINK" ]; then
    echo "⚠️  Lattice Compositor not linked in ComfyUI"
    echo "Creating symlink..."
    mkdir -p "$COMFYUI_DIR/custom_nodes"
    ln -s "$PROJECT_ROOT" "$LATTICE_LINK"
    echo "✅ Symlink created"
fi

# Activate venv if it exists (for Nix environments)
if [ -f "$COMFYUI_DIR/venv/bin/activate" ]; then
    echo "Activating virtual environment..."
    source "$COMFYUI_DIR/venv/bin/activate"
fi

# Start ComfyUI
echo "=========================================="
echo "Starting ComfyUI for Testing"
echo "=========================================="
echo ""
echo "ComfyUI directory: $COMFYUI_DIR"
echo "Port: 8188"
echo "URL: http://localhost:8188"
echo ""
echo "Press Ctrl+C to stop"
echo ""

cd "$COMFYUI_DIR"
python main.py --port 8188
