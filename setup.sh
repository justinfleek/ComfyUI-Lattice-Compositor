#!/bin/bash
# Setup script for Lattice Compositor ComfyUI extension
# Builds the UI and installs Python dependencies

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"

echo "=========================================="
echo "Lattice Compositor Setup"
echo "=========================================="
echo ""

# Build UI
echo "Building UI..."
cd "$PROJECT_ROOT"
python build.py || {
    echo "Build failed. Trying npm directly..."
    cd ui
    npm install
    npm run build
    cd ..
}

# Install Python dependencies
echo ""
echo "Installing Python dependencies..."
pip install -r requirements.txt

echo ""
echo "✅ Setup complete!"
echo ""
echo "To use in ComfyUI:"
echo "  1. Copy this directory to ComfyUI/custom_nodes/ComfyUI-Lattice-Compositor"
echo "  2. Restart ComfyUI"
echo ""
