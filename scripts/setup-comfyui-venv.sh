#!/bin/bash
# Set up ComfyUI virtual environment (for Nix shell compatibility)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ ComfyUI not found. Run: bash scripts/setup-comfyui-local.sh"
    exit 1
fi

cd "$COMFYUI_DIR"

# Create venv if it doesn't exist
if [ ! -d "venv" ]; then
    echo "Creating virtual environment..."
    python3 -m venv venv
fi

# Activate and upgrade pip
echo "Setting up virtual environment..."
source venv/bin/activate
pip install --upgrade pip setuptools wheel

# Install ComfyUI dependencies
if [ -f "requirements.txt" ]; then
    echo "Installing ComfyUI dependencies..."
    pip install -r requirements.txt
fi

# Install Lattice Compositor dependencies
echo "Installing Lattice Compositor dependencies..."
cd "$PROJECT_ROOT"
pip install -r requirements.txt

echo "✅ Virtual environment ready!"
