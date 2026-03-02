#!/bin/bash
# Start ComfyUI with proper environment setup

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

cd "$COMFYUI_DIR"

# Activate venv if it exists
if [ -f "venv/bin/activate" ]; then
    echo "Activating virtual environment..."
    source venv/bin/activate
fi

# Start ComfyUI
echo "Starting ComfyUI on http://localhost:8188"
echo "Press Ctrl+C to stop"
echo ""

python main.py --port 8188
