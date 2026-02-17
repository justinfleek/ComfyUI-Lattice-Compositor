#!/bin/bash
# Quick start ComfyUI - minimal setup

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COMFYUI_DIR="$PROJECT_ROOT/ComfyUI"

cd "$COMFYUI_DIR"

# Activate venv
if [ -f "venv/bin/activate" ]; then
    source venv/bin/activate
fi

# Start ComfyUI
echo "🚀 Starting ComfyUI..."
echo "📍 URL: http://localhost:8188"
echo ""
python main.py --port 8188
