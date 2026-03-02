#!/bin/bash
# Stop ComfyUI - kills process on port 8188

cd "$(dirname "$0")/../ComfyUI"

echo "🛑 Stopping ComfyUI..."

# Try PID file first
if [ -f "comfyui.pid" ]; then
    PID=$(cat comfyui.pid)
    kill "$PID" 2>/dev/null && echo "✅ Stopped via PID file (PID: $PID)" || echo "⚠️  PID $PID not found"
    rm -f comfyui.pid
fi

# Force kill anything on port 8188
if command -v lsof >/dev/null 2>&1; then
    lsof -ti:8188 2>/dev/null | xargs -r kill -9 && echo "✅ Killed process on port 8188"
fi

# Kill any remaining python main.py processes
pkill -9 -f 'python.*main.py' 2>/dev/null && echo "✅ Killed remaining ComfyUI processes"

sleep 1
if curl -s -o /dev/null -w '%{http_code}' http://localhost:8188 2>/dev/null | grep -q '200'; then
    echo "⚠️  ComfyUI still responding - may need manual kill"
else
    echo "✅ ComfyUI stopped"
fi
