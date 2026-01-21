#!/bin/bash
# Simple ComfyUI starter - fixes Nix library paths

cd "$(dirname "$0")/../ComfyUI"

if [ -f "venv/bin/activate" ]; then
    source venv/bin/activate
fi

# Fix Nix library paths for venv-installed PyTorch
# Nix isolates libraries, but venv's pip-installed packages need system libs
if [ -d "/nix/store" ]; then
    # Find Nix's libstdc++ and add to LD_LIBRARY_PATH
    NIX_LIBSTDCXX=$(find /nix/store -name 'libstdc++.so.6' -path '*/gcc-*/lib/*' 2>/dev/null | head -1 | xargs dirname 2>/dev/null || echo "")
    if [ -n "$NIX_LIBSTDCXX" ] && [ -d "$NIX_LIBSTDCXX" ]; then
        export LD_LIBRARY_PATH="$NIX_LIBSTDCXX:${LD_LIBRARY_PATH:-}"
    fi
    # Also try common Nix glibc paths
    for libpath in /nix/store/*-glibc-*/lib /nix/store/*-gcc-*/lib; do
        if [ -d "$libpath" ] && [ -f "$libpath/libstdc++.so.6" ]; then
            export LD_LIBRARY_PATH="$libpath:${LD_LIBRARY_PATH:-}"
            break
        fi
    done
fi

echo "🚀 Starting ComfyUI..."
echo "📍 http://localhost:8188"
if [ -n "$LD_LIBRARY_PATH" ]; then
    echo "🔧 Using LD_LIBRARY_PATH: $LD_LIBRARY_PATH"
fi
echo ""
python main.py --port 8188
