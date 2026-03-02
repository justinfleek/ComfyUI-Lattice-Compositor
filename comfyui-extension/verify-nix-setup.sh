#!/bin/bash
# Verification script for Nix dev shell setup
set -e

echo "=========================================="
echo "Nix Dev Shell Verification"
echo "=========================================="
echo ""

echo "1. Checking Python environment..."
python --version
echo ""

echo "2. Checking PyTorch installation..."
python -c "
import torch
print(f'  torch version: {torch.__version__}')
print(f'  CUDA available: {torch.cuda.is_available()}')
if torch.cuda.is_available():
    print(f'  CUDA version: {torch.version.cuda}')
    print(f'  GPU count: {torch.cuda.device_count()}')
"
echo ""

echo "3. Checking torchvision and torchaudio..."
python -c "
import torchvision
import torchaudio
print(f'  torchvision: {torchvision.__version__}')
print(f'  torchaudio: {torchaudio.__version__}')
"
echo ""

echo "4. Checking other nixpkgs packages..."
python -c "
import numpy
import scipy
import sympy
print(f'  numpy: {numpy.__version__}')
print(f'  scipy: {scipy.__version__}')
print(f'  sympy: {sympy.__version__}')
"
echo ""

echo "5. Checking tools..."
which uv && uv --version || echo "  uv: not found"
which bun && bun --version || echo "  bun: not found"
which git && git --version || echo "  git: not found"
echo ""

echo "6. Checking requirements-dev.txt..."
if [ -f "requirements-dev.txt" ]; then
    LINE_COUNT=$(wc -l < requirements-dev.txt)
    echo "  requirements-dev.txt found ($LINE_COUNT lines)"
    echo "  First 5 packages:"
    grep -v "^#" requirements-dev.txt | grep -v "^$" | head -5 | sed 's/^/    /'
else
    echo "  requirements-dev.txt NOT found"
fi
echo ""

echo "7. Checking installed user packages..."
if [ -d "$HOME/.local/lib/python3"* ]; then
    PACKAGE_COUNT=$(python -m pip list --user 2>/dev/null | wc -l || echo "0")
    echo "  User packages directory exists"
    echo "  Installed packages: $PACKAGE_COUNT"
    if [ "$PACKAGE_COUNT" -gt "5" ]; then
        echo "  Sample packages:"
        python -m pip list --user 2>/dev/null | head -10 | tail -5 | sed 's/^/    /'
    fi
else
    echo "  No user packages installed yet (will install on first shell entry)"
fi
echo ""

echo "8. Checking installation marker..."
if [ -f "$HOME/.local/.lattice-packages-installed" ]; then
    echo "  Installation marker found"
    echo "  Last installed: $(stat -c %y "$HOME/.local/.lattice-packages-installed" 2>/dev/null || stat -f %Sm "$HOME/.local/.lattice-packages-installed" 2>/dev/null || echo "unknown")"
else
    echo "  Installation marker not found (packages will install on next shell entry)"
fi
echo ""

echo "=========================================="
echo "✅ Verification complete!"
echo "=========================================="
