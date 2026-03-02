#!/bin/bash
# Quick test to verify Python packages are working

echo "=== Quick Python Environment Test ==="
echo ""

echo "1. Python version:"
python --version
echo ""

echo "2. Testing core packages:"
python -c "import torch; print(f'  ✅ torch: {torch.__version__}')" 2>&1
python -c "import numpy; print(f'  ✅ numpy: {numpy.__version__}')" 2>&1
python -c "import torchvision; print(f'  ✅ torchvision: {torchvision.__version__}')" 2>&1
python -c "import torchaudio; print(f'  ✅ torchaudio: {torchaudio.__version__}')" 2>&1
echo ""

echo "3. Testing CUDA:"
python -c "import torch; print(f'  CUDA available: {torch.cuda.is_available()}')" 2>&1
echo ""

echo "4. Testing other packages:"
python -c "import scipy; print(f'  ✅ scipy: {scipy.__version__}')" 2>&1
python -c "import fastapi; print(f'  ✅ fastapi installed')" 2>&1
python -c "import pydantic; print(f'  ✅ pydantic installed')" 2>&1
echo ""

echo "5. Checking user-installed packages:"
python -m pip list --user 2>/dev/null | wc -l | xargs echo "  Packages in ~/.local:"
echo ""

echo "✅ All tests complete!"
