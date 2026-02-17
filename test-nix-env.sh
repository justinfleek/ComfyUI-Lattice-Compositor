#!/bin/bash
set -e

echo "=== Testing Python Environment ==="
python --version

echo ""
echo "=== Testing PyTorch ==="
python -c "import torch; print(f'torch: {torch.__version__}'); print(f'CUDA available: {torch.cuda.is_available()}'); print(f'CUDA version: {torch.version.cuda if torch.cuda.is_available() else \"N/A\"}')"

echo ""
echo "=== Testing other packages ==="
python -c "import numpy; print(f'numpy: {numpy.__version__}')"
python -c "import torchvision; print(f'torchvision: {torchvision.__version__}')"
python -c "import torchaudio; print(f'torchaudio: {torchaudio.__version__}')"

echo ""
echo "=== Testing uv ==="
which uv && uv --version || echo "uv not found"

echo ""
echo "=== Checking if requirements-dev.txt exists ==="
if [ -f "requirements-dev.txt" ]; then
    echo "requirements-dev.txt found ($(wc -l < requirements-dev.txt) lines)"
else
    echo "requirements-dev.txt NOT found"
fi

echo ""
echo "=== Checking installed packages ==="
python -m pip list --user 2>/dev/null | head -20 || echo "No user packages installed yet"

echo ""
echo "✅ Environment test complete!"
