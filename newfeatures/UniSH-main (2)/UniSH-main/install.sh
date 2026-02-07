#!/bin/bash
set -e

# ==========================================
#         UniSH Auto-Install Script
# ==========================================

get_cuda_version() {
    if [ ! -z "$1" ]; then echo "$1"; return; fi
    if command -v nvidia-smi &> /dev/null; then
        DRIVER_CUDA_MAJOR=$(nvidia-smi | grep "CUDA Version" | awk -F'CUDA Version:' '{print $2}' | awk -F'.' '{print $1}' | tr -d '[:space:]')
        if [ "$DRIVER_CUDA_MAJOR" == "12" ]; then echo "12.1"; elif [ "$DRIVER_CUDA_MAJOR" == "11" ]; then echo "11.8"; else echo "12.1"; fi
    else echo "12.1"; fi
}

if [[ -z "$CONDA_PREFIX" ]]; then
    echo "❌ Error: Please activate the conda environment first!"
    exit 1
fi

TARGET_CUDA=$(get_cuda_version "$1")
echo "========================================"
echo "   Detected/Selected CUDA: $TARGET_CUDA"
echo "========================================"

if [[ "$TARGET_CUDA" == "12.1" ]]; then TORCH_INDEX_URL="https://download.pytorch.org/whl/cu121";
elif [[ "$TARGET_CUDA" == "11.8" ]]; then TORCH_INDEX_URL="https://download.pytorch.org/whl/cu118";
else TORCH_INDEX_URL=""; fi

echo "[1/6] Installing PyTorch 2.4.1 (CUDA $TARGET_CUDA)..."
pip install torch==2.4.1 torchvision==0.19.1 --index-url $TORCH_INDEX_URL

echo "[2/6] Installing Safe Requirements..."
pip install -r requirements.txt

echo "[3/6] Installing Custom Utils3D..."
pip install "git+https://github.com/EasternJournalist/utils3d.git@3fab839f0be9931dac7c8488eb0e1600c236e183"

echo "[4/6] Installing Heavy Dependencies..."
pip install open3d==0.19.0 --no-deps
pip install ultralytics==8.3.227 --no-deps
pip install timm==1.0.24 --no-deps

echo "[5/6] Installing MMCV & PyTorch3D..."
pip install mmcv==2.2.0 --no-deps --no-binary mmcv
pip install "git+https://github.com/facebookresearch/pytorch3d.git@stable" --no-build-isolation

echo "[6/6] Installing SAM 2 (With Setuptools Fix)..."

pip install setuptools==69.5.1 wheel
rm -rf _tmp_install_sam2

mkdir -p _tmp_install_sam2
cd _tmp_install_sam2

echo "   -> Cloning SAM 2..."
git clone https://github.com/facebookresearch/segment-anything-2.git --depth 1
cd segment-anything-2

echo "   -> Patching setup.py..."
python -c "
path = 'setup.py'
with open(path, 'r') as f: c = f.read()
c = c.replace('torch>=2.5.1', 'torch>=2.4.1')
with open(path, 'w') as f: f.write(c)
"
pip install . --no-deps --no-build-isolation
cd ../..
rm -rf _tmp_install_sam2

echo "========================================"
echo "Installation Complete!"
python -c "import torch; print(f'PyTorch: {torch.__version__} | CUDA: {torch.version.cuda}')"
echo "========================================"