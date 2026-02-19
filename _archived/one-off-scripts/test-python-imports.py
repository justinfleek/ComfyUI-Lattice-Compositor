#!/usr/bin/env python3
"""Test Python package imports to verify installation."""
import sys

errors = []
success = []

def test_import(name, package=None):
    """Test importing a package."""
    if package is None:
        package = name
    try:
        __import__(package)
        success.append(name)
        return True
    except ImportError as e:
        errors.append(f"{name}: {e}")
        return False
    except Exception as e:
        errors.append(f"{name}: Unexpected error - {e}")
        return False

print("=" * 60)
print("Python Package Import Test")
print("=" * 60)
print(f"Python version: {sys.version}")
print(f"Python executable: {sys.executable}")
print()

print("Testing core packages from nixpkgs...")
test_import("torch")
test_import("torchvision")
test_import("torchaudio")
test_import("numpy")
test_import("scipy")
test_import("sympy")
test_import("pytest")
test_import("aiohttp")
test_import("fastapi")
test_import("pydantic")
test_import("opencv", "cv2")

print()
print("Testing torch CUDA...")
try:
    import torch
    print(f"  torch version: {torch.__version__}")
    print(f"  CUDA available: {torch.cuda.is_available()}")
    if torch.cuda.is_available():
        print(f"  CUDA version: {torch.version.cuda}")
        print(f"  GPU count: {torch.cuda.device_count()}")
except Exception as e:
    errors.append(f"torch CUDA check: {e}")

print()
print("=" * 60)
print("Results")
print("=" * 60)
print(f"✅ Successful imports: {len(success)}")
for name in success:
    print(f"   ✓ {name}")

if errors:
    print(f"\n❌ Failed imports: {len(errors)}")
    for error in errors:
        print(f"   ✗ {error}")
    sys.exit(1)
else:
    print("\n✅ All packages imported successfully!")
    sys.exit(0)
