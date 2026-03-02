# Local ComfyUI Setup for Testing

## Overview

ComfyUI is installed locally in the repo (gitignored) for:
- ✅ E2E testing with Playwright
- ✅ Verifying custom node installation works
- ✅ Testing user experience
- ✅ Development and debugging

**Important**: ComfyUI is in `.gitignore` - it's never committed to the repo.

## Quick Setup

### One-Time Setup

```bash
# From project root
bash scripts/setup-comfyui-local.sh
```

This will:
1. Clone ComfyUI to `./ComfyUI/` (gitignored)
2. Install ComfyUI dependencies
3. Create symlink: `ComfyUI/custom_nodes/ComfyUI-Lattice-Compositor` → project root
4. Install Lattice Compositor dependencies from `requirements.txt`

### Start ComfyUI for Testing

```bash
# Option 1: Use helper script
bash scripts/start-comfyui-test.sh

# Option 2: Manual
cd ComfyUI
python main.py --port 8188
```

### Run E2E Tests

In another terminal:
```bash
cd ui
npm run test:playwright
```

## Directory Structure

```
ComfyUI-Lattice-Compositor/
├── ComfyUI/                    # ← Gitignored, local ComfyUI install
│   ├── custom_nodes/
│   │   └── ComfyUI-Lattice-Compositor -> ../../  # Symlink to project root
│   └── ...
├── src/                        # Python custom node code
├── ui/                         # Frontend code
├── requirements.txt            # Python dependencies (for users)
└── scripts/
    ├── setup-comfyui-local.sh  # Setup script
    └── start-comfyui-test.sh   # Start script
```

## Why This Approach?

### ✅ Benefits

1. **Realistic Testing** - Tests run against actual ComfyUI installation
2. **User Experience** - Verify installation works like users will experience it
3. **Requirements.txt Validation** - Ensures `requirements.txt` works correctly
4. **E2E Tests** - Can run full Playwright tests locally
5. **Development** - Easy to test changes without external setup

### ✅ User Installation (Production)

Users install like any other ComfyUI custom node:

```bash
cd ComfyUI/custom_nodes
git clone <repo-url> ComfyUI-Lattice-Compositor
cd ComfyUI-Lattice-Compositor
pip install -r requirements.txt
```

Our `requirements.txt` ensures this works seamlessly.

## Maintenance

### Update ComfyUI

```bash
cd ComfyUI
git pull
pip install -r requirements.txt
```

### Reinstall Everything

```bash
rm -rf ComfyUI
bash scripts/setup-comfyui-local.sh
```

### Verify Installation

```bash
bash ui/scripts/setup-comfyui-test.sh
```

## CI/CD Considerations

For CI, you can:
1. Clone ComfyUI in CI workflow
2. Install dependencies
3. Run E2E tests
4. Or use a Docker image with ComfyUI pre-installed

## Notes

- ComfyUI is **never committed** (in `.gitignore`)
- Symlink ensures changes to project are immediately available in ComfyUI
- `requirements.txt` is user-friendly - just `pip install -r requirements.txt`
- Works seamlessly with Nix dev shell (ComfyUI runs outside Nix)
