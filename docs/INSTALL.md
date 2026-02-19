# Installation Guide

## Quick Install (ComfyUI Extension)

### Method 1: Git Clone (Recommended)

```bash
cd ComfyUI/custom_nodes
git clone https://github.com/justinfleek/lattice-compositor.git ComfyUI-Lattice-Compositor
cd ComfyUI-Lattice-Compositor
pip install -r requirements.txt
```

**Restart ComfyUI.** The Lattice icon will appear in your sidebar.

### Method 2: Build from Source

If you want to build the UI yourself:

```bash
# Clone the repository
git clone https://github.com/justinfleek/lattice-compositor.git
cd lattice-compositor

# Build the UI
python build.py

# Or manually:
cd ui
npm install
npm run build

# Install Python dependencies
pip install -r requirements.txt

# Copy to ComfyUI
cp -r . /path/to/ComfyUI/custom_nodes/ComfyUI-Lattice-Compositor
```

## Requirements

- **ComfyUI** (latest version recommended)
- **Python 3.10+** (Python 3.13+ recommended)
- **Node.js 18+** (only needed for building from source)

## Python Dependencies

The extension requires minimal dependencies (most are provided by ComfyUI):

```
numpy>=2.4.0
pillow>=12.1.0
scipy>=1.16.3
```

Install with:
```bash
pip install -r requirements.txt
```

## Verification

After installation, verify it's working:

1. Start ComfyUI
2. Look for the **Lattice** icon (video icon) in the sidebar
3. Click it to open the Motion Compositor
4. You should see the full compositor interface

## Troubleshooting

### Extension not appearing

1. Check that `__init__.py` exists in the extension directory
2. Check ComfyUI console for error messages
3. Verify `web/js/lattice-compositor.js` exists
4. Check browser console (F12) for JavaScript errors

### Build errors

If building from source fails:

1. Ensure Node.js 18+ is installed: `node --version`
2. Clear node_modules: `rm -rf ui/node_modules && cd ui && npm install`
3. Check for TypeScript errors: `cd ui && npm run typecheck`

### Python import errors

1. Verify Python version: `python --version` (should be 3.10+)
2. Reinstall dependencies: `pip install -r requirements.txt --force-reinstall`
3. Check that `src/lattice/__init__.py` exists and exports `NODE_CLASS_MAPPINGS`
