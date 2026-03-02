#!/usr/bin/env python3
"""Build script for Lattice Compositor ComfyUI extension.

Builds the UI and prepares the extension for installation.
Usage: python build.py
"""

import subprocess
import sys
import os
from pathlib import Path

def run_command(cmd, cwd=None, shell=False):
    """Run a shell command and return success status."""
    # On Windows, use .cmd extension for npm
    if sys.platform == "win32" and isinstance(cmd, list) and cmd[0] == "npm":
        cmd = ["npm.cmd"] + cmd[1:]
    
    print(f"Running: {' '.join(cmd) if isinstance(cmd, list) else cmd}")
    try:
        result = subprocess.run(
            cmd, 
            cwd=cwd, 
            shell=shell,
            check=False,
            capture_output=False
        )
        if result.returncode != 0:
            print(f"ERROR: Command failed with exit code {result.returncode}")
            return False
        return True
    except FileNotFoundError as e:
        print(f"ERROR: Command not found: {e}")
        return False

def main():
    """Build the extension."""
    project_root = Path(__file__).parent
    ui_dir = project_root / "ui"
    web_dir = project_root / "web" / "js"
    
    print("=" * 60)
    print("Building Lattice Compositor for ComfyUI")
    print("=" * 60)
    print()
    
    # Check if UI directory exists
    if not ui_dir.exists():
        print("ERROR: UI directory not found!")
        return 1
    
    # Check if node_modules exists
    if not (ui_dir / "node_modules").exists():
        print("Installing UI dependencies...")
        if not run_command(["npm", "install"], cwd=ui_dir):
            print("ERROR: Failed to install UI dependencies")
            print("   Make sure Node.js is installed: https://nodejs.org/")
            return 1
        print("Dependencies installed")
        print()
    
    # Build UI
    print("Building UI...")
    if not run_command(["npm", "run", "build"], cwd=ui_dir):
        print("ERROR: UI build failed")
        return 1
    
    # Verify build output
    if not web_dir.exists():
        print(f"ERROR: Build output directory not found: {web_dir}")
        return 1
    
    if not (web_dir / "lattice-compositor.js").exists():
        print(f"ERROR: Build output not found: {web_dir / 'lattice-compositor.js'}")
        return 1
    
    print("UI built successfully")
    print()
    print("=" * 60)
    print("Build complete!")
    print("=" * 60)
    print()
    print("Next steps:")
    print("  1. Install Python dependencies: pip install -r requirements.txt")
    print("  2. Copy this directory to ComfyUI/custom_nodes/ComfyUI-Lattice-Compositor")
    print("  3. Restart ComfyUI")
    print()
    print("Or use: npm run install (installs Python deps)")
    print()
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
