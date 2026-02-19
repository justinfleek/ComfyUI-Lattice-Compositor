# One-Time Nix Setup (Windows PowerShell)

## Quick Setup Commands

Run these commands **once** in PowerShell. After the first run, everything is cached and fast.

### Step 1: Enter WSL and navigate to project
```powershell
wsl
cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor
```

### Step 2: Enter the Nix dev shell (builds everything)
```bash
nix develop --accept-flake-config
```

**First time**: This will take 10-30 minutes as it downloads/builds:
- PyTorch with CUDA support
- All Python packages from nixpkgs
- Installs packages from requirements-dev.txt

**Subsequent times**: Fast! (uses cache)

### Step 3: Verify everything works
```bash
./verify-nix-setup.sh
```

### Step 4: Exit when done
```bash
exit  # Exits nix shell
exit  # Exits WSL, back to PowerShell
```

## What Happens

1. **First `nix develop`**:
   - Downloads PyTorch, CUDA libraries, and all dependencies
   - Builds Python environment with packages from nixpkgs
   - Installs 172 packages from `requirements-dev.txt` to `~/.local`
   - Creates cache marker at `~/.local/.lattice-packages-installed`

2. **Subsequent `nix develop`**:
   - Uses cached builds (fast!)
   - Only reinstalls if `requirements-dev.txt` changes

## All-in-One PowerShell Script

Save this as `setup-nix.ps1` and run it:

```powershell
# Enter WSL and set up Nix environment
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config"
```

Or run directly:
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config && ./verify-nix-setup.sh"
```

## Daily Usage (After First Setup)

Once set up, just run:
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config"
```

This enters the shell instantly (everything cached).

## Troubleshooting

### If build fails or times out:
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config --command bash"
```

### To reinstall packages from requirements-dev.txt:
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && rm ~/.local/.lattice-packages-installed && nix develop --accept-flake-config"
```

### To check what's installed:
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config --command python -m pip list --user"
```

## Notes

- **Everything persists** - Nix caches builds in `/nix/store` (persists across sessions)
- **Packages persist** - Installed to `~/.local` in WSL (persists)
- **One-time setup** - After first run, `nix develop` is instant
- **Isolated** - Doesn't touch your Windows Python at all
