# PowerShell script to set up Nix dev environment
# Run this once, then use 'nix develop' directly in WSL

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Setting up Nix Dev Environment" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

Write-Host "This will:" -ForegroundColor Yellow
Write-Host "  1. Enter WSL" -ForegroundColor Yellow
Write-Host "  2. Navigate to project directory" -ForegroundColor Yellow
Write-Host "  3. Enter Nix dev shell (first time takes 10-30 min)" -ForegroundColor Yellow
Write-Host "  4. Install all Python packages" -ForegroundColor Yellow
Write-Host ""

Write-Host "After first run, 'nix develop' will be instant!" -ForegroundColor Green
Write-Host ""

$response = Read-Host "Continue? (Y/N)"
if ($response -ne 'Y' -and $response -ne 'y') {
    Write-Host "Cancelled." -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "Entering WSL and starting Nix dev shell..." -ForegroundColor Cyan
Write-Host "(First time: This downloads/builds PyTorch + all packages)" -ForegroundColor Yellow
Write-Host ""

# Enter WSL and run nix develop
wsl bash -c "cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config"

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Setup complete!" -ForegroundColor Green
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "To use again, just run:" -ForegroundColor Yellow
Write-Host "  wsl bash -c 'cd /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor && nix develop --accept-flake-config'" -ForegroundColor White
Write-Host ""
