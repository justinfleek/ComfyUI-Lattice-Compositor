# Install Lattice Compositor requirements in ComfyUI embedded Python
# Usage: .\install-requirements.ps1 [path-to-comfyui-portable]

param(
    [string]$ComfyUIPath = "C:\ComfyUI_windows_portable"
)

$pythonExe = Join-Path $ComfyUIPath "python_embeded\python.exe"
$requirementsFile = Join-Path $PSScriptRoot "requirements.txt"

if (-not (Test-Path $pythonExe)) {
    Write-Host "ERROR: Python executable not found at: $pythonExe"
    Write-Host ""
    Write-Host "Usage: .\install-requirements.ps1 [path-to-comfyui-portable]"
    Write-Host "Example: .\install-requirements.ps1 C:\ComfyUI_windows_portable"
    exit 1
}

if (-not (Test-Path $requirementsFile)) {
    Write-Host "ERROR: requirements.txt not found at: $requirementsFile"
    exit 1
}

Write-Host "Installing Lattice Compositor requirements..."
Write-Host "Python: $pythonExe"
Write-Host "Requirements: $requirementsFile"
Write-Host ""

& $pythonExe -m pip install --upgrade pip
& $pythonExe -m pip install -r $requirementsFile

Write-Host ""
Write-Host "Installation complete!"
Write-Host "Restart ComfyUI to load the extension."
