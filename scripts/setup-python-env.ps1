# One-command Python env: create .venv and install package (aiohttp, etc.) so IDE and type checker see real deps.
# Usage: .\scripts\setup-python-env.ps1
# Then: Select .venv\Scripts\python.exe as your Python interpreter in the IDE.

$ErrorActionPreference = "Stop"
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$VenvPath = Join-Path $ProjectRoot ".venv"
$PythonExe = Join-Path $VenvPath "Scripts\python.exe"

if (-not (Test-Path $VenvPath)) {
    Write-Host "Creating .venv..."
    python -m venv $VenvPath
}

Write-Host "Installing package (aiohttp, numpy, etc.)..."
& $PythonExe -m pip install --upgrade pip -q
& $PythonExe -m pip install -e $ProjectRoot -q

Write-Host "Done. Use .venv\Scripts\python.exe as your IDE interpreter."
