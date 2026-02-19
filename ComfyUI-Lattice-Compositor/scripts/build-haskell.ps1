# Build entire Lattice Haskell library (src/lattice). Run from repo root.
# Usage: .\scripts\build-haskell.ps1   or   pwsh -File scripts/build-haskell.ps1
$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Push-Location $root
try {
    cabal build
    exit $LASTEXITCODE
} finally {
    Pop-Location
}
