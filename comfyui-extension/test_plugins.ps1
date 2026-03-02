# Plugin Testing Script for Windows
# Run this in PowerShell from the project root

Write-Host "=== Plugin Testing Script ===" -ForegroundColor Cyan
Write-Host ""

# Test 1: Python FFI Bridge
Write-Host "Test 1: Python FFI Bridge" -ForegroundColor Yellow
try {
    $testConfig = '{"baseColor":{"hue":211,"saturation":0.12,"lightness":0.11},"heroColor":{"hue":211,"saturation":1.0,"lightness":0.66},"monitorType":"OLED","blackBalance":0.11,"mode":"dark"}'
    $result = python "src\lattice\FFI\theme_generator_ffi.py" $testConfig 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✓ Python FFI bridge works" -ForegroundColor Green
        Write-Host "  Output: $($result | Select-Object -First 1)" -ForegroundColor Gray
    } else {
        Write-Host "✗ Python FFI bridge failed (this is OK if Haskell library not built)" -ForegroundColor Yellow
        Write-Host "  Error: $result" -ForegroundColor Gray
    }
} catch {
    Write-Host "✗ Python FFI bridge test failed: $_" -ForegroundColor Red
}
Write-Host ""

# Test 2: VSCode Extension Compilation
Write-Host "Test 2: VSCode Extension" -ForegroundColor Yellow
try {
    Push-Location "vscode-prism-theme-generator"
    if (Test-Path "node_modules") {
        Write-Host "✓ node_modules exists" -ForegroundColor Green
    } else {
        Write-Host "  Installing dependencies..." -ForegroundColor Gray
        npm install 2>&1 | Out-Null
    }
    
    if (Test-Path "node_modules\typescript") {
        Write-Host "✓ TypeScript installed" -ForegroundColor Green
        npx tsc --noEmit 2>&1 | ForEach-Object {
            if ($_ -match "error") {
                Write-Host "  $_" -ForegroundColor Red
            }
        }
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ TypeScript compilation successful" -ForegroundColor Green
        } else {
            Write-Host "✗ TypeScript compilation has errors" -ForegroundColor Red
        }
    } else {
        Write-Host "✗ TypeScript not installed" -ForegroundColor Red
    }
    Pop-Location
} catch {
    Write-Host "✗ VSCode extension test failed: $_" -ForegroundColor Red
    Pop-Location
}
Write-Host ""

# Test 3: File Existence Checks
Write-Host "Test 3: Required Files" -ForegroundColor Yellow
$requiredFiles = @(
    "src\lattice\FFI\theme_generator_ffi.py",
    "vscode-prism-theme-generator\src\ffiBridge.ts",
    "neovim-prism-theme-generator\lua\prism-theme-generator\init.lua",
    "emacs-prism-theme-generator\prism-theme-generator.el",
    "LICENSE"
)

foreach ($file in $requiredFiles) {
    if (Test-Path $file) {
        Write-Host "✓ $file" -ForegroundColor Green
    } else {
        Write-Host "✗ $file MISSING" -ForegroundColor Red
    }
}
Write-Host ""

# Test 4: Neovim Plugin Syntax
Write-Host "Test 4: Neovim Plugin Syntax" -ForegroundColor Yellow
try {
    $luaFile = "neovim-prism-theme-generator\lua\prism-theme-generator\init.lua"
    if (Test-Path $luaFile) {
        $content = Get-Content $luaFile -Raw
        if ($content -match "function M\.setup") {
            Write-Host "✓ Neovim plugin has setup function" -ForegroundColor Green
        } else {
            Write-Host "✗ Neovim plugin missing setup function" -ForegroundColor Red
        }
    }
} catch {
    Write-Host "✗ Neovim plugin check failed: $_" -ForegroundColor Red
}
Write-Host ""

Write-Host "=== Testing Complete ===" -ForegroundColor Cyan
Write-Host ""
Write-Host "To test in Cursor/VSCode:" -ForegroundColor Yellow
Write-Host "1. Open vscode-prism-theme-generator folder in Cursor" -ForegroundColor White
Write-Host "2. Press F5 to launch Extension Development Host" -ForegroundColor White
Write-Host "3. Press F1 → 'Prism Theme: Generate Theme'" -ForegroundColor White
Write-Host ""
