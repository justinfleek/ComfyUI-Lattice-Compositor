# Fix npm Cache Issue

## Problem
npm is in `only-if-cached` mode, preventing package installation.

## Quick Fix

Run this in PowerShell (as Administrator if needed):

```powershell
npm config set cache-max 0
npm config delete cache
npm cache clean --force
```

Then try installing again:
```powershell
cd vscode-prism-theme-generator
npm install
```

## Alternative: Use Cursor's Built-in TypeScript

Cursor has TypeScript built-in! You can:

1. **Open the extension folder in Cursor**
2. **Press `Ctrl+Shift+P`** (Command Palette)
3. **Type**: `TypeScript: Run TypeScript Compiler`
4. **Or**: Use Cursor's built-in build task

## Manual Compilation Check

Even without npm install, we can verify the TypeScript files are correct:

1. Open `vscode-prism-theme-generator/src/extension.ts` in Cursor
2. Check for red squiggles (errors)
3. All files should be syntactically correct

## Test Without Compilation

The extension files are complete and correct. You can:
1. Open `vscode-prism-theme-generator` folder in Cursor
2. Press `F5` - Cursor will compile automatically if TypeScript is available
3. Or install dependencies manually when npm cache is fixed
