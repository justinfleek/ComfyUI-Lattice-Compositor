# Prism Theme Generator

VSCode extension for generating base16 color themes with:
- **Color wheel** for selecting base and hero colors
- **Monitor-specific black balance** (OLED vs LCD)
- **Automatic theme generation** (light/dark modes, multiple variants)
- **Lean4 mathematical proofs** for color conversions and black balance

## Features

### Color Selection
- Interactive color wheel for base color (background tint)
- Interactive color wheel for hero color (accent color)
- Real-time HSL and hex display

### Monitor Support
- **OLED**: True black support (0% lightness = pure black)
- **LCD**: Backlight bleed compensation (minimum ~2% lightness)
- Adjustable black balance slider

### Theme Generation
- **Dark Mode**: Multiple variants (pure-black, ultra-dark, dark, tuned, balanced)
- **Light Mode**: Multiple variants (light, bright, paper)
- Automatic generation based on monitor type and black balance

## Installation

### Option 1: Install from ZIP/VSIX

1. Download the latest release (`prism-theme-generator-<version>.zip` or `.vsix`)
2. Open VSCode
3. Press `F1` and type "Extensions: Install from VSIX..."
4. Select the downloaded file

### Option 2: Install from Source

```bash
cd vscode-prism-theme-generator
npm install
npm run compile
# Then press F5 in VSCode to run extension in development mode
```

### Option 3: Package Yourself

```bash
cd vscode-prism-theme-generator
npm install
npm run package:zip  # Creates ZIP file
# Or use VSCode's built-in packaging:
npm install -g vsce
vsce package  # Creates .vsix file
```

## Usage

1. Press `F1` and type "Prism Theme: Generate Theme"
2. Select base color from color wheel
3. Select hero color from color wheel
4. Choose monitor type (OLED/LCD)
5. Adjust black balance slider
6. Select theme mode (Dark/Light)
7. Click "Generate Themes"
8. Preview and export themes

## Architecture

- **Lean4**: Mathematical proofs for color conversions and black balance (`leancomfy/lean/Color/BlackBalance.lean`)
- **Haskell**: Theme generation engine (`src/lattice/Utils/BlackBalance.hs`, `src/lattice/Utils/Base16Theme.hs`)
- **FFI**: C bindings for VSCode extension (`src/lattice/FFI/ThemeGeneratorFFI.hs`)
- **TypeScript**: VSCode extension UI (`vscode-prism-theme-generator/src/`)

## Black Balance Mathematics

The extension uses Lean4 axioms to model monitor differences:

- **OLED**: `oled_black_balance(requested) = max(0, requested - offset)`
- **LCD**: `lcd_black_balance(requested) = max(lcd_min_black, requested)`

Where `lcd_min_black ≈ 0.02` (2% typical minimum due to backlight bleed).

## Development

```bash
# Build Haskell FFI
cd src/lattice/FFI
ghc -shared -fPIC ThemeGeneratorFFI.hs -o theme_generator.so

# Build VSCode extension
cd vscode-prism-theme-generator
npm install
npm run compile
npm run watch  # For development
```

## License

Same as main project.
