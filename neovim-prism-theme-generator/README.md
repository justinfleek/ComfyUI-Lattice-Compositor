# Prism Theme Generator for Neovim

Neovim plugin for generating base16 color themes with:
- **Color wheel** for selecting base and hero colors
- **Monitor-specific black balance** (OLED vs LCD)
- **Automatic theme generation** (light/dark modes, multiple variants)
- **Lean4 mathematical proofs** for color conversions and black balance

## Features

### Color Selection
- Interactive color picker for base color (background tint)
- Interactive color picker for hero color (accent color)
- Real-time HSL and hex display

### Monitor Support
- **OLED**: True black support (0% lightness = pure black)
- **LCD**: Backlight bleed compensation (minimum ~2% lightness)
- Adjustable black balance slider

### Theme Generation
- **Dark Mode**: Multiple variants (pure-black, ultra-dark, dark, tuned, balanced)
- **Light Mode**: Multiple variants (light, bright, paper)
- Automatic generation based on monitor type and black balance

## Requirements

- Neovim 0.9.0+
- Python 3.8+ (for FFI bridge to Haskell)
- Haskell FFI library (`libprism-ffi.so`)

## Installation

### Using packer.nvim

```lua
use {
  'prism-compositor/neovim-prism-theme-generator',
  config = function()
    require('prism-theme-generator').setup()
  end
}
```

### Using lazy.nvim

```lua
{
  'prism-compositor/neovim-prism-theme-generator',
  cmd = { 'PrismThemeGenerate', 'PrismThemePreview' },
  config = function()
    require('prism-theme-generator').setup()
  end
}
```

### Manual Installation

```bash
git clone https://github.com/your-org/neovim-prism-theme-generator.git \
  ~/.config/nvim/pack/prism-theme-generator/start/neovim-prism-theme-generator
```

## Usage

### Commands

- `:PrismThemeGenerate` - Open theme generator UI
- `:PrismThemePreview` - Preview generated theme
- `:PrismThemeExport` - Export theme to file

### Example Workflow

1. Run `:PrismThemeGenerate`
2. Select base color from color picker
3. Select hero color from color picker
4. Choose monitor type (OLED/LCD)
5. Adjust black balance slider
6. Select theme mode (Dark/Light)
7. Click "Generate Themes"
8. Preview and apply theme

## Configuration

```lua
require('prism-theme-generator').setup({
  -- Path to Python bridge script
  python_bridge_path = os.getenv('PRISM_PYTHON_BRIDGE') or 'python',
  
  -- Path to Haskell FFI library
  haskell_lib_path = os.getenv('PRISM_FFI_LIB') or 'libprism-ffi.so',
  
  -- Default monitor type
  default_monitor_type = 'OLED',  -- or 'LCD'
  
  -- Default theme mode
  default_mode = 'dark',  -- or 'light'
  
  -- Auto-apply theme after generation
  auto_apply = false,
})
```

## Architecture

- **Lean4**: Mathematical proofs for color conversions and black balance
- **Haskell**: Theme generation engine
- **FFI**: C bindings for Neovim plugin
- **Lua**: Neovim plugin UI and integration

## Black Balance Mathematics

The plugin uses Lean4 axioms to model monitor differences:

- **OLED**: `oled_black_balance(requested) = max(0, requested - offset)`
- **LCD**: `lcd_black_balance(requested) = max(lcd_min_black, requested)`

Where `lcd_min_black ≈ 0.02` (2% typical minimum due to backlight bleed).

## Development

```bash
# Build Haskell FFI
cd src/lattice/FFI
ghc -shared -fPIC ThemeGeneratorFFI.hs -o theme_generator.so

# Test Neovim plugin
nvim --cmd "set rtp+=./neovim-prism-theme-generator"
```

## License

Same as main project.
