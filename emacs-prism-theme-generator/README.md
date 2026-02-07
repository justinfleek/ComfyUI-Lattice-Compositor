# Prism Theme Generator for Emacs

Emacs package for generating base16 color themes with:
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

- Emacs 27.1+
- Python 3.8+ (for FFI bridge to Haskell)
- Haskell FFI library (`libprism-ffi.so`)

## Installation

### Using use-package

```elisp
(use-package prism-theme-generator
  :load-path "~/path/to/emacs-prism-theme-generator"
  :config
  (prism-theme-generator-mode))
```

### Using straight.el

```elisp
(use-package prism-theme-generator
  :straight (:host github :repo "your-org/emacs-prism-theme-generator")
  :config
  (prism-theme-generator-mode))
```

### Manual Installation

```bash
git clone https://github.com/your-org/emacs-prism-theme-generator.git \
  ~/.emacs.d/lisp/prism-theme-generator
```

Add to your `~/.emacs.d/init.el`:

```elisp
(add-to-list 'load-path "~/.emacs.d/lisp/prism-theme-generator")
(require 'prism-theme-generator)
(prism-theme-generator-mode)
```

## Usage

### Commands

- `M-x prism-theme-generator` - Open theme generator UI
- `M-x prism-theme-preview` - Preview generated theme
- `M-x prism-theme-export` - Export theme to file

### Example Workflow

1. Run `M-x prism-theme-generator`
2. Select base color from color picker
3. Select hero color from color picker
4. Choose monitor type (OLED/LCD)
5. Adjust black balance slider
6. Select theme mode (Dark/Light)
7. Click "Generate Themes"
8. Preview and apply theme

## Configuration

```elisp
(customize-set-variable 'prism-theme-generator-python-bridge-path "python")
(customize-set-variable 'prism-theme-generator-haskell-lib-path "libprism-ffi.so")
(customize-set-variable 'prism-theme-generator-default-monitor-type 'OLED)
(customize-set-variable 'prism-theme-generator-default-mode 'dark)
(customize-set-variable 'prism-theme-generator-auto-apply nil)
```

## Architecture

- **Lean4**: Mathematical proofs for color conversions and black balance
- **Haskell**: Theme generation engine
- **FFI**: C bindings for Emacs plugin
- **Elisp**: Emacs plugin UI and integration

## Black Balance Mathematics

The package uses Lean4 axioms to model monitor differences:

- **OLED**: `oled_black_balance(requested) = max(0, requested - offset)`
- **LCD**: `lcd_black_balance(requested) = max(lcd_min_black, requested)`

Where `lcd_min_black ≈ 0.02` (2% typical minimum due to backlight bleed).

## Development

```bash
# Build Haskell FFI
cd src/lattice/FFI
ghc -shared -fPIC ThemeGeneratorFFI.hs -o theme_generator.so

# Test Emacs package
emacs --eval "(add-to-list 'load-path \".\")" \
      --eval "(require 'prism-theme-generator)"
```

## License

Same as main project.
