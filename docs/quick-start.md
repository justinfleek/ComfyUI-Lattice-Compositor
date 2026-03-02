# Quick Start

Get up and running with Lattice Compositor Standalone Edition.

## Prerequisites

- **Nix** with flakes enabled
- **Git**

### Enable Nix Flakes

If you haven't already:

```bash
# Add to ~/.config/nix/nix.conf or /etc/nix/nix.conf
experimental-features = nix-command flakes
```

## Setup

### 1. Enter Development Environment

```bash
cd standalone-edition
nix develop
```

This provides:
- GHC 9.x
- Cabal
- PureScript compiler (purs)
- Spago
- Lean4 (lake)
- All required libraries

### 2. Build Components

**Haskell Backend:**
```bash
cabal build
```

**PureScript Frontend:**
```bash
cd lattice-core/purescript
spago build
```

**Lean Proofs:**
```bash
cd lattice-core/lean
lake build
```

### 3. Run Tests

**Haskell:**
```bash
cabal test
```

**PureScript:**
```bash
cd lattice-core/purescript
spago test
```

## Development Workflow

### Making Changes

1. Edit PureScript files in `lattice-core/purescript/src/`
2. Edit Haskell files in `lattice-core/haskell/` or `src/haskell/`
3. Edit Lean proofs in `lattice-core/lean/`

### Rebuilding

```bash
# Quick rebuild
cabal build
cd lattice-core/purescript && spago build

# Full clean rebuild
cabal clean && cabal build
cd lattice-core/purescript && rm -rf output && spago build
```

### Type Extraction

When modifying types in Lean:

```bash
cd lattice-core/lean
lake build
# Extracted types are generated automatically
```

## Project Layout

```
standalone-edition/
├── lattice-core/
│   ├── purescript/     # Frontend
│   ├── haskell/        # Backend  
│   └── lean/           # Proofs
├── src/haskell/        # More Haskell
├── nix/                # Build config
└── docs/               # Documentation
```

## Next Steps

- Read [ARCHITECTURE.md](../ARCHITECTURE.md) for system design
- Check [docs/rfc/](./rfc/) for technical specifications
- See [CONTRIBUTING.md](../CONTRIBUTING.md) for contribution guidelines
