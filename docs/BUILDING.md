# Building

Complete build instructions for Lattice Compositor Standalone Edition.

## Build Systems

This project uses multiple build systems:

| Component | Build System | Config File |
|-----------|--------------|-------------|
| Haskell   | Cabal        | `lattice.cabal` |
| PureScript| Spago        | `lattice-core/purescript/spago.yaml` |
| Lean4     | Lake         | `lattice-core/lean/lakefile.lean` |
| Nix       | Nix Flakes   | `flake.nix` |

## Nix Build

### Development Shell

```bash
nix develop
```

Provides all tools: GHC, Cabal, purs, spago, lake, etc.

### Build Packages

```bash
# Build Haskell library
nix build .#lattice

# Build Armitage CLI
nix build .#armitage

# Build UI
nix build .#ui
```

## Cabal Build

### Library

```bash
cabal build
```

### Executables

```bash
# Armitage build system
cabal build armitage

# Armitage proxy
cabal build armitage-proxy
```

### Tests

```bash
# All tests
cabal test

# Specific test suite
cabal test render-api-property
```

## PureScript Build

```bash
cd lattice-core/purescript

# Build
spago build

# Build with bundling
spago bundle-app

# Test
spago test

# REPL
spago repl
```

## Lean4 Build

```bash
cd lattice-core/lean

# Build all
lake build

# Clean and rebuild
lake clean && lake build

# Run extraction
lake exe extract
```

## Full Build Sequence

```bash
# 1. Enter Nix shell
nix develop

# 2. Build Lean proofs (generates types)
cd lattice-core/lean && lake build && cd ../..

# 3. Build Haskell backend
cabal build

# 4. Build PureScript frontend
cd lattice-core/purescript && spago build && cd ../..

# 5. Run tests
cabal test
cd lattice-core/purescript && spago test
```

## Clean Build

```bash
# Haskell
cabal clean

# PureScript
cd lattice-core/purescript && rm -rf output .spago

# Lean
cd lattice-core/lean && lake clean

# Nix
rm -rf result result-*
```

## Troubleshooting

### Missing Dependencies

If Cabal can't find dependencies:

```bash
cabal update
cabal build --only-dependencies
```

### PureScript Package Issues

```bash
cd lattice-core/purescript
rm -rf .spago output
spago install
spago build
```

### Lean Lake Issues

```bash
cd lattice-core/lean
lake clean
lake update
lake build
```

### Nix Cache Issues

```bash
nix-collect-garbage
nix develop --refresh
```
