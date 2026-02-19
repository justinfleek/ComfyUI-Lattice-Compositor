# Lattice Compositor - Standalone Edition

A motion graphics compositor with bulletproof types, built on formal verification.

## Stack

- **Frontend:** PureScript + Halogen
- **Backend:** Haskell
- **Proofs:** Lean4
- **Build:** Nix

## Key Principle

Types are extracted from Lean proofs. No external schemas. No codegen scripts. Just theorems.

```
Lean4 Proofs → PureScript Types → Haskell Types → C Types
     ↓
  decode(encode(x)) = x  (proven, not tested)
```

## Quick Start

```bash
# Enter development environment
nix develop

# Build PureScript frontend
cd lattice-core/purescript && spago build

# Build Haskell backend
cabal build

# Verify proofs
cd lattice-core/lean && lake build
```

## Project Structure

```
standalone-edition/
├── lattice-core/           # Core type-safe implementations
│   ├── purescript/         # Frontend (Halogen components)
│   ├── haskell/            # Backend services
│   ├── lean/               # Formal proofs + type extraction
│   ├── c/                  # C type bindings
│   └── python/             # Python bindings
├── src/
│   ├── haskell/            # Haskell library modules
│   ├── armitage/           # Build system (DICE, CAS)
│   └── tools/              # Development scripts
├── nix/                    # Nix modules and overlays
├── proofs/                 # Additional Lean proofs
├── linter/                 # Dhall linter configuration
├── tests/                  # Property-based tests
└── docs/                   # Documentation
    └── rfc/                # Technical RFCs
```

## Documentation

- [Architecture](./ARCHITECTURE.md) - System design and data flow
- [Quick Start](./docs/QUICK_START.md) - Getting started guide
- [Building](./docs/BUILDING.md) - Build instructions
- [Contributing](./CONTRIBUTING.md) - Contribution guidelines
- [RFCs](./docs/rfc/) - Technical specifications

## Why Formal Verification?

When LLMs generate code, they optimize for "looks right" and "compiles." This project uses Lean4 proofs to guarantee correctness:

1. **Types require proofs** - No type definition without a roundtrip proof
2. **Proofs must typecheck** - Lean's kernel verifies, not vibes
3. **`rfl` demands equality** - Terms must compute to the same thing
4. **Extraction mirrors the proof** - Generated code does exactly what was proven

Change a type, proof breaks, extraction fails, types stay in sync.

## License

MIT
