# Architecture

> Last Updated: March 2026

## Overview

Lattice is a motion graphics engine with formally verified types. Types are extracted from Lean4 proofs, ensuring correctness by construction.

## Stack

| Layer | Technology | Location |
|-------|------------|----------|
| Frontend | PureScript + Halogen | `lattice-core/purescript/` |
| Backend | Haskell | `lattice-core/haskell/`, `src/haskell/` |
| Proofs | Lean4 | `lattice-core/lean/`, `proofs/` |
| Schemas | PureScript | `hydrogen/` |
| Build | Nix | `nix/`, `flake.nix` |
| Bindings | C, Python | `lattice-core/c/`, `lattice-core/python/` |

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│  FRONTEND (PureScript + Halogen)                                │
│  lattice-core/purescript/src/Lattice/                           │
│  - UI.Layout.WorkspaceLayout    Main application shell          │
│  - UI.Components.*              Timeline, curves, dialogs       │
│  - UI.Store.ProjectStore        State management                │
└───────────────────────┬─────────────────────────────────────────┘
                        │ WebSocket (JSON)
                        ▼
┌─────────────────────────────────────────────────────────────────┐
│  BACKEND (Haskell)                                              │
│  lattice-core/haskell/ + src/haskell/                           │
│  - Services.Animation           Interpolation, easing           │
│  - Services.Particles           Simulation, forces              │
│  - Services.Effects             Blur, color, distort            │
│  - Services.Export              Video, matte, trajectory        │
└───────────────────────┬─────────────────────────────────────────┘
                        │
                        ▼
┌─────────────────────────────────────────────────────────────────┐
│  PROOFS (Lean4)                                                 │
│  lattice-core/lean/                                             │
│  - Extractable typeclass with roundtrip proofs                  │
│  - decode(encode(x)) = x proven for all types                   │
│  - Type extraction to PureScript, Haskell, C                    │
└─────────────────────────────────────────────────────────────────┘
```

## Directory Layout

```
LATTICE/
├── lattice-core/             # Core verified implementations
│   ├── purescript/           #   Frontend (Halogen components)
│   ├── haskell/              #   Backend services  
│   ├── lean/                 #   Proofs + type extraction
│   ├── c/                    #   C FFI bindings
│   └── python/               #   Python bindings
├── src/                      # Main Haskell library
│   ├── haskell/              #   Core modules
│   ├── armitage/             #   Build system
│   ├── inference/            #   AI inference
│   └── server/               #   WebSocket server
├── hydrogen/                 # PureScript schemas
├── proofs/                   # Additional Lean4 proofs
├── nix/                      # Nix configuration
├── tests/                    # Property tests
├── newfeatures/              # Research staging
└── comfyui-extension/        # [LEGACY] TS/Vue edition
```

## Key Design Decisions

### Types from Proofs

Every data type requires a Lean4 proof:

```lean
theorem Color_roundtrip (c : Color) : decode (encode c) = c := rfl
```

### Zero JavaScript FFI

PureScript creates pure request types. All IO goes through Haskell via WebSocket.

### Deterministic Evaluation

For AI video reproducibility:
- Seeded RNG (Mulberry32)
- Checkpoint system for particles
- Pure evaluation (no hidden state)

### UUID5 Only

All identifiers are deterministic UUID5. No random UUIDs.

## Build Commands

```bash
nix develop                    # Enter dev shell
cabal build                    # Build Haskell
cd lattice-core/purescript && spago build   # Build frontend
cd lattice-core/lean && lake build          # Verify proofs
```

## Related Documents

- [README.md](README.md) - Project overview
- [CONTRIBUTING.md](CONTRIBUTING.md) - Contribution guidelines
- [docs/INDEX.md](docs/INDEX.md) - Documentation map
- [docs/decisions/](docs/decisions/) - Architecture Decision Records
