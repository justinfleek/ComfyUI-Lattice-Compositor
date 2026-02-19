# Architecture

> Last Updated: February 2026

## Overview

Lattice Compositor Standalone Edition is a motion graphics engine with formally verified types. Unlike the ComfyUI edition (Vue/TypeScript), this version uses PureScript for the frontend and Haskell for the backend, with Lean4 proofs guaranteeing type correctness.

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  FRONTEND (PureScript + Halogen)                                            │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ lattice-core/purescript/src/                                          │  │
│  │ - Lattice.UI.Layout.WorkspaceLayout    Main application layout        │  │
│  │ - Lattice.UI.Components.Timeline       Timeline and keyframes         │  │
│  │ - Lattice.UI.Components.AddLayerDialog Layer creation                 │  │
│  │ - Lattice.UI.Components.CurveEditor    Animation curves               │  │
│  │ - Lattice.UI.Store.ProjectStore        State management               │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
└─────────────┬───────────────────────────────────────────────────────────────┘
              │ WebSocket (JSON)
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  BRIDGE (Lattice.Services.Bridge)                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ Zero JavaScript FFI - All browser operations go through Haskell       │  │
│  │ - Request/Response types                                              │  │
│  │ - RenderOp, StorageOp, ExportOp, MathOp, GenerateOp                  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
└─────────────┬───────────────────────────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  BACKEND (Haskell)                                                          │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ lattice-core/haskell/ + src/haskell/                                  │  │
│  │                                                                        │  │
│  │ Services:                                                              │  │
│  │ - Lattice.Services.Animation      Interpolation, easing, expressions  │  │
│  │ - Lattice.Services.Particles      CPU simulation, forces, turbulence  │  │
│  │ - Lattice.Services.Effects        Blur, color, distort, stylize       │  │
│  │ - Lattice.Services.Export         Video, matte, trajectory export     │  │
│  │ - Lattice.Services.Physics        Cloth, rigid body, collision        │  │
│  │                                                                        │  │
│  │ Schemas:                                                               │  │
│  │ - Lattice.Schemas.*               Type-safe data definitions          │  │
│  │                                                                        │  │
│  │ Utils:                                                                 │  │
│  │ - Lattice.Utils.Uuid5             Deterministic UUID generation       │  │
│  │ - Lattice.Utils.Security          Input validation                    │  │
│  │ - Lattice.Utils.NumericSafety     NaN/Infinity handling               │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
└─────────────┬───────────────────────────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  PROOFS (Lean4)                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ lattice-core/lean/                                                    │  │
│  │ - Extractable typeclass with roundtrip proofs                         │  │
│  │ - decode(encode(x)) = x proven for all types                          │  │
│  │ - Type extraction to PureScript, Haskell, C, Python                   │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Data Flow

### Type Extraction (Build Time)
```
1. Define type in Lean4 with Extractable instance
2. Write roundtrip proof: decode(encode(x)) = x
3. Lean verifies proof
4. Extract to target languages (PureScript, Haskell, C)
5. Generated code is correct by construction
```

### Runtime Request Flow
```
1. User action in PureScript UI
2. Create Request type (RenderOp, StorageOp, etc.)
3. Serialize to JSON
4. Send via WebSocket to Haskell backend
5. Backend processes request
6. Return Response
7. Update PureScript state
```

### Frame Evaluation
```
1. ProjectStore.currentFrame changes
2. Request frame evaluation from backend
3. For each layer:
   a. Evaluate property expressions
   b. Interpolate keyframed values
   c. Apply effects
4. Return rendered frame data
5. Display in UI
```

## Key Design Decisions

### Zero JavaScript FFI

PureScript frontend creates pure request types. All browser operations (file I/O, network, etc.) go through the Haskell bridge via WebSocket. Read-only browser queries (time, DOM state) are allowed via standard packages (`Effect.Now`, `web-html`).

### UUID5 Only

No UUID4/random UUIDs. All identifiers are deterministic UUID5 from `Lattice.Utils.Uuid5.Core`. This ensures reproducibility.

### No Stubs

Production grade System F Omega code only. No TODO comments, no placeholder implementations, no "coming soon" text.

## Directory Structure

```
standalone-edition/
├── lattice-core/
│   ├── purescript/
│   │   ├── src/Lattice/
│   │   │   ├── UI/              # Halogen components
│   │   │   ├── Services/        # Bridge, export, render queue
│   │   │   └── Utils/           # Shared utilities
│   │   └── test/                # PureScript tests
│   ├── haskell/
│   │   └── Lattice/             # Haskell implementation
│   ├── lean/
│   │   └── Lattice/             # Proofs and extraction
│   ├── c/                       # C type bindings
│   └── python/                  # Python bindings
├── src/
│   ├── haskell/Lattice/         # Additional Haskell modules
│   ├── armitage/                # Build system
│   └── tools/scripts/           # Development tools
├── nix/
│   ├── modules/                 # Flake modules
│   ├── overlays/                # Nixpkgs overlays
│   ├── packages/                # Package definitions
│   └── prelude/                 # Shared Nix functions
├── proofs/                      # Additional Lean proofs
├── linter/                      # Dhall linter config
├── tests/
│   └── property/                # Property-based tests
└── docs/
    └── rfc/                     # Technical RFCs
```

## Build System

### Nix

Primary build system. Provides reproducible builds and development environments.

```bash
nix develop              # Enter dev shell
nix build .#lattice      # Build Haskell package
nix build .#ui           # Build frontend
```

### Cabal

Haskell package management.

```bash
cabal build              # Build library
cabal test               # Run tests
```

### Spago

PureScript package management.

```bash
cd lattice-core/purescript
spago build              # Build PureScript
spago test               # Run tests
```

### Lake

Lean4 build system.

```bash
cd lattice-core/lean
lake build               # Build proofs
```

## Security

### Input Validation

All external data passes through validation in `Lattice.Utils.Security`:
- Schema validation
- NaN/Infinity rejection
- Path traversal prevention

### Determinism

For AI video generation, every frame must be reproducible:
- Seeded RNG (Mulberry32)
- Checkpoint system for particles
- Pure evaluation (no `random`, no `now` without explicit time parameter)
