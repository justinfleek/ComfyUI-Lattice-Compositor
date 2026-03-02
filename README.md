# Lattice

<div align="center">

**Motion Graphics Engine with Formally Verified Types**

[![Nix](https://img.shields.io/badge/Nix-Flakes-blue.svg)](https://nixos.wiki/wiki/Flakes)
[![Haskell](https://img.shields.io/badge/Haskell-GHC%209.6-purple.svg)](https://www.haskell.org/)
[![PureScript](https://img.shields.io/badge/PureScript-0.15-yellow.svg)](https://www.purescript.org/)
[![Lean4](https://img.shields.io/badge/Lean-4-green.svg)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

</div>

______________________________________________________________________

## Vision

Lattice is a **motion graphics compositor** for AI video generation workflows, built with **formal verification** at its core. Types are extracted from Lean4 proofs, not generated from schemas. When the proof compiles, the code is correct by construction.

```
Lean4 Proofs  ──►  PureScript Types  ──►  Haskell Types  ──►  C Types
     │
     └──►  decode(encode(x)) = x  (proven, not tested)
```

______________________________________________________________________

## Stack

| Layer | Technology | Purpose |
|-------|------------|---------|
| **Frontend** | PureScript + Halogen | Type-safe UI components |
| **Backend** | Haskell | Animation engine, effects, export |
| **Proofs** | Lean4 | Type extraction, correctness guarantees |
| **Build** | Nix | Reproducible builds, dev environments |
| **Bindings** | C, Python | FFI for external integrations |

______________________________________________________________________

## Quick Start

```bash
# Enter development environment
nix develop

# Build everything
cabal build                              # Haskell backend
cd lattice-core/purescript && spago build  # PureScript frontend
cd lattice-core/lean && lake build         # Verify proofs

# Run tests
cabal test
cd lattice-core/purescript && spago test
```

______________________________________________________________________

## Project Structure

```
LATTICE/
├── lattice-core/             # Core type-safe implementations
│   ├── purescript/           #   PureScript frontend (Halogen)
│   ├── haskell/              #   Haskell services
│   ├── lean/                 #   Lean4 proofs + type extraction
│   ├── c/                    #   C FFI bindings
│   └── python/               #   Python bindings
│
├── src/                      # Main Haskell library
│   ├── haskell/              #   Core modules
│   ├── armitage/             #   Build system (DICE, CAS)
│   ├── inference/            #   AI inference integration
│   └── server/               #   WebSocket server
│
├── hydrogen/                 # PureScript schema definitions
├── proofs/                   # Additional Lean4 proofs
├── nix/                      # Nix modules, overlays, packages
├── tests/                    # Property-based tests
├── bench/                    # Benchmarks
├── e2e/                      # End-to-end tests
│
├── newfeatures/              # Research integration staging
│   ├── MonarchRT/            #   Real-time video DiT (16 FPS)
│   ├── ACE-Step/             #   Music generation
│   ├── YUME/                 #   World model
│   ├── SAM3/                 #   Open-vocab segmentation
│   └── RESEARCH_PAPERS.md    #   190+ paper survey
│
├── comfyui-extension/        # [LEGACY] TypeScript/Vue edition
│   ├── ui/                   #   Vue 3 + TypeScript frontend
│   ├── src/                  #   Python ComfyUI nodes
│   └── ...                   #   All legacy TS/Vue/Python code
│
└── docs/                     # Documentation
    ├── INDEX.md              #   Documentation map
    ├── rfc/                  #   Technical specifications
    └── decisions/            #   Architecture Decision Records
```

______________________________________________________________________

## Key Principles

### 1. Types from Proofs

Every type definition requires a roundtrip proof in Lean4:

```lean
theorem Color_roundtrip (c : Color) : decode (encode c) = c := rfl
```

No proof, no type. Change the type, proof breaks, code won't compile.

### 2. Zero JavaScript FFI

The PureScript frontend creates pure request types. All browser operations go through Haskell via WebSocket. No `foreign import`, no escape hatches.

### 3. Deterministic by Design

For AI video generation, every frame must be reproducible:

- **Seeded RNG** — Mulberry32 algorithm
- **Checkpoint system** — Particles restore state on scrub  
- **Pure evaluation** — No `random`, no `now` without explicit time

### 4. No Technical Debt

Production-grade System F Omega code only:

- No `TODO` comments
- No placeholder implementations
- No stubs that throw
- No "coming soon" text

______________________________________________________________________

## Research Integration

Lattice integrates cutting-edge research for AI video acceleration. See [docs/decisions/0001-research-integration-roadmap.md](docs/decisions/0001-research-integration-roadmap.md) for the full plan.

### Active Research Areas

| Area | Key Papers | Status |
|------|------------|--------|
| **Real-time Diffusion** | Consistency Models, LCM-LoRA, MonarchRT | Planning |
| **Type-Safe Animation** | Granule, NumFuzz, graded monads | Planning |
| **Segmentation** | SAM 3 (270K concepts) | Staging |
| **World Models** | GameNGen, YUME, DIAMOND | Staging |
| **Voice Control** | F5-TTS, MinMo | Planning |
| **3D Neural** | 3D/4D Gaussian Splatting | Planning |

______________________________________________________________________

## ComfyUI Extension

The legacy TypeScript/Vue edition is maintained in `comfyui-extension/` for ComfyUI integration. See [comfyui-extension/README.md](comfyui-extension/README.md).

```bash
cd comfyui-extension
npm install
npm run build
```

______________________________________________________________________

## Documentation

| Document | Description |
|----------|-------------|
| [ARCHITECTURE.md](ARCHITECTURE.md) | System design and data flow |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution guidelines |
| [docs/INDEX.md](docs/INDEX.md) | Full documentation map |
| [docs/QUICK_START.md](docs/QUICK_START.md) | Getting started |
| [docs/BUILDING.md](docs/BUILDING.md) | Build instructions |
| [docs/rfc/](docs/rfc/) | Technical specifications |
| [docs/decisions/](docs/decisions/) | Architecture decisions |
| [PRD.md](PRD.md) | Product requirements |

______________________________________________________________________

## License

MIT — see [LICENSE](LICENSE)

______________________________________________________________________

<div align="center">

*Types are theorems. Proofs are programs.*

</div>
