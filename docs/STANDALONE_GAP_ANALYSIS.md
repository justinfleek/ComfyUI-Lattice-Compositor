# Standalone Edition Gap Analysis

**Date:** February 2026
**Status:** Assessment Complete

---

## Executive Summary

The **Standalone Edition** has strong foundations but is missing its entire UI layer. The backend (Lean4 proofs, PureScript services, Haskell types) is ~95% complete. The frontend (PureScript/Halogen UI) is **0% complete**.

### Quick Stats

| Component | Status | Notes |
|-----------|--------|-------|
| Lean4 Proofs | ✅ Complete | 246 files with verified types |
| PureScript Types/Services | ✅ Complete | 341 files, comprehensive test suite |
| Haskell Core | ✅ Complete | 190 files, Aleph integration |
| Aleph RFC Compliance | ✅ 87% | Minor bash script violations |
| **PureScript UI** | ❌ **0%** | No Halogen components exist |
| Nix Build | ✅ Working | flake.nix with proper structure |

---

## What's Complete

### 1. Core Logic (standalone/lattice-core/)

| Directory | Files | Coverage |
|-----------|-------|----------|
| lean/ | 246 | All domain types with proofs |
| purescript/ | 341 | Types, services, schemas, codecs |
| haskell/ | 190 | Type definitions, utilities |

The PureScript code includes:
- **34 core domain modules** (Animation, Effects, Particles, Physics, etc.)
- **60+ service modules** (BlendModes, Blur, ColorCorrection, Export, etc.)
- **Schema validation** for all JSON data
- **60+ test files** with property-based and unit tests

### 2. Aleph Integration (standalone/src/haskell/Aleph/)

| Module | Files | Purpose |
|--------|-------|---------|
| Aleph.Script | 25+ | Typed CLI tool wrappers |
| Aleph.Nix | 10+ | Nix DSL and FFI |

### 3. Build System

- `lattice.cabal` - Haskell build config
- `flake.nix` - Nix flake with proper module structure
- `spago.dhall` - PureScript package config
- Property tests integrated with haskemathesis

---

## What's Missing

### 1. UI Layer (CRITICAL - 0% complete)

The standalone edition has **NO user interface**. The Vue frontend in `comfyui/ui/` has:

| Category | Vue Components | PureScript Equivalent |
|----------|----------------|----------------------|
| Application Shell | 6 | **None** |
| Timeline | 9 | **None** |
| Properties Panels | 71 | **None** |
| Side Panels | 28 | **None** |
| Dialogs | 21 | **None** |
| Controls | 8 | **None** |
| Canvas/Viewport | 10 | **None** |
| Curve Editor | 4 | **None** |
| **TOTAL** | **167** | **0** |

### 2. Available Building Blocks (from IMPLEMENTATION/)

| Project | What It Provides | Integration Status |
|---------|-----------------|-------------------|
| purescript-radix-main | Dialog, Tabs Halogen components | NOT INTEGRATED |
| verified-purescript-main | Verified prelude from Lean | NOT INTEGRATED |
| straylight-web-main | Web project skeleton | NOT INTEGRATED |

### 3. Bash Scripts Needing Conversion (per RFC aleph-006)

These scripts have logic that should be Haskell:

| Script | Lines | Priority |
|--------|-------|----------|
| deploy.sh | 47 | High |
| worker-setup.sh | 22 | High |
| pep503-index.sh | 24 | Medium |
| wheel-install.sh | 24 | Medium |
| firecracker-build.sh | 21 | Low |
| wasm-build-plugin.sh | 33 | Low |

---

## Effort Estimation

### Option A: Build PureScript/Halogen UI from Scratch

| Phase | Effort | Description |
|-------|--------|-------------|
| Foundation | 4-6 weeks | App shell, routing, state management |
| Core Panels | 8-12 weeks | Timeline, Properties, Viewport |
| Controls | 4-6 weeks | ColorPicker, Sliders, Curve editor |
| Full Parity | 12-16 weeks | All 167 component equivalents |
| **TOTAL** | **28-40 weeks** | ~7-10 months |

### Option B: Hybrid Architecture

Keep Vue UI but have it call PureScript/Haskell backend via:
- WebSocket for real-time updates
- REST API for operations
- WASM for compute-heavy operations

| Phase | Effort | Description |
|-------|--------|-------------|
| API Layer | 2-3 weeks | Define Haskell servant API |
| WASM Compilation | 2-3 weeks | Compile PureScript to WASM |
| Vue Integration | 1-2 weeks | Connect existing UI to new backend |
| **TOTAL** | **5-8 weeks** | ~1-2 months |

### Option C: Extend Elm Demo

The Elm demo in `standalone/lattice-core/elm/` has basic 3D viewport. Could extend:

| Phase | Effort | Description |
|-------|--------|-------------|
| Elm-PureScript FFI | 2-3 weeks | Bridge Elm UI to PS services |
| Core UI | 6-8 weeks | Timeline, properties, panels |
| Full UI | 12-16 weeks | All functionality |
| **TOTAL** | **20-27 weeks** | ~5-7 months |

---

## IMPLEMENTATION Projects Integration Plan

### High Priority

| Project | Reason | Effort |
|---------|--------|--------|
| **purescript-radix-main** | Provides Dialog, Tabs, FocusTrap | 1 week |
| **verified-purescript-main** | Verified prelude for type safety | 1 week |

### Medium Priority

| Project | Reason | Effort |
|---------|--------|--------|
| **slide-main** | LLM inference if adding AI features | 2-3 weeks |
| **s4-main** | GPU kernels for inference | 2-3 weeks |

### Low Priority (Infrastructure)

| Project | Reason | Effort |
|---------|--------|--------|
| isospin-microvm-main | GPU virtualization | When needed |
| sensenet-main | Build infrastructure | When needed |
| trinity-engine-hs-dev | io_uring bindings | When needed |

---

## Recommended Roadmap

### Phase 1: Foundation (2-4 weeks)

1. ✅ Folder structure cleanup (DONE)
2. ⬜ Convert 2 high-priority bash scripts to Haskell
3. ⬜ Integrate purescript-radix-main into standalone
4. ⬜ Set up Halogen app skeleton with routing

### Phase 2: Minimal Viable UI (6-8 weeks)

1. ⬜ Basic workspace layout (sidebar, main area)
2. ⬜ Properties panel showing layer data
3. ⬜ Simple timeline with playhead
4. ⬜ 2D canvas viewport (no WebGL yet)

### Phase 3: Core Functionality (8-12 weeks)

1. ⬜ Full timeline with keyframes
2. ⬜ Animation curve editor
3. ⬜ Effects panel
4. ⬜ WebGL viewport integration

### Phase 4: Feature Parity (12-16 weeks)

1. ⬜ All property editors
2. ⬜ All dialogs
3. ⬜ Particle system UI
4. ⬜ Physics controls
5. ⬜ Export workflow

---

## Decision Points

### Q1: Should we build a full PureScript UI or use hybrid architecture?

**Recommendation:** Start with **Option B (Hybrid)** to get something working quickly, then incrementally move functionality to PureScript if desired.

### Q2: What's the MVP for standalone?

**Minimum Viable Standalone:**
- Layer display and selection
- Property editing for transform
- Timeline with play/pause
- Export to image sequence

### Q3: Do we maintain both editions or converge?

**Recommendation:** Maintain both:
- **ComfyUI Edition** for users who want node-based workflow
- **Standalone Edition** for users who want traditional After Effects workflow

They share the same core logic (PureScript services, Lean proofs).

---

## Files Modified by This Analysis

- Created: `docs/STANDALONE_GAP_ANALYSIS.md` (this file)
- Reference: `IMPLEMENTATION/COMFYUI-FEATURE-PARITY.md` (24-35 week estimate for full ComfyUI parity)
