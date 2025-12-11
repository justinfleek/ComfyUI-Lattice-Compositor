# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Weyl is an After Effects-caliber motion graphics compositor embedded as a ComfyUI extension. It enables spline drawing on depth maps, text animation along paths, particle systems, and matte export for Wan 2.1 video generation.

**Target**: 81 frames at 16fps (5.0625 seconds), dimensions divisible by 8.

## Build Commands

### Frontend (Vue + TypeScript)
```bash
cd ui
npm install
npm run dev          # Development server
npm run build        # Production build (outputs to dist/)
```

### Backend (Python)
```bash
pip install -r requirements.txt
```

### Full Build
```bash
# Nix (reference build)
nix build .#default

# Docker
docker build -t weyl-compositor .
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  FRONTEND (Vue 3 + TypeScript)                              │
│  ├── Canvas: Fabric.js 6.x → WebGL fallback                │
│  ├── UI: PrimeVue (matches ComfyUI)                        │
│  └── State: Pinia stores                                    │
├─────────────────────────────────────────────────────────────┤
│  BACKEND (Python + ComfyUI)                                 │
│  ├── Inference: DepthAnything, NormalCrafter, MatSeg       │
│  ├── Export: Frame sequence generation                      │
│  └── Routes: /weyl/* endpoints via aiohttp                 │
├─────────────────────────────────────────────────────────────┤
│  COMFYUI INTEGRATION                                        │
│  ├── web/js/extension.js - Sidebar registration            │
│  ├── nodes/*.py - Python nodes                             │
│  └── WEB_DIRECTORY = "./web/js"                            │
└─────────────────────────────────────────────────────────────┘
```

## Critical Library Notes

### Fabric.js 6.x
- **Uses ES6 classes**, NOT `createClass()` (removed in v6)
- Must register custom classes: `classRegistry.setClass(MyClass)`

```typescript
// CORRECT
class SplinePath extends Path {
  static type = 'SplinePath';
}
classRegistry.setClass(SplinePath);

// WRONG - does not exist
fabric.util.createClass(...)
```

### Bezier.js
- `.get(t)`, `.derivative(t)`, `.length()`, `.project(point)` - all work
- **`.getPointAtDistance(d)` does NOT exist** - must build arc-length LUT manually (see `ui/src/services/arcLength.ts` in specs)

## Key File Locations

```
specs/                           # Complete technical specifications
├── SPEC_01_FOUNDATION.md       # Requirements, tech stack, file structure
├── SPEC_02_TYPES.md            # TypeScript type definitions
├── SPEC_03_COMFYUI.md          # ComfyUI integration code
├── SPEC_04_FABRIC.md           # Custom Fabric.js classes
├── SPEC_05_SERVICES.md         # Core services (arc length, fonts, particles)
├── SPEC_06_UI.md               # Vue components, Pinia stores
└── SPEC_07_BUILD_TEST.md       # Build config, testing checklist

ui/                             # Vue application (to be built)
├── src/main.ts                 # App entry
├── src/stores/                 # Pinia state management
├── src/services/               # Business logic
├── src/fabric/                 # Custom Fabric.js classes
└── src/components/             # Vue components

web/js/extension.js             # ComfyUI sidebar registration
nodes/*.py                      # Python ComfyUI nodes
```

## Implementation Order

1. Nix flake setup + extension skeleton
2. ComfyUI integration (Section 5 in specs)
3. Canvas + depth map loading
4. Spline editor
5. Timeline + keyframes
6. Text on path animation
7. Particle system
8. Built-in generation (DepthAnything, etc.)
9. Matte export
10. GPU optimization (Blackwell/WebGPU)

## Core Concepts

- **Lazy model loading**: AI models load on-demand, unload under memory pressure
- **GPU tiers**: Detect cpu/webgl/webgpu/blackwell, enable optimized paths accordingly
- **Arc-length parameterization**: Required for even text spacing on curves
- **Matte export**: White = keep, Black = exclude (for Wan video generation)
