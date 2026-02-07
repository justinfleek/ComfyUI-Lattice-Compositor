# types/effects.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 3,319 (LARGEST file in codebase)
- **Location:** `ui/src/types/effects.ts`
- **Role:** Effect definitions, parameters, and EFFECT_DEFINITIONS constant

---

## IMPORTS (What it depends on) - 2 dependencies

| Import | From |
|--------|------|
| `WarpMesh`, `WarpPin` (types) | `./meshWarp` |
| `AnimatableProperty` (type) | `./project` |

**Note:** This file is mostly self-contained definitions with minimal imports.

---

## DEPENDENTS (What imports it) - 11 files (VERIFIED)

**Blast radius: 11 files use `EffectInstance`, 5 use `EFFECT_DEFINITIONS`**

> Verified 2026-01-10 via symbol usage grep (not just import paths)
> Note: `EffectInstance` is re-exported from `types/project.ts`, so import path count was misleading

| File | Symbol Used |
|------|-------------|
| `components/panels/EffectControlsPanel.vue` | EFFECT_DEFINITIONS, EffectInstance |
| `components/panels/EffectsPanel.vue` | EFFECT_DEFINITIONS, EffectInstance |
| `components/properties/ShapeProperties.vue` | EffectInstance (via project.ts) |
| `engine/layers/BaseLayer.ts` | EffectInstance |
| `engine/MotionEngine.ts` | EffectInstance (via project.ts) |
| `services/ai/stateSerializer.ts` | EffectInstance (via project.ts) |
| `services/effectProcessor.ts` | EffectInstance |
| `services/effects/meshDeformRenderer.ts` | EffectInstance (comment only) |
| `services/gpuBenchmark.ts` | EffectInstance |
| `services/layerEvaluationCache.ts` | EffectInstance (via project.ts) |
| `services/templateBuilder.ts` | EffectInstance |
| `stores/actions/effectActions.ts` | createEffectInstance, EffectInstance |
| `types/index.ts` | Re-export |
| `types/project.ts` | Re-export |
| `types/spline.ts` | SplinePathEffectInstance (related) |

---

## File Structure Analysis

The file is large (3,319 lines) because it contains **EFFECT_DEFINITIONS** - a massive constant object defining all built-in effects:

```typescript
// ~100 lines: Type definitions
export type EffectCategory = ...
export interface EffectParameter { ... }
export interface Effect { ... }
export interface EffectInstance { ... }
export interface EffectDefinition { ... }

// ~3,200 lines: Effect definitions constant
export const EFFECT_DEFINITIONS: Record<string, EffectDefinition> = {
  // Blur & Sharpen (~20 effects)
  "gaussian-blur": { ... },
  "box-blur": { ... },
  "directional-blur": { ... },
  ...

  // Color Correction (~25 effects)
  "brightness-contrast": { ... },
  "curves": { ... },
  "hue-saturation": { ... },
  ...

  // Distort (~15 effects)
  "bulge": { ... },
  "displacement": { ... },
  "mesh-deform": { ... },
  ...

  // Generate (~10 effects)
  "checkerboard": { ... },
  "fractal-noise": { ... },
  ...

  // Stylize (~15 effects)
  "glow": { ... },
  "emboss": { ... },
  ...

  // Time (~5 effects)
  "echo": { ... },
  "time-remap": { ... },
  ...

  // + many more categories
};
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    types/effects.ts                          │
│                     (3,319 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (2 dependencies)                              │
│  ├── ./meshWarp (WarpMesh, WarpPin)                         │
│  └── ./project (AnimatableProperty)                         │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (11 files) ← VERIFIED via symbol usage         │
│  ├── 2 components                                           │
│  ├── 3 services                                             │
│  ├── 1 engine file                                          │
│  └── 1 store action                                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: LOW (despite file size)**

This is a **data file**, not a logic file. Most of its size comes from effect parameter definitions, not complex code.

### Why It's Safe to Modularize

1. **Low import count** - Only 7 files would be affected
2. **Data, not logic** - Mostly static definitions
3. **Clear split points** - Effects are organized by category
4. **Type exports are simple** - Interfaces are small and stable

### Modularization Strategy

**Split by effect category into separate files:**

```
types/effects/
├── index.ts              (~100 lines - types + re-exports)
├── blur-sharpen.ts       (~300 lines)
├── color-correction.ts   (~400 lines)
├── distort.ts            (~300 lines)
├── generate.ts           (~200 lines)
├── keying.ts             (~150 lines)
├── matte.ts              (~150 lines)
├── noise-grain.ts        (~150 lines)
├── perspective.ts        (~100 lines)
├── stylize.ts            (~300 lines)
├── time.ts               (~200 lines)
├── transition.ts         (~200 lines)
└── utility.ts            (~100 lines)
```

**index.ts would:**
1. Import all category definitions
2. Merge into single EFFECT_DEFINITIONS object
3. Re-export all types
4. Preserve exact same public API

### Implementation Notes

1. **Keep types in index.ts** - `EffectInstance`, `EffectParameter`, etc.
2. **Each category file exports** - `const BLUR_SHARPEN_EFFECTS = { ... }`
3. **index.ts merges** - `export const EFFECT_DEFINITIONS = { ...BLUR_SHARPEN_EFFECTS, ...COLOR_CORRECTION_EFFECTS, ... }`
4. **Zero breaking changes** - All 7 importers continue to work unchanged
