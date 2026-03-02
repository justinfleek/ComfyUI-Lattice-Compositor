# Type Audit Summary

**Date:** 2026-01-11
**Audited:** `src/` directory (excluding node_modules, .d.ts files)

---

## Overall Counts

| Issue Type | Count |
|------------|-------|
| `: any` declarations | 272 |
| `as any` casts | 452 |
| `as unknown as` (lazy hack) | 88 |
| `@ts-ignore/@ts-expect-error` | 1 |
| `eslint-disable @typescript` | 2 |
| **TOTAL TYPE ISSUES** | **815** |

---

## Categorization by Fix Strategy

### INPUT BOUNDARIES (use `validation.ts`)
**Total: ~55 issues**

| Source | Count | Priority |
|--------|-------|----------|
| AI/Agent (`services/ai/`) | 12 | P0 - SECURITY |
| Migration/Import (`projectMigration`, `templateBuilder`, `PluginManager`) | 38 | P1 |
| API responses (`services/comfyui/`) | 5 | P1 |

**Fix approach:** Apply `ValidationResult<T>` pattern with `validateString()`, `validateFiniteNumber()`, `validateVec2()`, etc.

---

### NUMERIC CODE (use `numericSafety.ts`)
**Total: ~182 issues**

| Source | Count | Priority |
|--------|-------|----------|
| Physics (`services/physics/`) | 6 | P1 |
| Particles (`engine/particles/`, `particleSystem`) | 16 | P1 |
| Animation/Interpolation (`animation/`, `expressions/`) | 56 | P0 - HOT PATH |
| Transform controls | 12 | P1 |
| Export renderers (`services/export/`) | 92 | P2 |

**Fix approach:** Apply `ensureFinite()`, `safeDivide()`, `safeLerp()`, `clamp01()`, `safeNormalize2D()`, etc.

---

### INTERNAL (use `typeGuards.ts`)
**Total: ~345 issues**

| Source | Count | Priority |
|--------|-------|----------|
| Stores (`stores/`) | 76 | P1 |
| Components (`components/`) | 175 | P2 |
| Composables (`composables/`) | 38 | P2 |
| Engine/Layers (`engine/layers/`, `engine/core/`) | 56 | P1 |

**Fix approach:** Apply `isObject()`, `hasXY()`, `isFiniteNumber()`, `isAnimatableProperty()`, `assertDefined()`, etc.

---

### TEST FILES (low priority)
**Total: ~280 issues**

| Source | Count | Priority |
|--------|-------|----------|
| Test files (`__tests__/`) | 280 | P3 |
| Mock files (`__mocks__/`) | 11 | P3 |

**Note:** Test files can have looser typing since they're not production code. Focus on production code first.

---

## Top 20 Files by Issue Count

### `: any` declarations
| File | Count |
|------|-------|
| services/plugins/PluginManager.ts | 16 |
| components/properties/ParticleProperties.vue | 15 |
| services/expressions/layerContentExpressions.ts | 11 |
| __mocks__/three.ts | 11 |
| services/templateBuilder.ts | 10 |
| composables/useSplineInteraction.ts | 10 |
| components/properties/TextProperties.vue | 10 |
| components/timeline/PropertyTrack.vue | 8 |
| services/projectMigration.ts | 7 |
| components/panels/EffectControlsPanel.vue | 7 |

### `as any` casts
| File | Count |
|------|-------|
| __tests__/_deprecated/services/export/attackSurface.test.ts | 36 |
| __tests__/tutorials/tutorial-01-fundamentals.test.ts | 32 |
| engine/layers/TextLayer.ts | 15 |
| __tests__/stores/projectActions.test.ts | 14 |
| __tests__/security/jsonSanitizer.test.ts | 13 |
| __tests__/engine/MotionEngine.test.ts | 12 |
| services/particleSystem.ts | 9 |
| engine/TransformControlsManager.ts | 9 |
| engine/layers/LightLayer.ts | 9 |
| components/canvas/MeshWarpPinEditor.vue | 9 |

### `as unknown as` (lazy hack - FIX FIRST)
| File | Count |
|------|-------|
| stores/actions/layer/layerDefaults.ts | 17 |
| composables/useKeyboardShortcuts.ts | 9 |
| services/ai/actionExecutor.ts | 7 |
| services/physics/PhysicsEngine.ts | 6 |
| stores/layerStore/crud.ts | 4 |
| stores/actions/projectActions/serialization.ts | 4 |
| engine/animation/KeyframeEvaluator.ts | 4 |

---

## Fix Order (Category by Category)

### Phase 1: INPUT BOUNDARIES (validation.ts)
1. `services/ai/actionExecutor.ts` - **PARTIALLY DONE**
2. `services/plugins/PluginManager.ts`
3. `services/projectMigration.ts`
4. `services/templateBuilder.ts`
5. `services/comfyui/*.ts`

### Phase 2: NUMERIC CODE (numericSafety.ts)
1. `engine/animation/KeyframeEvaluator.ts`
2. `services/expressions/layerContentExpressions.ts`
3. `services/particleSystem.ts`
4. `services/physics/PhysicsEngine.ts`
5. `engine/TransformControlsManager.ts`
6. `services/export/*.ts`

### Phase 3: INTERNAL - Stores (typeGuards.ts)
1. `stores/actions/layer/layerDefaults.ts` - 17 lazy hacks
2. `stores/layerStore/crud.ts`
3. `stores/actions/projectActions/*.ts`

### Phase 4: INTERNAL - Engine
1. `engine/layers/TextLayer.ts`
2. `engine/layers/LightLayer.ts`
3. `engine/core/LayerManager.ts`

### Phase 5: INTERNAL - Components
1. `components/properties/ParticleProperties.vue`
2. `components/properties/TextProperties.vue`
3. `components/timeline/PropertyTrack.vue`
4. `components/panels/EffectControlsPanel.vue`
5. (remaining components)

### Phase 6: INTERNAL - Composables
1. `composables/useKeyboardShortcuts.ts`
2. `composables/useSplineInteraction.ts`
3. `composables/useAssetHandlers.ts`

### Phase 7: Test Files (optional)
- Lower priority, can be done after production code

---

## Utilities Available

### validation.ts (for INPUT BOUNDARIES)
- `ValidationResult<T>` type
- `validateString()`, `validateFiniteNumber()`, `validateInteger()`, `validateBoolean()`
- `validateVec2()`, `validateVec3()`, `validateColor()`
- `validateArray()`, `validateObject()`, `validateEnum()`
- `optional()`, `withDefault()`, `validateSchema()`

### numericSafety.ts (for NUMERIC CODE)
- `ensureFinite()`, `requireFinite()`
- `safeDivide()`, `safeMod()`, `safeSqrt()`
- `clamp()`, `clamp01()`, `clamp0255()`
- `safeLerp()`, `safeInverseLerp()`, `safeRemap()`
- `safeNormalize2D()`, `safeDistance2D()`
- `normalizeAngleDegrees()`, `approximately()`

### typeGuards.ts (for INTERNAL)
- `isObject()`, `isFiniteNumber()`, `isNonEmptyString()`, `isArray()`
- `hasXY()`, `hasXYZ()`, `hasDimensions()`, `isBoundingBox()`
- `isRGBColor()`, `isRGBAColor()`
- `isAnimatableProperty()`, `isKeyframe()`
- `hasAssetId()`, `hasCompositionId()`, `hasSource()`
- `hasPosition()`, `hasScale()`, `hasRotation()`
- `assertType()`, `assertDefined()`

---

## Rules

1. **NO NEW AD-HOC SOLUTIONS** - Use existing utilities only
2. **NO `as unknown as`** - This is a lazy hack, replace with proper validation
3. **NO `as any`** - Use type guards or validation
4. **Category by category** - Not file by file
5. **Property tests** - Add fast-check tests for numeric code
6. **Production code first** - Test files are lower priority

---

*Generated by type audit on 2026-01-11*
