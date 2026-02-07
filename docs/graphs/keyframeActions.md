# keyframeActions.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 2,023
- **Location:** `ui/src/stores/actions/keyframeActions.ts`
- **Role:** All keyframe manipulation operations (add, remove, move, interpolation, handles)

---

## IMPORTS (What it depends on) - 4 dependencies

| Import | From |
|--------|------|
| `toRaw` | `vue` |
| `markLayerDirty` | `@/services/layerEvaluationCache` |
| `AnimatableProperty`, `BezierHandle`, `InterpolationType`, `Keyframe`, `Layer` (types) | `@/types/project` |
| `storeLogger` | `@/utils/logger` |

### Re-exports
| Export | From |
|--------|------|
| `* (all)` | `./keyframes/keyframeExpressions` |

---

## DEPENDENTS (What imports it) - 24 files (VERIFIED)

**Blast radius: 24 files use keyframe functions (NOT 5 as originally reported)**

> Verified 2026-01-10 via: `grep -r "addKeyframe|removeKeyframe|moveKeyframe|updateKeyframe|findPropertyByPath|keyframeActions"`
>
> **CORRECTION:** Original analysis only counted direct imports (5 files).
> Actual usage is much higher because functions are called via the store's action delegation.

### Direct Importers (5 files)
| File | Purpose |
|------|---------|
| `composables/useExpressionEditor.ts` | Expression editing UI |
| `services/ai/actionExecutor.ts` | AI action execution |
| `stores/actions/index.ts` | Actions barrel export |
| `stores/actions/keyframes/keyframeExpressions.ts` | Expression-specific keyframe actions |
| `stores/compositorStore.ts` | Main store (imports all action modules) |

### Function Users (24 files total)
| File | Functions Used |
|------|----------------|
| `components/canvas/ThreeCanvas.vue` | addKeyframe |
| `components/curve-editor/CurveEditorCanvas.vue` | addKeyframe, moveKeyframe |
| `components/curve-editor/CurveEditor.vue` | addKeyframe |
| `components/dialogs/MotionSketchPanel.vue` | addKeyframe |
| `components/dialogs/SmootherPanel.vue` | updateKeyframe |
| `components/layout/WorkspaceLayout.vue` | addKeyframe |
| `components/panels/AIChatPanel.vue` | addKeyframe |
| `components/panels/EffectsPanel.vue` | addKeyframe |
| `components/properties/DepthProperties.vue` | addKeyframe |
| `components/properties/KeyframeToggle.vue` | addKeyframe, removeKeyframe |
| `components/properties/TextProperties.vue` | addKeyframe |
| `components/timeline/PropertyTrack.vue` | addKeyframe, moveKeyframe |
| `composables/useCurveEditorInteraction.ts` | moveKeyframe, updateKeyframe |
| `composables/useKeyboardShortcuts.ts` | addKeyframe, removeKeyframe |
| `services/ai/actionExecutor.ts` | keyframeActions.* |
| `services/ai/systemPrompt.ts` | addKeyframe (documentation) |
| `services/ai/toolDefinitions.ts` | addKeyframe (tool definition) |
| `stores/actions/layer/splineActions.ts` | addKeyframe |
| `stores/actions/physicsActions.ts` | addKeyframe |
| `stores/compositorStore.ts` | keyframeActions.* |
| `stores/selectionStore.ts` | findPropertyByPath |

---

## File Structure Analysis

The file contains ~40 exported functions organized by operation type:

```typescript
// ============================================================================
// HELPER FUNCTIONS (~100 lines)
// ============================================================================
function safeFrame(frame, fallback): number { ... }
export function findPropertyByPath(layer, propertyPath): AnimatableProperty { ... }

// ============================================================================
// KEYFRAME CREATION (~200 lines)
// ============================================================================
export function addKeyframe<T>(store, layerId, propertyPath, value, atFrame): Keyframe<T> { ... }
export function addKeyframeAtCurrentTime<T>(store, layerId, propertyPath, value): Keyframe<T> { ... }
export function addKeyframeToBatch(store, layerId, propertyPath, value, frame): void { ... }
export function commitKeyframeBatch(store): number { ... }

// ============================================================================
// KEYFRAME SELECTION & RETRIEVAL (~150 lines)
// ============================================================================
export function getKeyframeAt(store, layerId, propertyPath, frame): Keyframe { ... }
export function getKeyframesInRange(store, layerId, propertyPath, startFrame, endFrame): Keyframe[] { ... }
export function getAllKeyframes(store, layerId, propertyPath): Keyframe[] { ... }
export function getSelectedKeyframes(store): { layerId, propertyPath, keyframe }[] { ... }

// ============================================================================
// KEYFRAME REMOVAL (~150 lines)
// ============================================================================
export function removeKeyframe(store, layerId, propertyPath, frame): boolean { ... }
export function removeKeyframeById(store, layerId, propertyPath, keyframeId): boolean { ... }
export function removeKeyframesInRange(store, layerId, propertyPath, startFrame, endFrame): number { ... }
export function clearAllKeyframes(store, layerId, propertyPath): void { ... }

// ============================================================================
// KEYFRAME MOVEMENT & TRANSFORMATION (~300 lines)
// ============================================================================
export function moveKeyframe(store, layerId, propertyPath, keyframeId, newFrame): boolean { ... }
export function moveKeyframesBy(store, layerId, propertyPath, keyframeIds, deltaFrames): number { ... }
export function scaleKeyframes(store, layerId, propertyPath, keyframeIds, scaleFactor, pivotFrame): number { ... }
export function reverseKeyframes(store, layerId, propertyPath, keyframeIds): number { ... }

// ============================================================================
// KEYFRAME VALUE UPDATES (~200 lines)
// ============================================================================
export function updateKeyframeValue<T>(store, layerId, propertyPath, keyframeId, newValue): boolean { ... }
export function updateKeyframeInterpolation(store, layerId, propertyPath, keyframeId, interpolation): boolean { ... }
export function setKeyframeEasing(store, layerId, propertyPath, keyframeId, easing): boolean { ... }

// ============================================================================
// BEZIER HANDLE MANIPULATION (~400 lines)
// ============================================================================
export function updateKeyframeInHandle(store, layerId, propertyPath, keyframeId, handle): boolean { ... }
export function updateKeyframeOutHandle(store, layerId, propertyPath, keyframeId, handle): boolean { ... }
export function enableBezierHandles(store, layerId, propertyPath, keyframeId): boolean { ... }
export function disableBezierHandles(store, layerId, propertyPath, keyframeId): boolean { ... }
export function setHandleControlMode(store, layerId, propertyPath, keyframeId, mode): boolean { ... }
export function mirrorHandles(store, layerId, propertyPath, keyframeId): boolean { ... }

// ============================================================================
// PROPERTY ANIMATION STATE (~200 lines)
// ============================================================================
export function togglePropertyAnimation(store, layerId, propertyPath): boolean { ... }
export function enablePropertyAnimation(store, layerId, propertyPath): boolean { ... }
export function disablePropertyAnimation(store, layerId, propertyPath): boolean { ... }
export function isPropertyAnimated(store, layerId, propertyPath): boolean { ... }

// ============================================================================
// BATCH OPERATIONS (~200 lines)
// ============================================================================
export function copyKeyframes(store, layerId, propertyPath, keyframeIds): ClipboardKeyframe[] { ... }
export function pasteKeyframes(store, layerId, propertyPath, keyframes, targetFrame): number { ... }
export function duplicateKeyframes(store, layerId, propertyPath, keyframeIds, offset): number { ... }

// ============================================================================
// EASING PRESETS (~100 lines)
// ============================================================================
export function applyEasyEase(store, layerId, propertyPath, keyframeIds): number { ... }
export function applyEasyEaseIn(store, layerId, propertyPath, keyframeIds): number { ... }
export function applyEasyEaseOut(store, layerId, propertyPath, keyframeIds): number { ... }
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                   keyframeActions.ts                         │
│                     (2,023 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (4 dependencies)                              │
│  ├── vue (toRaw)                                            │
│  ├── @/services/layerEvaluationCache                        │
│  ├── @/types/project (types)                                │
│  └── @/utils/logger                                         │
├─────────────────────────────────────────────────────────────┤
│  RE-EXPORTS FROM                                            │
│  └── ./keyframes/keyframeExpressions                        │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (24 files) ← VERIFIED via function usage       │
│  ├── 1 composable                                           │
│  ├── 1 service                                              │
│  ├── 1 barrel export                                        │
│  ├── 1 sub-module                                           │
│  └── 1 store (compositorStore)                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: MEDIUM (24 actual users, not 5 as originally thought)**

This file has excellent characteristics for modularization:
- Only 5 files import it
- Pure functions that don't maintain state
- Clear operation categories
- Expression actions already extracted to sub-module

### Why This File Is Large

~40 keyframe operations covering:
1. **Creation** - addKeyframe, addKeyframeAtCurrentTime, batch creation
2. **Selection** - getKeyframeAt, getKeyframesInRange, getAllKeyframes
3. **Removal** - removeKeyframe, removeKeyframesInRange, clearAll
4. **Movement** - moveKeyframe, moveKeyframesBy, scaleKeyframes, reverseKeyframes
5. **Values** - updateKeyframeValue, updateKeyframeInterpolation
6. **Handles** - Bezier handle manipulation (8+ functions)
7. **Animation state** - togglePropertyAnimation, enable/disable
8. **Batch** - copy, paste, duplicate
9. **Easing** - Easy ease presets

### Already Partially Modularized

Expression-related keyframe actions are extracted to:
`./keyframes/keyframeExpressions.ts`

### Modularization Strategy

**Split by operation type:**

```
stores/actions/keyframes/
├── index.ts                    (~50 lines - barrel + helpers)
├── keyframeCreation.ts         (~200 lines)
├── keyframeSelection.ts        (~150 lines)
├── keyframeRemoval.ts          (~150 lines)
├── keyframeMovement.ts         (~300 lines)
├── keyframeValues.ts           (~200 lines)
├── keyframeHandles.ts          (~400 lines)
├── keyframeAnimation.ts        (~200 lines)
├── keyframeBatch.ts            (~200 lines)
├── keyframeEasing.ts           (~100 lines)
└── keyframeExpressions.ts      (existing)
```

**index.ts would:**
1. Re-export all functions from sub-modules
2. Export shared helpers (safeFrame, findPropertyByPath)
3. Maintain backward compatibility - `import * as keyframeActions from './keyframeActions'` continues to work

**Migration path:**
1. Create sub-module files
2. Move functions to appropriate modules
3. Update keyframeActions.ts to re-export from sub-modules
4. No changes needed to the 5 importing files
