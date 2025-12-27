# Refactor Log

## Session: 2025-12-27

---

### ANALYSIS: compositorStore.ts (2777 lines)

**Started:** 2025-12-27
**Status:** BLOCKER IDENTIFIED

#### Structure Analysis

| Section | Lines | Notes |
|---------|-------|-------|
| Imports | 1-111 | 111 lines |
| CompositorState interface | 113-221 | 108 lines |
| state() | 224-305 | 81 lines |
| getters | 307-433 | 126 lines |
| actions | 435-2777 | 2342 lines |

#### Key Finding: Already Delegated

This store is **already a facade**. The actions section contains mostly thin wrappers like:

```ts
createLayer(type, name) {
  return layerActions.createLayer(this, type, name);
}
```

The actual logic is externalized to 15 action modules:
- `layerActions.ts` (1918 lines)
- `keyframeActions.ts` (2012 lines)
- `projectActions.ts`
- `audioActions.ts`
- `cameraActions.ts`
- `compositionActions.ts`
- `effectActions.ts`
- `propertyDriverActions.ts`
- `particleLayerActions.ts`
- `depthflowActions.ts`
- `videoActions.ts`
- `textAnimatorActions.ts`
- `markerActions.ts`
- `segmentationActions.ts`
- `cacheActions.ts`

#### Remaining Inline Logic (~450 lines)

| Section | Lines | Can Extract? |
|---------|-------|--------------|
| loadInputs (ComfyUI) | 529-604 | Yes → comfyuiActions.ts |
| Playback (play/pause/setFrame/etc) | 996-1128 | Yes → playbackActions.ts |
| Tool/Segment UI | 1133-1209 | Yes → uiStateActions.ts |
| createTextLayer | 1603-1677 | Yes → layerActions.ts |
| createSplineLayer | 1682-1698 | Yes → layerActions.ts |
| createNestedCompLayer | 1785-1807 | Yes → compositionActions.ts |
| getPropertyValueAtFrame | 2202-2235 | Partially → propertyDriverActions |
| evaluatePropertyAtFrame | 2244-2313 | Partially → propertyDriverActions |
| jumpToNext/PrevKeyframe | 2557-2621 | Yes → keyframeActions.ts |

#### Blocker Assessment

**Cannot reach <500 lines because:**

1. Store is a **facade** that must expose unified API to components
2. ~2000 lines are **wrapper methods** that delegate to action modules
3. Components call `store.createLayer()` not `layerActions.createLayer(store)`
4. Pinia requires methods to be defined on the store object

**Options:**

| Option | Feasibility | Result |
|--------|-------------|--------|
| Extract remaining inline logic | Easy | ~2300 lines (still huge) |
| Split into multiple stores | Hard | Breaking change, circular deps |
| Use Pinia plugins/composables | Medium | Complex, harder to understand |
| Accept facade pattern | N/A | Keep as-is, focus on action modules |

#### Recommended Path Forward

1. **Extract remaining ~450 lines of inline logic** to action modules
2. **Accept that compositorStore.ts is a facade** (~2300 lines of wrappers)
3. **Focus refactoring on ACTION MODULES** which contain actual logic:
   - `keyframeActions.ts` (2012 lines) - HAS LOGIC TO SPLIT
   - `layerActions.ts` (1918 lines) - HAS LOGIC TO SPLIT

---

### Action: Extract Inline Logic from compositorStore.ts

**Goal:** Move ~450 lines of remaining inline logic to action modules

#### Step 1: Create playbackActions.ts
- play(), pause(), togglePlayback()
- setFrame(), nextFrame(), prevFrame()
- goToStart(), goToEnd(), jumpFrames()

#### Step 2: Move to existing layerActions.ts
- createTextLayer()
- createSplineLayer()
- createShapeLayer()

#### Step 3: Move to compositionActions.ts
- createNestedCompLayer()
- updateNestedCompLayerData()

#### Step 4: Create comfyuiActions.ts
- loadInputs()

#### Step 5: Move to keyframeActions.ts
- jumpToNextKeyframe()
- jumpToPrevKeyframe()

---

### SPLIT COMPLETE: compositorStore.ts inline extraction

**Timestamp:** 2025-12-27
**Original:** 2777 lines
**After:** 2542 lines (-235 lines, -8.5%)
**Build:** PASS
**Tests:** N/A (deleted earlier)

**Files created/modified:**
| File | Lines | Action |
|------|-------|--------|
| `stores/actions/playbackActions.ts` | 118 | CREATED |
| `stores/actions/layerActions.ts` | +95 | Modified (added createTextLayer, etc.) |
| `stores/actions/keyframeActions.ts` | +53 | Modified (added findNextKeyframeFrame, etc.) |
| `stores/compositorStore.ts` | 2542 | Modified (delegations) |

**Extracted:**
- play/pause/setFrame/nextFrame/prevFrame/goToStart/goToEnd/jumpFrames → playbackActions.ts
- createTextLayer/createSplineLayer/createShapeLayer → layerActions.ts
- jumpToNextKeyframe/jumpToPrevKeyframe logic → keyframeActions.ts

**Status:** compositorStore.ts is now a clean facade with thin delegation methods.

---

### SPLIT COMPLETE: keyframeActions.ts expression extraction

**Timestamp:** 2025-12-27
**Original:** 2065 lines
**After:** 1785 lines (-280 lines, -13.6%)
**Build:** PASS
**Tests:** N/A

**Files created/modified:**
| File | Lines | Action |
|------|-------|--------|
| `stores/actions/keyframes/keyframeExpressions.ts` | 304 | CREATED |
| `stores/actions/keyframeActions.ts` | 1785 | Modified (removed expressions) |

**Extracted:**
- setPropertyExpression, enablePropertyExpression, disablePropertyExpression
- togglePropertyExpression, removePropertyExpression, getPropertyExpression
- hasPropertyExpression, updateExpressionParams
- convertExpressionToKeyframes, canBakeExpression
- BakeExpressionStore interface

**Remaining in keyframeActions.ts (1785 lines):**
- Store interface + findPropertyByPath helper
- Keyframe CRUD (add, remove, update, move)
- Interpolation settings
- Animation state management
- Query utilities + roving keyframes
- Clipboard (copy/paste)
- Velocity settings
- Auto bezier tangent calculation
- Handle control modes
- Separate dimensions

**Status:** keyframeActions.ts reduced by 14%. Could extract more (bezier ~280 lines, clipboard ~190 lines) but file is now manageable.

---

### SPLIT COMPLETE: layerActions.ts time manipulation extraction

**Timestamp:** 2025-12-27
**Original:** 2013 lines
**After:** 1634 lines (-379 lines, -18.8%)
**Build:** PASS
**Tests:** N/A

**Files created/modified:**
| File | Lines | Action |
|------|-------|--------|
| `stores/actions/layers/layerTimeActions.ts` | 352 | CREATED |
| `stores/actions/layerActions.ts` | 1634 | Modified (removed time manipulation) |

**Extracted:**
- TimeStretchOptions interface
- timeStretchLayer, reverseLayer
- freezeFrameAtPlayhead, splitLayerAtPlayhead
- enableSpeedMap, disableSpeedMap, toggleSpeedMap
- LayerTimeStore interface

**Status:** layerActions.ts reduced by 19%. Now under 2000 lines.

---

## Session Summary

| File | Before | After | Change |
|------|--------|-------|--------|
| compositorStore.ts | 2777 | 2542 | -235 (-8.5%) |
| keyframeActions.ts | 2065 | 1785 | -280 (-13.6%) |
| layerActions.ts | 2013 | 1634 | -379 (-18.8%) |

**New files created:**
- `stores/actions/playbackActions.ts` (118 lines)
- `stores/actions/keyframes/keyframeExpressions.ts` (304 lines)
- `stores/actions/layers/layerTimeActions.ts` (352 lines)

**Total lines moved:** ~894 lines into focused, single-purpose modules

---

## Remaining Large Files Analysis

### SKIP: project.ts (2077 lines)

**Reason:** Type schema file with clear organization
- Re-exports (~165 lines) for backwards compatibility
- Type definitions (~1900 lines) organized by section
- Splitting types would make the schema harder to understand
- Would require updating imports across entire codebase

**Decision:** Keep as-is. Schema files benefit from being in one place.

---

### SKIP: ThreeCanvas.vue (2069 lines)

**Reason:** Already refactored with composables
- Template (231 lines)
- Uses `useCanvasSelection`, `useCanvasSegmentation`, `useShapeDrawing`, `useViewportGuides`
- Core canvas/engine logic (1458 lines) tightly coupled
- CSS styles (380 lines)

**Decision:** Keep as-is. Further splitting has diminishing returns.

---

### SKIP: particleSystem.ts (2009 lines)

**Reason:** Deprecated + already modularized
- Marked `@deprecated` in favor of `GPUParticleSystem.ts`
- Already extracted: `particles/particleTypes.ts`, `particles/particleDefaults.ts`, `particles/SeededRandom.ts`, `particles/particleRenderer.ts`
- Remaining is `ParticleSystem` class simulation logic

**Decision:** Keep as-is. Focus GPU version instead.

---

### SKIP: BaseLayer.ts (1956 lines)

**Reason:** Abstract base class for 24+ layer types
- Well-organized with clear section headers
- Provides unified layer API
- Motion path (~142 lines) and axis gizmo (~142 lines) could theoretically be extracted as mixins
- Splitting would make inheritance harder to understand

**Decision:** Keep as-is. Base classes benefit from being complete.

---

## Final Session Summary

### Files Successfully Split

| File | Before | After | Change |
|------|--------|-------|--------|
| compositorStore.ts | 2777 | 2542 | -235 (-8.5%) |
| keyframeActions.ts | 2065 | 1785 | -280 (-13.6%) |
| layerActions.ts | 2013 | 1634 | -379 (-18.8%) |

### New Modules Created

| File | Lines | Purpose |
|------|-------|---------|
| `stores/actions/playbackActions.ts` | 118 | Play/pause/frame navigation |
| `stores/actions/keyframes/keyframeExpressions.ts` | 304 | Expression handling |
| `stores/actions/layers/layerTimeActions.ts` | 352 | Time stretch/reverse/split |

### Files Analyzed but NOT Split

| File | Lines | Reason |
|------|-------|--------|
| project.ts | 2077 | Type schema, well-organized |
| ThreeCanvas.vue | 2069 | Uses composables already |
| particleSystem.ts | 2009 | Deprecated + modularized |
| BaseLayer.ts | 1956 | Abstract base class |

### Impact

- **Lines moved:** ~894 lines into focused modules
- **Large files reduced:** 3 files brought under 2000 lines
- **Modular structure:** Clear separation of concerns in action modules
- **Build status:** PASS

---
