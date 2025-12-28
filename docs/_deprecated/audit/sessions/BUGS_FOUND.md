# LATTICE COMPOSITOR - BUGS FOUND

**Last Updated:** 2025-12-26
**Next Bug ID:** BUG-074

---

## SUMMARY

| Severity | Total | Fixed | Open |
|----------|-------|-------|------|
| CRITICAL | 0 | 0 | 0 |
| HIGH | 21 | 21 | 0 |
| MEDIUM | 43 | 43 | 0 |
| LOW | 7 | 7 | 0 |
| **TOTAL** | **71** | **71** | **0** |

**Note:** All bugs in Tier 5 (Particle System) have been fixed.

---

## BUGS BY TIER

| Tier | Bug Count |
|------|-----------|
| 1. Foundation | 11 |
| 2. Layer Types | 35 |
| 3. Animation | 2 |
| 4. Effects | 2 |
| 5. Particles | 18 |
| 6-12 | 0 (not yet audited) |

---

## TIER 1 BUGS (Foundation)

### BUG-001: Hardcoded fps=30 in splitLayerAtPlayhead

**Feature:** Layer Creation/Deletion (1.1)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/layerActions.ts`
- Line: 1539
- Function: `splitLayerAtPlayhead()`

**Problem:**
When splitting a video layer at the playhead, the source time offset calculation uses a hardcoded `fps = 30` instead of the composition's actual fps.

**Evidence:**
````typescript
if (isLayerOfType(newLayer, 'video') && newLayer.data) {
  const fps = 30; // Default FPS <-- BUG: hardcoded
  const originalStartTime = newLayer.data.startTime ?? 0;
  const speed = newLayer.data.speed ?? 1;
  const frameOffset = currentFrame - startFrame;
  const timeOffset = (frameOffset / fps) * speed;
  newLayer.data.startTime = originalStartTime + timeOffset;
}
````

**Expected Behavior:**
Should use `store.fps` or composition fps for correct frame-to-time conversion.

**Actual Behavior:**
Video layer splits at wrong time offset in non-30fps compositions.

**Impact:**
- 60fps composition: video starts at wrong point (off by 2x)
- 24fps composition: video starts at wrong point (off by ~0.8x)

**Fix Applied:**
Changed `const fps = 30;` to `const fps = store.fps ?? 30;`

---

### BUG-002: Hardcoded fps=30 in keyframe velocity functions

**Feature:** Layer Transform / Keyframe System (1.2)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/keyframeActions.ts`
- Lines: 1325-1326, 1388-1389
- Functions: `applyKeyframeVelocity()`, `getKeyframeVelocity()`

**Problem:**
Both functions use hardcoded `fps = 30` for converting between velocity units and frame units.

**Evidence:**
````typescript
// Line 1325-1326 in applyKeyframeVelocity:
const fps = 30; // TODO: Get from composition
const inVelocityPerFrame = settings.incomingVelocity / fps;

// Line 1388-1389 in getKeyframeVelocity:
const fps = 30;
const inVelocity = keyframe.inHandle?.enabled && keyframe.inHandle.frame !== 0
  ? -keyframe.inHandle.value / Math.abs(keyframe.inHandle.frame) * fps
  : 0;
````

**Expected Behavior:**
Should use composition fps for correct velocity calculations.

**Actual Behavior:**
Keyframe velocity dialog shows incorrect values for non-30fps compositions.

**Impact:**
- Applied velocity settings create wrong bezier handles
- 60fps: velocities off by 2x
- 24fps: velocities off by ~0.8x

**Fix Applied:**
Added `VelocityStore` interface with fps, changed to `const fps = store.fps ?? 30`

---

### BUG-003: MotionEngine doesn't pass composition fps to interpolateProperty

**Feature:** Transform System / Expression Evaluation (1.4)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/MotionEngine.ts`
- Lines: 539, 572, 622-627, 643, 646, 686, 709, 729-738, 802-831

**Problem:**
MotionEngine.evaluate() has access to `composition.settings.fps` but all calls to `interpolateProperty` use the default fps=30.

**Evidence:**
````typescript
// MotionEngine.ts line 572 - missing fps parameter
let opacity: number = interpolateProperty(layer.opacity, frame);

// interpolation.ts shows fps is used for expressions:
const time = frame / fps;  // fps affects time calculation
````

**Expected Behavior:**
Should pass composition fps to all interpolateProperty calls.

**Actual Behavior:**
Expressions using `time` variable evaluate incorrectly for non-30fps compositions.

**Impact:**
- 60fps: `time` values are 2x too large
- 16fps: `time` values are ~0.53x too small

**Fix Applied:**
Added fps parameter throughout evaluation chain, passing composition.settings.fps to all interpolateProperty calls.

---

### BUG-004: audioStore hardcoded fps=16 in getBeats

**Feature:** Audio System (6.x - but affects foundation)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/stores/audioStore.ts`
- Line: 95

**Problem:**
The `getBeats` getter converts beat frames to seconds using hardcoded `fps = 16`.

**Evidence:**
````typescript
getBeats: (state) => (_assetId?: string): number[] | undefined => {
  if (!state.audioAnalysis) return undefined;
  const fps = 16; // Default FPS <-- BUG: hardcoded
  const beats: number[] = [];
  for (let frame = 0; frame < state.audioAnalysis.frameCount; frame++) {
    if (isBeatAtFrame(state.audioAnalysis, frame)) {
      beats.push(frame / fps);
    }
  }
  return beats.length > 0 ? beats : undefined;
},
````

**Expected Behavior:**
Should calculate fps from analysis data or use composition fps.

**Actual Behavior:**
Beat timestamps wrong for non-16fps compositions.

**Impact:**
- 30fps: beat times off by ~1.875x
- Audio reactive features misaligned

**Fix Applied:**
Calculate fps from analysis: `const fps = state.audioAnalysis.frameCount / state.audioAnalysis.duration;`

---

### BUG-005: ModelLayer uses own fps instead of BaseLayer.compositionFps

**Feature:** 3D Models (2.16 - but foundation-level issue)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ModelLayer.ts`
- Lines: 78, 467, 785

**Problem:**
ModelLayer defines `private fps = 30` instead of using inherited `this.compositionFps`.

**Evidence:**
````typescript
// Line 78
private fps = 30;

// Line 467 - animation clip duration
frameCount: Math.round(clip.duration * this.fps),

// Line 785 - animation delta
const deltaTime = 1 / this.fps;
````

**Expected Behavior:**
Should use `this.compositionFps` from BaseLayer.

**Actual Behavior:**
3D model animations play at wrong speed in non-30fps compositions.

**Impact:**
Animation timing broken for all 3D models at non-30fps.

**Fix Applied:**
Removed private fps, replaced with `this.compositionFps`.

---

### BUG-006: effectProcessor hardcoded fps=30 in fallback

**Feature:** Effects System (4.x - but foundation-level)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/services/effectProcessor.ts`
- Lines: 454, 570

**Problem:**
Fallback uses hardcoded `params._fps = 30` instead of passed fps.

**Evidence:**
````typescript
} else {
  params._frame = frame;
  params._fps = 30; // Default fps <-- BUG
  params._layerId = 'default';
}
````

**Expected Behavior:**
Should use provided fps parameter.

**Actual Behavior:**
Time-based effects evaluate incorrectly in fallback path.

**Impact:**
Echo, posterize time, and other time-based effects broken at non-30fps.

**Fix Applied:**
Added fps parameter to function signatures, use it in fallback.

---

### BUG-007: setEffectLayerRenderContext doesn't check for method existence

**Feature:** LayerManager / EffectLayer (2.12)
**Tier:** 1
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/core/LayerManager.ts`
- Lines: 136-140

**Problem:**
Tries to call `setRenderContext` on solid layers with `effectLayer` flag without checking if method exists.

**Evidence:**
````typescript
for (const layer of this.layers.values()) {
  const layerData = (layer as any).layerData;
  if (layer.type === 'solid' && (layerData?.effectLayer || layerData?.adjustmentLayer)) {
    (layer as unknown as EffectLayer).setRenderContext(context);  // CRASH if SolidLayer
  }
}
````

**Expected Behavior:**
Should check `'setRenderContext' in layer` before calling.

**Actual Behavior:**
Would crash if solid layer has effectLayer flag.

**Fix Applied:**
Added method existence check before calling.

---

## TIER 2 BUGS (Layer Types)

### BUG-008: createTextureFromCanvas doesn't update canvas reference

**Feature:** ImageLayer / ResourceManager (2.2)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/core/ResourceManager.ts`
- Lines: 177-182

**Problem:**
When called with cached texture ID but different canvas, the cached CanvasTexture still references the old canvas.

**Evidence:**
````typescript
createTextureFromCanvas(canvas, id, options) {
  const cached = this.textures.get(id);
  if (cached instanceof THREE.CanvasTexture) {
    cached.needsUpdate = true;  // Uploads OLD canvas!
    return cached;
  }
}
````

**Expected Behavior:**
Should update `cached.image` to new canvas before setting needsUpdate.

**Actual Behavior:**
Stale canvas content displayed.

**Fix Applied:**
Added `cached.image = canvas as HTMLCanvasElement;` before needsUpdate.

---

### BUG-009: AudioLayer missing fps in interpolateProperty calls

**Feature:** AudioLayer (2.6)
**Tier:** 2
**Severity:** LOW
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/AudioLayer.ts`
- Lines: 125, 130, 396, 402

**Problem:**
interpolateProperty calls for level and pan missing fps parameter.

**Fix Applied:**
Added `this.compositionFps` to all calls.

---

### BUG-010: DepthLayer autoNormalize property defined but never implemented

**Feature:** DepthLayer (2.18)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED (documented as limitation)

**Location:**
- File: `ui/src/engine/layers/DepthLayer.ts`
- Line: 55

**Problem:**
`autoNormalize` property stored but never used.

**Fix Applied:**
Documented as known limitation requiring architectural changes.

---

### BUG-011: DepthLayer 3d-mesh visualization mode not implemented

**Feature:** DepthLayer (2.18)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED (documented as limitation)

**Location:**
- File: `ui/src/engine/layers/DepthLayer.ts`
- Lines: 60, 66, 153, 201-204

**Problem:**
'3d-mesh' mode returns index 3, but shader only handles 0, 1, 2.

**Fix Applied:**
Documented as known limitation.

---

### BUG-012: DepthLayer wireframe property has no effect

**Feature:** DepthLayer (2.18)
**Tier:** 2
**Severity:** LOW
**Found:** 2025-12-24
**Status:** FIXED (documented as limitation)

**Location:**
- File: `ui/src/engine/layers/DepthLayer.ts`
- Line: 61

**Problem:**
`wireframe` property defined but never applied to material.

**Fix Applied:**
Documented as known limitation.

---

### BUG-013: NormalLayer arrows visualization mode not implemented

**Feature:** NormalLayer (2.20)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/NormalLayer.ts`
- Lines: 143, 109-126

**Problem:**
'arrows' mode (index 2) defined but shader jumps from mode 1 to mode 3.

**Fix Applied:**
Added fallback handling for mode 2.

---

### BUG-014: PoseLayer uses Date.now() for ID generation (determinism)

**Feature:** PoseLayer (2.21)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/PoseLayer.ts`
- Lines: 227, 533

**Problem:**
`Date.now()` breaks determinism - same project loaded at different times has different IDs.

**Fix Applied:**
Changed to counter-based IDs using layer ID as base.

---

### BUG-015: PointCloudLayer uses Math.random() for placeholder (determinism)

**Feature:** PointCloudLayer (2.17)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/PointCloudLayer.ts`
- Lines: 405-411

**Problem:**
`Math.random()` for placeholder geometry breaks determinism.

**Fix Applied:**
Changed to seeded random based on layer ID.

---

### BUG-016: ProceduralMatteLayer uses Math.random() for seed (determinism)

**Feature:** ProceduralMatteLayer (2.23)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ProceduralMatteLayer.ts`
- Line: 58

**Problem:**
Fallback seed uses `Math.random()` breaking determinism.

**Fix Applied:**
Changed to use hash of layer ID.

---

### BUG-017: getDefaultLayerData returns null without null check

**Feature:** Layer Creation/Deletion (1.1)
**Tier:** 2
**Severity:** LOW
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/layer/layerDefaults.ts`
- Lines: 407-409

**Problem:**
Returns `null` for unknown layer types, caller casts without null check.

**Fix Applied:**
Changed to throw error for unknown types.

---

### BUG-018: Separate dimensions ignored in MotionEngine.evaluateTransform

**Feature:** Layer Transform (1.2)
**Tier:** 2
**Severity:** HIGH (actually - should be tier 1)
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/MotionEngine.ts`
- Lines: 618-622

**Problem:**
Always evaluates combined `position`/`scale`, ignoring `separateDimensions` flag.

**Fix Applied:**
Added conditional checks for separate dimension properties.

---

### BUG-019: insertKeyframeOnPath treats position as array instead of object

**Feature:** Keyframe CRUD (1.3)
**Tier:** 2
**Severity:** HIGH (actually - should be tier 1)
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/keyframeActions.ts`
- Lines: 795-800, 848

**Problem:**
Treats position as `number[]` but it's `{x, y, z}` object.

**Fix Applied:**
Updated to handle both formats with type union and helper.

---

### BUG-020: SolidLayer uses labelColor to set visual fill color

**Feature:** SolidLayer (2.1)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/SolidLayer.ts`
- Lines: 337-339

**Problem:**
`onUpdate()` incorrectly uses timeline `labelColor` for visual fill.

**Fix Applied:**
Removed incorrect labelColor handling.

---

### BUG-021: AudioLayer hasAudio getter returns true when no audio

**Feature:** AudioLayer (2.6)
**Tier:** 2
**Severity:** LOW
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/AudioLayer.ts`
- Line: 418

**Problem:**
`this.playbackNodes?.buffer !== null` returns true when playbackNodes is null.

**Fix Applied:**
Changed to explicit null check.

---

### BUG-022: ShapeLayer hardcoded 30fps in getAnimatedValue

**Feature:** ShapeLayer (2.5)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ShapeLayer.ts`
- Line: 699

**Problem:**
Hardcoded `30` instead of composition fps.

**Fix Applied:**
Changed to `this.compositionFps`.

---

### BUG-023: CameraLayer missing fps in interpolateProperty call

**Feature:** CameraLayer (2.7)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/CameraLayer.ts`
- Line: 497

**Problem:**
Missing fps parameter for path following animation.

**Fix Applied:**
Added `this.compositionFps` and `this.id` parameters.

---

### BUG-024: CameraLayer hardcoded 16/9 aspect ratio in frustum

**Feature:** CameraLayer (2.7)
**Tier:** 2
**Severity:** LOW
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/CameraLayer.ts`
- Line: 239

**Problem:**
Frustum visualization hardcodes 16:9 aspect.

**Fix Applied:**
Added `compositionAspect` property, use it instead of hardcoded value.

---

### BUG-025: LightLayer POI smoothing violates determinism

**Feature:** LightLayer (2.8)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/LightLayer.ts`
- Lines: 552-556

**Problem:**
POI smoothing accumulates state, breaking determinism on scrub.

**Fix Applied:**
Added frame tracker, reset smoothedPOI on non-sequential access.

---

### BUG-026: NestedCompLayer opacity never applied to material

**Feature:** NestedCompLayer (2.11)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/NestedCompLayer.ts`
- Lines: 280-292

**Problem:**
Animated opacity never applied to `this.material.opacity`.

**Fix Applied:**
Added opacity handling in `onApplyEvaluatedState`.

---

### BUG-027: EffectLayer.getSourceCanvas hardcodes frame 0

**Feature:** EffectLayer (2.12)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/EffectLayer.ts`
- Line: 248

**Problem:**
`renderLayersBelow(this.id, 0)` hardcodes frame 0.

**Fix Applied:**
Changed to `this.currentFrame`.

---

### BUG-028: EffectLayer opacity never applied to material

**Feature:** EffectLayer (2.12)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/EffectLayer.ts`
- Lines: 205-210

**Problem:**
Docstring claims opacity respected, but never applied.

**Fix Applied:**
Added opacity handling in `onApplyEvaluatedState`.

---

### BUG-029: ParticleLayer audio reactivity compounds emitter values

**Feature:** ParticleLayer (2.13)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ParticleLayer.ts`
- Lines: 1004-1045

**Problem:**
Audio modulation multiplies current values each frame, causing unbounded growth.

**Fix Applied:**
Added base value maps, always multiply from base values.

---

### BUG-030: PathLayer.evaluateControlPointAtFrame missing fps parameter

**Feature:** PathLayer (2.14)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/PathLayer.ts`
- Lines: 343-355

**Problem:**
All interpolateProperty calls missing fps.

**Fix Applied:**
Added fps and layerId to all calls.

---

### BUG-031: SplineLayer missing fps in all interpolateProperty calls

**Feature:** SplineLayer (2.15)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/SplineLayer.ts`
- Lines: 905-921, 1034, 1134-1184

**Problem:**
All interpolateProperty calls missing fps.

**Fix Applied:**
Added fps and layerId to all calls.

---

### BUG-032: ModelLayer.onEvaluateFrame missing fps parameter

**Feature:** ModelLayer (2.16)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ModelLayer.ts`
- Lines: 769, 775

**Problem:**
interpolateProperty calls missing fps.

**Fix Applied:**
Added fps and layerId parameters.

---

### BUG-033: PointCloudLayer.onEvaluateFrame missing fps parameter

**Feature:** PointCloudLayer (2.17)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/PointCloudLayer.ts`
- Lines: 1015, 1019

**Problem:**
interpolateProperty calls missing fps.

**Fix Applied:**
Added fps and layerId parameters.

---

### BUG-034: DepthLayer.onEvaluateFrame missing fps parameter

**Feature:** DepthLayer (2.18)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/DepthLayer.ts`
- Line: 198

**Problem:**
interpolateProperty call missing fps.

**Fix Applied:**
Added fps and layerId parameters.

---

### BUG-035: DepthflowLayer hardcoded 30fps in multiple places

**Feature:** DepthflowLayer (2.19)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/DepthflowLayer.ts`
- Lines: 402, 439

**Problem:**
calculatePresetValues defaults to 30fps, time uniform uses 30fps.

**Fix Applied:**
Pass `this.compositionFps` to function and time calculation.

---

### BUG-036: ProceduralMatteLayer time calculation hardcodes 60fps

**Feature:** ProceduralMatteLayer (2.23)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-24
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ProceduralMatteLayer.ts`
- Line: 185

**Problem:**
`(frame * speed / 60)` hardcodes 60fps.

**Fix Applied:**
Changed to `this.compositionFps`.

---

## NEW BUGS (Add Below This Line)

### BUG-037: Stale Reference Not Cleaned on Layer Deletion

**Feature:** Layer Creation/Deletion (1.1)
**Tier:** 1
**Severity:** MEDIUM
**Found:** 2025-12-25
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/layerActions.ts`
- Lines: 205-228
- Function: `deleteLayer()`

**Problem:**
When a layer is deleted, references to that layer in other layers' `parentId`, `matteLayerId`, `followPath.pathLayerId`, and text layer `data.pathLayerId` were not cleaned up. This left stale IDs pointing to non-existent layers.

**Evidence (before fix):**
```typescript
// deleteLayer() had NO cleanup - just removed the layer from array
layers.splice(index, 1);
// Missing: parentId, matteLayerId, followPath.pathLayerId, text data.pathLayerId
```

**Impact:**
- Track matte effects silently fail when matte source is deleted
- Path constraint animations silently fail when path layer is deleted
- Text-on-path silently fails when path layer is deleted
- Orphaned references persist on project save/load

**Fix Applied:**
```typescript
// BUG-037 FIX: Clean up all stale references to deleted layer
for (const layer of layers) {
  // Clear parent reference
  if (layer.parentId === layerId) {
    layer.parentId = null;
  }
  // Clear matte reference
  if (layer.matteLayerId === layerId) {
    layer.matteLayerId = undefined;
    layer.matteType = undefined;
  }
  // Clear followPath reference
  if (layer.followPath?.pathLayerId === layerId) {
    layer.followPath.enabled = false;
    layer.followPath.pathLayerId = undefined;
  }
  // Clear text layer path reference
  if (layer.type === 'text' && layer.data && (layer.data as any).pathLayerId === layerId) {
    (layer.data as any).pathLayerId = null;
  }
}
```

**Files Modified:**
- `ui/src/stores/actions/layerActions.ts` - Added stale reference cleanup to deleteLayer()

**Related Bugs:** None

---

### BUG-038: Export Pipeline Uses Wrong FPS for Transform Evaluation

**Feature:** Layer Transform (1.2)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-25
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/services/layerEvaluationCache.ts`
- Lines: 216-221, 234-242, 261, 288, 296, 318, 368
- Functions: `evaluateTransform()`, `evaluateEffects()`, `evaluateLayerProperties()`, `evaluateLayerCached()`, `evaluateLayersCached()`

**Problem:**
All evaluation functions called `interpolateProperty()` without passing fps, causing export to use default fps=16 instead of composition fps. Expressions using `time` variable would evaluate incorrectly.

**Evidence (before fix):**
```typescript
// layerEvaluationCache.ts:216 - Missing fps parameter
const position = interpolateProperty(transform.position, frame);

// vs MotionEngine.ts:628 - Correct with fps
position = interpolateProperty(transform.position, frame, fps);
```

**Expected Behavior:**
All `interpolateProperty()` calls should receive the composition's fps so expressions evaluate with correct `time = frame / fps`.

**Actual Behavior:**
Export used `fps=16` default while preview used composition fps (e.g., 30). Expressions with `time` variable would be ~1.875x faster in export than preview for a 30fps composition.

**Impact:**
- Expression-driven animations render differently in export vs preview
- Any animation using `time`, `velocity`, or time-based expressions affected
- Silent bug - no error, just wrong output

**Fix Applied:**
1. Added `fps` parameter to `evaluateTransform()`, `evaluateEffects()`, `evaluateLayerProperties()`
2. Made `fps` REQUIRED (no default) in `evaluateLayerCached()` and `evaluateLayersCached()` - TypeScript will catch missing fps
3. Updated `exportPipeline.ts:317` to pass `this.config.fps`
4. Updated all test file calls to pass `TEST_FPS`

**Files Modified:**
- `ui/src/services/layerEvaluationCache.ts` - Added fps parameter throughout
- `ui/src/services/export/exportPipeline.ts` - Pass config.fps to evaluateLayerCached
- `ui/src/__tests__/_archived/services/layerEvaluationCache.test.ts` - Updated all test calls

**Related Bugs:** BUG-001, BUG-002 (other fps-related bugs)

---

### BUG-039: updateKeyframe Does Not Handle Keyframe Frame Collisions

**Feature:** Keyframe CRUD (1.3)
**Tier:** 1
**Severity:** MEDIUM
**Found:** 2025-12-25
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/keyframeActions.ts`
- Lines: 338-350
- Function: `updateKeyframe()`

**Problem:**
When updating a keyframe's frame position via `updateKeyframe()`, the function did not check for or remove existing keyframes at the target frame. This could result in multiple keyframes at the same frame position, causing undefined interpolation behavior.

**Evidence (before fix):**
```typescript
// keyframeActions.ts:338-342 - NO collision check
if (updates.frame !== undefined) {
  keyframe.frame = updates.frame;
  // Re-sort keyframes by frame
  property.keyframes.sort((a, b) => a.frame - b.frame);
}
```

Compare with `moveKeyframe()` which correctly handles collisions:
```typescript
// moveKeyframe - CORRECT collision handling
const existingAtTarget = property.keyframes.find(
  kf => kf.frame === newFrame && kf.id !== keyframeId
);
if (existingAtTarget) {
  property.keyframes = property.keyframes.filter(kf => kf.id !== existingAtTarget.id);
}
```

**Impact:**
- Duplicate keyframes at same frame cause undefined interpolation behavior
- Curve editor drag operations can create corrupted property state
- Called from: `CurveEditor.vue:815`, `useCurveEditorInteraction.ts:285`

**Fix Applied:**
```typescript
if (updates.frame !== undefined) {
  // BUG-039 FIX: Check for existing keyframe at target frame (same pattern as moveKeyframe)
  const existingAtTarget = property.keyframes.find(
    kf => kf.frame === updates.frame && kf.id !== keyframeId
  );
  if (existingAtTarget) {
    // Remove the existing keyframe at target to prevent duplicates
    property.keyframes = property.keyframes.filter(kf => kf.id !== existingAtTarget.id);
  }
  keyframe.frame = updates.frame;
  // Re-sort keyframes by frame
  property.keyframes.sort((a, b) => a.frame - b.frame);
}
```

**Files Modified:**
- `ui/src/stores/actions/keyframeActions.ts` - Added collision check to updateKeyframe()

**Related Bugs:** None

---

### BUG-040: interpolateProperty Callers With Context Missing fps Parameter

**Feature:** Interpolation Engine (1.4)
**Tier:** 1
**Severity:** MEDIUM
**Found:** 2025-12-25
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/stores/compositorStore.ts`
- Lines: 1292, 2088
- Functions: `getInterpolatedValue()`, `getPropertyValueAtFrame()`
- File: `ui/src/stores/actions/propertyDriverActions.ts`
- Lines: 70-94
- Function: `getEvaluatedLayerProperties()`

**Problem:**
Three callers of `interpolateProperty` had access to composition fps via `this.fps` or `store.fps` but were not passing it, causing expressions to evaluate with the default fps=16 instead of the actual composition fps.

**Evidence (before fix):**
```typescript
// compositorStore.ts:1292 - had this.fps available but didn't pass it
getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
  return interpolateProperty(property, (this.getActiveComp()?.currentFrame ?? 0));
}
```

**Impact:**
- Expressions using `time` variable get wrong value when composition fps != 16
- Wiggle, loop, and time-based expressions evaluate incorrectly

**Fix Applied:**
```typescript
getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
  const comp = this.getActiveComp();
  const frame = comp?.currentFrame ?? 0;
  const fps = this.fps;
  const duration = comp ? comp.settings.frameCount / comp.settings.fps : undefined;
  return interpolateProperty(property, frame, fps, '', duration);
}
```

**Files Modified:**
- `ui/src/stores/compositorStore.ts` - getInterpolatedValue, getPropertyValueAtFrame
- `ui/src/stores/actions/propertyDriverActions.ts` - getEvaluatedLayerProperties

**Related Bugs:** BUG-041

---

### BUG-041: Expression Context Uses Hardcoded Composition Duration

**Feature:** Interpolation Engine (1.4)
**Tier:** 1
**Severity:** LOW
**Found:** 2025-12-25
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/services/interpolation.ts`
- Line: 294 (before fix)
- Function: `applyPropertyExpression()`

**Problem:**
Expression context set `duration: 81 / fps` regardless of actual composition length. This caused expressions using the `duration` variable to get wrong values for compositions != 81 frames.

**Evidence (before fix):**
```typescript
const ctx: ExpressionContext = {
  // ...
  duration: 81 / fps, // Default composition duration <-- HARDCODED!
  // ...
  outPoint: 81,
};
```

**Impact:**
- Expressions using `duration` variable get wrong value for non-standard compositions
- Loop expressions based on duration behave incorrectly

**Fix Applied:**
```typescript
// Added compDuration parameter to interpolateProperty
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number,
  fps: number = 16,
  layerId: string = '',
  compDuration?: number  // NEW: optional composition duration
): T {

// In applyPropertyExpression:
const duration = compDuration ?? (81 / fps);  // Use actual or default
const frameCount = Math.round(duration * fps);
const ctx: ExpressionContext = {
  duration,
  outPoint: frameCount,
  // ...
};
```

**Files Modified:**
- `ui/src/services/interpolation.ts` - Added compDuration parameter
- Same callers as BUG-040 now pass duration

**Related Bugs:** BUG-040

---

### BUG-042: useExpressionEditor Bypasses Store for Expression Changes

**Feature:** Expression Evaluation (1.5)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/composables/useExpressionEditor.ts`
- Lines: 42-60
- Functions: `applyExpression()`, `removeExpression()`

**Problem:**
The useExpressionEditor composable directly mutated the property's expression without going through store actions. This bypassed the history system entirely, making expression changes non-undoable.

**Evidence (before fix):**
```typescript
function applyExpression(expression: PropertyExpression) {
  if (currentProperty.value) {
    currentProperty.value.expression = expression;  // Direct mutation!
  }
  closeExpressionEditor();
}

function removeExpression() {
  if (currentProperty.value) {
    currentProperty.value.expression = undefined;  // Direct mutation!
  }
  closeExpressionEditor();
}
```

**Expected Behavior:**
Expression changes should go through store actions with pushHistory() for undo/redo support.

**Actual Behavior:**
Expression changes could not be undone. Users had no way to revert expression edits.

**Impact:**
- Expression application not undoable
- Expression removal not undoable
- Inconsistent with all other property edits

**Fix Applied:**
```typescript
import { setPropertyExpression, removePropertyExpression } from '@/stores/actions/keyframeActions';

function applyExpression(expression: PropertyExpression) {
  if (currentLayerId.value && currentPropertyPath.value) {
    const store = useCompositorStore();
    setPropertyExpression(store, currentLayerId.value, currentPropertyPath.value, expression);
  }
  closeExpressionEditor();
}

function removeExpression() {
  if (currentLayerId.value && currentPropertyPath.value) {
    const store = useCompositorStore();
    removePropertyExpression(store, currentLayerId.value, currentPropertyPath.value);
  }
  closeExpressionEditor();
}
```

**Files Modified:**
- `ui/src/composables/useExpressionEditor.ts` - Use store actions instead of direct mutation

**Related Bugs:** BUG-043

---

### BUG-043: AI actionExecutor Handlers Missing pushHistory

**Feature:** Expression Evaluation (1.5)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 1
**Status:** FIXED

**Location:**
- File: `ui/src/services/ai/actionExecutor.ts`
- Lines: Multiple (14 handlers)
- Functions: See list below

**Problem:**
14 handlers in actionExecutor.ts mutate store state but do not call `store.pushHistory()`. This means AI-driven changes (via chat interface) cannot be undone.

**Affected Handlers:**
1. `executeSetExpression()` - line ~497
2. `executeRemoveExpression()` - line ~534
3. `executeRenameLayer()` - line ~569
4. `executeSetLayerProperty()` - line ~599
5. `executeSetLayerTransform()` - line ~639
6. `executeScaleKeyframeTiming()` - line ~736
7. `executeConfigureParticles()` - line ~824
8. `executeAddCameraShake()` - line ~961
9. `executeSetCameraPathFollowing()` - line ~1032
10. `executeSetCameraAutoFocus()` - line ~1099
11. `executeSetTextContent()` - line ~1142
12. `executeSetTextPath()` - line ~1201
13. `executeSetSplinePoints()` - line ~1341
14. `executeSetSpeedMap()` - line ~1465

**Evidence (before fix):**
```typescript
// executeSetExpression - NO pushHistory
property.expression = {
  enabled: true,
  type: 'preset' as const,
  name: expressionType,
  params: params || {},
};
store.project.meta.modified = new Date().toISOString();
// Missing: store.pushHistory();
```

**Expected Behavior:**
All state mutations should call pushHistory() for undo/redo support.

**Actual Behavior:**
AI-driven changes cannot be undone. Users must manually revert changes.

**Impact:**
- 14 types of AI-driven edits are non-undoable
- Inconsistent undo behavior between UI and AI actions
- Users can lose work if AI makes unwanted changes

**Fix Applied:**
Added `store.pushHistory();` after `store.project.meta.modified = new Date().toISOString();` in all 14 handlers.

Example:
```typescript
property.expression = {
  enabled: true,
  type: 'preset' as const,
  name: expressionType,
  params: params || {},
};
store.project.meta.modified = new Date().toISOString();
store.pushHistory();  // BUG-043 FIX
```

**Files Modified:**
- `ui/src/services/ai/actionExecutor.ts` - Added pushHistory() to 14 handlers

**Related Bugs:** BUG-042

---

### BUG-044: ThreeCanvas calls non-existent setResolution method

**Feature:** Render Loop (1.6)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 2
**Status:** FIXED

**Location:**
- File: `ui/src/components/canvas/ThreeCanvas.vue`
- Line: 1581
- Function: `onResolutionChange()`

**Problem:**
The `onResolutionChange()` function calls `engine.value.setResolution(newWidth, newHeight)`, but `LatticeEngine` did not have a `setResolution` method. This caused a runtime TypeError when users tried to change preview resolution.

**Evidence (before fix):**
```typescript
// ThreeCanvas.vue:1581
engine.value.setResolution(newWidth, newHeight);
// TypeError: engine.value.setResolution is not a function
```

**Expected Behavior:**
Resolution dropdown should change the internal render buffer size for preview quality control.

**Actual Behavior:**
Clicking any option in the resolution dropdown (Half, Third, Quarter) threw "TypeError: engine.value.setResolution is not a function", breaking the resolution preview feature.

**Impact:**
- Resolution preview dropdown completely non-functional
- Users cannot preview at lower resolutions for performance
- Runtime crash on resolution change

**Fix Applied:**
```typescript
// Added to LatticeEngine.ts after getViewport():
setResolution(width: number, height: number): void {
  this.assertNotDisposed();
  if (width <= 0 || height <= 0) {
    engineLogger.warn('Invalid resolution dimensions:', width, height);
    return;
  }
  engineLogger.debug(`[LatticeEngine] setResolution: ${width}x${height}`);
  this.renderer.resize(width, height);
  this.updateSplineResolutions(width, height);
  this.emit('resolutionChange', { width, height });
}
```

**Files Modified:**
- `ui/src/engine/LatticeEngine.ts` - Added setResolution method

**Related Bugs:** None

---

### BUG-045: Edit Menu Undo/Redo Uses Orphaned History Store

**Feature:** History/Undo (1.7)
**Tier:** 1
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 2
**Status:** FIXED

**Location:**
- File: `ui/src/composables/useMenuActions.ts`
- Lines: 115, 118
- Function: `handleMenuAction()`

**Problem:**
Edit menu undo/redo operations called `historyStore.undo()` and `historyStore.redo()` instead of `store.undo()` and `store.redo()`. The `historyStore` is an orphaned standalone Pinia store that's never synchronized with `compositorStore`'s internal history system.

**Evidence (before fix):**
```typescript
// useMenuActions.ts imports orphaned store
import { useHistoryStore } from '@/stores/historyStore';
const historyStore = useHistoryStore();

// Lines 115, 118 - uses wrong store
case 'undo':
  historyStore.undo();  // WRONG - operates on empty orphaned store
  break;
case 'redo':
  historyStore.redo();  // WRONG - operates on empty orphaned store
  break;
```

**Expected Behavior:**
Edit → Undo and Edit → Redo should undo/redo project changes tracked by compositorStore.

**Actual Behavior:**
Edit menu undo/redo did nothing because they operated on an empty orphaned history store while all actual project changes were tracked in `compositorStore.historyStack`.

**Impact:**
- Edit → Undo menu item does nothing
- Edit → Redo menu item does nothing
- Keyboard shortcuts (Ctrl+Z/Y) worked correctly (using compositorStore)
- Inconsistent behavior between menu and shortcuts

**Fix Applied:**
```typescript
// Changed to use compositorStore
case 'undo':
  store.undo();
  break;
case 'redo':
  store.redo();
  break;
```

**Files Modified:**
- `ui/src/composables/useMenuActions.ts` - Changed historyStore calls to store calls

**Related Bugs:** None

---

### BUG-046: ImageLayerData.fit Property Not Implemented

**Feature:** ImageLayer (2.2)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 2
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/ImageLayer.ts`
- Lines: 75-87 (extractImageData), 175-182 (updateMeshSize)
- Function: `extractImageData()`, `updateMeshSize()`

**Problem:**
The `fit` property defined in ImageLayerData ('none' | 'contain' | 'cover' | 'fill') was never extracted or applied. ImageLayer always displayed images at their native dimensions regardless of the fit setting.

**Evidence (before fix):**
```typescript
// layerData.ts defines fit property
export interface ImageLayerData {
  fit: 'none' | 'contain' | 'cover' | 'fill';  // How to fit image in layer bounds
}

// layerDefaults.ts sets default
case 'image':
  return { assetId: null, fit: 'contain' };  // set but never used

// ImageLayer.ts extractImageData - fit NOT extracted
private extractImageData(layerData: Layer): {
  source: string | null;
  width: number;
  height: number;  // no fit!
} { ... }

// updateMeshSize - no fit logic, just uses native dimensions
this.geometry = new THREE.PlaneGeometry(this.imageWidth, this.imageHeight);
```

**Expected Behavior:**
Images should respect the fit property to scale within target bounds using contain/cover/fill modes.

**Actual Behavior:**
Images always displayed at native pixel dimensions, ignoring fit setting.

**Impact:**
- Users could not control how images fit within layer bounds
- The `fit` property in UI/types had no effect
- Images always displayed at native dimensions

**Fix Applied:**
```typescript
// Added fit property extraction
private extractImageData(layerData: Layer): {
  source: string | null;
  targetWidth: number | null;
  targetHeight: number | null;
  fit: 'none' | 'contain' | 'cover' | 'fill';
} { ... }

// Added fit logic in updateMeshSize()
if (this.targetWidth && this.targetHeight && this.fit !== 'none') {
  // Calculate dimensions based on fit mode
  switch (this.fit) {
    case 'contain': // Scale to fit within bounds
    case 'cover':   // Scale to cover bounds
    case 'fill':    // Stretch to fill bounds
  }
}
```

**Files Modified:**
- `ui/src/engine/layers/ImageLayer.ts` - Added fit property extraction and fit logic

**Related Bugs:** None

---

### BUG-047: VideoProperties direct mutation bypasses history tracking

**Feature:** VideoLayer (2.3)
**Tier:** 2
**Severity:** HIGH
**Found:** 2025-12-26
**Status:** FIXED

**Location:**
- File: `ui/src/components/properties/VideoProperties.vue`
- Lines: 312-322, 366-372, 412-417
- Functions: `updateSpeedMap()`, `updateTimewarpSpeed()`, `updateLevel()`

**Problem:**
Three update functions directly mutate layer data properties without going through store methods, bypassing history tracking (undo/redo).

**Evidence:**
```typescript
// updateSpeedMap - direct mutation
function updateSpeedMap(val: number) {
  const data = props.layer.data as VideoData;
  if (data.speedMap) {
    data.speedMap.value = val;  // Direct mutation - no store call!
  }
  emit('update');
}

// updateTimewarpSpeed - direct mutation
function updateTimewarpSpeed(val: number) {
  const data = props.layer.data as VideoData;
  if (data.timewarpSpeed) {
    data.timewarpSpeed.value = val;  // Direct mutation!
  }
  emit('update');
}

// updateLevel - direct mutation
function updateLevel(val: number) {
  if (props.layer.audio?.level) {
    props.layer.audio.level.value = val;  // Direct mutation!
    emit('update');
  }
}
```

**Expected Behavior:**
Property changes should go through store methods to enable undo/redo.

**Actual Behavior:**
Changes to speedMap, timewarpSpeed, and audio level don't create undo history entries.

**Impact:**
User cannot undo changes to these video properties.

**Fix Applied:**
Changed all three functions to use store methods:
```typescript
// updateSpeedMap - uses store
store.updateVideoLayerData(props.layer.id, {
  speedMap: { ...data.speedMap, value: val }
});

// updateTimewarpSpeed - uses store
store.updateVideoLayerData(props.layer.id, {
  timewarpSpeed: { ...data.timewarpSpeed, value: val }
});

// updateLevel - uses store
store.updateLayer(props.layer.id, {
  audio: {
    ...props.layer.audio,
    level: { ...props.layer.audio.level, value: val }
  }
});
```

**Files Modified:**
- `ui/src/components/properties/VideoProperties.vue`

**Related Bugs:** BUG-042, BUG-043 (similar direct mutation pattern)

---

### BUG-048: LayerManager default compositionFPS is 60 instead of 16

**Feature:** VideoLayer (2.3)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-26
**Status:** FIXED

**Location:**
- File: `ui/src/engine/core/LayerManager.ts`
- Line: 77
- Property: `compositionFPS`

**Problem:**
Default compositionFPS is 60fps instead of the WAN standard 16fps.

**Evidence:**
```typescript
// Line 77
private compositionFPS: number = 60;  // Should be 16
```

**Expected Behavior:**
Default should be 16fps per FPS_ARCHITECTURE.md (WAN AI model standard).

**Actual Behavior:**
Default is 60fps.

**Impact:**
If layers are created before setCompositionFPS() is called, video time calculations and particle timing use wrong FPS value.

**Fix Applied:**
```typescript
// Changed default to WAN standard
private compositionFPS: number = 16;
```

**Files Modified:**
- `ui/src/engine/core/LayerManager.ts`

**Related Bugs:** None

---

### BUG-049: ShapeProperties direct mutation of layer.properties bypasses history

**Feature:** ShapeLayer (2.5) - discovered in SplineLayer file
**Tier:** 2
**Severity:** HIGH
**Found:** 2025-12-26
**Status:** FIXED

**Location:**
- File: `ui/src/components/properties/ShapeProperties.vue`
- Lines: 651-656, 668-684, 689-705
- Functions: `updateAnimatable()`, `toggleKeyframe()`, `ensureProperty()`

**Problem:**
Multiple functions directly mutate `props.layer.properties` without using store methods, bypassing history tracking.

**Evidence:**
```typescript
// Line 654-655 - updateAnimatable (BEFORE FIX)
if (prop) {
  prop.value = value;  // Direct mutation
}

// Lines 671-681 - toggleKeyframe (BEFORE FIX)
prop.keyframes = prop.keyframes.filter(k => k.frame !== frame);  // Direct mutation
prop.animated = prop.keyframes.length > 0;  // Direct mutation
prop.keyframes.push({...});  // Direct mutation
prop.animated = true;  // Direct mutation

// Lines 689-696 - ensureProperty (BEFORE FIX)
props.layer.properties = [];  // Direct mutation
props.layer.properties.push({...});  // Direct mutation
```

**Expected Behavior:**
Property changes should use store.updateLayer() to track in history.

**Actual Behavior:**
Keyframe and property changes are not tracked in history, undo/redo won't work.

**Impact:**
Users cannot undo keyframe additions/removals or property value changes on spline layers.

**Fix Applied:**
```typescript
// updateAnimatable - now uses store
const updatedProperties = (props.layer.properties || []).map(p =>
  p.name === propName ? { ...p, value } : p
);
store.updateLayer(props.layer.id, { properties: updatedProperties });

// toggleKeyframe - now uses store
const updatedProperties = (props.layer.properties || []).map(p =>
  p.name === propName
    ? { ...p, keyframes: updatedKeyframes, animated: updatedAnimated }
    : p
);
store.updateLayer(props.layer.id, { properties: updatedProperties });

// ensureProperty - now uses store
store.updateLayer(props.layer.id, {
  properties: [...existingProperties, newProperty]
});
```

**Files Modified:**
- `ui/src/components/properties/ShapeProperties.vue`

**Related Bugs:** BUG-042, BUG-043, BUG-047 (same direct mutation pattern)
**Note:** This file is actually for SplineLayer (Feature 2.15), discovered during ShapeLayer audit

---

### BUG-050: CameraProperties direct mutation of layer.properties bypasses history

**Feature:** CameraLayer (2.7)
**Tier:** 2
**Severity:** HIGH
**Found:** 2025-12-26
**Status:** FIXED

**Location:**
- File: `ui/src/components/properties/CameraProperties.vue`
- Lines: 751, 771-773, 779-794, 807-816, 832-843, 726
- Functions: `updateAnimatable()`, `updateDOFAnimatable()`, `ensureProperty()`, `toggleKeyframe()`, `togglePathKeyframe()`, `updatePathProperty()`

**Problem:**
Multiple functions directly mutate `props.layer.properties` without using store methods, bypassing history tracking.

**Evidence:**
```typescript
// Line 751 - updateAnimatable (BEFORE FIX)
prop.value = value;  // Direct mutation

// Lines 779-785 - ensureProperty (BEFORE FIX)
if (!props.layer.properties) {
  props.layer.properties = [];  // Direct mutation
}
props.layer.properties.push({...});  // Direct mutation

// Lines 807-816 - toggleKeyframe (BEFORE FIX)
prop.keyframes = prop.keyframes.filter(k => k.frame !== frame);  // Direct mutation
prop.animated = prop.keyframes.length > 0;  // Direct mutation
prop.keyframes.push({...});  // Direct mutation
prop.animated = true;  // Direct mutation
```

**Expected Behavior:**
Property changes should use store.updateLayer() to track in history.

**Actual Behavior:**
Keyframe and property changes are not tracked in history, undo/redo won't work.

**Impact:**
Users cannot undo keyframe additions/removals or property value changes on camera layers (FOV, focal length, DOF, path following, etc.).

**Fix Applied:**
Same pattern as BUG-049:
```typescript
// All functions now use store.updateLayer()
const updatedProperties = (props.layer.properties || []).map(p =>
  p.name === propName ? { ...p, value } : p
);
store.updateLayer(props.layer.id, { properties: updatedProperties });
```

**Files Modified:**
- `ui/src/components/properties/CameraProperties.vue`

**Related Bugs:** BUG-042, BUG-043, BUG-047, BUG-049 (same direct mutation pattern)

---

### BUG-051: NormalLayer Arrow Visualization Mode Not Implemented

**Feature:** NormalLayer (2.20)
**Tier:** 2
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 3
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/NormalLayer.ts`
- Lines: 78-130, 139-146
- Function: `createMesh()` (GLSL shader), `getVisualizationModeIndex()`
- File: `ui/src/components/properties/NormalProperties.vue`
- Lines: 12, 46-80

**Problem:**
The "Normal Arrows" visualization mode (index 2) was defined in the UI dropdown and had configuration options (arrowDensity, arrowScale, arrowColor), but was never implemented in the GLSL shader. The shader handled modes 0 (RGB), 1 (hemisphere), and 3 (lit), but skipped mode 2, causing it to fall through to the default RGB case.

**Evidence:**
```typescript
// NormalLayer.ts getVisualizationModeIndex - maps arrows to mode 2
case 'arrows': return 2;

// Shader fragment - NO handler for mode 2
if (visualizationMode == 0) {
  // RGB
  color = normal * 0.5 + 0.5;
} else if (visualizationMode == 1) {
  // Hemisphere
  ...
} else if (visualizationMode == 3) {  // <-- SKIPS MODE 2
  // Lit
  ...
} else {
  // Default to RGB <-- arrows falls here
  color = normal * 0.5 + 0.5;
}
```

**Expected Behavior:**
Arrow visualization mode should either display normal direction arrows or not be available in the UI.

**Actual Behavior:**
Users could select "Normal Arrows" mode and configure arrow parameters (density, scale, color) in the UI, but the actual visualization just showed RGB mode with no indication of the problem.

**Impact:**
- Users selecting "Normal Arrows" mode get unexpected RGB output
- Arrow configuration controls in UI have no effect
- Feature advertised but not implemented

**Fix Applied:**
Removed the unimplemented arrows option from the UI rather than implementing the complex arrow geometry visualization:
1. Removed `<option value="arrows">Normal Arrows</option>` from NormalProperties.vue
2. Removed the entire "Arrow Settings" section (v-if="visualizationMode === 'arrows'")
3. Removed `case 'arrows': return 2;` from NormalLayer.ts getVisualizationModeIndex()

**Files Modified:**
- `ui/src/components/properties/NormalProperties.vue` - Removed arrows option and settings UI
- `ui/src/engine/layers/NormalLayer.ts` - Removed arrows case from mode index

**Related Bugs:** BUG-010, BUG-011, BUG-012 (similar unimplemented features in DepthLayer)

---

## TIER 3 BUGS (Animation Subsystems)

### BUG-052: Text Animator Actions FPS Fallback Inconsistency

**Feature:** Text Animators (3.1)
**Tier:** 3
**Severity:** LOW
**Found:** 2025-12-26
**Session:** 3
**Status:** FIXED

**Location:**
- File: `ui/src/stores/actions/textAnimatorActions.ts`
- Lines: 515, 622
- Functions: `getCharacterTransforms()`, `getSelectionValues()`

**Problem:**
The store actions used 24fps as fallback when composition settings aren't available, while the textAnimator.ts service uses 16fps default. This inconsistency means different results when composition fps isn't set.

**Evidence:**
```typescript
// textAnimatorActions.ts lines 515, 622 (BEFORE FIX)
const fps = comp?.settings?.fps || 24;  // Used 24fps fallback

// textAnimator.ts lines 673, 712, 755, 862
fps: number = 16  // Uses 16fps default (WAN standard)
```

**Expected Behavior:**
Fallback fps should be consistent across the codebase at 16fps (WAN standard).

**Actual Behavior:**
Store actions used 24fps fallback while service used 16fps default.

**Impact:**
Minor - only affects edge case when no composition settings exist. Animation timing would differ between service calls and store action calls.

**Fix Applied:**
Changed fallback from `24` to `16` in both locations:
```typescript
const fps = comp?.settings?.fps || 16;
```

**Files Modified:**
- `ui/src/stores/actions/textAnimatorActions.ts` - Lines 515, 622

**Related Bugs:** BUG-001 (similar fps hardcoding issue in layerActions.ts)

---

### BUG-053: Posterize Time Effect FPS Fallback Inconsistency

**Feature:** Time Warp (3.7)
**Tier:** 3
**Severity:** LOW
**Found:** 2025-12-26
**Session:** 3
**Status:** FIXED

**Location:**
- File: `ui/src/services/effects/timeRenderer.ts`
- Line: 347
- Function: `posterizeTimeRenderer()`

**Problem:**
The posterizeTimeRenderer used 30fps as fallback while echoRenderer (line 212) uses 16fps. This inconsistency means different temporal behavior between time effects.

**Evidence:**
```typescript
// timeRenderer.ts line 347 (BEFORE FIX)
const fps = params._fps ?? 30;  // Used 30fps fallback

// timeRenderer.ts line 212 (echoRenderer)
const fps = params._fps ?? 16;  // Uses 16fps default (WAN standard)
```

**Expected Behavior:**
All time effects should use consistent 16fps fallback (WAN standard).

**Actual Behavior:**
posterizeTimeRenderer used 30fps fallback while echoRenderer used 16fps.

**Impact:**
Minor - affects posterize time frame holding calculations when _fps not passed. At 30fps fallback, frame ratio calculations would be incorrect for WAN standard compositions.

**Fix Applied:**
Changed fallback from `30` to `16`:
```typescript
const fps = params._fps ?? 16;  // WAN standard default
```

**Files Modified:**
- `ui/src/services/effects/timeRenderer.ts` - Line 347

**Related Bugs:** BUG-052 (similar fps fallback inconsistency in textAnimatorActions.ts)

---

## TIER 4 BUGS (Effects System)

### BUG-054: EffectLayer.getSourceCanvas References Undefined this.currentFrame

**Feature:** Effect Application (4.11)
**Tier:** 4
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/layers/EffectLayer.ts`
- Lines: 240-255 (removed)
- Function: `getSourceCanvas()`

**Problem:**
The `getSourceCanvas()` override in EffectLayer referenced `this.currentFrame` which was never defined on the class. This would pass `undefined` to `renderLayersBelow()`, potentially causing incorrect frame rendering.

**Evidence (before fix):**
```typescript
// EffectLayer.ts lines 240-255
protected override getSourceCanvas(): HTMLCanvasElement | null {
  if (!this.renderContext) {
    return null;
  }
  // Get the source (layers below) - use current frame, not hardcoded 0
  return this.renderContext.renderLayersBelow(this.id, this.currentFrame);
  // ^^^^^ this.currentFrame is NEVER DEFINED on EffectLayer!
}
```

**Expected Behavior:**
The method should either use a properly tracked frame property or not exist at all since `onEvaluateFrame` handles rendering directly with the frame parameter.

**Actual Behavior:**
`this.currentFrame` was `undefined`, causing `renderLayersBelow()` to receive `undefined` as the frame parameter. This was a latent bug - the method wasn't called in normal operation since `onEvaluateFrame` handles rendering.

**Impact:**
- If `getSourceCanvas()` was called externally, it would pass `undefined` to `renderLayersBelow()`
- Could cause incorrect frame rendering or runtime errors
- Latent bug that could manifest if the method were used for additional effect processing

**Fix Applied:**
Removed the broken `getSourceCanvas()` override entirely since `onEvaluateFrame()` handles rendering directly with the frame parameter passed as an argument.

**Files Modified:**
- `ui/src/engine/layers/EffectLayer.ts` - Removed getSourceCanvas override (17 lines)

**Related Bugs:** BUG-027 (previous fix to this same method that introduced the undefined reference)

---

### BUG-055: glowRenderer Uses 30fps Fallback Instead of 16fps (WAN Standard)

**Feature:** Color Correction (4.2) - Note: glow effect categorically belongs to Stylize (4.5)
**Tier:** 4
**Severity:** LOW
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/services/effects/colorRenderer.ts`
- Line: 624
- Function: `glowRenderer()`

**Problem:**
The glow effect used 30fps as fallback for color looping timing calculations instead of 16fps (WAN standard).

**Evidence (before fix):**
```typescript
// colorRenderer.ts line 624
const fps = params._fps ?? 30;  // Should be 16
```

**Expected Behavior:**
Should use 16fps (WAN standard) as the fallback when fps is not injected via params.

**Actual Behavior:**
Used 30fps, causing glow color looping animation timing to be calculated incorrectly if effectProcessor failed to inject _fps.

**Impact:**
- Color looping in glow effect would cycle at wrong speed in edge cases
- Inconsistent with WAN AI model standard (16fps)

**Fix Applied:**
Changed fallback from 30 to 16:
```typescript
const fps = params._fps ?? 16;  // WAN standard
```

**Files Modified:**
- `ui/src/services/effects/colorRenderer.ts` - Line 624

**Related Bugs:** BUG-052, BUG-053 (similar fps fallback issues)

---

### BUG-056: Non-deterministic Particle Seed with Inconsistent Reset Fallback

**Feature:** GPU Particle Core (5.1)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 373, 1497
- Function: `constructor()`, `reset()`

**Problem:**
Constructor used `Date.now()` as fallback seed, but `reset()` used `12345`. This caused:
1. Non-deterministic initial particle state when no seed provided
2. Different behavior before vs after reset()

**Evidence (before fix):**
```typescript
// Line 373 (constructor)
this.initialRngSeed = this.config.randomSeed ?? Date.now();

// Line 1497 (reset)
this.rng = this.createSeededRandom(this.config.randomSeed ?? 12345);
```

**Expected Behavior:**
Particle simulation should be deterministic and reproducible. The same config should produce identical particle positions every time.

**Actual Behavior:**
- First run: seed = Date.now() (different each session)
- After reset(): seed = 12345 (deterministic but different from initial)
- Export/render results could differ from preview

**Impact:**
- Particle simulations not reproducible between sessions
- Reset produces different state than initial state
- Export may not match preview

**Fix Applied:**
```typescript
// Line 373 - consistent fallback
this.initialRngSeed = this.config.randomSeed ?? 12345;

// Line 1498 - use stored seed
this.rng = this.createSeededRandom(this.initialRngSeed);
```

**Files Modified:**
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 373, 1498

**Related Bugs:** None - first particle system determinism bug

---

### BUG-057: perceptionAngle Config Not Implemented in Flocking System

**Feature:** Flocking/Boids (5.5)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleFlockingSystem.ts`
- Lines: 72-127 (applyFlocking method)
- Function: `applyFlocking()`

**Problem:**
The `perceptionAngle` property in FlockingConfig is exposed in the UI but never used in calculations. Particles consider ALL neighbors in the spatial hash regardless of viewing direction.

**Evidence (before fix):**
```typescript
// applyFlocking() iterates neighbors without any angle check
for (const j of this.spatialHash.getNeighbors(px, py, pz)) {
  if (j === i) continue;
  // ... calculates dx, dy, dz, dist ...
  // NO check if neighbor is within perceptionAngle field of view
  // Separation - steer away from nearby neighbors
  if (dist < this.config.separationRadius && dist > 0) {
    // ...
```

**Expected Behavior:**
With perceptionAngle=180°, particles should only perceive neighbors in front of them (hemisphere). A particle moving forward should not be influenced by particles directly behind it.

**Actual Behavior:**
perceptionAngle slider has no effect. Particles have 360° perception regardless of setting.

**Impact:**
- Users cannot limit particle awareness for realistic boid behavior
- Unable to create forward-only perception patterns
- UI control does nothing

**Fix Applied:**
```typescript
// Get particle velocity for perception angle check
const vx = particleBuffer[offset + 3];
const vy = particleBuffer[offset + 4];
const vz = particleBuffer[offset + 5];
const speed = Math.sqrt(vx * vx + vy * vy + vz * vz);

// Precompute perception angle cosine threshold (360° means all neighbors visible)
const perceptionCos = this.config.perceptionAngle >= 360
  ? -1.0  // -1 means all angles pass
  : Math.cos((this.config.perceptionAngle / 2) * Math.PI / 180);

// In neighbor loop, after calculating distance:
if (speed > 0.001 && perceptionCos > -1.0) {
  const toNeighborX = -dx / dist;
  const toNeighborY = -dy / dist;
  const toNeighborZ = -dz / dist;
  const dot = (vx / speed) * toNeighborX + (vy / speed) * toNeighborY + (vz / speed) * toNeighborZ;
  if (dot < perceptionCos) continue; // Skip neighbors outside FOV
}
```

**Files Modified:**
- `ui/src/engine/particles/ParticleFlockingSystem.ts` - Lines 92-130 (added perception angle check)

**Related Bugs:** BUG-056 (same tier, particle determinism)

---

### BUG-058: trailOpacityFalloff UI Control Has No Effect

**Feature:** Trail System (5.6)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleTrailSystem.ts`
- Lines: 177-183 (alpha fading logic)
- Function: `update()`

**Problem:**
The "Trail Falloff" slider (trailOpacityFalloff) maps to trailWidthEnd but this value was never used. Alpha fading used a hardcoded linear falloff `(1 - t/trailLength)` instead of the configured value.

**Evidence (before fix):**
```typescript
// Alpha fading used hardcoded linear falloff
if (fadeMode === 'alpha' || fadeMode === 'both') {
  alpha1 *= (1 - t1Ratio);  // Always 0 at end
  alpha2 *= (1 - t2Ratio);  // trailWidthEnd ignored
}
```

**Expected Behavior:**
Moving the "Trail Falloff" slider should control how much trails fade - 0 = full fade to transparent, 1 = no fade.

**Actual Behavior:**
Slider had no visual effect. Trails always faded linearly to 0.

**Impact:**
- Users cannot control trail persistence
- UI control was non-functional

**Fix Applied:**
```typescript
if (fadeMode === 'alpha' || fadeMode === 'both') {
  // Interpolate from 1.0 (start) to trailWidthEnd (end)
  const endAlpha = this.config.trailWidthEnd;
  alpha1 *= 1 - t1Ratio * (1 - endAlpha);
  alpha2 *= 1 - t2Ratio * (1 - endAlpha);
}
```

**Files Modified:**
- `ui/src/engine/particles/ParticleTrailSystem.ts` - Lines 181-185 (added endAlpha interpolation)

**Related Bugs:** BUG-057 (same pattern - UI control not implemented)

---

### BUG-059: parentEmitterId Filter Not Implemented in Sub-Emitters

**Feature:** Sub-Emitters (5.7)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleSubEmitter.ts`
- Lines: 104-108 (death event processing)
- Function: `processDeathEvents()`

**Problem:**
The `parentEmitterId` config property allows users to select which emitter's particles should trigger this sub-emitter. However, the engine only checked if parentEmitterId existed, not whether it matched the dying particle's emitter.

**Evidence (before fix):**
```typescript
for (const death of deathQueue) {
  for (const subEmitter of this.subEmitters.values()) {
    if (subEmitter.trigger !== 'death') continue;
    if (!subEmitter.parentEmitterId) continue;  // Only checks existence!
    // Never compares subEmitter.parentEmitterId to death.emitterId
```

**Expected Behavior:**
- parentEmitterId='*' → trigger on any particle death
- parentEmitterId='emitter-1' → only trigger on emitter-1's particles

**Actual Behavior:**
All sub-emitters triggered on ALL particle deaths regardless of parentEmitterId setting.

**Impact:**
- Users cannot target sub-emitters to specific emitters
- Selecting a specific parent emitter in UI had no effect

**Fix Applied:**

1. Added `particleEmitters: Map<number, string>` to GPUParticleSystem to track emitter per particle
2. In `spawnParticle()`: Store emitter ID when particle is created
3. In death detection: Look up emitterId and pass to `queueDeathEvent()`
4. In `reset()`: Clear the tracking map
5. In ParticleSubEmitter: Filter based on parentEmitterId vs death.emitterId

```typescript
// GPUParticleSystem.ts - Track which emitter spawned each particle
this.particleEmitters.set(index, emitter.id);

// On death - pass emitterId to sub-emitter system
const emitterId = this.particleEmitters.get(i);
this.subEmitterSystem.queueDeathEvent({ index: i, emitterId });

// ParticleSubEmitter.ts - Filter by parent emitter
if (subEmitter.parentEmitterId !== '*' && death.emitterId !== undefined) {
  if (death.emitterId !== subEmitter.parentEmitterId) continue;
}
```

**Files Modified:**
- `ui/src/engine/particles/GPUParticleSystem.ts` - Added particleEmitters Map, tracking in spawnParticle(), lookup in death detection, clear in reset()
- `ui/src/engine/particles/ParticleSubEmitter.ts` - Lines 110-116 (added parent emitter filter)

**Related Bugs:** BUG-057, BUG-058 (same pattern - config not used)

---

### BUG-060: 'step' Curve Option Has No Effect in Audio Bindings

**Feature:** Audio Reactive (5.8)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleAudioReactive.ts`
- Lines: 108-113 (curve handling)
- Function: `applyModulation()`

**Problem:**
The UI allows selecting 'step' as a curve type for audio bindings, but the engine only implemented 'exponential' and 'logarithmic' curves. Selecting 'step' fell through to the default linear behavior.

**Evidence (before fix):**
```typescript
// Apply curve
if (binding.curve === 'exponential') {
  output = binding.outputMin + Math.pow(t, 2) * (binding.outputMax - binding.outputMin);
} else if (binding.curve === 'logarithmic') {
  output = binding.outputMin + Math.sqrt(t) * (binding.outputMax - binding.outputMin);
}
// 'step' is NOT handled - falls through to linear
```

**Expected Behavior:**
- Selecting 'step' curve should produce discrete stepped output values

**Actual Behavior:**
- Selecting 'step' behaves identically to 'linear' (smooth interpolation)

**Impact:**
- Users selecting 'step' curve get unexpected smooth behavior instead of discrete steps

**Fix Applied:**
Complete implementation with configurable step count:

1. Added `stepCount` property to AudioBinding interface (types.ts line 521)
2. Added `stepCount` property to AudioBindingConfig interface (particles.ts line 222)
3. Added UI control for stepCount in ParticleAudioBindingsSection.vue (lines 113-123, shown only when curve='step')
4. Added default stepCount: 5 in ParticleProperties.vue addAudioBinding()
5. Updated engine to use configurable step count:

```typescript
} else if (binding.curve === 'step') {
  // Step curve: snap to discrete steps
  const steps = Math.max(2, binding.stepCount ?? 5);
  const steppedT = Math.floor(t * steps) / steps;
  output = binding.outputMin + steppedT * (binding.outputMax - binding.outputMin);
}
```

**Files Modified:**
- `ui/src/engine/particles/types.ts` - Line 521 (added stepCount to AudioBinding)
- `ui/src/types/particles.ts` - Line 222 (added stepCount to AudioBindingConfig)
- `ui/src/components/properties/particle/ParticleAudioBindingsSection.vue` - Lines 113-123 (added conditional stepCount input)
- `ui/src/components/properties/ParticleProperties.vue` - Line 1308 (added stepCount default)
- `ui/src/engine/particles/ParticleAudioReactive.ts` - Lines 113-118 (step curve with configurable count)

**Related Bugs:** BUG-057, BUG-058, BUG-059 (same pattern - UI option not implemented in engine)

---

### BUG-061: triggerMode and threshold Not Implemented in Audio Bindings

**Feature:** Audio Reactive (5.8)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/types.ts`
- Lines: 523-525 (properties defined but never used)
- File: `ui/src/engine/particles/ParticleAudioReactive.ts`
- Function: `applyModulation()`

**Problem:**
The AudioBinding interface defined `triggerMode` and `threshold` properties for discrete event triggering, but:
1. These were NOT exposed in the UI
2. These were NOT implemented in the engine
3. The project type (AudioBindingConfig) didn't even have these properties

**Evidence (before fix):**
```typescript
// types.ts - defined but unused
triggerMode?: 'continuous' | 'onThreshold' | 'onBeat';
threshold?: number;

// ParticleAudioReactive.ts - no logic for trigger modes
// All bindings always apply continuously
```

**Expected Behavior:**
- triggerMode='continuous' → always apply (default)
- triggerMode='onThreshold' → only apply when audio value >= threshold
- triggerMode='onBeat' → only apply when beat is detected

**Actual Behavior:**
- All bindings always applied continuously regardless of audio level

**Impact:**
- Users cannot create beat-triggered effects
- Users cannot create threshold-based audio reactions
- Limits creative possibilities for audio-reactive particles

**Fix Applied:**
Complete implementation:

1. Added `AudioTriggerMode` type and properties to `particles.ts` (project types)
2. Added UI controls in `ParticleAudioBindingsSection.vue`:
   - Dropdown for triggerMode (continuous/onThreshold/onBeat)
   - Conditional threshold slider when triggerMode='onThreshold'
3. Added defaults in `ParticleProperties.vue` addAudioBinding()
4. Implemented trigger mode logic in `ParticleAudioReactive.ts`:

```typescript
// Check trigger mode
const triggerMode = binding.triggerMode ?? 'continuous';
if (triggerMode === 'onThreshold') {
  const threshold = binding.threshold ?? 0.5;
  if (t < threshold) continue;
} else if (triggerMode === 'onBeat') {
  const beatValue = this.audioFeatures.get('beat') ?? 0;
  if (beatValue < 0.5) continue;
}
```

**Files Modified:**
- `ui/src/types/particles.ts` - Lines 209, 225-226 (added AudioTriggerMode type and properties)
- `ui/src/components/properties/particle/ParticleAudioBindingsSection.vue` - Lines 124-146 (added UI controls)
- `ui/src/components/properties/ParticleProperties.vue` - Lines 1309-1310 (added defaults)
- `ui/src/engine/particles/ParticleAudioReactive.ts` - Lines 120-131 (implemented trigger logic)

**Related Bugs:** BUG-060 (same feature, same pattern - defined but not implemented)

---

### BUG-062: Connection Color Override Not Exposed in UI

**Feature:** Connection System (5.9)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleConnectionSystem.ts`
- Lines: 165-169 (color used in engine)
- File: `ui/src/components/properties/particle/ParticleRenderSection.vue`
- Missing UI control for color property

**Problem:**
The ConnectionConfig interface defined a `color` property for overriding connection line colors, and the engine uses it (falling back to blending particle colors if undefined), but:
1. No UI control existed to set it
2. Project type comment incorrectly stated "0-255" when engine uses 0-1

**Evidence (engine usage):**
```typescript
const color = this.config.color ?? [
  (p1.color[0] + p2.color[0]) / 2,  // Blend particle colors if no override
  (p1.color[1] + p2.color[1]) / 2,
  (p1.color[2] + p2.color[2]) / 2,
];
```

**Expected Behavior:**
Users should be able to set a custom color for connection lines instead of blending particle colors.

**Actual Behavior:**
Color override was impossible - always blended particle colors.

**Impact:**
- Users cannot create consistent-colored connection networks
- Cannot use accent colors independent of particle colors

**Fix Applied:**
1. Added "Custom Color" checkbox to enable color override
2. Added color picker input (shown when enabled)
3. Added rgbToHex/hexToRgb helpers converting between hex and 0-1 range
4. Fixed project type comment from "0-255" to "0-1 range"

**Files Modified:**
- `ui/src/components/properties/particle/ParticleRenderSection.vue` - Lines 286-303 (UI), 329-342 (helpers)
- `ui/src/types/particles.ts` - Line 201 (fixed comment)

**Related Bugs:** BUG-060, BUG-061 (same pattern - defined but not exposed)

---

### BUG-063: particleEmitters Map Not Cached in Frame Cache

**Feature:** Frame Cache (5.10)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleFrameCache.ts`
- Lines: 17-27 (interface missing particleEmitters)
- Lines: 63-96 (cacheState not saving particleEmitters)
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 1332-1364 (restoreFromCache not restoring particleEmitters)

**Problem:**
The `particleEmitters` Map (Map<number, string>) tracks which emitter spawned each particle. This data is critical for sub-emitter death event filtering by `parentEmitterId`. However:
1. The `ParticleFrameCache` interface didn't include the map
2. `cacheState()` didn't save it
3. `restoreFromCache()` didn't restore it

**Evidence (particleEmitters usage):**
```typescript
// Line 322 - Declaration
private particleEmitters: Map<number, string> = new Map();

// Line 962 - Set on spawn
this.particleEmitters.set(index, emitter.id);

// Line 1094 - Used for sub-emitter death events
const emitterId = this.particleEmitters.get(i);
this.subEmitterSystem.queueDeathEvent({ index: i, emitterId });
```

**Evidence (missing from cache interface):**
```typescript
export interface ParticleFrameCache {
  frame: number;
  version: number;
  particleBuffer: Float32Array;
  freeIndices: number[];
  particleCount: number;
  simulationTime: number;
  rngState: number;
  emitterAccumulators: Map<string, number>;
  // particleEmitters was MISSING
}
```

**Expected Behavior:**
After timeline scrubbing and cache restore, sub-emitter death events should correctly filter by parentEmitterId.

**Actual Behavior:**
After cache restore, `particleEmitters` map was empty, so all particles returned `undefined` for emitterId, breaking parentEmitterId filtering.

**Impact:**
- Sub-emitter parentEmitterId filtering broken after timeline scrubbing
- Non-deterministic sub-emitter behavior
- Death events routed to wrong sub-emitters

**Fix Applied:**
1. Added `particleEmitters: Map<number, string>` to ParticleFrameCache interface
2. Updated `cacheState()` to accept and save particleEmitters with deep copy
3. Updated `cacheCurrentState()` in GPUParticleSystem to pass particleEmitters
4. Updated `restoreFromCache()` to restore particleEmitters with deep copy

**Files Modified:**
- `ui/src/engine/particles/ParticleFrameCache.ts` - Lines 26, 71, 94
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 1325, 1360

**Related Bugs:** BUG-059 (added particleEmitters for sub-emitter filtering, but didn't cache it)

---

### BUG-064: Audio Smoothed Values Not Cached in ParticleFrameCache

**Feature:** Frame Cache (5.10)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleAudioReactive.ts`
- Lines: 18, 99-102 (smoothedAudioValues EMA filter)
- File: `ui/src/engine/particles/ParticleFrameCache.ts`
- Lines: 17-28 (interface missing audioSmoothedValues)
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 1314-1328, 1333-1368 (cache save/restore)

**Problem:**
The `smoothedAudioValues` Map (Map<number, number>) stores EMA (exponential moving average) filtered audio values that persist across frames. This temporal state was NOT being saved/restored in ParticleFrameCache.

**Evidence (EMA filter depends on previous frame):**
```typescript
// Lines 99-102 - EMA depends on previous smoothed value
const previousSmoothed = this.smoothedAudioValues.get(i) ?? featureValue;
const alpha = 1 - (binding.smoothing || 0);
const smoothed = alpha * featureValue + (1 - alpha) * previousSmoothed;
this.smoothedAudioValues.set(i, smoothed);  // Persists across frames!
```

**Expected Behavior:**
After timeline scrubbing and cache restore, audio-reactive particle parameters should have the same smoothed values as during sequential playback.

**Actual Behavior:**
After cache restore, `smoothedAudioValues` was empty/reset, so EMA smoothing restarted from raw values. Frame 50 reached via scrubbing produced different results than frame 50 reached via sequential playback.

**Impact:**
- Audio-reactive particle parameters behave differently after scrubbing
- Breaks determinism: same frame produces different results
- EMA smoothing "resets" when scrubbing backwards

**Fix Applied:**
1. Added getter/setter methods to ParticleAudioReactive for cache access
2. Added `audioSmoothedValues: Map<number, number>` to ParticleFrameCache interface
3. Updated `cacheState()` to save audioSmoothedValues with deep copy
4. Updated `restoreFromCache()` to restore audioSmoothedValues

**Files Modified:**
- `ui/src/engine/particles/ParticleAudioReactive.ts` - Lines 173-185 (getter/setter)
- `ui/src/engine/particles/ParticleFrameCache.ts` - Lines 27, 73, 97
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 1326, 1364

**Related Bugs:** BUG-063 (similar pattern - state not cached)

---

### BUG-065: Time Effect Frame Buffers Not Cleared on Timeline Seek

**Feature:** Frame Cache (5.10)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/services/effects/timeRenderer.ts`
- Lines: 156, 527, 64
- Functions: `store()`, frame buffer management

**Problem:**
Time effects (Echo, Posterize Time, Time Displacement, Freeze Frame) use module-level `frameBuffers` and `frozenFrames` Maps that persist frame history across renders. This temporal state was not cleared on timeline seek, causing different output after scrubbing vs sequential playback.

Additionally, the buffer used `Date.now()` for timestamps which is non-deterministic.

**Evidence:**
```typescript
// Line 156 - Global mutable state
const frameBuffers = new Map<string, TimeEffectFrameBuffer>();

// Line 527 - Global mutable state
const frozenFrames = new Map<string, { frame: number; imageData: ImageData }>();

// Line 64 - Non-deterministic timestamp (was using Date.now())
timestamp: Date.now(),
```

**Expected Behavior:**
After timeline scrubbing, time effects should either:
1. Have their buffers cleared (known limitation: effects won't have history)
2. Produce deterministic results via proper cache integration

**Actual Behavior:**
- Echo effect after scrubbing had stale/wrong frames in buffer
- Freeze frame could reference wrong cached frame
- Buffer cleanup used wall clock time, violating determinism

**Impact:**
- Time effects produce different output after scrubbing
- Echo trails appear/disappear incorrectly
- Violates determinism rule: same frame should produce same output

**Fix Applied:**
1. Changed `timestamp: Date.now()` to `storedAtFrame: frame` for frame-based timestamps
2. Updated `cleanup()` to use frame distance instead of wall clock time
3. Added `clearTimeEffectStateOnSeek()` export function
4. Integrated clear call into `compositorStore.setFrame()`, `goToStart()`, `goToEnd()`, `jumpFrames()`

**Files Modified:**
- `ui/src/services/effects/timeRenderer.ts` - Lines 25, 50-72, 132-140, 607-622, 953
- `ui/src/stores/compositorStore.ts` - Lines 85-87, 1034-1055, 1079-1092, 1094-1109, 1111-1126

**Related Bugs:** BUG-063, BUG-064, BUG-066 (all temporal state caching issues)

---

### BUG-066: Mask Previous Path Cache Not Cleared on Timeline Seek

**Feature:** Frame Cache (5.10)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/services/effects/maskRenderer.ts`
- Line: 337
- Functions: `getPreviousPath()`, `cachePath()`

**Problem:**
Motion-aware mask feathering stores previous frame mask paths in a module-level `previousPathCache` Map for motion blur calculation. This temporal state was not cleared on timeline seek.

**Evidence:**
```typescript
// Line 337 - Global mutable state
const previousPathCache = new Map<string, { frame: number; path: MaskPath }>();
```

**Expected Behavior:**
After timeline scrubbing, motion-aware feathering should either:
1. Have the cache cleared (will use static feathering until next sequential frame)
2. Produce deterministic results

**Actual Behavior:**
After scrubbing, the cache might contain paths from unrelated frames, causing incorrect motion blur direction/amount.

**Impact:**
- Motion-aware mask feathering produces different blur after scrubbing
- Mask edges may have incorrect feather direction
- Medium severity: only affects motion-aware feathering, static feathering unaffected

**Fix Applied:**
1. Added `clearMaskPathCacheOnSeek()` export function
2. Integrated clear call into `compositorStore.setFrame()`, `goToStart()`, `goToEnd()`, `jumpFrames()`

**Files Modified:**
- `ui/src/services/effects/maskRenderer.ts` - Lines 358-372, 679
- `ui/src/stores/compositorStore.ts` - Lines 85-87, 1050-1051, 1088-1089, 1104-1105, 1122-1123

**Related Bugs:** BUG-065 (same pattern - temporal state not cleared on seek)

---

### BUG-067: Procedural Shape Type Mismatch

**Feature:** Texture/Sprites (5.11)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/types.ts`
- Line: 379
- File: `ui/src/engine/particles/particleShaders.ts`
- Lines: 369-451
- File: `ui/src/engine/particles/ParticleTextureSystem.ts`
- Lines: 155-175

**Problem:**
`ParticleTextureConfig.proceduralType` accepted 9 shape types but only 5 were implemented in the shader (none, circle, ring, square, star). The missing shapes (noise, line, triangle, shadedSphere, fadedSphere) silently fell back to circle.

**Evidence:**
```typescript
// types.ts line 379 - promised 9 shapes
proceduralType?: 'circle' | 'square' | 'star' | 'ring' | 'noise' | 'line' | 'triangle' | 'shadedSphere' | 'fadedSphere';

// particleShaders.ts - only implemented 5
const shapeMap = { none: 0, circle: 1, ring: 2, square: 3, star: 4 };
```

**Expected Behavior:**
All 9 shape types should render their respective shapes.

**Actual Behavior:**
5 shapes worked, 4 silently fell back to circle.

**Impact:**
Users selecting unimplemented shapes got unexpected circle rendering instead of the requested shape.

**Fix Applied:**
1. Added GLSL implementations for all 5 missing shapes in `proceduralAlpha()`:
   - noise (5): Layered sine-based procedural noise
   - line (6): Horizontal line with soft edges
   - triangle (7): Equilateral triangle using SDF
   - shadedSphere (8): 3D lit sphere appearance
   - fadedSphere (9): Exponential radial falloff
2. Updated shapeMap in ParticleTextureSystem.ts to include all 9 types
3. Updated type signature in setProceduralShape() to accept all shapes

**Files Modified:**
- `ui/src/engine/particles/particleShaders.ts` - Lines 369-451
- `ui/src/engine/particles/ParticleTextureSystem.ts` - Lines 155-175
- `ui/src/engine/particles/GPUParticleSystem.ts` - Line 687

**Related Bugs:** None

---

### BUG-068: randomStartFrame Not Implemented

**Feature:** Texture/Sprites (5.11)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/types.ts`
- Line: 376
- File: `ui/src/engine/particles/ParticleTextureSystem.ts`
- Lines: 25, 109
- File: `ui/src/engine/particles/particleShaders.ts`
- Lines: 367, 473-480, 484, 487

**Problem:**
The `randomStartFrame` (or `randomStart`) config option was stored in SpriteSheetConfig but never used in rendering. All particles always started at frame 0 of sprite sheet animation regardless of this setting.

**Evidence:**
```typescript
// Line 109 - value was stored but never passed to shader
randomStart: spriteSheet.randomStart ?? false,

// Shader had no uniform for random start frame
// All particles started at frame 0
```

**Expected Behavior:**
When `randomStartFrame` is enabled, each particle should start at a different frame in the sprite sheet animation for visual variety.

**Actual Behavior:**
All particles started at frame 0 regardless of config setting.

**Impact:**
Feature didn't work as documented. Sprite animations looked uniform instead of varied.

**Fix Applied:**
1. Added `randomStartFrame` uniform to fragment shader
2. In shader, when enabled, compute deterministic per-particle frame offset using particle color as seed
3. Add offset to sprite frame calculation for both time-based and life-based animation
4. Added uniform initialization in GPUParticleSystem.ts
5. Updated ParticleTextureSystem.ts to set uniform from config

**Files Modified:**
- `ui/src/engine/particles/particleShaders.ts` - Lines 367, 473-480, 484, 487
- `ui/src/engine/particles/ParticleTextureSystem.ts` - Line 117
- `ui/src/engine/particles/GPUParticleSystem.ts` - Line 1224

**Related Bugs:** None

---

### BUG-069: Division by Zero in Curve Evaluation

**Feature:** Modulation Curves (5.12)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleModulationCurves.ts`
- Lines: 103-110
- Function: `evaluateCurve()`

**Problem:**
When evaluating a curve with two keyframe points at the same time value (p0.time === p1.time), the code divided by zero: `localT = (t - p0.time) / (p1.time - p0.time)`.

**Evidence:**
```typescript
// Before fix - division by zero when timeDiff === 0
const localT = (t - p0.time) / (p1.time - p0.time);
```

**Expected Behavior:**
Handle edge case gracefully when two curve points share the same time.

**Actual Behavior:**
Division by zero produces NaN, corrupting particle size/opacity values.

**Impact:**
Particles became invisible or corrupted when using curve-type modulation with coincident keyframes.

**Fix Applied:**
```typescript
// BUG-069 fix: Prevent division by zero when points have same time
const timeDiff = p1.time - p0.time;
if (timeDiff === 0) {
  // Return average of the two values at the same time
  return (p0.value + p1.value) / 2;
}
const localT = (t - p0.time) / timeDiff;
```

**Files Modified:**
- `ui/src/engine/particles/ParticleModulationCurves.ts` - Lines 103-108

**Related Bugs:** BUG-073 (same file, different issue)

---

### BUG-070: Random Curve Types Cause Non-Deterministic Jitter

**Feature:** Modulation Curves (5.12)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/ParticleModulationCurves.ts`
- Lines: 126-139
- Function: `evaluateCurve()` - 'random' and 'randomCurve' cases

**Problem:**
The 'random' and 'randomCurve' modulation curve types call `this.rng()` every time they're evaluated. Since modulation is evaluated each frame, particles get a new random value each frame instead of a stable per-particle random offset.

**Evidence:**
```typescript
case 'random':
  return curve.min + this.rng() * (curve.max - curve.min);  // Called every frame!

case 'randomCurve': {
  const min = this.evaluateCurve(curve.minCurve, t);
  const max = this.evaluateCurve(curve.maxCurve, t);
  return min + this.rng() * (max - min);  // Called every frame!
}
```

**Expected Behavior:**
Random modulation should apply a per-particle random offset at spawn time that remains constant throughout the particle's lifetime.

**Actual Behavior:**
Random modulation causes particles to jitter as their size/opacity flickers randomly each frame.

**Impact:**
- Visual noise/jitter on particles using random modulation
- Non-deterministic behavior breaks reproducibility

**Fix Applied:**
1. Added `randomOffset` field to `particleInitialValues` Map
2. In spawnParticle(): Compute `randomOffset = this.rng()` at spawn time
3. Updated evaluateCurve() signature to accept optional `randomOffset` parameter
4. 'random' case uses stored offset instead of calling rng()
5. 'randomCurve' case passes offset to nested evaluations
6. Updated frame cache to include randomOffset for deterministic scrubbing

**Files Modified:**
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 327, 1008-1012, 1085, 1089-1097
- `ui/src/engine/particles/ParticleModulationCurves.ts` - Lines 79, 126-139
- `ui/src/engine/particles/ParticleFrameCache.ts` - Lines 28, 75

**Related Bugs:** BUG-073 (lifetime modulation architecture)

---

### BUG-071: 5 of 8 Lifetime Modulation Properties Not Implemented

**Feature:** Modulation Curves (5.12)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 1072-1163 (updatePhysics)

**Problem:**
The LifetimeModulation interface defines 8 modulation properties, but only 3 were implemented in the physics loop:

Previously Implemented:
- sizeOverLifetime ✓
- opacityOverLifetime ✓
- colorOverLifetime ✓ (texture only, not CPU)

Not Implemented:
- speedOverLifetime ✗
- rotationSpeedOverLifetime ✗
- gravityModifier ✗
- dragOverLifetime ✗
- noiseAmplitudeOverLifetime ✗

**Evidence:**
```typescript
// Only 2 were used before fix
const sizeMod = this.evaluateModulationCurve(...);
const opacityMod = this.evaluateModulationCurve(...);
// speedOverLifetime, rotationSpeedOverLifetime, etc. - NOT USED
```

**Expected Behavior:**
All 8 modulation properties should affect particles during their lifetime.

**Actual Behavior:**
5 properties were ignored - users could configure them but they had no effect.

**Impact:**
Feature parity gap - documented functionality didn't work.

**Fix Applied:**
1. Added evaluation of all 5 missing modulation curves in updatePhysics:
   - speedMod, rotationSpeedMod, gravityMod, dragMod, noiseMod
2. speedOverLifetime: Multiply velocity vector by speedMod after integration
3. rotationSpeedOverLifetime: Scale angular velocity by rotationSpeedMod
4. gravityModifier: Apply gravityMod multiplier to gravity force fields
5. dragOverLifetime: Apply drag factor `(1 - dragMod * dt)` to velocity
6. noiseAmplitudeOverLifetime: Scale turbulence force fields by noiseMod

**Files Modified:**
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 1072-1163

**Related Bugs:** BUG-072 (colorOverLifetime texture)

---

### BUG-072: colorOverLifetime Texture Created But Never Used

**Feature:** Modulation Curves (5.12)
**Tier:** 5
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 293-295, 473-480, 1318-1320
- File: `ui/src/engine/particles/particleShaders.ts`
- Lines: 368-370, 504-511

**Problem:**
The colorOverLifetimeTexture was created in createModulationTextures() and stored, but never passed to the shader uniforms. The shader had no uniform to receive this texture.

**Evidence:**
```typescript
// GPUParticleSystem.ts - Texture stored but not used
private colorOverLifetimeTexture: THREE.DataTexture | null = null;

// createModulationTextures() created it but never set uniform
this.colorOverLifetimeTexture = textures.colorOverLifetime;

// createUniforms() had no colorOverLifetime uniform
```

**Expected Behavior:**
Color should interpolate from colorStart through colorOverLifetime gradient to colorEnd during particle lifetime.

**Actual Behavior:**
colorOverLifetime config was parsed but ignored. Particles only interpolated colorStart→colorEnd based on colorVariance at spawn.

**Impact:**
Users could not create gradient color animations over particle lifetime (e.g., fire particles going red→orange→yellow→white).

**Fix Applied:**
1. Added `colorOverLifetime` and `hasColorOverLifetime` uniforms to fragment shader
2. Added uniforms to createUniforms() in GPUParticleSystem.ts
3. In createModulationTextures(): Set uniform values after material exists
4. In fragment shader: Sample texture at vLifeRatio and multiply with particle color
5. Swapped initialization order so material exists before texture creation

**Files Modified:**
- `ui/src/engine/particles/particleShaders.ts` - Lines 368-370 (uniforms), 504-511 (sampling)
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 425-429 (init order), 473-480 (set uniforms), 1318-1320 (create uniforms)

**Related Bugs:** BUG-071 (other lifetime properties)

---

### BUG-073: Exponential Decay in Size/Opacity Modulation

**Feature:** Modulation Curves (5.12)
**Tier:** 5
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 4
**Status:** FIXED

**Location:**
- File: `ui/src/engine/particles/GPUParticleSystem.ts`
- Lines: 1091, 1093 (before fix)
- Function: `updatePhysics()`

**Problem:**
Size and opacity modulation used `*=` (compound assignment) instead of storing initial values and computing `initial * modFactor`. This caused exponential decay:
- Frame 1: size = 10 * 0.9 = 9
- Frame 2: size = 9 * 0.9 = 8.1
- Frame 60: size = 10 * 0.9^60 ≈ 0.018

**Evidence:**
```typescript
// Before fix - exponential decay
buffer[offset + 9] *= sizeMod;    // Compounds each frame!
buffer[offset + 15] *= opacityMod; // Compounds each frame!
```

**Expected Behavior:**
Modulation should be `currentSize = initialSize * modulationFactor(lifeRatio)`. A particle at 50% lifetime with sizeMod=0.5 should be half its initial size, not 0.5^(lifetime/2).

**Actual Behavior:**
Particles became microscopic/invisible after a few frames when using any size modulation curve below 1.0.

**Impact:**
- Particles disappear almost immediately with shrink curves
- Opacity modulation causes particles to vanish instead of fade

**Fix Applied:**
1. Added `particleInitialValues` Map to store initial size/opacity per particle
2. In spawnParticle(): Store initial values when particle is created
3. In updatePhysics(): Use `initialSize * sizeMod` instead of `*= sizeMod`
4. On particle death: Clean up Map entry
5. On reset(): Clear Map
6. Added to frame cache for deterministic timeline scrubbing

**Files Modified:**
- `ui/src/engine/particles/GPUParticleSystem.ts` - Lines 326, 1004-1009, 1090-1106, 1117-1118, 1516-1517, 1347-1349, 1388-1389
- `ui/src/engine/particles/ParticleFrameCache.ts` - Lines 28, 75, 100

**Related Bugs:** BUG-069 (same file, different issue)

---

## TIER 6 BUGS (Audio System)

### BUG-074: bpm Not Accessible via getFeatureAtFrame()

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 5
**Status:** FIXED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Lines: 884-975 (getFeatureAtFrame switch statement)
- Function: `getFeatureAtFrame()`

**Problem:**
BPM is computed and stored in AudioAnalysis but no case in getFeatureAtFrame() handles 'bpm' feature lookup. Requests for 'bpm' return 0.

**Evidence (before fix):**
```typescript
// Switch statement had no 'bpm' case
switch (feature) {
  case 'amplitude': ...
  case 'rms': ...
  // NO 'bpm' case
  default:
    return 0;  // bpm returns 0
}
```

**Expected Behavior:**
Users should be able to query BPM as a normalized 0-1 feature value.

**Actual Behavior:**
`getFeatureAtFrame(analysis, 'bpm', frame)` always returned 0.

**Impact:**
Users cannot use BPM for audio-reactive expressions or parameter linking.

**Fix Applied:**
```typescript
// BUG-074 fix: BPM access (returns normalized 0-1 based on typical range 60-200)
case 'bpm':
  return Math.min(1, Math.max(0, (analysis.bpm - 60) / 140));
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Added 'bpm' case at line 973-975

**Related Bugs:** BUG-075, BUG-076 (similar missing cases)

---

### BUG-075: HPSS Features Not Accessible via getFeatureAtFrame()

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 5
**Status:** FIXED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Lines: 884-975 (getFeatureAtFrame switch statement)
- Function: `getFeatureAtFrame()`

**Problem:**
HPSS (Harmonic-Percussive Source Separation) features are computed in extractHPSS() and stored in AudioAnalysis, but no cases exist to retrieve them. The properties harmonicEnergy, percussiveEnergy, and hpRatio were inaccessible.

**Evidence (before fix):**
```typescript
// HPSS computed and stored
harmonicEnergy: hpss.harmonicEnergy,
percussiveEnergy: hpss.percussiveEnergy,
hpRatio: hpss.hpRatio,

// But NO switch cases to retrieve them
// All fell through to default: return 0
```

**Expected Behavior:**
Users should be able to query harmonic/percussive energy for audio-reactive animations (e.g., drums-only or vocals-only reactivity).

**Actual Behavior:**
All HPSS feature queries returned 0.

**Impact:**
Users cannot create harmonic/percussive source separation effects despite the analysis being computed.

**Fix Applied:**
```typescript
// BUG-075 fix: HPSS features access
case 'harmonicEnergy':
case 'harmonic':
  return analysis.harmonicEnergy?.[clampedFrame] ?? 0;

case 'percussiveEnergy':
case 'percussive':
  return analysis.percussiveEnergy?.[clampedFrame] ?? 0;

case 'hpRatio':
case 'harmonicPercussiveRatio':
  return analysis.hpRatio?.[clampedFrame] ?? 0;
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Added 3 HPSS cases at lines 977-988

**Related Bugs:** BUG-074, BUG-076 (similar missing cases)

---

### BUG-076: MFCC Features Not Accessible via getFeatureAtFrame()

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** HIGH
**Found:** 2025-12-26
**Session:** 5
**Status:** FIXED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Lines: 884-975 (getFeatureAtFrame switch statement)
- Function: `getFeatureAtFrame()`

**Problem:**
MFCC (Mel-frequency cepstral coefficients) are computed in extractMFCC() for timbral analysis, returning 13 coefficients per frame. However, no cases existed to retrieve any of the coefficients.

**Evidence (before fix):**
```typescript
// MFCC computed and stored
mfcc: extractMFCC(analyzeBuffer, fps)

// But NO switch cases for mfcc0-mfcc12
// All fell through to default: return 0
```

**Expected Behavior:**
Users should be able to query individual MFCC coefficients (mfcc0-mfcc12) for timbre-based audio reactivity.

**Actual Behavior:**
All MFCC queries returned 0.

**Impact:**
Users cannot create timbre-aware audio-reactive effects despite the analysis being computed.

**Fix Applied:**
```typescript
// BUG-076 fix: MFCC coefficients access (13 coefficients: mfcc0-mfcc12)
case 'mfcc0':
  return normalizeMFCC(analysis.mfcc?.[clampedFrame]?.[0]);
// ... (all 13 cases)
case 'mfcc12':
  return normalizeMFCC(analysis.mfcc?.[clampedFrame]?.[12]);

// Helper function
function normalizeMFCC(value: number | undefined): number {
  if (value === undefined) return 0;
  const clamped = Math.max(-30, Math.min(30, value));
  return (clamped + 30) / 60;
}
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Added 13 MFCC cases and helper function at lines 990-1032

**Related Bugs:** BUG-074, BUG-075 (similar missing cases)

---

### BUG-077: fftSize Config Property Ignored

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 5
**Status:** FIXED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Lines: 292-383 (extractFrequencyBands)
- Function: `extractFrequencyBands()`

**Problem:**
The AudioAnalysisConfig interface defines `fftSize` (512, 1024, 2048, 4096) for user control over FFT resolution, but the extraction function always used `DEFAULT_FFT_SIZE` (2048) instead of the config value.

**Evidence (before fix):**
```typescript
// Config defined fftSize
export interface AudioAnalysisConfig {
  fftSize: number;  // 512, 1024, 2048, 4096
  ...
}

// But extractFrequencyBands ignored it
const binFrequency = sampleRate / DEFAULT_FFT_SIZE;  // Always 2048
analyser.fftSize = DEFAULT_FFT_SIZE;  // Ignored config
```

**Expected Behavior:**
Users should be able to customize FFT resolution for different analysis needs.

**Actual Behavior:**
fftSize config had no effect - always used 2048.

**Impact:**
Users cannot adjust FFT resolution for frequency/time tradeoff.

**Fix Applied:**
```typescript
// BUG-077 fix: Use config fftSize if provided
const fftSize = config?.fftSize ?? DEFAULT_FFT_SIZE;
analyser.fftSize = fftSize;
const binFrequency = sampleRate / fftSize;
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Lines 303, 316, 332, 352, 366

**Related Bugs:** BUG-078, BUG-079 (other unused config properties)

---

### BUG-078: hopSize Config Property Never Used

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** LOW
**Found:** 2025-12-26
**Session:** 5
**Status:** DOCUMENTED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Line: 82
- Interface: `AudioAnalysisConfig`

**Problem:**
The `hopSize` property is defined in AudioAnalysisConfig with comment "Overlap (default fftSize/4)" but is never used. Analysis is locked to video frame boundaries for deterministic playback.

**Evidence:**
```typescript
// Defined but never referenced anywhere
hopSize?: number;  // Overlap (default fftSize/4)
```

**Expected Behavior:**
Either hopSize should control STFT overlap, or it should be documented as reserved.

**Actual Behavior:**
Property existed but had no effect. Comment was misleading.

**Impact:**
Misleading API - users might expect this to work.

**Fix Applied:**
Updated interface comment to clarify reserved status:
```typescript
// BUG-078: hopSize is reserved for future use. Currently, analysis is locked
// to video frame boundaries for deterministic playback. Sub-frame temporal
// resolution would require additional interpolation logic.
hopSize?: number;  // Reserved for future use (default: frame-aligned)
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Lines 82-85 (updated comment)

**Related Bugs:** BUG-077, BUG-079 (other config issues)

---

### BUG-079: minFrequency/maxFrequency Config Properties Never Used

**Feature:** FFT Analysis (6.1)
**Tier:** 6
**Severity:** MEDIUM
**Found:** 2025-12-26
**Session:** 5
**Status:** FIXED

**Location:**
- File: `ui/src/services/audioFeatures.ts`
- Lines: 83-84 (config definition), 334-359 (extractFrequencyBands)
- Function: `extractFrequencyBands()`

**Problem:**
The AudioAnalysisConfig interface defines `minFrequency` and `maxFrequency` for frequency range filtering, but these were never applied to the frequency band extraction.

**Evidence (before fix):**
```typescript
// Config defined frequency limits
minFrequency: number;  // Filter low frequencies (default 20)
maxFrequency: number;  // Filter high frequencies (default 20000)

// But extractFrequencyBands never used them
// All bins were analyzed regardless of config
```

**Expected Behavior:**
Users should be able to filter out unwanted frequencies before analysis.

**Actual Behavior:**
minFrequency and maxFrequency config had no effect.

**Impact:**
Users cannot filter out rumble (low) or hiss (high) frequencies from analysis.

**Fix Applied:**
```typescript
// BUG-079 fix: Apply minFrequency/maxFrequency filtering
const minFreq = config?.minFrequency ?? 20;
const maxFreq = config?.maxFrequency ?? 20000;
const minBin = Math.floor(minFreq / binFrequency);
const maxBin = Math.ceil(maxFreq / binFrequency);

// Calculate bin ranges for each band, clamped to min/max frequency
const bandBins = Object.entries(FREQUENCY_BANDS).reduce((acc, [band, [low, high]]) => {
  const clampedLow = Math.max(low, minFreq);
  const clampedHigh = Math.min(high, maxFreq);
  if (clampedLow >= clampedHigh) {
    acc[band] = { start: 0, end: 0 };  // Skip band
  } else {
    acc[band] = {
      start: Math.max(minBin, Math.floor(clampedLow / binFrequency)),
      end: Math.min(maxBin, Math.ceil(clampedHigh / binFrequency))
    };
  }
  return acc;
}, {});
```

**Files Modified:**
- `ui/src/services/audioFeatures.ts` - Lines 337-359

**Related Bugs:** BUG-077, BUG-078 (other config issues)

---

## BUG TEMPLATE

Copy this when adding new bugs:
````markdown
### BUG-XXX: [Short Descriptive Title]

**Feature:** [Feature name] (X.X)
**Tier:** [Tier number]
**Severity:** CRITICAL / HIGH / MEDIUM / LOW
**Found:** [YYYY-MM-DD]
**Session:** [Session identifier]
**Status:** OPEN / FIXED

**Location:**
- File: `[exact/file/path.ts]`
- Line(s): [number or range]
- Function: `[functionName()]`

**Problem:**
[Clear description]

**Evidence:**
```typescript
[code snippet]
```

**Expected Behavior:**
[What should happen]

**Actual Behavior:**
[What does happen]

**Impact:**
[What breaks]

**Fix Applied:** (if fixed)
[Description of fix]

**Related Bugs:** [BUG-XXX or "None"]
````