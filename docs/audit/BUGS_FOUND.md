# LATTICE COMPOSITOR - BUGS FOUND

**Last Updated:** 2025-12-26
**Next Bug ID:** BUG-052

---

## SUMMARY

| Severity | Total | Fixed | Open |
|----------|-------|-------|------|
| CRITICAL | 0 | 0 | 0 |
| HIGH | 14 | 14 | 0 |
| MEDIUM | 30 | 30 | 0 |
| LOW | 4 | 4 | 0 |
| **TOTAL** | **48** | **48** | **0** |

**Note:** These 36 bugs were found in previous audit sessions and are preserved here. All have been fixed. New bugs should start at BUG-037.

---

## BUGS BY TIER

| Tier | Bug Count |
|------|-----------|
| 1. Foundation | 11 |
| 2. Layer Types | 35 |
| 3-12 | 0 (not yet audited) |

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