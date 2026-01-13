# Phase 2 Migration Changes - Detailed Breakdown

> **Date:** 2026-01-12  
> **Purpose:** Show EXACTLY what code was changed, moved, and where it went  
> **Status:** ✅ COMPLETE

---

## Summary

**NO CODE WAS DELETED** - All implementation code was **MOVED** to appropriate domain stores.  
`compositorStore` now **DELEGATES** to domain stores instead of implementing directly.

---

## Changes Made

### 1. `setTimelineZoom` - Bug Fix

**Location:** `ui/src/stores/compositorStore.ts` (Line ~2751)

**BEFORE (WRONG - Direct State Mutation):**
```typescript
setTimelineZoom(zoom: number): void {
  useAnimationStore().timelineZoom = Math.max(0.1, Math.min(10, zoom)); // ❌ Direct mutation
}
```

**AFTER (CORRECT - Delegation):**
```typescript
setTimelineZoom(zoom: number): void {
  useAnimationStore().setTimelineZoom(zoom); // ✅ Delegates to method
}
```

**CODE MOVED TO:** `ui/src/stores/animationStore/index.ts` (Lines 289-295)
```typescript
setTimelineZoom(zoom: number): void {
  this.timelineZoom = Math.max(0.1, Math.min(10, zoom));
}
```

**Impact:** Fixed bug where state was mutated directly instead of using action method.

---

### 2. `getFrameState` - Frame Evaluation

**Location:** `ui/src/stores/compositorStore.ts` (Line ~1075)

**BEFORE (23 lines of implementation):**
```typescript
getFrameState(frame?: number): FrameState {
  const comp = this.getActiveComp();
  const targetFrame = frame ?? comp?.currentFrame ?? 0;

  // Get audio reactive data from audioStore
  const audioStore = useAudioStore();
  const audioReactive =
    audioStore.audioAnalysis && audioStore.reactiveMappings.length > 0
      ? {
          analysis: audioStore.audioAnalysis,
          mappings: audioStore.reactiveMappings,
        }
      : null;

  return motionEngine.evaluate(
    targetFrame,
    this.project,
    audioStore.audioAnalysis,
    this.activeCameraId,
    true, // useCache
    audioReactive,
  );
}
```

**AFTER (1 line delegation):**
```typescript
getFrameState(frame?: number): FrameState {
  return useAnimationStore().getFrameState(this, frame);
}
```

**CODE MOVED TO:** `ui/src/stores/animationStore/index.ts` (Lines 311-333)
```typescript
getFrameState(store: FrameEvaluationAccess, frame?: number): FrameState {
  const comp = store.getActiveComp();
  const targetFrame = frame ?? comp?.currentFrame ?? 0;

  // Get audio reactive data from audioStore
  const audioStore = useAudioStore();
  const audioReactive =
    audioStore.audioAnalysis && audioStore.reactiveMappings.length > 0
      ? {
          analysis: audioStore.audioAnalysis,
          mappings: audioStore.reactiveMappings,
        }
      : null;

  return motionEngine.evaluate(
    targetFrame,
    store.project,
    audioStore.audioAnalysis,
    store.activeCameraId,
    true, // useCache
    audioReactive,
  );
}
```

**New Interface Created:** `ui/src/stores/animationStore/types.ts`
```typescript
export interface FrameEvaluationAccess extends AnimationStoreAccess {
  /** Full project data (for MotionEngine.evaluate) */
  project: LatticeProject;
  /** Active camera ID (for frame evaluation) */
  activeCameraId: string | null;
}
```

**Impact:** Frame evaluation logic moved to `animationStore` where it belongs. Same functionality, better organization.

---

### 3. `getInterpolatedValue` - Property Interpolation

**Location:** `ui/src/stores/compositorStore.ts` (Line ~1341)

**BEFORE (9 lines of implementation):**
```typescript
getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
  const comp = this.getActiveComp();
  const frame = comp?.currentFrame ?? 0;
  const fps = this.fps;
  const duration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;
  return interpolateProperty(property, frame, fps, "", duration);
}
```

**AFTER (1 line delegation):**
```typescript
getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
  return useKeyframeStore().getInterpolatedValue(this, property);
}
```

**CODE MOVED TO:** `ui/src/stores/keyframeStore/evaluation.ts` (Lines 257-269)
```typescript
export function getInterpolatedValue<T>(
  store: PropertyEvaluationAccess,
  property: AnimatableProperty<T>,
): T {
  const comp = store.getActiveComp();
  const frame = comp?.currentFrame ?? 0;
  const fps = store.fps;
  const duration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;
  return interpolateProperty(property, frame, fps, "", duration);
}
```

**Also Added To:** `ui/src/stores/keyframeStore/index.ts` (Lines 666-674)
```typescript
getInterpolatedValue<T>(
  compositorStore: KeyframeStoreAccess,
  property: AnimatableProperty<T>,
): T {
  return getInterpolatedValueImpl(compositorStore, property);
}
```

**Impact:** Property interpolation moved to `keyframeStore` where it belongs. Same functionality, better organization.

---

### 4. `findSnapPoint` - Timeline Snapping

**Location:** `ui/src/stores/compositorStore.ts` (Line ~2343)

**BEFORE (19 lines of implementation):**
```typescript
findSnapPoint(
  frame: number,
  pixelsPerFrame: number,
  selectedLayerId?: string | null,
): SnapResult | null {
  const audioStore = useAudioStore();
  return findNearestSnap(
    frame,
    useAnimationStore().snapConfig,
    pixelsPerFrame,
    {
      layers: this.layers,
      selectedLayerId,
      currentFrame: this.getActiveComp()?.currentFrame ?? 0,
      audioAnalysis: audioStore.audioAnalysis,
      peakData: audioStore.peakData,
    },
  );
}
```

**AFTER (1 line delegation):**
```typescript
findSnapPoint(
  frame: number,
  pixelsPerFrame: number,
  selectedLayerId?: string | null,
): SnapResult | null {
  return useAnimationStore().findSnapPoint(this, frame, pixelsPerFrame, selectedLayerId);
}
```

**CODE MOVED TO:** `ui/src/stores/animationStore/index.ts` (Lines 358-377)
```typescript
findSnapPoint(
  store: SnapPointAccess,
  frame: number,
  pixelsPerFrame: number,
  selectedLayerId?: string | null,
): SnapResult | null {
  const audioStore = useAudioStore();
  return findNearestSnap(
    frame,
    this.snapConfig,
    pixelsPerFrame,
    {
      layers: store.layers,
      selectedLayerId,
      currentFrame: store.currentFrame,
      audioAnalysis: audioStore.audioAnalysis,
      peakData: audioStore.peakData,
    },
  );
}
```

**New Interface Created:** `ui/src/stores/animationStore/types.ts`
```typescript
export interface SnapPointAccess extends AnimationStoreAccess {
  /** Get layers array (for snap point calculation) */
  readonly layers: Layer[];
}
```

**Impact:** Timeline snapping logic moved to `animationStore` where it belongs. Same functionality, better organization.

---

### 5. `currentTime` Getter - Time Calculation

**Location:** `ui/src/stores/compositorStore.ts` (Line ~329)

**BEFORE (5 lines of implementation):**
```typescript
currentTime(state): number {
  const comp = state.project.compositions[state.activeCompositionId];
  if (!comp) return 0;
  return comp.currentFrame / comp.settings.fps;
}
```

**AFTER (1 line delegation):**
```typescript
currentTime(): number {
  return useAnimationStore().getCurrentTime(this);
}
```

**CODE MOVED TO:** `ui/src/stores/animationStore/index.ts` (Lines 344-348)
```typescript
getCurrentTime(store: AnimationStoreAccess): number {
  const comp = store.getActiveComp();
  if (!comp) return 0;
  return comp.currentFrame / comp.settings.fps;
}
```

**Impact:** Time calculation moved to `animationStore` where it belongs. Changed from getter to action (Pinia getters can't take parameters).

---

## Summary Statistics

- **Methods Migrated:** 5
- **Lines of Code Moved:** ~60 lines
- **Lines of Code Deleted:** 0 (all moved, not deleted)
- **New Interfaces Created:** 2 (`FrameEvaluationAccess`, `SnapPointAccess`)
- **New Methods Added:** 5 (one in each domain store)
- **Bugs Fixed:** 1 (`setTimelineZoom` direct state mutation)

---

## Verification

✅ **TypeScript Compiles:** 0 errors  
✅ **No Functionality Lost:** All code moved, not deleted  
✅ **Proper Delegation:** All methods delegate correctly  
✅ **Domain Separation:** Code moved to appropriate stores  

---

*Created: 2026-01-12*  
*Purpose: Transparent documentation of all Phase 2 migration changes*
