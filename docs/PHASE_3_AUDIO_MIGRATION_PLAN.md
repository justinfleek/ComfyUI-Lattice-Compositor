# Phase 3 Audio Migration Plan

> **Date:** 2026-01-12  
> **Status:** ⏳ IN PROGRESS

---

## Methods to Migrate

### 1. `loadAudio` - Property Driver System Update

**CURRENT (compositorStore.ts:2220-2228):**
```typescript
async loadAudio(file: File): Promise<void> {
  const audioStore = useAudioStore();
  await audioStore.loadAudio(file, this.project.composition.fps);
  // Update property driver system with new audio analysis
  const expressionStore = useExpressionStore();
  if (expressionStore.propertyDriverSystem && audioStore.audioAnalysis) {
    expressionStore.propertyDriverSystem.setAudioAnalysis(audioStore.audioAnalysis);
  }
}
```

**CHANGE:** Move property driver system update INTO `audioStore.loadAudio()`  
**TARGET:** `ui/src/stores/audioStore.ts` (after line 200, after `initializeReactiveMapper()`)

**AFTER (compositorStore.ts):**
```typescript
async loadAudio(file: File): Promise<void> {
  await useAudioStore().loadAudio(file, this.project.composition.fps);
}
```

**AFTER (audioStore.ts):**
```typescript
async loadAudio(file: File, fps: number): Promise<void> {
  // ... existing load logic ...
  
  // Initialize the audio reactive mapper
  this.initializeReactiveMapper();
  
  // Update property driver system with new audio analysis
  const expressionStore = useExpressionStore();
  if (expressionStore.propertyDriverSystem && this.audioAnalysis) {
    expressionStore.propertyDriverSystem.setAudioAnalysis(this.audioAnalysis);
  }
  
  // ... rest of method ...
}
```

---

### 2. `clearAudio` - Path Animators Cleanup

**CURRENT (compositorStore.ts:2232-2236):**
```typescript
clearAudio(): void {
  useAudioStore().clear();
  // Clear path animators (still managed locally)
  this.pathAnimators.clear();
}
```

**ISSUE:** `pathAnimators` is state in `compositorStore`, not `audioStore`

**OPTIONS:**
1. **Pass callback** - `audioStore.clear(callback)` to clear pathAnimators
2. **Keep separate** - compositorStore handles pathAnimators, audioStore just clears audio
3. **Move pathAnimators** - Move `pathAnimators` state to `audioStore` (bigger change)

**RECOMMENDATION:** Option 2 - Keep pathAnimators cleanup in compositorStore, but make it cleaner:
- `audioStore.clear()` handles audio cleanup
- `compositorStore.clearAudio()` delegates to audioStore AND clears pathAnimators

**AFTER (compositorStore.ts):**
```typescript
clearAudio(): void {
  useAudioStore().clear();
  this.pathAnimators.clear(); // Still managed here
}
```

**NOTE:** This is already clean - just removing the comment. The delegation is correct.

---

### 3. `getAudioFeatureAtFrame` - Frame Parameter

**CURRENT (compositorStore.ts:2246-2249):**
```typescript
getAudioFeatureAtFrame(feature: string, frame?: number): number {
  const targetFrame = frame ?? this.getActiveComp()?.currentFrame ?? 0;
  return useAudioStore().getFeatureAtFrame(feature, targetFrame);
}
```

**CHANGE:** Move frame resolution INTO `audioStore.getFeatureAtFrame()`  
**ISSUE:** `audioStore` doesn't have access to `getActiveComp()` or `currentFrame`

**OPTIONS:**
1. **Pass store access** - `audioStore.getFeatureAtFrame(store, feature, frame?)`
2. **Keep in compositorStore** - compositorStore resolves frame, audioStore just gets feature
3. **Accept frame always** - Require frame parameter (breaking change)

**RECOMMENDATION:** Option 1 - Pass store access for frame resolution

**AFTER (compositorStore.ts):**
```typescript
getAudioFeatureAtFrame(feature: string, frame?: number): number {
  return useAudioStore().getFeatureAtFrame(this, feature, frame);
}
```

**AFTER (audioStore.ts):**
```typescript
getFeatureAtFrame(
  store: { getActiveComp(): { currentFrame: number } | null },
  feature: string,
  frame?: number,
): number {
  const targetFrame = frame ?? store.getActiveComp()?.currentFrame ?? 0;
  return getFeatureAtFrame(this.audioAnalysis, feature, targetFrame);
}
```

---

## Summary

- **`loadAudio`**: Add property driver update to `audioStore.loadAudio()`
- **`clearAudio`**: Already clean, just remove comment
- **`getAudioFeatureAtFrame`**: Move frame resolution to `audioStore.getFeatureAtFrame()` with store access

---

*Created: 2026-01-12*
