# Phase 2: isPlaying Migration Plan

> **Date:** 2026-01-12  
> **Status:** Planning  
> **Approach:** Slow and methodical

---

## Current State Analysis

### State Location
- **File:** `ui/src/stores/compositorStore.ts`
- **Line:** 140 (interface), 225 (initialization)
- **Type:** `boolean`
- **Default:** `false`

### Usage Analysis

#### Internal Usage (compositorStore.ts)
- **Line 140:** State property declaration
- **Line 225:** Initialized to `false`

#### External Usage (animationStore/playback.ts)
- **Line 31:** `store.isPlaying = true;` in `play()` function
- **Line 40:** `store.isPlaying = false;` in `pause()` function
- **Line 17:** `if (playback.isPlaying) return;` - checks playbackStore.isPlaying
- **Line 48:** `if (playback.isPlaying)` - checks playbackStore.isPlaying

#### External Consumers (Found via grep - 15 files)
1. `ui/src/stores/compositorStore.ts` - State definition
2. `ui/src/stores/animationStore/types.ts` - `AnimationStoreAccess` interface
3. `ui/src/composables/useKeyboardShortcuts.ts` - Need to check usage
4. `ui/src/stores/animationStore/playback.ts` - Sets `store.isPlaying`
5. `ui/src/stores/audioStore.ts` - Need to check usage
6. `ui/src/components/layout/WorkspaceLayout.vue` - Need to check usage
7. `ui/src/engine/layers/SplineLayer.ts` - Need to check usage
8. `ui/src/components/preview/HDPreviewWindow.vue` - Need to check usage
9. `ui/src/components/panels/PreviewPanel.vue` - Need to check usage
10. `ui/src/components/layout/WorkspaceToolbar.vue` - Need to check usage
11. `ui/src/stores/playbackStore.ts` - Need to check if it has isPlaying
12. `ui/src/stores/actions/playbackActions.ts` - Need to check usage
13. `ui/src/services/vectorLOD.ts` - Need to check usage
14. `ui/src/engine/layers/AudioLayer.ts` - Need to check usage
15. Test files

---

## Architecture Understanding

### playbackStore Analysis Needed
- Does `playbackStore` have `isPlaying` state?
- Is `playbackStore.isPlaying` the source of truth?
- How does `compositorStore.isPlaying` relate to `playbackStore.isPlaying`?

### Current Pattern
From `animationStore/playback.ts`:
- `play()` function calls `playback.play()` (playbackStore)
- Then sets `store.isPlaying = true` (compositorStore)
- `pause()` function calls `playback.stop()` (playbackStore)
- Then sets `store.isPlaying = false` (compositorStore)

**Issue:** There's duplication - `playbackStore` manages playback, but `compositorStore.isPlaying` is also set.

---

## Migration Plan

### Option A: Use playbackStore.isPlaying as Source of Truth

**If `playbackStore` has `isPlaying` state:**

1. ✅ Add getter to `animationStore`: `get isPlaying() { return usePlaybackStore().isPlaying; }`
2. ✅ Remove `isPlaying` from `compositorStore` state (interface and initialization)
3. ✅ Remove `store.isPlaying = true/false` from `animationStore/playback.ts`
4. ✅ Update `AnimationStoreAccess` interface to remove `isPlaying` requirement
5. ✅ Add getter to compositorStore: `get isPlaying() { return useAnimationStore().isPlaying; }`
6. ✅ Update consumers to use `useAnimationStore().isPlaying` or `usePlaybackStore().isPlaying`

### Option B: Migrate isPlaying to animationStore State

**If `playbackStore` doesn't have `isPlaying` state:**

1. ✅ Add `isPlaying: boolean` to `AnimationState`
2. ✅ Initialize in `animationStore` state (default: false)
3. ✅ Update `animationStore/playback.ts` to set `useAnimationStore().isPlaying = true/false`
4. ✅ Remove `isPlaying` from `compositorStore` state
5. ✅ Add getter to compositorStore: `get isPlaying() { return useAnimationStore().isPlaying; }`
6. ✅ Update `AnimationStoreAccess` interface to remove `isPlaying` requirement (or make it read-only)
7. ✅ Update consumers

---

## Verification Checklist

### Before Migration:
- [ ] Check if `playbackStore` has `isPlaying` state
- [ ] Understand relationship between `playbackStore.isPlaying` and `compositorStore.isPlaying`
- [ ] Read all consumer files to understand usage patterns
- [ ] Verify `AnimationStoreAccess` usage

### During Migration:
- [ ] Choose Option A or B based on playbackStore architecture
- [ ] Add `isPlaying` to appropriate store (animationStore or getter from playbackStore)
- [ ] Remove from `compositorStore` state
- [ ] Update `animationStore/playback.ts` to not set `store.isPlaying`
- [ ] Update `AnimationStoreAccess` interface
- [ ] Add getter delegation in compositorStore

### After Migration:
- [ ] TypeScript compilation passes (`npx tsc --noEmit`)
- [ ] Linter passes (`npx biome check`)
- [ ] All consumers still work (backwards compatible)
- [ ] Manual testing: Play/pause functionality works

---

## Estimated Time

**Planning:** 20 minutes  
**Implementation:** 30-45 minutes  
**Verification:** 15-30 minutes  
**Total:** ~1-1.5 hours

---

## Next Steps

1. **Check playbackStore** - Does it have `isPlaying` state?
2. **Read consumer files** - Understand exact usage patterns
3. **Choose migration option** - Based on architecture
4. **Implement migration** - Step by step, verify after each step
5. **Test thoroughly** - TypeScript, linter, manual testing

---

*This plan will be executed slowly and methodically with verification at each step*
