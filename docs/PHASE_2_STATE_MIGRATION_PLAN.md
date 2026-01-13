# Phase 2 State Migration Plan

> **Date:** 2026-01-12  
> **Purpose:** Plan migration of remaining state properties from compositorStore to domain stores  
> **Status:** Planning phase

---

## Current State Analysis

### Animation State Properties

#### 1. `isPlaying: boolean` (compositorStore.ts:140)

**Current Architecture:**
- `playbackStore.ts` has its own `isPlaying` state (manages actual playback loop)
- `compositorStore.ts` has `isPlaying` state (UI flag, synced by animationStore/playback.ts)
- `animationStore/playback.ts` sets `store.isPlaying = true/false` (line 31, 40)

**Usage:**
- Set by: `animationStore/playback.ts` (play, pause methods)
- Read by: `audioStore.ts`, `playbackStore.ts` (checks compositorStore.isPlaying)
- Consumers: UI components that need to know playback state

**Migration Options:**

**Option A: Remove from compositorStore, use playbackStore directly**
- ✅ `playbackStore` already manages `isPlaying`
- ✅ Single source of truth
- ⚠️ Requires updating consumers to use `usePlaybackStore().isPlaying`
- ⚠️ `AnimationStoreAccess` interface expects `isPlaying` (line 18)

**Option B: Add to animationStore, delegate to playbackStore**
- ✅ Maintains animationStore API
- ✅ Single source of truth (playbackStore)
- ⚠️ Adds indirection layer

**Option C: Keep in compositorStore (backwards compat)**
- ✅ No consumer changes needed
- ❌ Duplicate state (redundant with playbackStore)

**Recommendation:** Option B - Add getter to animationStore that reads from playbackStore, remove from compositorStore

---

#### 2. `timelineZoom: number` (compositorStore.ts:210)

**Current State:**
- State in compositorStore (line 210, initialized to 1)
- Only used in compositorStore (no external consumers found)

**Migration:**
- ✅ Straightforward - move to animationStore state
- ✅ No external dependencies

**Action:** Migrate to `animationStore` state

---

#### 3. `snapConfig: SnapConfig` (compositorStore.ts:189)

**Current State:**
- State in compositorStore (line 189, initialized with DEFAULT_SNAP_CONFIG)
- Methods in compositorStore: `setSnapConfig`, `toggleSnapping`, `toggleSnapType` (lines 2407-2440)
- Used by: `findNearestSnap` helper (line 2393)

**Migration:**
- ✅ Move state to animationStore
- ✅ Move methods to animationStore
- ⚠️ Update `findNearestSnap` to accept snapConfig as parameter

**Action:** Migrate state and methods to `animationStore`

---

### Expression State Properties

#### 4. `propertyDriverSystem: PropertyDriverSystem | null` (compositorStore.ts:255)

**Current State:**
- State in compositorStore (line 255, initialized to null)
- Initialized by: `initializePropertyDriverSystem()` (delegates to expressionStore)
- Used by: Expression evaluation system

**Migration:**
- ✅ Move to expressionStore state
- ✅ Already managed by expressionStore methods

**Action:** Migrate to `expressionStore` state

---

#### 5. `propertyDrivers: PropertyDriver[]` (compositorStore.ts:256)

**Current State:**
- State in compositorStore (line 256, initialized to [])
- CRUD methods delegate to expressionStore
- Used by: Property driver evaluation system

**Note:** According to `expressionStore/index.ts` comment (line 12): "Property drivers are stored on compositorStore.propertyDrivers. This store is a coordination layer for these systems."

**Migration Decision Needed:**
- **Option A:** Keep in compositorStore (as documented)
- **Option B:** Migrate to expressionStore (for consistency)

**Recommendation:** Option B - Migrate to expressionStore for proper domain separation

**Action:** Migrate to `expressionStore` state (update comment in expressionStore)

---

## Migration Priority

### High Priority (Straightforward)
1. ✅ `timelineZoom` → animationStore (no dependencies)
2. ✅ `snapConfig` + methods → animationStore (clear ownership)

### Medium Priority (Requires Decisions)
3. ⏳ `isPlaying` → animationStore getter (delegates to playbackStore)
4. ⏳ `propertyDriverSystem` → expressionStore
5. ⏳ `propertyDrivers` → expressionStore (update comment)

---

## Migration Steps

### Step 1: Migrate `timelineZoom`

1. Add `timelineZoom: number` to `AnimationState`
2. Initialize in `animationStore` state (default: 1)
3. Remove from `compositorStore` state
4. Add getter to compositorStore: `get timelineZoom() { return useAnimationStore().timelineZoom; }`
5. Update consumers (if any) to use animationStore directly

### Step 2: Migrate `snapConfig` + Methods

1. Add `snapConfig: SnapConfig` to `AnimationState`
2. Initialize in `animationStore` state (default: DEFAULT_SNAP_CONFIG)
3. Move `setSnapConfig`, `toggleSnapping`, `toggleSnapType` to animationStore
4. Remove from `compositorStore` state and methods
5. Add getter to compositorStore: `get snapConfig() { return useAnimationStore().snapConfig; }`
6. Update `findNearestSnap` to accept snapConfig parameter
7. Update consumers to use animationStore methods

### Step 3: Migrate `isPlaying`

1. Add getter to `animationStore`: `get isPlaying() { return usePlaybackStore().isPlaying; }`
2. Remove `isPlaying` from `compositorStore` state
3. Remove `store.isPlaying = true/false` from `animationStore/playback.ts`
4. Update `AnimationStoreAccess` interface to remove `isPlaying` (or make optional)
5. Update consumers to use `useAnimationStore().isPlaying` or `usePlaybackStore().isPlaying`

### Step 4: Migrate Expression State

1. Add `propertyDriverSystem: PropertyDriverSystem | null` to `ExpressionState`
2. Add `propertyDrivers: PropertyDriver[]` to `ExpressionState`
3. Initialize in `expressionStore` state
4. Remove from `compositorStore` state
5. Update expressionStore methods to use local state
6. Update comment in expressionStore/index.ts
7. Update consumers to use expressionStore state

---

## Testing Checklist

After each migration:
- [ ] TypeScript compilation passes (`npx tsc --noEmit`)
- [ ] Linter passes (`npx biome check`)
- [ ] All tests pass (`npm test`)
- [ ] UI components still work (manual testing)
- [ ] No regressions in playback/expression functionality

---

## Estimated Time

- `timelineZoom`: 30 minutes
- `snapConfig` + methods: 1-2 hours
- `isPlaying`: 1-2 hours (requires consumer updates)
- Expression state: 1-2 hours

**Total:** ~4-7 hours

---

## Next Steps

1. Start with `timelineZoom` (simplest)
2. Migrate `snapConfig` + methods
3. Migrate `isPlaying` (requires careful consumer updates)
4. Migrate expression state
