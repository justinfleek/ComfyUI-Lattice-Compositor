# Phase 2: snapConfig Migration Plan

> **Date:** 2026-01-12  
> **Status:** Planning  
> **Approach:** Slow and methodical

---

## Current State Analysis

### State Location
- **File:** `ui/src/stores/compositorStore.ts`
- **Line:** 189 (interface), 258 (initialization)
- **Type:** `SnapConfig` (from `@/services/timelineSnap`)
- **Default:** `{ ...DEFAULT_SNAP_CONFIG }`

### Methods Location
- **File:** `ui/src/stores/compositorStore.ts`
- **Lines:** 2410-2443
- **Methods:**
  1. `setSnapConfig(config: Partial<SnapConfig>)` - Line 2410
  2. `toggleSnapping()` - Line 2413
  3. `toggleSnapType(type: ...)` - Line 2416

### Usage Analysis

#### Internal Usage (compositorStore.ts)
- **Line 2396:** `findNearestSnap(frame, this.snapConfig, pixelsPerFrame, {...})`
  - Method: `findNearestSnap(frame, pixelsPerFrame, selectedLayerId?)`
  - Uses `this.snapConfig` directly

#### External Consumers (Found via grep)
1. **`ui/src/components/timeline/TimelinePanel.vue`** - Need to check usage
2. **`ui/src/components/timeline/PropertyTrack.vue`** - Need to check usage
3. **`ui/src/components/curve-editor/CurveEditor.vue`** - Need to check usage
4. **`ui/src/stores/actions/projectActions/serialization.ts`** - Need to check usage
5. **`ui/src/__tests__/tutorials/tutorial-01-fundamentals.test.ts`** - Test file

---

## Migration Plan

### Step 1: Add to AnimationState ✅

**File:** `ui/src/stores/animationStore/types.ts`

**Change:**
```typescript
export interface AnimationState {
  // ... existing fields ...
  /** Timeline snap configuration */
  snapConfig: SnapConfig;
}
```

**Import:** Add `import type { SnapConfig } from "@/services/timelineSnap";`

---

### Step 2: Initialize in animationStore State ✅

**File:** `ui/src/stores/animationStore/index.ts`

**Change:**
```typescript
import { DEFAULT_SNAP_CONFIG } from "@/services/timelineSnap";

state: (): AnimationState => ({
  // ... existing fields ...
  snapConfig: { ...DEFAULT_SNAP_CONFIG },
}),
```

---

### Step 3: Add Methods to animationStore ✅

**File:** `ui/src/stores/animationStore/index.ts`

**Add actions:**
```typescript
actions: {
  // ... existing actions ...
  
  /**
   * Set snap configuration
   */
  setSnapConfig(config: Partial<SnapConfig>): void {
    this.snapConfig = { ...this.snapConfig, ...config };
  },
  
  /**
   * Toggle snapping on/off
   */
  toggleSnapping(): void {
    this.snapConfig.enabled = !this.snapConfig.enabled;
  },
  
  /**
   * Toggle specific snap type
   */
  toggleSnapType(
    type:
      | "grid"
      | "keyframes"
      | "beats"
      | "peaks"
      | "layerBounds"
      | "playhead",
  ): void {
    type BooleanSnapKey =
      | "snapToGrid"
      | "snapToKeyframes"
      | "snapToBeats"
      | "snapToPeaks"
      | "snapToLayerBounds"
      | "snapToPlayhead";
    const typeMap: Record<typeof type, BooleanSnapKey> = {
      grid: "snapToGrid",
      keyframes: "snapToKeyframes",
      beats: "snapToBeats",
      peaks: "snapToPeaks",
      layerBounds: "snapToLayerBounds",
      playhead: "snapToPlayhead",
    };
    const key = typeMap[type];
    this.snapConfig[key] = !this.snapConfig[key];
  },
}
```

---

### Step 4: Update compositorStore.findNearestSnap ✅

**File:** `ui/src/stores/compositorStore.ts`

**Current (Line 2396):**
```typescript
return findNearestSnap(frame, this.snapConfig, pixelsPerFrame, {...});
```

**Change to:**
```typescript
return findNearestSnap(
  frame,
  useAnimationStore().snapConfig,
  pixelsPerFrame,
  {...}
);
```

**Import:** Ensure `useAnimationStore` is imported (already is at line 113)

---

### Step 5: Remove from compositorStore State ✅

**File:** `ui/src/stores/compositorStore.ts`

**Remove:**
- Line 189: `snapConfig: SnapConfig;` from interface
- Line 258: `snapConfig: { ...DEFAULT_SNAP_CONFIG },` from state initialization

---

### Step 6: Add Getter Delegation ✅

**File:** `ui/src/stores/compositorStore.ts`

**Add getter:**
```typescript
getters: {
  // ... existing getters ...
  
  // Snap config (delegated to animationStore)
  snapConfig(): SnapConfig {
    return useAnimationStore().snapConfig;
  },
}
```

---

### Step 7: Update compositorStore Methods to Delegate ✅

**File:** `ui/src/stores/compositorStore.ts`

**Replace methods (lines 2410-2443):**
```typescript
setSnapConfig(config: Partial<SnapConfig>): void {
  useAnimationStore().setSnapConfig(config);
},

toggleSnapping(): void {
  useAnimationStore().toggleSnapping();
},

toggleSnapType(
  type:
    | "grid"
    | "keyframes"
    | "beats"
    | "peaks"
    | "layerBounds"
    | "playhead",
): void {
  useAnimationStore().toggleSnapType(type);
},
```

---

### Step 8: Verify Consumers ✅

**Check each consumer:**
1. ✅ `TimelinePanel.vue` - Verify usage pattern
2. ✅ `PropertyTrack.vue` - Verify usage pattern
3. ✅ `CurveEditor.vue` - Verify usage pattern
4. ✅ `serialization.ts` - Verify serialization/deserialization
5. ✅ Test file - Update if needed

**Expected:** All consumers use `compositorStore.snapConfig` or `compositorStore.setSnapConfig()` - should continue working via getter/method delegation

---

## Verification Checklist

### Before Migration:
- [ ] Read all consumer files to understand usage patterns
- [ ] Verify `findNearestSnap` usage in compositorStore
- [ ] Check if serialization needs updates

### During Migration:
- [ ] Add `snapConfig` to `AnimationState` interface
- [ ] Initialize in `animationStore` state
- [ ] Add methods to `animationStore`
- [ ] Update `compositorStore.findNearestSnap` to use animationStore
- [ ] Remove from `compositorStore` state
- [ ] Add getter delegation
- [ ] Update method delegations

### After Migration:
- [ ] TypeScript compilation passes (`npx tsc --noEmit`)
- [ ] Linter passes (`npx biome check`)
- [ ] All consumers still work (backwards compatible)
- [ ] Test file passes
- [ ] Manual testing: Toggle snapping, change snap config

---

## Estimated Time

**Planning:** 15 minutes  
**Implementation:** 30-45 minutes  
**Verification:** 15-30 minutes  
**Total:** ~1-1.5 hours

---

## Next Steps

1. **Read consumer files** - Understand exact usage patterns
2. **Implement migration** - Step by step, verify after each step
3. **Test thoroughly** - TypeScript, linter, manual testing
4. **Document completion** - Update progress docs

---

*This plan will be executed slowly and methodically with verification at each step*
