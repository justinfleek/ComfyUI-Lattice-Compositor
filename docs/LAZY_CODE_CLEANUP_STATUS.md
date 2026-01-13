# Lazy Code Cleanup Status

> **Date:** 2026-01-12  
> **Status:** ⚠️ **INTRODUCED TECHNICAL DEBT** - Need to fix before continuing

---

## Problem

During Phase 2-4 migration, I introduced `as unknown as` type assertions which are **exactly the lazy code patterns we're trying to eliminate**.

**Current count:** 4 instances of `as unknown as` in `compositorStore.ts`

---

## Instances Introduced (NOW FIXED ✅)

1. ✅ **Line 330:** `currentTime()` getter - FIXED (uses state directly)
2. ✅ **Line 341:** `visibleLayers()` getter - FIXED (uses state directly)
3. ✅ **Line 347:** `displayedLayers()` getter - FIXED (uses state directly)
4. ✅ **Line 421:** `cameraLayers()` getter - FIXED (uses state directly)

**Solution:** Pinia getters access `state` parameter directly, not `this` (which refers to state, not store instance).

---

## Root Cause

Pinia getters have `this` typed as the store instance, but when delegating to other stores that expect `CompositorStoreAccess`, TypeScript doesn't recognize that `compositorStore` implements that interface.

**The real issue:** `compositorStore` should properly implement `CompositorStoreAccess`, but Pinia stores don't implement TypeScript interfaces directly.

---

## Proper Solution

Instead of type assertions, we should:

1. **Option A:** Create helper objects that properly implement the interface
   ```typescript
   visibleLayers(): Layer[] {
     return useLayerStore().getVisibleLayers({
       getActiveCompLayers: () => this.getActiveCompLayers(),
       project: this.project,
       pushHistory: () => this.pushHistory(),
     });
   }
   ```

2. **Option B:** Make the store methods accept partial interfaces
   ```typescript
   // In layerStore/hierarchy.ts
   export function getVisibleLayers(
     store: { getActiveCompLayers(): Layer[] },
   ): Layer[] {
     // Only needs getActiveCompLayers, not full CompositorStoreAccess
   }
   ```

3. **Option C:** Convert getters to actions (breaks API)

**RECOMMENDATION:** Option B - Make interfaces minimal and only require what's actually needed.

---

## Remaining Work Before Lazy Code Cleanup

**~17 methods/getters remaining:**
- Phase 5: 11 methods/getters
- Settings Getters: 6 getters

**Order:**
1. ✅ Finish Phase 2-4 migration (DONE)
2. ⏳ Complete Phase 5 + Settings Getters (~17 remaining)
3. ⏳ DELETE compositorStore.ts
4. ⏳ **THEN** Start lazy code cleanup phase

**Lazy Code Patterns to Fix (After Phase 5):**
- `as any`, `as unknown as` type assertions
- `!` non-null assertions
- `??`, `|| 0`, `|| []`, `|| {}` fallbacks
- `?.` optional chaining abuse
- `@ts-ignore`, `@ts-expect-error`
- **NaN, Infinity, null handling**
- **isFinite, isNaN checks**
- **And many more patterns...**

---

## Action Items

1. ✅ **FIX NOW:** Replace all `as unknown as` with proper interface implementations
2. ⏳ **AFTER PHASE 5:** Begin systematic lazy code cleanup (Phase 6)
3. ⏳ **TARGET:** Zero `as unknown as`, `as any`, `!`, `??`, `|| 0` patterns

---

*Created: 2026-01-12*  
*Purpose: Track lazy code cleanup progress*
