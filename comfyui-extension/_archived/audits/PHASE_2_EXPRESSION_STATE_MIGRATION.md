# Phase 2: Expression State Migration Plan

> **Date:** 2026-01-12  
> **Status:** Planning  
> **Approach:** Slow and methodical

---

## Current State Analysis

### State Location
- **File:** `ui/src/stores/compositorStore.ts`
- **Lines:** 184-185 (interface), 252-253 (initialization)
- **Properties:**
  1. `propertyDriverSystem: PropertyDriverSystem | null` (default: null)
  2. `propertyDrivers: PropertyDriver[]` (default: [])

### Usage Analysis

#### Internal Usage (compositorStore.ts)
- **Line 2281:** `if (this.propertyDriverSystem && audioStore.audioAnalysis) { this.propertyDriverSystem.setAudioAnalysis(...) }`

#### External Usage (expressionStore/drivers.ts)
- **Line 28:** `store.propertyDriverSystem = new PropertyDriverSystem();`
- **Line 31:** `store.propertyDriverSystem.setPropertyGetter(...)`
- **Line 40:** `store.propertyDriverSystem.setAudioAnalysis(...)`
- **Line 44:** `for (const driver of store.propertyDrivers) { ... }`
- **Line 57:** `if (!store.propertyDriverSystem) { return new Map(); }`
- **Line 158:** `store.propertyDriverSystem.evaluateLayerDrivers(...)`
- **Line 174:** `if (store.propertyDriverSystem) { ... }`
- **Line 184:** `store.propertyDrivers.push(driver);`
- **Line 254:** `store.propertyDrivers.findIndex(...)`
- **Line 258:** `store.propertyDrivers.splice(index, 1);`
- **Line 261:** `store.propertyDriverSystem.removeDriver(...)`
- **Line 277:** `store.propertyDrivers.find(...)`
- **Line 284:** `store.propertyDriverSystem.updateDriver(...)`
- **Line 298:** `store.propertyDrivers.filter(...)`
- **Line 310:** `store.propertyDrivers.find(...)`
- **Line 315:** `store.propertyDriverSystem.updateDriver(...)`

#### ExpressionStore Comment
- **Line 12:** "Property drivers are stored on compositorStore.propertyDrivers. This store is a coordination layer for these systems."
- **This comment needs to be updated after migration**

---

## Migration Plan

### Step 1: Add to ExpressionState ✅

**File:** `ui/src/stores/expressionStore/types.ts`

**Current:** `ExpressionState` is empty `{}`

**Change:** Add properties:
```typescript
export interface ExpressionState {
  propertyDriverSystem: PropertyDriverSystemAccess | null;
  propertyDrivers: PropertyDriver[];
}
```

**Note:** `PropertyDriverSystemAccess` is already defined in types.ts (line 39)

---

### Step 2: Initialize in expressionStore State ✅

**File:** `ui/src/stores/expressionStore/index.ts`

**Change:**
```typescript
state: (): ExpressionState => ({
  propertyDriverSystem: null,
  propertyDrivers: [],
}),
```

---

### Step 3: Update ExpressionStoreAccess Interface ✅

**File:** `ui/src/stores/expressionStore/types.ts`

**Current:** `ExpressionStoreAccess` has `propertyDriverSystem` and `propertyDrivers` (lines 39-41)

**Change:** These should remain in `ExpressionStoreAccess` for backwards compatibility, but will now read from `expressionStore` state via getters

---

### Step 4: Update drivers.ts to Use expressionStore State ✅

**File:** `ui/src/stores/expressionStore/drivers.ts`

**Change:** All `store.propertyDriverSystem` and `store.propertyDrivers` references need to use `useExpressionStore()` instead

**Pattern:**
- `store.propertyDriverSystem` → `useExpressionStore().propertyDriverSystem`
- `store.propertyDrivers` → `useExpressionStore().propertyDrivers`

**But wait:** `drivers.ts` functions receive `store: ExpressionStoreAccess` parameter. We need to:
1. Get `expressionStore` instance inside each function
2. Access `expressionStore.propertyDriverSystem` and `expressionStore.propertyDrivers`
3. Update `ExpressionStoreAccess` to not require these properties (or make them optional)

**Better approach:** Update `ExpressionStoreAccess` to remove `propertyDriverSystem` and `propertyDrivers`, and access them directly from `useExpressionStore()` inside the functions.

---

### Step 5: Update compositorStore ✅

**File:** `ui/src/stores/compositorStore.ts`

**Changes:**
1. Remove `propertyDriverSystem` and `propertyDrivers` from state interface (lines 184-185)
2. Remove from state initialization (lines 252-253)
3. Add getters for backwards compatibility:
   ```typescript
   propertyDriverSystem(): PropertyDriverSystem | null {
     return useExpressionStore().propertyDriverSystem;
   },
   propertyDrivers(): PropertyDriver[] {
     return useExpressionStore().propertyDrivers;
   },
   ```
4. Update line 2281 to use getter or `useExpressionStore()` directly

---

### Step 6: Update Comment ✅

**File:** `ui/src/stores/expressionStore/index.ts`

**Change:** Update comment on line 12:
```typescript
* Property drivers are stored on expressionStore.propertyDrivers.
* This store manages the property driver system state.
```

---

## Verification Checklist

### Before Migration:
- [ ] Read all `drivers.ts` functions to understand exact usage patterns
- [ ] Verify `ExpressionStoreAccess` interface usage
- [ ] Check if any other files access `compositorStore.propertyDriverSystem` or `propertyDrivers`

### During Migration:
- [ ] Add properties to `ExpressionState` interface
- [ ] Initialize in `expressionStore` state
- [ ] Update `drivers.ts` to use `useExpressionStore()` instead of `store.propertyDriverSystem/propertyDrivers`
- [ ] Update `ExpressionStoreAccess` interface (remove or make optional)
- [ ] Remove from `compositorStore` state
- [ ] Add getters to `compositorStore`
- [ ] Update compositorStore line 2281
- [ ] Update comment in expressionStore/index.ts

### After Migration:
- [ ] TypeScript compilation passes (`npx tsc --noEmit`)
- [ ] Linter passes (`npx biome check`)
- [ ] All consumers still work (backwards compatible)
- [ ] Manual testing: Property drivers work correctly

---

## Estimated Time

**Planning:** 20 minutes  
**Implementation:** 45-60 minutes  
**Verification:** 20-30 minutes  
**Total:** ~1.5-2 hours

---

## Next Steps

1. **Read drivers.ts completely** - Understand all usage patterns
2. **Check ExpressionStoreAccess** - Verify interface requirements
3. **Implement migration** - Step by step, verify after each step
4. **Test thoroughly** - TypeScript, linter, manual testing

---

*This plan will be executed slowly and methodically with verification at each step*
