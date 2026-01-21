# Incremental State Snapshots Implementation Plan

> **Status:** 🔴 **BLOCKED** - Must fix errors first before implementation  
> **Date:** 2026-01-18  
> **Principle:** Zero shortcuts, zero half-measures, zero "acceptable for now"

---

## Executive Summary

**Current State:** Full project snapshots (entire `LatticeProject` cloned)  
**Target State:** Incremental/delta snapshots (only changed properties)  
**Blocking Issues:** Multiple errors must be fixed before refactor can proceed safely

**⚠️ CRITICAL:** No shortcuts or temporary solutions. All errors must be fixed before implementing incremental snapshots.

---

## Why Incremental State Snapshots?

### Current Problem: Full Project Snapshots

```typescript
// Current: Snapshot entire project (expensive)
const snapshot = structuredClone<LatticeProject>(toRaw(this.project));
// Memory: ~5-50MB per snapshot × 50 snapshots = 250MB-2.5GB
// Performance: Deep cloning entire project is slow
```

**Issues:**
- **Memory:** Each snapshot stores entire project (all layers, compositions, assets, metadata)
- **Performance:** Deep cloning large projects is expensive
- **Scalability:** Memory usage grows linearly with project size
- **Memory Leak:** Known bug - ~744KB leak per undo/redo cycle (see `memory.test.ts:183`)

### Target Solution: Incremental/Delta Snapshots

```typescript
// Target: Snapshot only changed properties
interface StateDelta {
  path: string[];  // e.g., ["compositions", "main", "layers", "layer_123", "data", "text"]
  oldValue: unknown;
  newValue: unknown;
  timestamp: number;
}

// Memory: ~1-10KB per delta × 50 deltas = 50KB-500KB (99% reduction)
// Performance: Only serialize changed paths
```

**Benefits:**
- **Memory:** 99% reduction (only changed properties stored)
- **Performance:** Faster snapshots (only serialize diffs)
- **Scalability:** Memory usage independent of project size
- **Fix Memory Leak:** Structural sharing prevents reference retention

---

## Blocking Issues (Must Fix First)

### 🔴 CRITICAL: Memory Leak in History System

**Location:** `ui/src/__tests__/performance/memory.test.ts:183`  
**Status:** Known bug, documented but not fixed  
**Impact:** ~744KB leak per undo/redo cycle, ~372MB after 500 cycles

**Root Cause:**
```typescript
// History snapshots retain references to layer objects
// structuredClone() creates deep copies but Vue reactivity proxies may retain references
const snapshot = structuredClone(toRaw(this.project));  // May not fully isolate
```

**Fix Required:**
1. Verify `structuredClone()` fully isolates Vue reactive proxies
2. Implement structural sharing for unchanged objects
3. Add memory leak tests that pass (currently `.fails()`)
4. Verify no references retained after GC

**Priority:** 🔴 **MUST FIX BEFORE REFACTOR** - Incremental snapshots won't help if we leak memory

---

### 🔴 CRITICAL: Type Escapes (698 instances)

**Location:** `docs/TYPE_ESCAPE_AUDIT.md`  
**Status:** 194/698 fixed (27.8%), 504 remaining  
**Impact:** Type safety violations could corrupt state during diff/merge

**Required Fixes:**
- `Record<string, unknown>` (136 instances) - Must be proper interfaces
- `: unknown` (235 instances) - Must be specific types
- `as any` (82 instances) - Must use proper type narrowing
- `as unknown` (43 instances) - Must use proper type guards
- `unknown as` (33 instances) - Must remove double assertions
- `Record<string, any>` (71 instances) - Must be typed interfaces
- `: any` (70 instances) - Must be proper types
- `z.unknown()` (28 instances) - Must be proper Zod schemas

**Why Critical for Incremental Snapshots:**
- Diff algorithm needs strict types to identify changes
- Merge algorithm needs type safety to prevent corruption
- Type escapes could cause silent data corruption during undo/redo

**Priority:** 🔴 **MUST FIX BEFORE REFACTOR** - Type safety required for diff/merge

---

### 🟡 HIGH: Fragmented History Architecture

**Location:** `docs/MASTER_AUDIT_2026-01-18.md:279-308`  
**Status:** Working but convoluted  
**Impact:** Confusing architecture makes refactor risky

**Current State:**
- `historyStore.ts` exists but orphaned (not used)
- `projectStore.ts` manages history methods
- `compositorStore.ts` stores history state
- Domain stores call `store.pushHistory()` → compositorStore → projectStore

**Fix Required:**
1. Decide: Integrate `historyStore.ts` OR remove it
2. Consolidate history state in one location
3. Update all consumers to use unified API
4. Remove architectural confusion

**Priority:** 🟡 **SHOULD FIX BEFORE REFACTOR** - Clean architecture required for incremental snapshots

---

### 🟡 HIGH: Missing Type Safety in History Operations

**Location:** `ui/src/stores/projectStore.ts:448-477`  
**Status:** Type assertions removed, but need verification  
**Impact:** Need strict typing for diff/merge operations

**Current State:**
```typescript
// Fixed: Removed type assertions
const snapshot: LatticeProject = structuredClone<LatticeProject>(toRaw(this.project));
```

**Required Verification:**
1. Verify `structuredClone<T>()` properly types all nested objects
2. Ensure no `any` types leak through
3. Add runtime validation for snapshot integrity
4. Test type safety with complex nested structures

**Priority:** 🟡 **SHOULD VERIFY BEFORE REFACTOR** - Type safety critical for diff/merge

---

## Implementation Plan

### Phase 1: Fix Blocking Errors (REQUIRED)

**Status:** 🔴 **NOT STARTED**  
**Estimated Time:** 2-4 weeks

#### 1.1 Fix Memory Leak
- [ ] Investigate root cause of memory leak
- [ ] Verify `structuredClone()` isolation
- [ ] Implement structural sharing for unchanged objects
- [ ] Add memory leak tests that pass
- [ ] Verify no references retained after GC
- [ ] Document fix in `memory.test.ts`

**Files:**
- `ui/src/stores/projectStore.ts`
- `ui/src/__tests__/performance/memory.test.ts`

#### 1.2 Fix Type Escapes (504 remaining)
- [ ] Fix `Record<string, unknown>` (136 instances)
- [ ] Fix `: unknown` (235 instances)
- [ ] Fix `as any` (82 instances)
- [ ] Fix `as unknown` (43 instances)
- [ ] Fix `unknown as` (33 instances)
- [ ] Fix `Record<string, any>` (71 instances)
- [ ] Fix `: any` (70 instances)
- [ ] Fix `z.unknown()` (28 instances)
- [ ] Verify all fixes with `npx tsc --noEmit`
- [ ] Update `TYPE_ESCAPE_AUDIT.md` with progress

**Files:**
- All files listed in `docs/TYPE_ESCAPE_AUDIT.md`
- `ui/src/schemas/**/*.ts` (Zod schemas)

#### 1.3 Consolidate History Architecture
- [ ] Decide: Use `historyStore.ts` OR remove it
- [ ] Consolidate history state in one location
- [ ] Update all consumers to use unified API
- [ ] Remove architectural confusion
- [ ] Document final architecture

**Files:**
- `ui/src/stores/historyStore.ts`
- `ui/src/stores/projectStore.ts`
- `ui/src/stores/compositorStore.ts`
- All files calling `pushHistory()`

#### 1.4 Verify Type Safety
- [ ] Verify `structuredClone<T>()` types all nested objects
- [ ] Ensure no `any` types leak through
- [ ] Add runtime validation for snapshot integrity
- [ ] Test type safety with complex nested structures
- [ ] Document type safety guarantees

**Files:**
- `ui/src/stores/projectStore.ts`
- `ui/src/__tests__/services/undoredo.property.test.ts`

---

### Phase 2: Implement Incremental State Snapshots (AFTER ERRORS FIXED)

**Status:** 🔴 **BLOCKED** - Cannot start until Phase 1 complete  
**Estimated Time:** 3-5 weeks

#### 2.1 Design Delta Structure
- [ ] Define `StateDelta` interface
- [ ] Design path-based change tracking
- [ ] Design merge algorithm for deltas
- [ ] Design diff algorithm (old → new)
- [ ] Handle edge cases (nested objects, arrays, circular refs)
- [ ] Document delta structure

**Files:**
- `ui/src/stores/history/types.ts` (new)

#### 2.2 Implement Diff Algorithm
- [ ] Implement `diffState(oldState, newState): StateDelta[]`
- [ ] Handle all property types (primitives, objects, arrays)
- [ ] Handle nested structures (compositions, layers, effects)
- [ ] Handle array changes (add, remove, reorder)
- [ ] Optimize for performance (avoid deep comparison)
- [ ] Add comprehensive tests

**Files:**
- `ui/src/stores/history/diff.ts` (new)
- `ui/src/__tests__/stores/history/diff.test.ts` (new)

#### 2.3 Implement Merge Algorithm
- [ ] Implement `mergeState(baseState, deltas): LatticeProject`
- [ ] Handle conflict resolution
- [ ] Handle out-of-order deltas
- [ ] Handle missing base state
- [ ] Optimize for performance
- [ ] Add comprehensive tests

**Files:**
- `ui/src/stores/history/merge.ts` (new)
- `ui/src/__tests__/stores/history/merge.test.ts` (new)

#### 2.4 Integrate with History System
- [ ] Replace full snapshots with delta snapshots
- [ ] Update `pushHistory()` to use diff
- [ ] Update `undo()` to use merge
- [ ] Update `redo()` to use merge
- [ ] Maintain backward compatibility
- [ ] Add migration for existing history stacks

**Files:**
- `ui/src/stores/projectStore.ts`
- `ui/src/stores/historyStore.ts` (if integrated)

#### 2.5 Performance Optimization
- [ ] Benchmark memory usage (target: 99% reduction)
- [ ] Benchmark snapshot speed (target: <10ms)
- [ ] Benchmark undo/redo speed (target: <50ms)
- [ ] Optimize diff algorithm (avoid unnecessary comparisons)
- [ ] Optimize merge algorithm (batch operations)
- [ ] Add performance tests

**Files:**
- `ui/src/__tests__/performance/history-performance.test.ts` (new)

#### 2.6 Testing & Verification
- [ ] Add comprehensive integration tests
- [ ] Test all layer types (20+ types)
- [ ] Test complex nested structures
- [ ] Test edge cases (empty projects, large projects)
- [ ] Test memory leak fix (verify no leaks)
- [ ] Test type safety (verify no type escapes)
- [ ] Update existing tests

**Files:**
- `ui/src/__tests__/integration/undo-redo-incremental.test.ts` (new)
- `ui/src/__tests__/performance/memory.test.ts` (update)

---

## Success Criteria

### Phase 1: Error Fixes
- ✅ Memory leak test passes (no leaks after 500 cycles)
- ✅ Zero type escapes (`npx tsc --noEmit` passes)
- ✅ History architecture consolidated
- ✅ Type safety verified

### Phase 2: Incremental Snapshots
- ✅ Memory usage reduced by 99% (measured)
- ✅ Snapshot speed <10ms (measured)
- ✅ Undo/redo speed <50ms (measured)
- ✅ All tests pass
- ✅ Backward compatibility maintained

---

## Risk Assessment

### High Risk: Type Escapes
**Impact:** Data corruption during diff/merge  
**Mitigation:** Fix all 504 type escapes before Phase 2

### High Risk: Memory Leak
**Impact:** System becomes unusable over time  
**Mitigation:** Fix memory leak before Phase 2

### Medium Risk: Merge Conflicts
**Impact:** Undo/redo could corrupt state  
**Mitigation:** Comprehensive testing, conflict resolution algorithm

### Medium Risk: Performance Regression
**Impact:** Slower undo/redo than current system  
**Mitigation:** Performance benchmarks, optimization passes

---

## Timeline

**Phase 1 (Error Fixes):** 2-4 weeks  
**Phase 2 (Implementation):** 3-5 weeks  
**Total:** 5-9 weeks

**⚠️ CRITICAL:** Phase 2 cannot start until Phase 1 is 100% complete. No shortcuts.

---

## References

- `docs/TYPE_ESCAPE_AUDIT.md` - Type escape audit
- `docs/MASTER_AUDIT_2026-01-18.md` - Architecture audit
- `ui/src/__tests__/performance/memory.test.ts` - Memory leak test
- `ui/src/stores/projectStore.ts` - Current history implementation
- `ui/src/stores/historyStore.ts` - Orphaned history store

---

## Notes

**No Shortcuts Policy:**
- ❌ No "acceptable for now" solutions
- ❌ No temporary workarounds
- ❌ No partial implementations
- ✅ Fix errors completely before refactor
- ✅ Implement incremental snapshots properly
- ✅ Verify with comprehensive tests

**This is a production-grade codebase. Every change must be done correctly.**
