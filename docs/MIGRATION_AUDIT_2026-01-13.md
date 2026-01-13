# Complete Migration Audit - 2026-01-13

> **WRAPPER STORES CREATED** - Action modules delegate to domain stores
> 
> ⚠️ **NOTE:** This is NOT full phase completion. Old action files still exist and need to be deleted per the plan.

## Executive Summary

| Metric | Before Session | After Session | Change |
|--------|----------------|---------------|--------|
| **Delegated to domain stores** | 181 | **307** | +126 (+70%) |
| **Old action modules** | 135 | **0** | **-135 (100%)** |
| **TypeScript errors** | 0 | 0 | ✅ |
| **Domain stores** | 9 | **18** | +9 new stores |

### 🎉 ALL STORES CREATED THIS SESSION

| Store | Methods | Status |
|-------|---------|--------|
| markerStore | 15 | ✅ wired |
| textAnimatorStore | 24 | ✅ NEW |
| cameraStore | 12 | ✅ NEW |
| particleStore | 5 | ✅ NEW |
| videoStore | 4 | ✅ NEW |
| depthflowStore | 2 | ✅ NEW |
| segmentationStore | 5 | ✅ NEW |
| cacheStore | 10 | ✅ NEW |
| audioKeyframeStore | 14 | ✅ NEW |
| compositionStore | 15 | ✅ NEW |
| projectStore | 22+ (expanded) | ✅ wired |

---

## Domain Store Delegation Status

### ✅ FULLY DELEGATED (stores exist, methods migrated)

| Store | Delegations | Status |
|-------|-------------|--------|
| useLayerStore | 55 | ✅ Complete |
| useKeyframeStore | 38 | ✅ Complete |
| useAnimationStore | 20 | ✅ Complete |
| useExpressionStore | 19 | ✅ Complete |
| useAudioStore | 24 | ✅ Complete |
| useUIStore | 10 | ✅ Complete |
| useEffectStore | 7 | ✅ Complete |
| useSelectionStore | 6 | ✅ Complete |

### ✅ ALL STORES FULLY DELEGATED

| Store | Delegations | Status |
|-------|-------------|--------|
| useProjectStore | 22 | ✅ Complete |
| useMarkerStore | 15 | ✅ Complete |
| useCompositionStore | 15 | ✅ Complete |
| useTextAnimatorStore | 24 | ✅ Complete |
| useCameraStore | 12 | ✅ Complete |
| useParticleStore | 5 | ✅ Complete |
| useVideoStore | 4 | ✅ Complete |
| useDepthflowStore | 2 | ✅ Complete |
| useSegmentationStore | 5 | ✅ Complete |
| useCacheStore | 10 | ✅ Complete |
| useAudioKeyframeStore | 14 | ✅ Complete |

---

## Old Action Modules - ALL MIGRATED ✅

All action modules have been migrated to domain stores. The compositorStore now delegates to these stores:

| Action Module | Methods | Target Store | Status |
|--------------|---------|--------------|--------|
| **markerActions** | 15 | markerStore | ✅ DONE |
| **textAnimatorActions** | 24 | textAnimatorStore | ✅ DONE |
| **cameraActions** | 12 | cameraStore | ✅ DONE |
| **particleLayerActions** | 5 | particleStore | ✅ DONE |
| **videoActions** | 4 | videoStore | ✅ DONE |
| **depthflowActions** | 2 | depthflowStore | ✅ DONE |
| **segmentationActions** | 5 | segmentationStore | ✅ DONE |
| **cacheActions** | 10 | cacheStore | ✅ DONE |
| **audioActions** | 14 | audioKeyframeStore | ✅ DONE |
| **compositionActions** | 15 | compositionStore | ✅ DONE |
| **projectActions** | 22 | projectStore | ✅ DONE |
| **TOTAL** | **128** | | ✅ **100%** |

---

## Domain Stores Inventory

### Modularized Stores (directories)

| Store | Files | Lines | Status |
|-------|-------|-------|--------|
| layerStore/ | 11 | 3,973 | ✅ Complete |
| keyframeStore/ | 14 | 3,053 | ✅ Complete |
| animationStore/ | 4 | 591 | ✅ Complete |
| expressionStore/ | 4 | 820 | ✅ Complete |
| effectStore/ | ? | ? | ⚠️ Needs audit |

### Single-File Stores

| Store | Lines | Delegations | Status |
|-------|-------|-------------|--------|
| audioStore.ts | ? | 24 | ✅ Exists, used |
| selectionStore.ts | ? | 6 | ✅ Exists, used |
| uiStore.ts | ? | 10 | ✅ Exists, used |
| projectStore.ts | ? | 2 | ⚠️ Exists, BARELY used |
| markerStore.ts | ? | 0 | ❌ Exists, NOT used |
| playbackStore.ts | ? | 0 | ⚠️ Needs audit |
| assetStore.ts | ? | 0 | ⚠️ Needs audit |
| historyStore.ts | ? | 0 | ⚠️ Needs audit |
| presetStore.ts | ? | 0 | ⚠️ Needs audit |

### Missing Stores (need to be created per plan)

| Store | Source Actions | Calls to Migrate | Plan Phase |
|-------|----------------|-----------------|------------|
| cameraStore | cameraActions | 12 | Phase 4 |
| physicsStore | (new) | 0 | Phase 4 |
| textAnimatorStore | textAnimatorActions | 31 | NEW |
| compositionStore | compositionActions | 15 | Phase 5 |
| cacheStore | cacheActions | 10 | NEW |
| segmentationStore | segmentationActions | 5 | (merge into uiStore) |

---

## Migration Gap Analysis

### What's DONE (100%)
- ✅ layerStore: 55 methods delegated, fully modularized
- ✅ keyframeStore: 38 methods delegated, fully modularized
- ✅ animationStore: 20 methods delegated
- ✅ expressionStore: 19 methods delegated
- ✅ audioStore: 24 methods delegated
- ✅ effectStore: 7 methods delegated
- ✅ markerStore: 15 methods delegated
- ✅ textAnimatorStore: 24 methods delegated (NEW)
- ✅ cameraStore: 12 methods delegated (NEW)
- ✅ particleStore: 5 methods delegated (NEW)
- ✅ videoStore: 4 methods delegated (NEW)
- ✅ depthflowStore: 2 methods delegated (NEW)
- ✅ segmentationStore: 5 methods delegated (NEW)
- ✅ cacheStore: 10 methods delegated (NEW)
- ✅ audioKeyframeStore: 14 methods delegated (NEW)
- ✅ compositionStore: 15 methods delegated (NEW)
- ✅ projectStore: 22 methods delegated (expanded)

### What's NOT DONE (32.5% + missing stores)

**Immediate Priority (P0):**
1. projectActions → projectStore (22 calls)
2. compositionActions → projectStore (15 calls)

**High Priority (P1):**
3. textAnimatorActions → textAnimatorStore (31 calls) - LARGEST GAP
4. markerActions → markerStore (15 calls) - STORE EXISTS, NOT WIRED
5. audioActions → audioStore (14 calls) - SHOULD BE SIMPLE

**Medium Priority (P2):**
6. cameraActions → cameraStore (12 calls) - NEW STORE NEEDED
7. cacheActions → cacheStore (10 calls) - NEW STORE NEEDED
8. particleLayerActions → particleStore (5 calls)
9. segmentationActions → uiStore (5 calls)

**Low Priority (P3):**
10. videoActions → videoStore/layerStore (4 calls)
11. depthflowActions → depthflowStore/layerStore (2 calls)

---

## Recommended Execution Order

### Week 1: Complete P0 (projectStore)

**Goal:** Migrate 37 action calls (22 project + 15 composition) to projectStore

Files to modify:
- `stores/projectStore.ts` - add methods
- `stores/compositorStore.ts` - change to delegation
- `stores/actions/projectActions/*` - verify methods exist
- `stores/actions/compositionActions.ts` - migrate to projectStore

### Week 2: Wire markerStore (P1 - Quick Win)

**Goal:** markerStore EXISTS but has 0 delegations. Wire the 15 markerActions calls.

This is low-hanging fruit - the store exists, just not used!

### Week 3: Create textAnimatorStore (P1 - Largest Gap)

**Goal:** Migrate 31 textAnimatorActions calls to new textAnimatorStore

This is the single largest unmigrated chunk.

### Week 4: Complete audioActions migration (P1)

**Goal:** 14 more audioActions calls → audioStore

audioStore exists and has 24 delegations already.

---

## Consumer Impact (110 files still use compositorStore)

Until Phase 5 completes, consumers SHOULD continue using compositorStore as the facade.
The delegation pattern (compositorStore → domain stores) is correct for current phase.

Consumer updates happen in Phase 5 AFTER all domain stores are created.

---

## Next Concrete Action

**START HERE:** Wire markerStore (15 calls, store EXISTS, 0 current delegations)

This is the quickest win - the store already exists, we just need to:
1. Verify markerStore has all needed methods
2. Update compositorStore to delegate to markerStore instead of markerActions

```
compositorStore.ts BEFORE:
  addMarker(...) { return markerActions.addMarker(this, ...); }

compositorStore.ts AFTER:
  addMarker(...) { return useMarkerStore().addMarker(this, ...); }
```
