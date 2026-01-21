# Master Refactor Status - CODE VERIFIED

> **Date:** 2026-01-19 (UPDATED)  
> **Methodology:** Actual code verification, not documentation pattern matching  
> **Status:** ✅ **VERIFICATION IN PROGRESS** - Updated with latest migration status  
> **Latest Update:** Phase 5 Consumer Migration: ✅ All production files migrated. ✅ 7 test files migrated. ⚠️ 1 test file remaining (`benchmarks.test.ts`). Fixed composable migration errors (useKeyboardShortcuts.ts, useShapeDrawing.ts, useViewportGuides.ts). TypeScript errors: 256 total. Phase 5.5 Type Proof Refactoring: ✅ 106 files complete, ~859 `??` patterns removed. **Latest Session (2026-01-19):** Removed 195 patterns from 23 service files. Remaining: **1,057** `??` patterns across 156 files (49 in services, 1 in stores, rest in engine/components/composables) - Verified via grep.

---

## ⚠️ CRITICAL FINDINGS

### Issue 1: clearSelection() Doesn't Delegate

**Found:** `compositorStore.clearSelection()` (line 1062) does NOT delegate to layerStore

**Evidence:**
- `compositorStore.ts:1062-1065`: Calls `selectionStore.clearAll()` directly
- `layerStore/hierarchy.ts:178-180`: Has `clearSelection()` function that calls `selectionStore.clearLayerSelection()`
- `layerStore/index.ts:340-342`: Exposes `clearSelection()` action

**Problem:** compositorStore bypasses layerStore even though layerStore has the method

---

### Issue 2: Method Count Discrepancy

**Documentation Claims:** 45 layer domain methods  
**Actual Count in layerStore:** **60+ methods** (need full count)

**Methods Found in layerStore/index.ts (partial count):**
1. setClipboard
2. clearClipboard
3. getClipboardLayers
4. createLayer
5. deleteLayer
6. updateLayer
7. updateLayerData
8. duplicateLayer
9. moveLayer
10. renameLayer
11. updateLayerTransform
12. toggleLayerLock
13. toggleLayerVisibility
14. toggleLayerSolo
15. bringToFront
16. sendToBack
17. bringForward
18. sendBackward
19. copySelectedLayers
20. pasteLayers
21. cutSelectedLayers
22. setLayerParent
23. toggleLayer3D
24. selectLayer
25. deselectLayer
26. clearSelection
27. createTextLayer
28. createSplineLayer
29. createShapeLayer
30. replaceLayerSource
31. sequenceLayers
32. applyExponentialScale
33. timeStretchLayer
34. reverseLayer
35. freezeFrameAtPlayhead
36. splitLayerAtPlayhead
37. enableSpeedMap
38. disableSpeedMap
39. toggleSpeedMap
40. getLayerById
41. getLayerChildren
42. getLayerDescendants
43. getVisibleLayers
44. getDisplayedLayers
45. getRootLayers
46. addSplineControlPoint
47. insertSplineControlPoint
48. updateSplineControlPoint
49. deleteSplineControlPoint
50. enableSplineAnimation
51. addSplinePointKeyframe
52. addSplinePointPositionKeyframe
53. updateSplinePointWithKeyframe
54. getEvaluatedSplinePoints
55. isSplineAnimated
56. hasSplinePointKeyframes
57. simplifySpline
58. smoothSplineHandles
59. convertTextLayerToSplines
60. copyPathToPosition

**Plus:** `_regenerateKeyframeIds` (internal)

**Total:** At least 60 methods in layerStore

---

### Issue 3: Methods Still in compositorStore

**Need to verify:** Which methods in compositorStore still have their own implementation vs delegate

**Found so far:**
- `clearSelection()` - Does NOT delegate (calls selectionStore directly)
- `selectAllLayers()` - Does NOT delegate (batch operation?)
- `deleteSelectedLayers()` - Does NOT delegate (batch operation?)
- `duplicateSelectedLayers()` - Does NOT delegate (batch operation?)

**Question:** Are these "layer methods" that should be migrated, or batch operations that are fine to stay?

---

## VERIFICATION NEEDED

### TODO: Complete Method Audit

1. **Count ALL methods in layerStore/index.ts**
   - Read entire file
   - Count actual method definitions
   - List them all

2. **Verify compositorStore delegation**
   - For each method in layerStore, check if compositorStore delegates
   - List methods that DON'T delegate
   - Determine if they should delegate or are intentionally different

3. **Compare against STORE_MIGRATION_CONSUMERS.md**
   - Does the 45-method count match reality?
   - Are spline operations counted separately?
   - Are batch operations counted?

4. **Check for methods that should be migrated but aren't**
   - Methods in compositorStore that are layer-related but not in layerStore
   - Methods that should delegate but don't

---

## HONEST STATUS

**I DON'T KNOW the actual status because:**
- I haven't counted all methods in layerStore
- I haven't verified all compositorStore delegations
- I was pattern matching from documentation instead of verifying code
- I found at least one method (`clearSelection`) that doesn't delegate properly

**What I DO know:**
- layerStore has at least 60 methods (not 45)
- compositorStore.clearSelection() doesn't delegate to layerStore
- Some batch operations (selectAllLayers, deleteSelectedLayers, duplicateSelectedLayers) don't delegate

**What I NEED to do:**
- Read layerStore/index.ts completely and count methods
- Read compositorStore.ts and verify each layer method delegates
- Create accurate status based on actual code, not documentation

---

*This document represents honest verification status - incomplete but accurate to what was verified*
