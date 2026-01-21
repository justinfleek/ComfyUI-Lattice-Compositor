# ALL TODOS SUMMARY

**Generated:** 2024-12-19  
**Purpose:** Complete inventory of all TODOs, FIXMEs, and pending work items

---

## 🔴 CRITICAL PRIORITY

### Phase 2 Getter Decisions
**Status:** ✅ **COMPLETE** - All 6 decisions made (2026-01-18)

**Next Steps:**
- ⏳ Migrate consumers to use new getter locations (~82 files remaining)

---

## 🟠 HIGH PRIORITY - Architectural Refactoring

### 1. KeyframeStoreAccess Elimination
**Status:** ✅ **READY TO START** - Phase 2 getter decisions complete

**Work Required:**
- Refactor ~20+ keyframeStore methods to remove KeyframeStoreAccess parameter
- Update all callers (including physicsStore.bakePhysicsToKeyframes)
- Use decided getters: `animationStore.currentFrame`, `projectStore.getFps()`, `projectStore.getFrameCount()`

**Estimated Effort:** 4-6 hours

---

### 2. Phase 5 Consumer Migration
**Status:** ⏳ **IN PROGRESS** - ~82 files remaining (~73% complete)

**Progress:**
- ✅ 74 files migrated (2026-01-18)
- ⏳ ~82 files remaining

**Estimated Effort:** 1-2 weeks (incremental)

---

### 3. CompositorStore Deletion
**Status:** ⏳ **PENDING** - After consumer migration

**Work Required:**
- Delete `compositorStore.ts` (currently 2,540 lines)
- Verify no remaining dependencies

**Dependencies:**
- ✅ All consumer files migrated
- ✅ All getter decisions made

**Estimated Effort:** 1 hour

---

## 🟡 MEDIUM PRIORITY

### 1. TypeScript Test Errors
**Status:** ⏳ **PENDING** - 2,472 errors total

**Work Required:**
- Fix test files using old compositorStore API
- Update test mocks and helpers

**Estimated Effort:** 1-2 weeks (incremental)

---

### 2. Phase 3 State Deduplication
**Status:** ⏳ **PENDING**

**Work Required:**
- Remove duplicate audio state getters from compositorStore
- Ensure audioStore is single source of truth

**Getters to Remove:**
- `audioAnalysis`, `audioBuffer`, `audioFile`, `audioVolume`, `audioMuted`, `audioLoadingState`, `audioMappings`, `audioReactiveMappings`, `pathAnimators`

**Estimated Effort:** 1-2 hours

---

### 3. Phase 3 Effect Methods Migration
**Status:** ⏳ **PENDING**

**Methods Remaining:**
- `duplicateEffect`
- `setLayerStylesEnabled`, `setStyleEnabled`, `updateStyleProperty`, `setStyle`
- `setLayerStyles`, `copyLayerStyles`, `pasteLayerStyles`, `pasteLayerStylesToMultiple`
- `clearLayerStyles`, `addDropShadow`, `addStroke`, `addOuterGlow`

**Estimated Effort:** 2-3 hours

---

## 🟢 LOW PRIORITY

### 1. Lazy Code Cleanup
**Status:** ⏳ **PENDING** - ~7,000+ patterns

**Work Required:**
- Fix `|| 0`, `??`, `?.`, `as any`, `as unknown as`, etc.
- Systematic pattern fixes

**Progress:**
- ✅ 128+ type escape patterns fixed (2026-01-18)
- ⏳ ~7,000+ remaining

**Estimated Effort:** 4-6 weeks (systematic)

---

### 2. Schema Creation
**Status:** ⏳ **PENDING** - 8 type files missing schemas

**Files Needing Schemas:**
- physics.ts (991 lines)
- shapes.ts (845 lines)
- layerStyles.ts (722 lines)
- effects.ts (3,320 lines)
- presets.ts (825 lines)
- meshWarp.ts (279 lines)
- masks.ts (270 lines)
- assets.ts (157 lines)

**Estimated Effort:** 1-2 weeks

---

### 3. File Modularization
**Status:** ⏳ **PENDING** - 232 files >500 lines

**Priority Files:**
- types/effects.ts (3,233 lines)
- compositorStore.ts (2,540 lines) - Will be deleted
- workflowTemplates.ts (2,449 lines)
- ParticleProperties.vue (2,449 lines)
- GPUParticleSystem.ts (2,083 lines) - ✅ DELETED (migrated to VerifiedGPUParticleSystem)

**Estimated Effort:** 3-6 months (incremental)

---

## 📋 CODE TODOS (Incremental Cleanup)

### VerifiedGPUParticleSystem TODOs (6 items)

1. **Line 767:** `// TODO: Read back results (async, would need to handle this properly)`
   - **Location:** WebGPU compute readback
   - **Priority:** Medium
   - **Context:** Async result reading from GPU

2. **Line 834:** `// TODO: Check audio features for beat detection`
   - **Location:** Burst emission on beat
   - **Priority:** Medium
   - **Context:** Audio-reactive burst emission

3. **Line 954:** `undefined // TODO: Get random offset from particleInitialValues`
   - **Location:** Modulation curve evaluation
   - **Priority:** High
   - **Context:** Deterministic random curve evaluation

4. **Line 1103:** `// TODO: Refactor subsystems to use VerifiedSpatialHash directly`
   - **Location:** Spatial hash integration
   - **Priority:** Medium
   - **Context:** Remove adapter layer

5. **Line 1254:** `// TODO: Create adapter to bridge VerifiedSpatialHash to SpatialHashGrid interface`
   - **Location:** Collision system integration
   - **Priority:** Medium
   - **Context:** Compatibility layer

6. **Line 1262:** `// TODO: Create adapter to bridge VerifiedSpatialHash to SpatialHashGrid interface`
   - **Location:** Flocking system integration
   - **Priority:** Medium
   - **Context:** Compatibility layer

---

### Python API TODOs (3 items)

1. **lattice_api_proxy.py line 594:** `# TODO: Actual depth estimation implementation`
   - **Priority:** Medium
   - **Context:** Depth estimation endpoint

2. **lattice_api_proxy.py line 647:** `# TODO: Actual normal map generation implementation`
   - **Priority:** Medium
   - **Context:** Normal map endpoint

3. **lattice_api_proxy.py line 696:** `# TODO: Actual segmentation implementation`
   - **Priority:** Medium
   - **Context:** Segmentation endpoint

---

### Component TODOs (3 items)

1. **useAssetHandlers.ts line 79:** Remove CompositorStoreAccess parameter from createShapeLayer
   - **Priority:** High
   - **Context:** Consumer migration

2. **WorkspaceLayout.vue line 832:** Implement "Allow user to save frames or add to project"
   - **Priority:** Low
   - **Context:** UI feature

3. **ExportPanel.vue line 195:** Implement backend availability check
   - **Priority:** Medium
   - **Context:** Export functionality

---

### CompositorStore TODOs (1 item)

1. **Line 2361:** Remove TODO comment "TODO: Remove after consumer migration"
   - **Priority:** Low
   - **Context:** Cleanup after deletion

---

### Test TODOs (7 items)

1. **memory.test.ts line 250:** Implement effect processing API test
   - **Priority:** Medium

2. **memory.test.ts line 280:** Implement canvas pool API test
   - **Priority:** Medium

3. **benchmarks.test.ts line 265:** Implement effect processing API test
   - **Priority:** Medium

4. **benchmarks.test.ts line 272:** Implement export API test
   - **Priority:** Medium

5. **tutorial-01:** Fix registerAsset() method test
   - **Priority:** Medium

6. **tutorial-02:** Fix animatedControlPoints API test
   - **Priority:** Medium

7. **workflowTemplates.contract.test.ts line 960:** Add validateWorkflowParams() function
   - **Priority:** Medium

---

## 📊 SUMMARY

**Total TODOs:** 50+ items

**By Priority:**
- 🔴 Critical: 1 item (Consumer migration - 82 files)
- 🟠 High: 3 items (KeyframeStoreAccess, Consumer Migration, CompositorStore Deletion)
- 🟡 Medium: 3 items (TypeScript Errors, Phase 3 work)
- 🟢 Low: 3 items (Lazy Code, Schemas, Modularization)
- 📋 Incremental: 40+ items (Code TODOs, Test TODOs)

**By Category:**
- Architectural Refactoring: 3 items
- Code Cleanup: 40+ items
- Test Improvements: 7 items
- API Implementation: 3 items
- Documentation: 1 item

**Completed Recently:**
- ✅ Phase 2 Getter Decisions (6 items)
- ✅ Phase 4 Physics Refactoring
- ✅ GPUParticleSystem → VerifiedGPUParticleSystem migration
- ✅ 74 consumer files migrated

---

## 🎯 RECOMMENDED NEXT ACTIONS

1. **HIGH PRIORITY:** Complete consumer migration (~82 files remaining)
2. **HIGH PRIORITY:** KeyframeStoreAccess elimination (4-6 hours)
3. **MEDIUM PRIORITY:** Fix VerifiedGPUParticleSystem TODO line 954 (random offset for modulation)
4. **MEDIUM PRIORITY:** Fix TypeScript test errors (2,472 errors)
5. **LOW PRIORITY:** Continue lazy code cleanup incrementally

---

*Last Updated: 2024-12-19*  
*Source: CRITICAL_TODOS_TRACKING.md + codebase grep*
