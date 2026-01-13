# Documentation Index

## Current Status (2026-01-12)

| Phase | Status | Description | Documentation |
|-------|--------|-------------|---------------|
| **Phase 0** | ✅ COMPLETE | 6 critical memory bugs fixed (BUG-243 to BUG-248) | [MASTER_REFACTOR_STATUS.md](MASTER_REFACTOR_STATUS.md#phase-0-critical-bug-fixes-weeks-1-2--complete) |
| **Phase 1** | ✅ COMPLETE | Layer store migration (46/46 methods + 3 batch operations) | [PHASE_1_COMPLETE_VERIFICATION.md](PHASE_1_COMPLETE_VERIFICATION.md), [PHASE_1_MIGRATION_AUDIT.md](PHASE_1_MIGRATION_AUDIT.md) |
| **Phase 2** | ⏳ IN PROGRESS | Method verification complete, state migration in progress (~5%) | [PHASE_2_AUDIT_SUMMARY.md](PHASE_2_AUDIT_SUMMARY.md), [PHASE_2_STATE_MIGRATION_PROGRESS.md](PHASE_2_STATE_MIGRATION_PROGRESS.md) |
| **Phase 3** | ❌ NOT STARTED | Audio & Effects migration | [MASTER_REFACTOR_STATUS.md](MASTER_REFACTOR_STATUS.md#phase-3-audio--effects-weeks-19-26--not-started) |

---

## 🔴 CRITICAL: Technical Debt & Schema Audit (2026-01-12)

### Type System Abuse: 7,793 Issues

| Category | Count |
|----------|-------|
| Type escapes (`any`) | 581 |
| Type assertions (`as X`, `!`) | 3,417 |
| Runtime guards (`??`, `?.`) | 3,564 |
| Lazy defaults (`\|\| 0`) | 231 |

**See:** [PROJECT_PROGRESS.md](PROJECT_PROGRESS.md#-technical-debt-audit-2026-01-12) for full breakdown

### Schema System: 40% Coverage

| Status | Count |
|--------|-------|
| ✅ Covered type files | 10 |
| ❌ Missing schema files | 8 |
| 🔴 Wrong schemas | 1 (ShapeLayerData) |

**Missing:** physics.ts, shapes.ts, layerStyles.ts, effects.ts, presets.ts, meshWarp.ts, masks.ts, assets.ts

**See:** [PROJECT_PROGRESS.md](PROJECT_PROGRESS.md#-schema-system-status-2026-01-12) for details

---

### Phase 1 Progress
- [x] layerStore.ts created with interface
- [x] Exported from stores/index.ts
- [x] Dependency graph: [layerActions.md](graphs/layerActions.md)
- [x] **MODULARIZED** (2026-01-10): layerStore split into 8 modules:
  - `types.ts` (159 lines) - interfaces and type definitions
  - `crud.ts` (366 lines) - create, delete, update, duplicate, move
  - `clipboard.ts` (131 lines) - copy, paste, cut operations
  - `hierarchy.ts` (233 lines) - parenting, 3D mode, hierarchy queries
  - `specialized.ts` (278 lines) - text, spline, shape layer, source replacement
  - `time.ts` (429 lines) - time stretch, reverse, freeze, split, speedmap
  - `batch.ts` (180 lines) - sequence layers, exponential scale
  - `index.ts` (401 lines) - store definition with type-safe CompositorStoreAccess
- [x] createLayer migrated (2026-01-10)
- [x] deleteLayer migrated (2026-01-10)
- [x] updateLayer migrated (2026-01-10)
- [x] updateLayerData migrated (2026-01-10)
- [x] duplicateLayer migrated (2026-01-10)
- [x] moveLayer migrated (2026-01-10)
- [x] setLayerParent migrated (2026-01-10)
- [x] copySelectedLayers migrated (2026-01-10)
- [x] pasteLayers migrated (2026-01-10)
- [x] cutSelectedLayers migrated (2026-01-10)
- [x] toggleLayer3D migrated (2026-01-10)
- [x] createTextLayer migrated (2026-01-10)
- [x] createSplineLayer migrated (2026-01-10)
- [x] createShapeLayer migrated (2026-01-10)
- [x] replaceLayerSource migrated (2026-01-10)
- [x] selectLayer migrated (2026-01-10)
- [x] deselectLayer migrated (2026-01-10)
- [x] clearSelection migrated (2026-01-10)
- [x] sequenceLayers migrated (2026-01-10)
- [x] applyExponentialScale migrated (2026-01-10)
- [x] timeStretchLayer migrated (2026-01-10)
- [x] reverseLayer migrated (2026-01-10)
- [x] freezeFrameAtPlayhead migrated (2026-01-10)
- [x] splitLayerAtPlayhead migrated (2026-01-10)
- [x] enableSpeedMap migrated (2026-01-10)
- [x] disableSpeedMap migrated (2026-01-10)
- [x] toggleSpeedMap migrated (2026-01-10)
- [x] compositorStore delegates to layerStore (23 methods + 1 alias)
- [x] All tests pass (287 layer tests)
- [x] 27 methods in layerStore, 7 not yet delegated (speedMap, clearSelection, query methods)
- [ ] 18 remaining layer methods (27/45 complete - 60%)
- [ ] splineActions (~15 methods) pending
- [ ] 60 consumer files updated

---

## Master Refactor Plan

**[MASTER_REFACTOR_PLAN.md](MASTER_REFACTOR_PLAN.md)** - Complete 10-month modularization plan (v1.1)

| Metric | Value |
|--------|-------|
| Files over 500 lines | 232 |
| Total oversized lines | 293,457 |
| Consumer files to migrate | 99 |
| Cross-domain actions | 19 |
| Duration | 10 months (42 weeks) |

### Supporting Documents

| Document | Purpose |
|----------|---------|
| [MASTER_REFACTOR_STATUS.md](MASTER_REFACTOR_STATUS.md) | **PRIMARY STATUS** - Current progress, what's done vs what's not |
| [STORE_MIGRATION_CONSUMERS.md](STORE_MIGRATION_CONSUMERS.md) | All 99 consumer files with exact method-to-store mapping |
| [CROSS_DOMAIN_ACTIONS.md](CROSS_DOMAIN_ACTIONS.md) | 19 cross-domain actions with coordination patterns |
| [COMPOSITORSTORE_BREAKDOWN.md](COMPOSITORSTORE_BREAKDOWN.md) | What remains in compositorStore after Phase 1 |

### Phase 2 Documentation

| Document | Purpose |
|----------|---------|
| [PHASE_2_AUDIT_SUMMARY.md](PHASE_2_AUDIT_SUMMARY.md) | **MAIN SUMMARY** - Complete verification of 63 methods, remaining work |
| [PHASE_2_METHODICAL_AUDIT.md](PHASE_2_METHODICAL_AUDIT.md) | Detailed audit of 35 keyframe methods |
| [PHASE_2_ANIMATION_AUDIT.md](PHASE_2_ANIMATION_AUDIT.md) | Detailed audit of 11 animation methods |
| [PHASE_2_EXPRESSION_AUDIT.md](PHASE_2_EXPRESSION_AUDIT.md) | Detailed audit of 17 expression methods |
| [PHASE_2_STATE_MIGRATION_PLAN.md](PHASE_2_STATE_MIGRATION_PLAN.md) | Plan for migrating 5 remaining state properties |
| [PHASE_2_STATE_MIGRATION_PROGRESS.md](PHASE_2_STATE_MIGRATION_PROGRESS.md) | Progress tracking for state migration (1/5 complete) |
| [SESSION_REVIEW_2026-01-12.md](SESSION_REVIEW_2026-01-12.md) | Complete review of 2026-01-12 session work |

**Key Strategy:**
1. Phase 0: Fix critical bugs FIRST (canvas leaks, WebGL context loss)
2. Create layerStore FIRST to break chicken-and-egg cycle
3. Migrate one domain at a time with rollback checkpoints
4. Delete compositorStore in Phase 5 after all consumers migrated

---

## Dependency Graphs (P0 Files - VERIFIED 2026-01-10)

High-risk files analyzed for modularization. **All counts verified via symbol usage, not import paths.**

| File | Lines | Verified Users | Risk | Graph |
|------|-------|----------------|------|-------|
| `types/effects.ts` | 3,319 | 11 | Low | [effects-types.md](graphs/effects-types.md) |
| `stores/compositorStore.ts` | 3,292 | 101 | High | [deps](graphs/compositorStore.md) ⭐ [TARGET](graphs/compositorStore-target-architecture.md) |
| `services/comfyui/workflowTemplates.ts` | 2,715 | 2 | Very Low | [workflowTemplates.md](graphs/workflowTemplates.md) |
| `components/properties/ParticleProperties.vue` | 2,683 | 2 | Very Low | [ParticleProperties.md](graphs/ParticleProperties.md) |
| `engine/particles/GPUParticleSystem.ts` | 2,330 | 19 | Low | [GPUParticleSystem.md](graphs/GPUParticleSystem.md) |
| `services/particleSystem.ts` | 2,299 | 5 | Low | [particleSystem.md](graphs/particleSystem.md) |
| `engine/layers/ParticleLayer.ts` | 2,201 | 5 | Low | [ParticleLayer.md](graphs/ParticleLayer.md) |
| `components/canvas/ThreeCanvas.vue` | 2,197 | 10 | Medium | [ThreeCanvas.md](graphs/ThreeCanvas.md) |
| `types/project.ts` | 2,194 | 95+ | Critical | [project-types.md](graphs/project-types.md) |
| `engine/layers/BaseLayer.ts` | 2,120 | 28 | Medium | [BaseLayer.md](graphs/BaseLayer.md) |
| `stores/actions/keyframeActions.ts` | 2,023 | 24 | Medium | [keyframeActions.md](graphs/keyframeActions.md) |
| `components/curve-editor/CurveEditor.vue` | 2,006 | 11 | Medium | [CurveEditor.md](graphs/CurveEditor.md) |
| `stores/actions/layerActions.ts` | 1,847 | 7 | Medium | [layerActions.md](graphs/layerActions.md) ⭐ PHASE 1 |

### Modularization Priority (Safest First)

1. ✅ `workflowTemplates.ts` - 2 users, pure templates
2. ✅ `ParticleProperties.vue` - 2 users, already has sub-components
3. ✅ `particleSystem.ts` - 5 users, legacy CPU fallback
4. ✅ `ParticleLayer.ts` - 5 users, contained to engine
5. ✅ `types/effects.ts` - 11 users, mostly data definitions
6. ⚠️ `ThreeCanvas.vue` - 10 users, main viewport
7. ⚠️ `CurveEditor.vue` - 11 users, already has composables
8. ⚠️ `GPUParticleSystem.ts` - 19 users, self-contained subsystem
9. ⚠️ `keyframeActions.ts` - 24 users, pure functions
10. ⚠️ `BaseLayer.ts` - 28 users, all layers depend on it
11. ⚠️ `compositorStore.ts` - 101 users, central state
12. 🔴 `types/project.ts` - 95+ users, foundational types

---

## Architecture Plans

### compositorStore.ts → Domain-Driven Stores

**Master Plan:** [MASTER_REFACTOR_PLAN.md](MASTER_REFACTOR_PLAN.md) - Full execution phases and timeline

**Target Architecture:** [compositorStore-target-architecture.md](graphs/compositorStore-target-architecture.md)

**Analysis:** [compositorStore-modularization-plan.md](graphs/compositorStore-modularization-plan.md) - State slice analysis

**Problem:** 3,292-line god object with 101 dependents. Everything routes through it.

**Solution:** Replace with 12 focused domain stores:

| Store | Responsibility | Lines |
|-------|----------------|-------|
| projectStore | Project file, assets | ~200 |
| compositionStore | Multi-comp navigation | ~150 |
| layerStore | Layer CRUD, hierarchy | ~300 |
| keyframeStore | Keyframe CRUD | ~400 |
| expressionStore | Expressions, drivers | ~300 |
| playbackStore | Time authority | ~150 |
| audioStore | Audio, reactive | ~400 |
| cameraStore | 3D cameras, viewport | ~300 |
| historyStore | Undo/redo | ~200 |
| uiStore | Panel visibility, tools | ~150 |
| comfyuiStore | ComfyUI connection | ~100 |
| segmentationStore | SAM2/MatSeg | ~200 |

**Migration:** Update 101 files to import domain stores directly. No wrappers. Delete compositorStore when done.

**Action modules fate:** Absorbed into their domain stores (audioActions → audioStore, etc.)

---

## Verification Methodology

**IMPORTANT:** Always verify blast radius by symbol USAGE, not import paths.

### Why Import Counting Fails

```
# WRONG - counts import statements (misses re-exports)
grep -r "from.*moduleName" | wc -l

# RIGHT - counts actual symbol usage
grep -r "\bSymbolName\b" | wc -l
```

### Standard Verification Commands

```bash
# 1. Find main exports
grep "^export" path/to/file.ts | head -20

# 2. Count symbol usage (exclude tests and the file itself)
grep -r "\bExportedSymbol\b" ui/src --include="*.ts" --include="*.vue" | \
  grep -v __tests__ | grep -v _deprecated | grep -v "filename.ts" | \
  cut -d: -f1 | sort -u | wc -l

# 3. List all users
grep -r "\bExportedSymbol\b" ui/src --include="*.ts" --include="*.vue" | \
  grep -v __tests__ | grep -v _deprecated | grep -v "filename.ts" | \
  cut -d: -f1 | sort -u

# 4. Check for re-exports
grep -r "export.*SymbolName" ui/src --include="*.ts" | grep -v "original-file.ts"
```

### Common Pitfalls

1. **Re-exports:** `types/project.ts` re-exports from 10+ modules
2. **Store delegation:** `compositorStore.ts` exposes action functions via `store.actionName()`
3. **Barrel exports:** `index.ts` files aggregate and re-export
4. **Type-only imports:** Some symbols only used as types, not runtime

---

## Checklists (from MASTER_CHECKLIST.md)

| File | Sections | Lines |
|------|----------|-------|
| components.md | 19 | 265 |
| services.md | 20 | 286 |
| engine.md | 6 | 97 |
| stores.md | 5 | 64 |
| lattice.md | 4 | 50 |
| types.md | 1 | 30 |
| composables.md | 1 | 25 |
| utils.md | 1 | 15 |
| workers.md | 1 | 10 |
| ui.md | 1 | 9 |
| config.md | 1 | 8 |
| styles.md | 1 | 8 |

## Audit (from MASTER_AUDIT.md)

| File | Content | Lines |
|------|---------|-------|
| instructions.md | Audit rules | 58 |
| bugs.md | Bug registry | 85 |
| particle-audit.md | Particle system audit | 449 |
| coverage.md | Codebase coverage | 362 |
| services.md | Services audit | 411 |
| engine.md | Engine audit | 102 |
| stores.md | Stores audit | 168 |
| lattice.md | Lattice/Python audit | 82 |
| pipelines-overview.md | Pipeline overview | 200 |
| pipelines-layers.md | Layer coverage | 251 |
| pipelines-browser.md | Browser tests | 280 |
| pipelines-coverage.md | Function coverage | 340 |
| pipelines-status.md | Status & next steps | 394 |

## Original Files (KEEP - DO NOT DELETE)

- MASTER_CHECKLIST.md (789 lines) - Source of truth
- MASTER_AUDIT.md (3164 lines) - Source of truth
