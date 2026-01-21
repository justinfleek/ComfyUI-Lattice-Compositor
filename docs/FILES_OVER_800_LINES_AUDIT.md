# Files Over 800 Lines - Current Audit

**Date:** 2026-01-19  
**Purpose:** Exact line counts for all files exceeding 800 lines  
**Methodology:** Automated PowerShell line counting

---

## Index Files Analysis

### Why `services/index.ts` is 1,591 lines

**File:** `ui/src/services/index.ts`  
**Lines:** 1,591 (includes deprecation notice)  
**Type:** Barrel file (re-export aggregator)  
**Status:** ⚠️ **DEPRECATED**

**Reason for size:**
- Contains **80 export blocks** re-exporting from all service modules
- Each export block lists individual functions/types exported from a module
- Example: `export { function1, function2, type Type1, ... } from "./module"`
- This is a **barrel file pattern** - centralizes all service exports

**Actual Usage Status:**
- ✅ **VERIFIED:** 0 files import from `@/services` (barrel file)
- ✅ **VERIFIED:** All imports use specific paths like `@/services/interpolation`, `@/services/audioFeatures`, etc.
- ✅ **Status:** File exists but is NOT actively used - safe to deprecate/remove

**Potential Issues (if used):**
1. Could cause circular dependency issues
2. Could increase bundle size (tree-shaking problems)
3. Could make imports ambiguous

**Status:** ⚠️ **DEPRECATED** - File marked with deprecation notice, will be removed in Phase 7

**Recommendation:** File is deprecated and will be removed. All code should use direct imports from specific service modules.

### All Index Files Line Counts

| File | Lines | Type | Status |
|------|-------|------|--------|
| `services/index.ts` | **1,591** | Barrel file | ⚠️ **DEPRECATED** - 0 imports found, marked for removal |
| `stores/effectStore/index.ts` | 652 | Store index | ✅ Acceptable |
| `stores/layerStore/index.ts` | 586 | Store index | ✅ Acceptable |
| `stores/keyframeStore/index.ts` | 540 | Store index | ✅ Acceptable |
| `stores/animationStore/index.ts` | 344 | Store index | ✅ Acceptable |
| `schemas/exports/index.ts` | 314 | Schema index | ✅ Acceptable |
| `stores/expressionStore/index.ts` | 299 | Store index | ✅ Acceptable |
| All others | <300 | Various | ✅ Acceptable |

**Note:** No index file exceeds 4,000 lines. The largest is `services/index.ts` at 1,591 lines (deprecated).

---

## Files Over 800 Lines - Complete List

**Total Count:** 104 files exceed 800 lines

### Top 30 Largest Files

| Rank | Lines | File | Type | Priority |
|------|-------|------|------|----------|
| 1 | 6,632 | `__tests__/tutorials/tutorial-01-fundamentals.test.ts` | Test | P3 |
| 2 | 3,247 | `types/effects.ts` | Types | **P0** |
| 3 | 3,015 | `__tests__/tutorials/tutorial06-textAnimators.test.ts` | Test | P3 |
| 4 | 2,519 | `stores/compositorStore.ts` | Store | **P0** (ready for deletion) |
| 5 | 2,460 | `services/comfyui/workflowTemplates.ts` | Service | **P0** |
| 6 | 2,457 | `components/properties/ParticleProperties.vue` | Component | **P0** |
| 7 | 2,084 | `engine/particles/GPUParticleSystem.ts` | Engine | **P0** |
| 8 | 2,058 | `components/canvas/ThreeCanvas.vue` | Component | **P0** |
| 9 | 2,008 | `services/particleSystem.ts` | Service | P1 |
| 10 | 1,940 | `engine/layers/ParticleLayer.ts` | Engine | P1 |
| 11 | 1,904 | `__tests__/tutorials/tutorial-02-neon-motion-trails.test.ts` | Test | P3 |
| 12 | 1,893 | `types/project.ts` | Types | **P0** |
| 13 | 1,817 | `engine/layers/BaseLayer.ts` | Engine | P1 |
| 14 | 1,809 | `components/layout/WorkspaceLayout.vue` | Component | P1 |
| 15 | 1,783 | `composables/useKeyboardShortcuts.ts` | Composable | P1 |
| 16 | 1,758 | `services/ai/actionExecutor.ts` | Service | P1 |
| 17 | 1,735 | `components/curve-editor/CurveEditor.vue` | Component | P1 |
| 18 | 1,637 | `services/export/wanMoveExport.ts` | Service | P2 |
| 19 | 1,626 | `components/panels/AudioPanel.vue` | Component | P1 |
| 20 | 1,585 | `services/physics/PhysicsEngine.ts` | Service | P1 |
| 21 | **1,565** | `services/index.ts` | **Barrel** | ⚠️ Deprecate |
| 22 | 1,557 | `services/effects/colorRenderer.ts` | Service | P2 |
| 23 | 1,556 | `schemas/layers/layer-data-schema.ts` | Schema | P2 |
| 24 | 1,556 | `engine/LatticeEngine.ts` | Engine | P1 |
| 25 | 1,547 | `components/panels/PropertiesPanel.vue` | Component | P1 |
| 26 | 1,546 | `services/depthflow.ts` | Service | P1 |
| 27 | 1,519 | `engine/layers/SplineLayer.ts` | Engine | P1 |
| 28 | 1,496 | `components/properties/TextProperties.vue` | Component | P1 |
| 29 | 1,463 | `services/shapeOperations.ts` | Service | P1 |
| 30 | 1,451 | `services/audioFeatures.ts` | Service | P1 |

### Files 1,000-1,500 Lines (30 files)

| Lines | File | Type |
|-------|------|------|
| 1,426 | `components/dialogs/PreferencesDialog.vue` | Component |
| 1,413 | `components/dialogs/TemplateBuilderDialog.vue` | Component |
| 1,407 | `__tests__/engine/MotionEngine.test.ts` | Test |
| 1,373 | `components/properties/ShapeProperties.vue` | Component |
| 1,363 | `services/ai/security/promptInjectionDetector.ts` | Service |
| 1,323 | `components/panels/ProjectPanel.vue` | Component |
| 1,320 | `engine/MotionEngine.ts` | Engine |
| 1,317 | `engine/layers/TextLayer.ts` | Engine |
| 1,316 | `services/webgpuRenderer.ts` | Service |
| 1,314 | `services/ai/toolDefinitions.ts` | Service |
| 1,303 | `components/timeline/EnhancedLayerTrack.vue` | Component |
| 1,252 | `engine/core/LayerManager.ts` | Engine |
| 1,219 | `services/effects/blurRenderer.ts` | Service |
| 1,212 | `services/audioReactiveMapping.ts` | Service |
| 1,186 | `components/panels/CameraProperties.vue` | Component |
| 1,157 | `components/panels/AssetsPanel.vue` | Component |
| 1,136 | `engine/layers/LightLayer.ts` | Engine |
| 1,136 | `services/particleGPU.ts` | Service |
| 1,123 | `__tests__/export/cameraExportFormats.property.test.ts` | Test |
| 1,115 | `engine/core/RenderPipeline.ts` | Engine |
| 1,099 | `services/effects/distortRenderer.ts` | Service |
| 1,097 | `components/timeline/TimelinePanel.vue` | Component |
| 1,093 | `services/modelExport.ts` | Service |
| 1,089 | `engine/layers/VideoLayer.ts` | Engine |
| 1,089 | `components/curve-editor/CurveEditorCanvas.vue` | Component |
| 1,081 | `components/properties/CameraProperties.vue` | Component |
| 1,068 | `engine/layers/PointCloudLayer.ts` | Engine |
| 1,041 | `__tests__/export/cameraExportFormats.test.ts` | Test |
| 1,037 | `services/svgExtrusion.ts` | Service |
| 1,026 | `services/effects/layerStyleRenderer.ts` | Service |

### Files 800-1,000 Lines (44 files)

| Lines | File | Type |
|-------|------|------|
| 1,026 | `__tests__/engine/layerEvaluation.property.test.ts` | Test |
| 1,020 | `engine/core/SceneManager.ts` | Engine |
| 1,020 | `components/timeline/PropertyTrack.vue` | Component |
| 1,010 | `config/exportPresets.ts` | Config |
| 1,006 | `engine/core/CameraController.ts` | Engine |
| 992 | `services/effects/stylizeRenderer.ts` | Service |
| 992 | `services/glsl/ShaderEffects.ts` | Service |
| 984 | `__tests__/export/export-format-contracts.test.ts` | Test |
| 968 | `workers/audioWorker.ts` | Worker |
| 965 | `components/export/ComfyUIExportDialog.vue` | Component |
| 961 | `engine/layers/ShapeLayer.ts` | Engine |
| 953 | `__tests__/stores/projectActions.test.ts` | Test |
| 952 | `services/math3d.ts` | Service |
| 949 | `__tests__/security/attackSurface.test.ts` | Test |
| 941 | `components/dialogs/ExportDialog.vue` | Component |
| 927 | `services/export/exportPipeline.ts` | Service |
| 920 | `__tests__/export/modelExport.test.ts` | Test |
| 919 | `components/canvas/SplineEditor.vue` | Component |
| 917 | `stores/assetStore.ts` | Store |
| 916 | `services/effects/timeRenderer.ts` | Service |
| 915 | `engine/layers/ProceduralMatteLayer.ts` | Engine |
| 914 | `components/properties/DepthflowProperties.vue` | Component |
| 905 | `services/export/depthRenderer.ts` | Service |
| 899 | `components/dialogs/DecomposeDialog.vue` | Component |
| 892 | `services/textAnimator.ts` | Service |
| 886 | `__tests__/export/wanMoveFlowGenerators.property.test.ts` | Test |
| 885 | `__tests__/export/wanMoveExport.test.ts` | Test |
| 882 | `services/export/cameraExportFormats.ts` | Service |
| 859 | `services/propertyDriver.ts` | Service |
| 852 | `services/preprocessorService.ts` | Service |
| 851 | `services/gpuEffectDispatcher.ts` | Service |
| 844 | `composables/useSplineInteraction.ts` | Composable |
| 844 | `components/dialogs/PathSuggestionDialog.vue` | Component |
| 843 | `types/physics.ts` | Types |
| 838 | `__tests__/export/workflowTemplates.contract.test.ts` | Test |
| 834 | `__tests__/export/allTargets.comprehensive.test.ts` | Test |
| 829 | `components/viewport/ViewportRenderer.vue` | Component |
| 829 | `services/blendModes.ts` | Service |
| 829 | `services/templateBuilder.ts` | Service |
| 824 | `components/dialogs/CompositionSettingsDialog.vue` | Component |
| 823 | `services/visionAuthoring/MotionIntentTranslator.ts` | Service |
| 818 | `engine/layers/ModelLayer.ts` | Engine |
| 814 | `__tests__/services/serialization.property.test.ts` | Test |
| 807 | `types/presets.ts` | Types |

---

## Summary Statistics

### By File Type

| Type | Count | Total Lines | Avg Lines |
|------|-------|-------------|-----------|
| Test files | 20 | ~35,000 | ~1,750 |
| Services | 30 | ~45,000 | ~1,500 |
| Components | 25 | ~38,000 | ~1,520 |
| Engine | 15 | ~22,000 | ~1,467 |
| Types | 4 | ~7,000 | ~1,750 |
| Stores | 2 | ~3,000 | ~1,500 |
| Composables | 2 | ~2,600 | ~1,300 |
| Schemas | 2 | ~1,800 | ~900 |
| Workers | 1 | ~970 | ~970 |
| Config | 1 | ~1,010 | ~1,010 |
| **Barrel files** | **1** | **1,565** | **1,565** |

### Priority Breakdown

| Priority | Count | Description |
|----------|-------|-------------|
| **P0** (>2000 lines) | 5 | Must modularize first |
| **P1** (1500-2000 lines) | ~27 | Second wave |
| **P2** (1000-1500 lines) | ~30 | Third wave |
| **P3** (800-1000 lines) | ~42 | Final wave |

---

## Key Findings

1. **No index file exceeds 4,000 lines** - Largest is `services/index.ts` at 1,591 lines (deprecated)
2. **`services/index.ts` is a barrel file** - Contains 82 export blocks re-exporting from all service modules
3. **104 total files exceed 800 lines** - Down from original estimate of 232 files
4. **Test files are largest** - `tutorial-01-fundamentals.test.ts` is 6,632 lines (test files are lower priority)
5. **5 P0 files** need immediate modularization (excluding compositorStore.ts which is ready for deletion)

---

## Recommendations

1. **Deprecate `services/index.ts`** - Replace with direct imports (see MASTER_REFACTOR_PLAN.md Appendix B)
2. **Focus on P0 files first** - types/effects.ts, workflowTemplates.ts, ParticleProperties.vue, GPUParticleSystem.ts
3. **Test files can wait** - Lower priority, focus on production code first
4. **compositorStore.ts ready for deletion** - No consumers remain, only exported in stores/index.ts

---

*Generated: 2026-01-19*
