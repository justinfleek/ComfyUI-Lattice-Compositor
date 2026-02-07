# Remaining TypeScript Errors Analysis

**Generated:** 2026-01-07  
**Last Updated:** 2026-01-07  
**Total Errors:** 693 (down from 972, 279 fixed)  
**Recently Fixed:** ALL HARD errors (40 errors: TS2820 22, TS2779 8, TS2593 10), ALL export test files (72 errors), project.property.test.ts (createAnimatableProperty signature, ProceduralMatteType patterns), blendModes.ts (classic-color-burn/dodge display names), PointCloudLayer.ts (8 TS2779 errors), interpolation.property.test.ts (10 TS2593 errors), GPUParticleSystem.property.test.ts (createTestableSystem signature - 5 TS2345), deprecated scail tests (5 TS2345 - updated to test error handling), modelExport.test.ts (PointTrajectory format, SplineData structure with animatedControlPoints, UnifiedExportOptions callbacks, Camera3D structure - 11 TS2345), vaceControlExport.test.ts (SplineControlPoint format - 3 TS2345), wanMoveExport.test.ts (ControlPoint format - 5 TS2345), deprecated camera tests (cameraExportFormats.property.test.ts 5 TS2322/TS2353, depthRenderer.property.test.ts camera3DArb + hardcoded cameras - 8 TS2322/TS2739), EffectInstance missing properties (effectProcessor.browser.test.ts, strict-effectprocessor.property.test.ts - 2 TS2739), AnimatableProperty missing properties (strict-meshdeform.property.test.ts - 3 TS2739), ToolCall missing id (BUG-action-executor-undo-redo.regression.test.ts - 6 TS2345), benchmarks.test.ts (createAnimatableProperty signature - 1 TS2345), PropertyDriver evaluateDriver signature (BUG-property-driver-remap-div0.regression.test.ts - 6 TS2345), RigidBodyConfig missing properties (BUG-physics-mass-div0.regression.test.ts - 2 TS2345), templateBuilder.property.test.ts (ExposedPropertyType "position" -> "point" - 3 TS2345), arbitraries.ts layerTransformArb (LayerTransform requires AnimatableProperty - 1 TS2322), layerEvaluation.property.test.ts (22 errors), MotionEngine.test.ts (20 errors), NestedCompLayer/ParticleLayer properties (2 errors), regression tests (14 errors), store API fixes (25 errors), After Effects references removed (trade dress compliance). Total: 279 errors fixed.  
**Methodology:** `npx vue-tsc --noEmit` analysis

---

## Executive Summary

| Category | Count | Percentage | Difficulty | Estimated Files |
|----------|-------|------------|------------|-----------------|
| **EASY** | 295 | 43% | Low (proven pattern) | 20-30 files |
| **MEDIUM** | 398 | 57% | Medium (requires analysis) | 100-120 files (mostly test files) |
| **HARD** | 0 | 0% | High (architectural) | 0 files |
| **Total** | 693 | 100% | | 130-150 files |

### File Type Distribution

| File Type | Total Files | Files with Errors | Error Count | Primary Issue |
|-----------|-------------|-------------------|-------------|---------------|
| **Test Files** | 171 | 50-60 (29-35%) | 673 | Missing properties (TS2739/TS2322/TS2353) |
| **Source Files** | 200+ | 30-40 (15-20%) | 146 | Type mismatches (TS2322/TS2345) |
| **Vue Components** | 165 | 1 (0.6%) | 1 | Minimal errors remaining |

---

## Error Type Breakdown

| Error Code | Count | Description | Difficulty | Fix Strategy |
|------------|-------|-------------|------------|--------------|
| **TS2322** | 214 | Type not assignable | **MEDIUM** | Type assertions, null checks, correct type imports |
| **TS2353** | 98 | Object literal may only specify known properties | **MEDIUM** | Fix property names, remove invalid properties |
| **TS2739** | 91 | Type missing properties | **MEDIUM** | Add missing properties to interfaces/types |
| **TS18048** | 80 | Possibly undefined | **MEDIUM** | Add null/undefined checks, optional chaining |
| **TS2345** | 78 | Argument type not assignable | **MEDIUM** | Fix argument types, add type guards |
| **TS2339** | 69 | Property does not exist on type | **EASY** | Remove underscore prefixes (same pattern as previous fixes) |
| **TS2561** | 23 | Object is possibly undefined | **MEDIUM** | Add null checks, optional chaining |
| **TS2820** | 22 | Type instantiation is excessively deep | **HARD** | Refactor complex types, simplify generics |
| **TS2741** | 17 | Property missing in type | **MEDIUM** | Add missing properties |
| **TS18047** | 14 | Possibly null | **MEDIUM** | Add null checks |
| **TS2307** | 14 | Cannot find module | **EASY** | Fix import paths, add missing files |
| **TS2554** | 13 | Expected X arguments but got Y | **MEDIUM** | Fix function call signatures |
| **TS2551** | 12 | Property does not exist (suggestion) | **EASY** | Remove underscore prefixes (same pattern) |
| **TS2352** | 11 | Type assertion to unrelated type | **MEDIUM** | Fix type assertions, use correct types |
| **TS2593** | 10 | Type instantiation is excessively deep | **HARD** | Refactor complex types |
| **TS7006** | 10 | Parameter implicitly has 'any' type | **EASY** | Add explicit type annotations |
| **TS2779** | 8 | Type instantiation is excessively deep | **HARD** | Refactor complex types |
| **TS2614** | 6 | Module has no exported member | **EASY** | Fix imports, check exports |
| **TS2314** | 4 | Generic type requires X type arguments | **MEDIUM** | Add type arguments |
| **TS2305** | 4 | Module has no exported member | **EASY** | Fix imports |
| **TS2769** | 4 | No overload matches | **MEDIUM** | Fix function overloads |
| **Others** | 31 | Various rare errors | **VARIES** | Case-by-case fixes |

---

## Error Type Categories

### **EASY (115 errors - 14%)**
- **TS2339** (69): Underscore prefix removal - same pattern as previous fixes
- **TS2551** (12): Underscore prefix removal - same pattern
- **TS2307** (14): Import path fixes
- **TS7006** (10): Add explicit type annotations
- **TS2614** (6): Import fixes
- **TS2305** (4): Import fixes

**Fix Strategy:** Batch process underscore removals (same pattern as PropertiesPanel.vue, MenuBar.vue, etc.)

### **MEDIUM (665 errors - 81%)**
- **TS2322** (214): Type mismatches - need type assertions, null checks (202 in test files)
- **TS2353** (98): Invalid properties - fix property names (all 98 in test files)
- **TS2739** (91): Missing properties - add to interfaces (all 91 in test files)
- **TS18048** (80): Possibly undefined - add guards
- **TS2345** (78): Argument type mismatches - fix types
- **TS2561** (23): Possibly undefined - add checks
- **TS2741** (17): Missing properties - add to types
- **TS18047** (14): Possibly null - add checks
- **TS2554** (13): Function signature mismatches
- **TS2352** (11): Type assertion issues - fix assertions
- **TS2531** (3): Various type issues
- **TS2724** (2): Various type issues
- **TS2367** (2): Various type issues
- **TS2300** (2): Various type issues
- **TS2532** (2): Various type issues
- **TS2872** (1): Various type issues
- **TS2678** (1): Various type issues
- **TS2698** (1): Various type issues
- **TS2493** (1): Various type issues
- **TS2459** (1): Various type issues
- **TS2349** (1): Various type issues
- **TS18046** (1): Various type issues
- **TS2769** (4): Overload mismatches
- **TS2314** (4): Missing type arguments

**Fix Strategy:** Systematic review of test files (673 errors) and source files (146 errors), fix type mismatches. Most errors are in test files and follow similar patterns to export test fixes.

### **HARD (0 errors - 0%)**
✅ **ALL HARD ERRORS FIXED (2026-01-07)**
- **TS2820** (22): Fixed - String literal mismatches in test files (LayerType, BlendMode, ExportTarget)
- **TS2779** (8): Fixed - Optional property access assignments in PointCloudLayer.ts (changed to explicit null checks)
- **TS2593** (10): Fixed - Missing `it` import in interpolation.property.test.ts (added to vitest imports)

**Fix Strategy:** All HARD errors were actually simpler than expected - string literal fixes and proper null checks

---

## File-Level Error Count (Top Files by Category)

### Vue Component Files (Highest Priority - Underscore Pattern)

| File | Errors | Primary Error Types | Difficulty | Fix Pattern |
|------|--------|---------------------|------------|-------------|
| `components/materials/TextureUpload.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/dialogs/VectorizeDialog.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/panels/GenerativeFlowPanel.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/panels/LayerDecompositionPanel.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/dialogs/MotionSketchPanel.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/preview/HDPreviewWindow.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/controls/ScrubableNumber.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/properties/styles/SatinEditor.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/panels/AIGeneratePanel.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/timeline/LayerTrack.vue` | 11 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/materials/AssetUploader.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/controls/PropertyLink.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/properties/ExpressionInput.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/layout/CenterViewport.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/properties/particle/ParticleFlockingSection.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/panels/PreviewPanel.vue` | 10 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/properties/ShapeLayerProperties.vue` | 9 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/viewport/ViewportRenderer.vue` | 9 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/panels/RenderQueuePanel.vue` | 9 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| `components/layout/RightSidebar.vue` | 9 | TS2339, TS2551 | **EASY** | Remove underscore prefixes |
| *Plus ~60-70 more Vue components* | 5-15 each | TS2339, TS2551 | **EASY** | Same pattern |

**Total Vue Component Errors:** ~800-900 errors

### Test Files (Medium Priority - Type Fixtures)

| File | Errors | Primary Error Types | Difficulty | Fix Pattern |
|------|--------|---------------------|------------|-------------|
| `__tests__/_deprecated/properties/strict-vaceexport.property.test.ts` | 46 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/_deprecated/properties/strict-meshdeform.property.test.ts` | 43 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/export/svgExport.property.test.ts` | 40 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/integration/save-load-roundtrip.integration.test.ts` | 39 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/engine/layerEvaluation.property.test.ts` | 38 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/services/effectProcessor.property.test.ts` | 37 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/types/project.property.test.ts` | 32 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/_deprecated/services/export/allTargets.comprehensive.test.ts` | 29 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/services/interpolation.property.test.ts` | 29 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| `__tests__/export/wanMoveExport.test.ts` | 27 | TS2739, TS2322, TS2353 | **MEDIUM** | Add missing properties, fix types |
| *Plus ~30-40 more test files* | 10-25 each | TS2739, TS2322, TS2353 | **MEDIUM** | Same pattern |

**Total Test File Errors:** ~300-400 errors

### Source Files (Lower Priority - Complex Types)

| File | Errors | Primary Error Types | Difficulty | Fix Pattern |
|------|--------|---------------------|------------|-------------|
| `engine/particles/ParticleForceCalculator.ts` | 27 | TS2322, TS2820, TS2779 | **HARD** | Type refactoring, simplify generics |
| `engine/particles/ParticleSubEmitter.ts` | 16 | TS2322, TS2820 | **HARD** | Type refactoring |
| `engine/particles/ParticleEmitterLogic.ts` | 15 | TS2322, TS2820 | **HARD** | Type refactoring |
| `services/renderQueue/RenderQueueManager.ts` | 14 | TS2322, TS18048 | **MEDIUM** | Null checks, type fixes |
| *Plus ~5-10 more source files* | 5-15 each | TS2322, TS18048 | **MEDIUM-HARD** | Various |

**Total Source File Errors:** ~100-150 errors

---

## Recommended Fix Order

1. **Phase 1: Easy Wins (489 errors)**
   - Batch fix underscore prefixes (TS2339, TS2551) - same pattern as previous fixes
   - Fix import paths (TS2307, TS2614, TS2305)
   - Add explicit type annotations (TS7006)
   - **Estimated Time:** 2-3 hours
   - **Risk:** Low (proven pattern)

2. **Phase 2: Medium Complexity (677 errors)**
   - File-by-file analysis
   - Type system fixes (TS2322, TS2739, TS2353)
   - Null safety (TS18048, TS2561, TS18047)
   - Function signature fixes (TS2345, TS2554)
   - **Estimated Time:** 8-12 hours
   - **Risk:** Medium (requires careful analysis)

3. **Phase 3: Hard Refactoring (110 errors)**
   - Type instantiation depth issues (TS2820, TS2779)
   - Architectural review needed
   - **Estimated Time:** 4-6 hours
   - **Risk:** High (may require design changes)

---

## Progress Tracking

- **Starting Errors:** 4,320
- **Fixed:** 3,044 (70%)
- **Remaining:** 1,276 (30%)
- **Files Fixed:** 67 Vue components + 4 tutorial test files
- **Average Errors per File:** ~19 (remaining)

## File Count Summary

### Total Files in Codebase
- **Vue Components:** 165 files total
- **Test Files:** 171 files total
- **Source Files:** ~200+ files total

### Files with Errors (Estimated)
- **Vue Components:** ~80-90 files with errors (49-55% of Vue files)
  - Most have 5-15 errors each (underscore prefix pattern)
  - ~10-15 files have 10+ errors
- **Test Files:** ~40-50 files with errors (23-29% of test files)
  - Most have 10-40 errors each (type fixture issues)
  - ~5-10 files have 30+ errors
- **Source Files:** ~10-15 files with errors (5-8% of source files)
  - Most have 10-30 errors each (complex type issues)
  - ~3-5 files have 20+ errors (particle system)

### By Difficulty Level
- **EASY (489 errors):** ~70-80 Vue component files (underscore prefix pattern)
  - Average: ~6-7 errors per file
  - Pattern: Identical to 67 files already fixed
- **MEDIUM (677 errors):** ~50-60 files (test files + some Vue components)
  - Average: ~11-13 errors per file
  - Pattern: Type system fixes, null safety
- **HARD (110 errors):** ~5-10 files (particle system, complex generics)
  - Average: ~11-22 errors per file
  - Pattern: Type instantiation depth issues

---

## Notes

- Underscore prefix removal (TS2339/TS2551) follows the exact same pattern as PropertiesPanel.vue, MenuBar.vue, etc.
- Most remaining errors are in Vue components (template/script mismatches)
- Type system errors (TS2322, TS2739) require understanding the type definitions
- Deep type instantiation errors (TS2820, TS2779) may indicate architectural issues
