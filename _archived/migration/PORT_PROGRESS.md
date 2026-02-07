# TypeScript to Haskell/PureScript Port Progress

**Date:** 2026-02-02  
**Priority:** Porting TypeScript files without forbidden patterns

## Completed Ports

### Utilities (9 marked earlier + 11 more = 20)

1. ✅ **`utils/debounce.ts` → `src/lattice/Utils/Debounce.hs`**
2. ✅ **`utils/retry.ts` → `src/lattice/Utils/Retry.hs`**
3. ✅ **`utils/circuitBreaker.ts` → `src/lattice/Utils/CircuitBreaker.hs`**
4. ✅ **`utils/securityHeaders.ts` → `src/lattice/Utils/SecurityHeaders.hs`**
5. ✅ **`utils/logger.ts` → `src/lattice/Utils/Logger.hs`**
6. ✅ **`utils/schemaValidation.ts` → `src/lattice/Utils/SchemaValidation.hs`**
7. ✅ **`utils/uuid5.ts` → `src/lattice/Utils/Uuid5.hs`**
8. ✅ **`utils/typeUtils.ts` → `src/lattice/Utils/TypeUtils.hs`**
9. ✅ **`utils/icons.ts` → `src/lattice/Utils/Icons.hs`**
10. ✅ **`utils/arrayUtils.ts` → `src/lattice/Utils/ArrayUtils.hs`**
11. ✅ **`utils/colorUtils.ts` → `src/lattice/Utils/ColorUtils.hs`**
12. ✅ **`utils/errorHelpers.ts` → `src/lattice/Utils/ErrorHelpers.hs`**
13. ✅ **`utils/fpsUtils.ts` → `src/lattice/Utils/FpsUtils.hs`**
14. ✅ **`utils/numericSafety.ts` → `src/lattice/Utils/NumericSafety.hs`**
15. ✅ **`utils/typeGuards.ts` → `src/lattice/Utils/TypeGuards.hs`**
16. ✅ **`utils/validation.ts` → `src/lattice/Utils/Validation.hs`**
17. ✅ **`utils/labColorUtils.ts` → `src/lattice/Utils/LabColorUtils.hs`**
18. ✅ **`engine/animation/EasingFunctions.ts` → `src/lattice/Utils/Easing.hs`**
19. ✅ **`utils/interpolation` (logic) → `src/lattice/Utils/Interpolation.hs`**
20. ✅ **`utils/defaults` / theme → `src/lattice/Utils/Defaults.hs`, `Base16Theme.hs`, `BlackBalance.hs`** (as used by types/theme)

### Composables (pure logic; 12)

21. ✅ **`composables/useCurveEditorCoords.ts` → `src/lattice/Composables/CurveEditorCoords.hs`**
   - CurveViewState, CurveMargin, frameToScreenX, screenXToFrame, valueToScreenY, screenYToValue
   - getKeyframeScreenX/Y, getNumericValue, getKeyframeDisplayValue, getOutHandleX/Y, getInHandleX/Y
   - isKeyframeInView, calculateGridStep, getPropertyPath
22. ✅ **`composables/useSplineUtils.ts` → `src/lattice/Composables/SplineUtils.hs`**
   - evaluateBezier, evaluateBezierTangent, bezierArcLength
   - findClosestPointOnPath, findPointAtPosition (Either Text instead of throw)
   - generateSplinePath, generateCurvePreview, transformPointToComp, transformPointToLayer
   - calculateSmoothHandles, simplifyPath (Ramer-Douglas-Peucker)
23. ✅ **`composables/useCurveEditorView.ts` → `src/lattice/Composables/CurveEditorView.hs`**
   - SelectedKeyframe, createViewState, fitToView, fitSelectionToView
   - zoomIn, zoomOut, handleWheelZoomPure, panView (pure view math; no DOM)
24. ✅ **`composables/useCurveEditorKeyboard.ts` → `src/lattice/Composables/CurveEditorKeyboard.hs`**
   - goToPreviousKeyframe, goToNextKeyframe (return Maybe Double for frame to jump to)
25. ✅ **`composables/useGuides.ts` → `src/lattice/Composables/Guides.hs`**
   - Guide, GuideOrientation, GuideContextMenu, GuideStyle; addGuide, removeGuide, clearGuides, updateGuidePosition, getGuideStyle (pure; no DOM)
26. ✅ **`composables/useViewportControls.ts` → `src/lattice/Composables/ViewportControls.hs`**
   - zoomInValue, zoomOutValue, clampZoom, setZoomChecked; fitZoomWithPadding, viewportTransformFromFit; screenToScene (Either Text; pure math only)
27. ✅ **`composables/useCurveEditorDraw.ts` → `src/lattice/Composables/CurveEditorDraw.hs`**
   - getPropertyColor, propertyColorDefault; gridFrameLines, gridValueLines; CurveSegmentType, curveSegmentData (pure data for UI to draw)
28. ✅ **`composables/useShapeDrawing.ts` → `src/lattice/Composables/ShapeDrawing.hs`**
   - ShapeDrawBounds, computeShapeBounds (constrain, fromCenter); ShapeToolType; shapePathFromBounds (rectangle, ellipse, polygon, star)
29. ✅ **`composables/useCurveEditorInteraction.ts` → `src/lattice/Composables/CurveEditorInteraction.hs`**
   - SelectionBox, selectionBoxFromPoints, pointInSelectionBox, keyframesInBox; isKeyframeSelected, hitTestKeyframe, defaultHitRadius (pure; no DOM)
30. ✅ **`composables/useCanvasSelection.ts` → `src/lattice/Composables/CanvasSelection.hs`**
   - Rect, Point, rectsIntersect, rectContains, rectFromPoints, pointDistance; SelectionMode, SelectableItem, findItemsInRect, applySelection (pure; no DOM)
31. ✅ **`composables/useSplineInteraction.ts` → `src/lattice/Composables/SplineInteraction.hs`**
   - PenSubMode, DragTargetType, DragTarget, PointWithId; closeThreshold, isSplineOrPathType; activeToolTipForPenSubMode; screenToCanvas; findClickedPoint, closePathPreview (pure; bezier/path in SplineUtils)
32. ✅ **`composables/useViewportGuides.ts` → `src/lattice/Composables/ViewportGuides.hs`**
   - SafeFrameBounds, ResolutionPreset, ResolutionGuide, SafeFrameStyle; resolutionPresets; safeFrameLeftStyle, safeFrameRightStyle, safeFrameTopStyle, safeFrameBottomStyle, compositionBoundaryStyle; resolutionCropBounds, resolutionGuideFromPreset (pure; projection in UI)

**Lean4 verification (composables):**
- **`Lattice.Composables.Guides`** (`leancomfy/lean/Lattice/Composables/Guides.lean`): Guide, GuideOrientation, addGuide, removeGuide, clearGuides, updateGuidePosition; theorems: removeGuide_length_le, clearGuides_length, addGuide_length, updateGuidePosition_length.
- **`Lattice.Composables.ViewportControls`** (`leancomfy/lean/Lattice/Composables/ViewportControls.lean`): minZoom, maxZoom, clampZoom, zoomInValue, zoomOutValue, fitZoomWithPadding, screenToScene (Option ScreenToSceneResult); no NumericSafety dependency.
- **`Lattice.Composables.CurveEditorInteraction`** (`leancomfy/lean/Lattice/Composables/CurveEditorInteraction.lean`): SelectionBox, selectionBoxFromPoints, pointInSelectionBox, defaultHitRadius.
- **`Lattice.Composables.CanvasSelection`** (`leancomfy/lean/Lattice/Composables/CanvasSelection.lean`): Point, Rect, rectsIntersect, rectContains, rectFromPoints, pointDistance, SelectionMode.

### Schema (1)

23. ✅ **`schemas/shared-validation.ts` → `src/lattice/Schema/SharedValidation.hs`**

### Services (21)

22. ✅ **`engine/layers/blendModeUtils.ts` / `types/blendModes.ts` → `src/lattice/Services/BlendModes.hs`**
23. ✅ **`services/colorManagement/ColorProfileService.ts` → `src/lattice/Services/ColorProfile.hs`**
24. ✅ **`services/export*` (pipeline) → `src/lattice/Services/ExportPipeline.hs`**
25. ✅ **`services/expressions` (evaluator) → `src/lattice/Services/ExpressionEvaluator.hs`**
26. ✅ **`services/frameInterpolation` → `src/lattice/Services/FrameInterpolation.hs`**
27. ✅ **`schemas/*` (JSON validation) → `src/lattice/Services/JSONValidation.hs`**
28. ✅ **`services/math3d` → `src/lattice/Services/Math3D.hs`**
29. ✅ **`services/meshDeformation3D` / meshWarp → `src/lattice/Services/MeshWarpDeformation.hs`**
30. ✅ **`services/modelIntegrity` → `src/lattice/Services/ModelIntegrity.hs`**
31. ✅ **`services/pathMorphing` / shape path → `src/lattice/Services/PathMorphing.hs`**
32. ✅ **`services/physics/*` (forces) → `src/lattice/Services/PhysicsForces.hs`, `PhysicsRandom.hs`, `PhysicsVectorMath.hs`**
33. ✅ **`services/preprocessor` → `src/lattice/Services/PreprocessorService.hs`**
34. ✅ **`services/propertyDriver` → `src/lattice/Services/PropertyDriver.hs`**
35. ✅ **`services/propertyEvaluator` → `src/lattice/Services/PropertyEvaluator.hs`**
36. ✅ **`services/shapeOperations` → `src/lattice/Services/ShapeOperations.hs`**
37. ✅ **`services/ai/stateSerializer` → `src/lattice/Services/StateSerializer.hs`**
38. ✅ **`schemas/templateBuilder` / template builder → `src/lattice/Services/TemplateBuilder.hs`**
39. ✅ **`services/timelineSnap` → `src/lattice/Services/TimelineSnap.hs`**
40. ✅ **`services/exportTemplates` / workflow → `src/lattice/Services/WorkflowTemplates.hs`**
41. ✅ **`services/audio/stemSeparation.ts` → `src/lattice/Services/AudioStemSeparation.hs`**

### Types (domain types; many TS files under `types/`)

42. ✅ **`types/project.ts` → `src/lattice/Types/Project.hs`**
43. ✅ **`types/index.ts`, `layerData.ts`, primitives → `src/lattice/Types/Layer.hs`, `LayerData*.hs`, `Primitives.hs`, `Core.hs`**
44. ✅ **`types/animation.ts` → `src/lattice/Types/Animation.hs`**
45. ✅ **`types/effects.ts`, `schemas/effects/*` → `src/lattice/Types/Effects/*.hs`**
46. ✅ **`types/layerStyles.ts` → `src/lattice/Types/LayerStyles/*.hs`**
47. ✅ **`types/masks.ts` → `src/lattice/Types/Masks/*.hs`**
48. ✅ **`types/meshWarp.ts` → `src/lattice/Types/MeshWarp/*.hs`**
49. ✅ **`types/presets.ts` → `src/lattice/Types/Presets/*.hs`**
50. ✅ **`types/assets.ts` → `src/lattice/Types/Assets/Core.hs`**
51. ✅ **`types/transform.ts` → `src/lattice/Types/Transform.hs`**
52. ✅ **`types/colors` (in effects/color) → `src/lattice/Types/Color.hs`**
53. ✅ **`types/shapes.ts` → `src/lattice/Types/Shapes/Helpers.hs`**
54. ✅ **`types/physics.ts`, precision limits → `src/lattice/Types/PrecisionLimits.hs`** (and Physics in State)

### State / Stores (each store has Lattice.State.* + FFI bridge)

55. ✅ **`stores/animationStore/*` → `src/lattice/State/Animation*.hs`**
56. ✅ **`stores/assetStore.ts` → `src/lattice/State/Asset.hs`**
57. ✅ **`stores/audioStore.ts`, `audio/*` → `src/lattice/State/Audio*.hs`**
58. ✅ **`stores/audioKeyframeStore.ts` → `src/lattice/State/AudioKeyframe.hs`**
59. ✅ **`stores/cacheStore.ts` → `src/lattice/State/Cache.hs`**
60. ✅ **`stores/cameraStore.ts` → `src/lattice/State/Camera.hs`**
61. ✅ **`stores/compositionStore.ts` → `src/lattice/State/Composition.hs`**
62. ✅ **`stores/decompositionStore.ts` → `src/lattice/State/Decomposition.hs`**
63. ✅ **`stores/depthflowStore.ts` → `src/lattice/State/Depthflow.hs`**
64. ✅ **`stores/effectStore/*` → `src/lattice/State/Effect.hs`**
65. ✅ **`stores/expressionStore/*` → `src/lattice/State/Expression.hs`**
66. ✅ **`stores/historyStore.ts` → `src/lattice/State/History.hs`**
67. ✅ **`stores/keyframeStore/*` → `src/lattice/State/Keyframe*.hs`**
68. ✅ **`stores/layerStore/*` → `src/lattice/State/Layer*.hs`, `State/Layer/*.hs`**
69. ✅ **`stores/markerStore.ts` → `src/lattice/State/Marker.hs`**
70. ✅ **`stores/particleStore.ts`, `particlePreferences.ts` → `src/lattice/State/Particle.hs`, `ParticlePreferences.hs`**
71. ✅ **`stores/physicsStore.ts` → `src/lattice/State/Physics.hs`**
72. ✅ **`stores/playbackStore.ts` → `src/lattice/State/Playback.hs`**
73. ✅ **`stores/presetStore.ts` → `src/lattice/State/Preset.hs`**
74. ✅ **`stores/projectStore.ts` → `src/lattice/State/Project.hs`**
75. ✅ **`stores/selectionStore.ts` → `src/lattice/State/Selection.hs`**
76. ✅ **`stores/textAnimatorStore.ts` → `src/lattice/State/TextAnimator.hs`**
77. ✅ **`stores/themeStore.ts` → `src/lattice/State/Theme.hs`**
78. ✅ **`stores/toastStore.ts` → `src/lattice/State/Toast.hs`**
79. ✅ **`stores/uiStore.ts` → `src/lattice/State/UI.hs`**
80. ✅ **`stores/validationLimitsStore.ts` → `src/lattice/State/ValidationLimits.hs`**
81. ✅ **`stores/videoStore.ts` → `src/lattice/State/Video.hs`**
82. ✅ **`stores/actions/layer/layerDefaults.ts` → `src/lattice/State/LayerDefaults.hs`**

### FFI (JS bridge; one per store/state — not “delete TS” yet, but port exists)

83+. ✅ **All `Lattice.FFI.*` modules** — bridge to PureScript/JS for each State module (AnimationState, AssetState, … VideoState, SchemaValidation, ProjectValidation, etc.). Logic lives in State; FFI is the boundary.

---

**Summary:** ~83+ TS-equivalent areas have Haskell implementations in `src/lattice/`. The UI still imports from the TS files; the HS code is used via FFI or parallel path. “Remaining” in TYPESCRIPT_MISSING_PORTS should be reduced by the above once those TS files are removed and callers switched to HS/PS.

## Verification

All ports verified for:

- ✅ No `any` types
- ✅ No `unknown` types
- ✅ No type assertions (`as unknown as`)
- ✅ No non-null assertions (`!`)
- ✅ No nullish coalescing (`??`)
- ✅ No logical OR defaults (`||`)
- ✅ No TypeScript ignore comments (`@ts-ignore`, `@ts-expect-error`)
- ✅ **No `error`, `undefined`, `userError`, `throwIO` with strings**
- ✅ **All errors use `Either Text a` (not `Either SomeException a`)**
- ✅ No `unsafe*` functions
- ✅ No partial functions (`head`, `tail`, `fromJust`, `!!`)
- ✅ Explicit types at function boundaries
- ✅ Proper error handling (Either Text a pattern)
- ✅ System F/Omega proofs documented

**See:** `docs/HASKELL_PORT_RULES.md` for complete forbidden patterns list.

## Haskell build (avoid technical debt)

- **Base files:** `lattice.cabal`, `cabal.project` at repo root; all 212+ Lattice modules listed in `exposed-modules`.
- **Command:** From repo root run `cabal build` (or `.\scripts\build-haskell.ps1` / `./scripts/build-haskell.sh`).
- **Rule:** After adding any new `.hs` file, add its module to `lattice.cabal` and ensure `cabal build` passes before committing.
- **Docs:** `docs/HASKELL_BUILD.md`.

## Remaining (to be updated in TYPESCRIPT_MISSING_PORTS)

After removing the ~83 ported areas above from the missing list, remaining is ~273 TS files (engine/runtime, composables, many services, schemas, workers). See `docs/TYPESCRIPT_MISSING_PORTS.md` — remove any line whose functionality is now in Haskell/PureScript.
