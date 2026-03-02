# Store Migration Consumer Manifest

> **Purpose:** Tactical migration guide listing every compositorStore consumer and their exact changes
> **Generated:** 2026-01-10
> **Consumer Files:** 99
> **Store Methods Used:** ~260

---

## Table of Contents

1. [Method-to-Store Mapping](#1-method-to-store-mapping)
2. [Consumer File Analysis](#2-consumer-file-analysis)
3. [Migration Complexity Scores](#3-migration-complexity-scores)
4. [Cross-Domain Methods](#4-cross-domain-methods)

---

## 1. Method-to-Store Mapping

### Legend

| Store | Abbreviation | Description |
|-------|--------------|-------------|
| layerStore | **L** | Layer CRUD, hierarchy, **TEXT ANIMATORS** |
| keyframeStore | **K** | Keyframe CRUD, interpolation |
| animationStore | **A** | Playback, frame, time |
| audioStore | **AU** | Audio buffer, analysis, mappings |
| effectStore | **E** | Effects, styles |
| cameraStore | **C** | Cameras, viewports |
| selectionStore | **S** | Selection state (EXISTS) |
| historyStore | **H** | Undo/redo (EXISTS) |
| projectStore | **P** | Project, compositions |
| uiStore | **U** | Tools, panels, preferences, **SEGMENTATION** |
| physicsStore | **PH** | Physics simulation |
| expressionStore | **X** | Expressions, drivers, property links (NEW) |
| assetStore | **AS** | Assets, imports (EXISTS) |

**Total: 13 Domain Stores**

---

### Layer Domain (layerStore) - 45 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `createLayer` | 979 | Most used method |
| `getLayerById` | 736 | |
| `updateLayer` | 212 | |
| `createTextLayer` | 189 | |
| `updateLayerTransform` | 150 | |
| `updateLayerData` | 119 | |
| `layers` | 69 | Getter |
| `setLayerParent` | 42 | |
| `nestSelectedLayers` | 35 | Uses selection |
| `splitLayerAtPlayhead` | 25 | Uses animation |
| `updateSplineControlPoint` | 17 | |
| `duplicateLayer` | 16 | |
| `updateVideoLayerData` | 14 | |
| `addLayer` | 13 | |
| `renameLayer` | 11 | |
| `displayedLayers` | 5 | Getter |
| `createSplineLayer` | 5 | |
| `deleteLayer` | 10 | |
| `moveLayer` | 6 | |
| `sequenceLayers` | 6 | |
| `timeStretchLayer` | 1 | Uses animation |
| `toggleLayerVisibility` | 1 | |
| `toggleLayerSolo` | 1 | |
| `toggleLayerLock` | 1 | |
| `toggleLayer` | 2 | |
| `replaceLayerSource` | 1 | |
| `reverseSelectedLayers` | 1 | Uses selection |
| `reverseLayer` | 1 | |
| `sendToBack` | 1 | |
| `sendBackward` | 1 | |
| `bringToFront` | 1 | |
| `bringForward` | 1 | |
| `freezeFrameAtPlayhead` | 3 | Uses animation |
| `deleteSplineControlPoint` | 3 | |
| `insertSplineControlPoint` | 1 | |
| `smoothSplineHandles` | 1 | |
| `simplifySpline` | 1 | |
| `autoCalculateBezierTangents` | 2 | |
| `autoCalculateAllBezierTangents` | 3 | |
| `enableSplineAnimation` | 1 | |
| `hasSplinePointKeyframes` | 1 | |
| `getEvaluatedSplinePoints` | 1 | |
| `onVideoMetadataLoaded` | 1 | |
| `createVideoLayer` | 1 | |
| `createShapeLayer` | 1 | |
| `createParticleLayer` | 1 | |

---

### Keyframe Domain (keyframeStore) - 35 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `addKeyframe` | 393 | |
| `setKeyframeInterpolation` | 47 | |
| `setKeyframeHandle` | 31 | |
| `selectedKeyframeIds` | 25 | Selection state |
| `removeKeyframe` | 17 | |
| `setKeyframeControlMode` | 14 | |
| `pasteKeyframes` | 12 | |
| `copyKeyframes` | 12 | |
| `setKeyframeValue` | 7 | |
| `addKeyframeToSelection` | 8 | Selection |
| `updateKeyframeHandles` | 4 | |
| `moveKeyframe` | 8 | |
| `timeReverseKeyframes` | 6 | |
| `applyEasingPresetToKeyframes` | 6 | |
| `applyKeyframeVelocity` | 4 | |
| `setKeyframeHandleWithMode` | 3 | |
| `selectKeyframes` | 2 | |
| `hasKeyframesInClipboard` | 4 | |
| `getAllKeyframeFrames` | 2 | |
| `clearKeyframeSelection` | 2 | |
| `hasKeyframeSelection` | 2 | |
| `updateKeyframe` | 2 | |
| `getKeyframeVelocity` | 1 | |
| `moveKeyframes` | 1 | |
| `scaleKeyframeTiming` | 1 | |
| `clearKeyframes` | 1 | |

---

### Animation/Playback Domain (animationStore) - 20 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `setFrame` | 500 | |
| `currentFrame` | 192 | Getter |
| `frameCount` | 70 | Getter |
| `fps` | 36 | Getter |
| `isPlaying` | 14 | Getter |
| `jumpToNextKeyframe` | 12 | |
| `jumpToPrevKeyframe` | 8 | |
| `jumpFrames` | 8 | |
| `togglePlayback` | 8 | |
| `goToEnd` | 7 | |
| `currentTime` | 6 | Getter |
| `prevFrame` | 6 | |
| `nextFrame` | 6 | |
| `play` | 5 | |
| `pause` | 5 | |
| `goToStart` | 3 | |
| `jumpToNextMarker` | 2 | |
| `jumpToPreviousMarker` | 2 | |

---

### Audio Domain (audioStore) - 25 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `audioAnalysis` | 44 | Getter |
| `audioReactiveMapper` | 23 | |
| `audioBuffer` | 18 | Getter |
| `pathAnimators` | 11 | |
| `audioFile` | 11 | Getter |
| `peakData` | 7 | |
| `audioReactiveMappings` | 6 | |
| `audioMappings` | 6 | |
| `audioLoadingState` | 6 | |
| `audioLoadingProgress` | 4 | |
| `audioLoadingPhase` | 4 | |
| `audioLoadingError` | 3 | |
| `loadAudio` | 2 | |
| `audioVolume` | 2 | |
| `updateAudioMapping` | 1 | |
| `toggleAudioMute` | 1 | |
| `setPeakData` | 1 | |
| `setAudioVolume` | 1 | |
| `setAudioMuted` | 1 | |
| `removeAudioMapping` | 1 | |
| `getAudioReactiveValuesForLayer` | 1 | Cross-domain |
| `getAudioMappings` | 1 | |
| `createAudioPropertyDriver` | 1 | Cross-domain |
| `convertAudioToKeyframes` | 1 | **CROSS-DOMAIN** |
| `clearAudio` | 1 | |
| `audioMuted` | 1 | |
| `addAudioMapping` | 1 | |

---

### Effect Domain (effectStore) - 15 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `addEffectToLayer` | 159 | |
| `updateEffectParameter` | 59 | |
| `setEffectParamAnimated` | 11 | |
| `removeEffectFromLayer` | 8 | |
| `toggleEffect` | 7 | |
| `reorderEffects` | 7 | |
| `getEffectParameterValue` | 2 | |

---

### Camera Domain (cameraStore) - 15 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `updateCamera` | 15 | |
| `updateViewportState` | 12 | |
| `activeCameraId` | 12 | Getter |
| `cameras` | 8 | Getter |
| `viewOptions` | 7 | Getter |
| `cameraKeyframes` | 6 | |
| `updateViewOptions` | 6 | |
| `addCameraKeyframe` | 4 | |
| `viewportState` | 3 | Getter |
| `activeCamera` | 3 | Getter |
| `getCameraKeyframes` | 2 | |
| `getCamera` | 2 | |
| `getActiveCameraAtFrame` | 2 | |
| `createCameraLayer` | 2 | |
| `getCameraAtFrame` | 1 | |

---

### Selection Domain (selectionStore) - 20 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `selectedLayerIds` | 129 | Getter |
| `selectLayer` | 47 | |
| `selectLayers` | 42 | |
| `selectedLayer` | 19 | Getter |
| `toggleSelection` | 10 | |
| `addToSelection` | 10 | |
| `clearSelection` | 7 | |
| `singleSelectedLayerId` | 6 | Getter |
| `selectAllLayers` | 6 | |
| `removeFromSelection` | 6 | |
| `hasSelection` | 6 | Getter |
| `hasMultipleSelected` | 4 | Getter |
| `selectAsset` | 2 | |
| `lastSelectedLayerId` | 2 | Getter |
| `duplicateSelectedLayers` | 2 | |
| `deleteSelectedLayers` | 2 | |
| `cutSelectedLayers` | 2 | |
| `copySelectedLayers` | 2 | |
| `selectProperty` | 1 | |
| `selectedPropertyPath` | 1 | Getter |

---

### History Domain (historyStore) - 8 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `pushHistory` | 147 | |
| `undo` | 143 | |
| `redo` | 114 | |
| `historyStack` | 37 | Getter |
| `historyIndex` | 22 | Getter |
| `canUndo` | 4 | Getter |
| `canRedo` | 2 | Getter |

---

### Project Domain (projectStore) - 30 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `project` | 425 | Getter |
| `getActiveCompLayers` | 271 | |
| `getActiveComp` | 86 | |
| `activeCompositionId` | 79 | Getter |
| `activeComposition` | 34 | Getter |
| `updateCompositionSettings` | 14 | |
| `hasUnsavedChanges` | 12 | Getter |
| `autosaveTimerId` | 12 | |
| `autosaveIntervalMs` | 12 | |
| `templates` | 11 | |
| `compositionBreadcrumbs` | 11 | Getter |
| `openCompositionIds` | 10 | Getter |
| `createComposition` | 54 | |
| `switchComposition` | 34 | |
| `hasProject` | 5 | Getter |
| `getComposition` | 5 | |
| `renameComposition` | 5 | |
| `lastUsedTemplateId` | 5 | |
| `projectStateHash` | 5 | |
| `enterNestedComp` | 8 | |
| `saveProject` | 1 | |
| `saveProjectAs` | 1 | |
| `saveProjectToServer` | 1 | |
| `loadProjectFromFile` | 1 | |
| `loadProjectFromServer` | 1 | |
| `newProject` | 1 | |
| `exportProject` | 120 | |
| `closeCompositionTab` | 1 | |
| `deleteComposition` | 1 | |
| `resizeComposition` | 1 | |
| `navigateToBreadcrumb` | 1 | |
| `navigateBack` | 1 | |
| `openCompositions` | 1 | |
| `breadcrumbPath` | 1 | |

---

### UI Domain (uiStore) - 25 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `snapConfig` | 58 | Getter |
| `preferences` | 56 | Getter |
| `curveEditorVisible` | 22 | Getter |
| `updatePreferences` | 16 | |
| `toggleCurveEditor` | 14 | |
| `currentTool` | 12 | Getter |
| `setSnapConfig` | 11 | |
| `hideMinimizedLayers` | 11 | Getter |
| `toggleSnapping` | 10 | |
| `setTool` | 10 | |
| `findSnapPoint` | 6 | |
| `frameCacheEnabled` | 6 | Getter |
| `setCurveEditorVisible` | 6 | |
| `toggleHideMinimizedLayers` | 5 | |
| `toggleSnapType` | 4 | |
| `shapeToolOptions` | 3 | Getter |
| `setTimelineZoom` | 3 | |
| `setHideMinimizedLayers` | 6 | |
| `setShapeToolOptions` | 1 | |
| `clearFrameCache` | 1 | |

---

### Segmentation Domain → uiStore - 10 methods

**Decision:** Segmentation is UI tool state, not core data. Goes to uiStore.

| Method | Usage Count | Target | Notes |
|--------|-------------|--------|-------|
| `segmentBoxStart` | 7 | **U** | UI tool state |
| `segmentPendingMask` | 5 | **U** | Pending mask preview |
| `setSegmentLoading` | 4 | **U** | Loading indicator |
| `setSegmentBoxStart` | 3 | **U** | Box selection start |
| `segmentMode` | 3 | **U** | Tool mode |
| `segmentIsLoading` | 3 | **U** | Loading state |
| `setSegmentPendingMask` | 2 | **U** | Preview mask |
| `setSegmentMode` | 2 | **U** | Tool mode change |
| `confirmSegmentMask` | 2 | **U** | Applies mask to layer (cross-domain) |
| `clearSegmentPendingMask` | 2 | **U** | Clear preview |

---

### Expression Domain → expressionStore (NEW) - 18 methods

**Decision:** Expressions are complex enough for their own domain store.

| Method | Usage Count | Target | Notes |
|--------|-------------|--------|-------|
| `enablePropertyExpression` | 46 | **X** | Core expression |
| `getPropertyExpression` | 32 | **X** | Query |
| `hasPropertyExpression` | 30 | **X** | Query |
| `configureExpressionSelector` | 15 | **X** | Expression config |
| `propertyDriverSystem` | 13 | **X** | State |
| `propertyDrivers` | 7 | **X** | State |
| `disablePropertyExpression` | 8 | **X** | Core expression |
| `getDriversForLayer` | 4 | **X** | Query |
| `setPropertyExpression` | 4 | **X** | Core expression |
| `removePropertyExpression` | 4 | **X** | Core expression |
| `updateExpressionParams` | 2 | **X** | Expression config |
| `togglePropertyExpression` | 2 | **X** | Toggle |
| `removePropertyDriver` | 2 | **X** | Driver management |
| `initializePropertyDriverSystem` | 1 | **X** | Initialization |
| `getDrivenValuesForLayer` | 1 | **X** | Query |
| `convertExpressionToKeyframes` | 1 | **X** | Cross-domain (calls keyframeStore) |
| `canBakeExpression` | 1 | **X** | Query |
| `createPropertyLink` | 1 | **X** | Property linking |

---

### Text Animator Domain → layerStore - 17 methods

**Decision:** Text animators operate on layer data, so they belong in layerStore.

| Method | Usage Count | Target | Notes |
|--------|-------------|--------|-------|
| `setAnimatorPropertyValue` | 143 | **L** | Text layer property |
| `getCharacterTransforms` | 140 | **L** | Text layer data |
| `addTextAnimator` | 140 | **L** | Modifies layer |
| `configureRangeSelector` | 129 | **L** | Animator config |
| `setTextPath` | 32 | **L** | Text layer path |
| `getCharacterPathPlacements` | 22 | **L** | Text layer data |
| `updateTextPath` | 10 | **L** | Modifies layer |
| `configureWigglySelector` | 8 | **L** | Animator config |
| `getTextPathConfig` | 7 | **L** | Text layer data |
| `getTextAnimators` | 6 | **L** | Text layer data |
| `hasTextPath` | 4 | **L** | Text layer check |
| `updateTextAnimator` | 3 | **L** | Modifies layer |
| `getTextAnimator` | 2 | **L** | Text layer data |
| `getRangeSelectionValue` | 2 | **L** | Animator query |
| `removeTextAnimator` | 1 | **L** | Modifies layer |
| `clearTextPath` | 1 | **L** | Modifies layer |
| `getTextContent` | 1 | **L** | Text layer data |

---

### Marker Domain (Move to animationStore) - 5 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `addMarkers` | 2 | |
| `getMarkers` | 2 | |
| `addMarker` | 1 | |
| `clearMarkers` | 1 | |

---

### Backend Detection (Move to uiStore) - 6 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `activeBackend` | 9 | |
| `hasWebGPU` | 7 | |
| `hasWebGL` | 4 | |
| `backendDescription` | 3 | |
| `supportsHighParticleCounts` | 1 | |
| `detectCapabilities` | 2 | |
| `applyLowEndPreset` | 2 | |
| `applyHighEndPreset` | 2 | |
| `resetToDefaults` | 2 | |

---

### Source Images (Move to projectStore) - 3 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `sourceImage` | 9 | |
| `depthMap` | 3 | |
| `width` | 22 | |
| `height` | 25 | |
| `backgroundColor` | 2 | |
| `assets` | 2 | |
| `removeUnusedAssets` | 1 | |

---

### Autosave (Move to projectStore) - 4 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `autosaveEnabled` | 8 | |
| `lastSaveTime` | 6 | |
| `lastSaveProjectId` | 7 | |
| `startAutosaveTimer` | 1 | |
| `stopAutosaveTimer` | 1 | |

---

### Property Setting (Shared across stores) - 5 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `setPropertyValue` | 7 | Route by property type |
| `evaluatePropertyAtFrame` | 3 | Cross-domain |
| `getPropertyValueAtFrame` | 1 | |
| `setPropertyAnimated` | 1 | |

---

### Clipboard (Move to uiStore) - 5 methods

| Method | Usage Count | Notes |
|--------|-------------|-------|
| `clipboard` | 8 | |
| `pasteLayers` | 2 | |
| `paste` | 1 | |
| `cutSelected` | 1 | |
| `copySelected` | 1 | |

---

## 2. Consumer File Analysis

### Canvas Components (6 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **ThreeCanvas.vue** | layers, currentFrame, updateLayer, selectedLayer, getLayerById, selectLayer, currentTool, viewOptions, snapConfig, setFrame, height, width, fps, segmentBoxStart, depthMap, backgroundColor, peakData | L, A, S, U, AU, P | HIGH |
| **SplineEditor.vue** | updateSplineControlPoint, setKeyframeHandle, setKeyframeInterpolation, selectedLayerIds, createLayer, addKeyframe | L, K, S | MEDIUM |
| **CurveEditor.vue** | selectedKeyframeIds, setKeyframeHandle, setKeyframeInterpolation, currentFrame, setFrame, fps, frameCount | K, A | MEDIUM |
| **CurveEditorCanvas.vue** | selectedKeyframeIds, setKeyframeHandle, addKeyframe, removeKeyframe, moveKeyframe | K | LOW |
| **MaskEditor.vue** | selectedLayer, updateLayerData | L, S | LOW |
| **MeshWarpPinEditor.vue** | selectedLayer, updateLayerData | L, S | LOW |

---

### Panel Components (17 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **AudioPanel.vue** | audioAnalysis, audioBuffer, audioFile, peakData, loadAudio, audioVolume, toggleAudioMute, convertAudioToKeyframes, addAudioMapping, getAudioMappings, updateAudioMapping, removeAudioMapping, audioMappings, audioReactiveMappings, audioReactiveMapper, audioLoadingState, audioLoadingProgress, audioLoadingPhase, audioLoadingError, clearAudio, setAudioVolume, setAudioMuted, setPeakData, createAudioPropertyDriver, getAudioReactiveValuesForLayer + layer methods | AU, L, K, A | **CRITICAL** |
| **PropertiesPanel.vue** | project, layers, selectedLayer, selectedLayerIds, updateLayerData, getLayerById | L, S, P | HIGH |
| **ProjectPanel.vue** | project, activeCompositionId, createComposition, switchComposition, hasProject, hasUnsavedChanges, saveProject, newProject | P | MEDIUM |
| **AssetsPanel.vue** | project, assets, selectAsset, removeUnusedAssets | P, S | LOW |
| **CameraProperties.vue** | updateCamera, addCameraKeyframe, getCameraKeyframes, activeCameraId, cameras | C, K | MEDIUM |
| **EffectsPanel.vue** | selectedLayer, addEffectToLayer, removeEffectFromLayer, reorderEffects, toggleEffect | L, E, S | MEDIUM |
| **EffectControlsPanel.vue** | updateEffectParameter, setEffectParamAnimated, getEffectParameterValue | E, K | LOW |
| **PreviewPanel.vue** | currentFrame, frameCount, fps, isPlaying, togglePlayback, play, pause | A | LOW |
| **ExportPanel.vue** | project, exportProject, width, height, fps, frameCount | P, A | LOW |
| **LayerDecompositionPanel.vue** | createLayer, updateLayerData, project | L, P | LOW |
| **RenderQueuePanel.vue** | project, exportProject | P | LOW |
| **AIGeneratePanel.vue** | createLayer, project | L, P | LOW |
| **Model3DProperties.vue** | selectedLayer, updateLayerData | L, S | LOW |
| **GenerativeFlowPanel.vue** | project, createLayer | L, P | LOW |
| **ExposedPropertyControl.vue** | getPropertyExpression, setPropertyValue | X, L | LOW |
| **AIChatPanel.vue** | project | P | LOW |
| **AlignPanel.vue** | selectedLayerIds, updateLayerTransform | L, S | LOW |

---

### Property Components (20 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **ParticleProperties.vue** | selectedLayer, updateLayerData, pushHistory | L, S, H | HIGH |
| **TextProperties.vue** | selectedLayer, updateLayerData, addTextAnimator, setAnimatorPropertyValue, setTextPath | L, S, Text | HIGH |
| **ShapeProperties.vue** | selectedLayer, updateLayerData | L, S | MEDIUM |
| **AudioProperties.vue** | audioAnalysis, audioBuffer, audioFile | AU | LOW |
| **PhysicsProperties.vue** | selectedLayer, updateLayerData | L, S | LOW |
| **DepthflowProperties.vue** | selectedLayer, updateLayerData | L, S | LOW |
| **VideoProperties.vue** | selectedLayer, updateVideoLayerData | L, S | LOW |
| **ExpressionInput.vue** | enablePropertyExpression, getPropertyExpression, hasPropertyExpression, disablePropertyExpression | X | LOW |
| **CameraProperties.vue** | updateCamera, addCameraKeyframe | C, K | LOW |
| **PathProperties.vue** | selectedLayer, updateSplineControlPoint | L, S | LOW |
| **PoseProperties.vue** | selectedLayer, updateLayerData | L, S | LOW |
| **LayerStylesPanel.vue** | selectedLayer, updateLayerData | L, S | LOW |
| Shape editors (15 files) | selectedLayer, updateLayerData | L, S | LOW each |

---

### Dialog Components (12 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **TemplateBuilderDialog.vue** | project, templates, exportProject | P | MEDIUM |
| **ExportDialog.vue** | project, exportProject, width, height, fps, frameCount | P, A | MEDIUM |
| **CompositionSettingsDialog.vue** | updateCompositionSettings, getActiveComp | P | LOW |
| **DecomposeDialog.vue** | createLayer, project | L, P | LOW |
| **PathSuggestionDialog.vue** | selectedLayer | L, S | LOW |
| **SmootherPanel.vue** | selectedKeyframeIds, setKeyframeInterpolation | K | LOW |
| **VectorizeDialog.vue** | createLayer | L | LOW |
| **FrameInterpolationDialog.vue** | project, currentFrame | P, A | LOW |
| **MotionSketchPanel.vue** | addKeyframe, currentFrame | K, A | LOW |
| **TimeStretchDialog.vue** | selectedLayer, timeStretchLayer | L, S | LOW |
| **ComfyUIExportDialog.vue** | project, exportProject | P | LOW |

---

### Timeline Components (6 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **TimelinePanel.vue** | currentFrame, setFrame, frameCount, fps, layers, selectedLayerIds, isPlaying, togglePlayback, snapConfig | A, L, S, U | HIGH |
| **EnhancedLayerTrack.vue** | layers, selectedLayerIds, selectLayer, updateLayer, addKeyframe, removeKeyframe, moveKeyframe, setKeyframeInterpolation | L, K, S | HIGH |
| **PropertyTrack.vue** | addKeyframe, selectedKeyframeIds, setKeyframeHandle, moveKeyframe | K | MEDIUM |
| **CompositionTabs.vue** | openCompositionIds, activeCompositionId, switchComposition, closeCompositionTab | P | LOW |
| **LayerTrack.vue** | selectedLayerIds, selectLayer, updateLayer | L, S | LOW |
| **Playhead.vue** | currentFrame, setFrame, isPlaying | A | LOW |

---

### Layout Components (5 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **WorkspaceLayout.vue** | project, hasProject, curveEditorVisible, setCurveEditorVisible | P, U | MEDIUM |
| **WorkspaceToolbar.vue** | currentTool, setTool, shapeToolOptions | U | LOW |
| **MenuBar.vue** | project, saveProject, newProject, undo, redo, canUndo, canRedo | P, H | MEDIUM |
| **RightSidebar.vue** | selectedLayer | S | LOW |
| **ViewOptionsToolbar.vue** | viewOptions, updateViewOptions | C | LOW |

---

### Composables (7 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **useKeyboardShortcuts.ts** | undo, redo, createLayer, deleteLayer, selectAllLayers, copySelectedLayers, pasteKeyframes, etc. (40+ methods) | ALL | **CRITICAL** |
| **useMenuActions.ts** | Similar to keyboard shortcuts | ALL | **CRITICAL** |
| **useAssetHandlers.ts** | createLayer, project | L, P | LOW |
| **useCanvasSegmentation.ts** | segmentBoxStart, setSegmentMode, confirmSegmentMask, etc. | Segmentation | MEDIUM |
| **useExpressionEditor.ts** | enablePropertyExpression, getPropertyExpression | X | LOW |
| **useShapeDrawing.ts** | createLayer, shapeToolOptions | L, U | LOW |
| **useViewportGuides.ts** | viewOptions, snapConfig | C, U | LOW |

---

### Services (4 files)

| File | Methods Used | Target Stores | Complexity |
|------|--------------|---------------|------------|
| **actionExecutor.ts** | createLayer, updateLayer, addKeyframe, addEffectToLayer, etc. (100+ methods) | ALL | **CRITICAL** |
| **stateSerializer.ts** | project | P | LOW |
| **cameraTrackingImport.ts** | createLayer, addCameraKeyframe | L, C, K | MEDIUM |
| **preprocessorService.ts** | sourceImage, depthMap | P | LOW |

---

## 3. Migration Complexity Scores

### CRITICAL (5 files) - Need comprehensive rewrite

| File | Lines | Store Methods | Why Critical |
|------|-------|---------------|--------------|
| `useKeyboardShortcuts.ts` | 1,766 | 40+ | Uses methods from ALL domains |
| `useMenuActions.ts` | ~500 | 30+ | Uses methods from ALL domains |
| `services/ai/actionExecutor.ts` | 1,869 | 100+ | AI actions touch everything |
| `AudioPanel.vue` | 1,851 | 27 | Cross-domain: audio + layers + keyframes |
| `ThreeCanvas.vue` | 2,197 | 17 | Uses 6 different domains |

### HIGH (12 files) - Significant refactoring

| File | Lines | Store Methods | Notes |
|------|-------|---------------|-------|
| `TimelinePanel.vue` | 1,140 | 9 | 4 domains |
| `EnhancedLayerTrack.vue` | 1,402 | 8 | 3 domains |
| `PropertiesPanel.vue` | 1,707 | 6 | Router for all properties |
| `ParticleProperties.vue` | 2,683 | 3 | Uses history |
| `TextProperties.vue` | 1,633 | 5 | Text animator methods |
| `CurveEditor.vue` | 2,006 | 7 | 2 domains |
| `SplineEditor.vue` | 1,049 | 6 | 3 domains |
| `MenuBar.vue` | 772 | 7 | Project + history |
| `WorkspaceLayout.vue` | 1,768 | 4 | 2 domains |
| `cameraTrackingImport.ts` | 854 | 3 | 3 domains |
| `CameraProperties.vue` | 1,324 | 5 | 2 domains |
| `TemplateBuilderDialog.vue` | 1,591 | 3 | Project access |

### MEDIUM (25 files) - Moderate changes

Files using 2-3 domains, 3-6 methods each.

### LOW (57 files) - Simple import swap

Files using 1 domain, 1-3 methods. Just change import statement.

---

## 4. Cross-Domain Methods

These methods touch multiple stores and need special handling:

| Method | Source Domain | Needs Access To | Migration Strategy |
|--------|---------------|-----------------|-------------------|
| `convertAudioToKeyframes` | Audio | Keyframes, Layers | audioStore calls keyframeStore |
| `convertExpressionToKeyframes` | Expression | Keyframes, Layers | expressionStore calls keyframeStore |
| `splitLayerAtPlayhead` | Layer | Animation | layerStore reads animationStore.currentFrame |
| `freezeFrameAtPlayhead` | Layer | Animation | layerStore reads animationStore.currentFrame |
| `timeStretchLayer` | Layer | Animation | layerStore reads animationStore |
| `nestSelectedLayers` | Layer | Selection | layerStore reads selectionStore |
| `reverseSelectedLayers` | Layer | Selection | layerStore reads selectionStore |
| `duplicateSelectedLayers` | Selection | Layer | selectionStore calls layerStore |
| `deleteSelectedLayers` | Selection | Layer | selectionStore calls layerStore |
| `copySelectedLayers` | Selection | Layer | Uses both |
| `cutSelectedLayers` | Selection | Layer | Uses both |
| `pasteKeyframes` | Keyframe | Selection | Uses selectedKeyframeIds |
| `copyKeyframes` | Keyframe | Selection | Uses selectedKeyframeIds |
| `jumpToNextKeyframe` | Animation | Keyframe | Needs keyframe positions |
| `jumpToPrevKeyframe` | Animation | Keyframe | Needs keyframe positions |
| `getAudioReactiveValuesForLayer` | Audio | Layer | Cross-reference |
| `createAudioPropertyDriver` | Audio | Expression | Creates driver |
| `evaluatePropertyAtFrame` | Shared | Layer, Keyframe, Expression | Complex evaluation |
| `getPropertyValueAtFrame` | Shared | Layer, Keyframe, Expression | Complex evaluation |

---

## 5. Migration Verification Checklist

For EACH file migrated:

- [ ] Old import removed: `import { useCompositorStore } from '@/stores/compositorStore'`
- [ ] New imports added for each domain store used
- [ ] All `store.method()` calls updated to `domainStore.method()`
- [ ] TypeScript compiles without errors
- [ ] Unit tests pass (if any)
- [ ] Manual smoke test of affected functionality

---

*Document Version: 1.0*
*Generated: 2026-01-10*
