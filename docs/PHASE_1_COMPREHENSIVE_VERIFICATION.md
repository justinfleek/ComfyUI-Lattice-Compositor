# Phase 1 Comprehensive Verification

**Date:** 2026-01-12
**Purpose:** Verify NO files are missing Phase 1 migration

## Method

1. Find ALL files calling `store.*layer` methods (Phase 1)
2. Find ALL files using `layerStore.*` methods (correct Phase 1)
3. Compare lists to find gaps
4. Verify each file individually

## Phase 1 Layer Methods

These methods should use `layerStore`:
- `createLayer`, `deleteLayer`, `updateLayer`, `duplicateLayer`
- `moveLayer`, `renameLayer`, `getLayerById`, `selectLayer`
- `createTextLayer`, `createSplineLayer`, `createShapeLayer`
- `createCameraLayer`, `createVideoLayer`, `replaceLayerSource`
- `freezeFrameAtPlayhead`, `splitLayerAtPlayhead`, `sequenceLayers`
- `addSplineControlPoint`, `updateSplineControlPoint`, `getEvaluatedSplinePoints`
- `convertTextLayerToSplines`, `toggleLayer`
- `getLayers`, `getSelectedLayers`, `getSelectedLayer`, `getLayerChildren`
- `deselectLayer`, `copyLayer`, `cutLayer`, `pasteLayer`
- `deleteSelectedLayers`, `duplicateSelectedLayers`
- `getClipboardLayers`, `clearClipboard`
- `setLayerParent`, `toggleLayer3D`, `selectAllLayers`, `clearSelection`
- `createNestedCompLayer`, `updateNestedCompLayerData`
- `timeStretchLayer`, `reverseLayer`
- `enableSpeedMap`, `disableSpeedMap`, `toggleSpeedMap`
- `applyExponentialScale`
- `insertSplineControlPoint`, `deleteSplineControlPoint`
- `enableSplineAnimation`, `addSplinePointKeyframe`, `addSplinePointPositionKeyframe`
- `updateSplinePointWithKeyframe`, `isSplineAnimated`, `hasSplinePointKeyframes`
- `simplifySpline`, `smoothSplineHandles`, `copyPathToPosition`
- `updateLayerTransform`
- `separatePositionDimensions`, `linkPositionDimensions`
- `separateScaleDimensions`, `linkScaleDimensions`
- `hasPositionSeparated`, `hasScaleSeparated`

## Files Calling store.*layer Methods

[Will be populated by grep results]

## Files Using layerStore.* Methods

[Will be populated by grep results]

## Files That Need Phase 1 Migration

[Will list files that call store.*layer but don't use layerStore]

## Verification Status

⏳ **IN PROGRESS** - Running comprehensive grep to find all files
