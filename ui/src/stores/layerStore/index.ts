/**
 * Layer Store
 *
 * Domain store for layer CRUD operations, hierarchy management, and transforms.
 *
 * MODULE STRUCTURE:
 * - types.ts: Type definitions and interfaces
 * - crud.ts: Create, read, update, delete, duplicate, move
 * - clipboard.ts: Copy, paste, cut operations
 * - hierarchy.ts: Parenting, 3D mode, hierarchy queries
 * - specialized.ts: Text layer, spline layer, shape layer, source replacement
 * - time.ts: Time stretch, reverse, freeze, split, speed map
 * - batch.ts: Sequence layers, exponential scale
 * - spline.ts: Spline control points, animation, simplification
 * - pathOperations.ts: Copy path to position keyframes
 */

import { defineStore } from "pinia";

// ============================================================================
// MODULE IMPORTS
// ============================================================================

// Types (re-export for consumers)
export type {
  LayerSourceReplacement,
  CreateLayerOptions,
  DeleteLayerOptions,
  DuplicateLayerOptions,
  SequenceLayersOptions,
  ExponentialScaleOptions,
  TimeStretchOptions,
  LayerState,
  CompositorStoreAccess,
} from "./types";

// CRUD operations
import {
  createLayer as createLayerImpl,
  deleteLayer as deleteLayerImpl,
  updateLayer as updateLayerImpl,
  updateLayerData as updateLayerDataImpl,
  duplicateLayer as duplicateLayerImpl,
  moveLayer as moveLayerImpl,
  renameLayer as renameLayerImpl,
  updateLayerTransform as updateLayerTransformImpl,
  toggleLayerLock as toggleLayerLockImpl,
  toggleLayerVisibility as toggleLayerVisibilityImpl,
  toggleLayerSolo as toggleLayerSoloImpl,
  bringToFront as bringToFrontImpl,
  sendToBack as sendToBackImpl,
  bringForward as bringForwardImpl,
  sendBackward as sendBackwardImpl,
  regenerateKeyframeIds,
} from "./crud";

// Clipboard operations
import {
  setClipboard as setClipboardImpl,
  clearClipboard as clearClipboardImpl,
  getClipboardLayers as getClipboardLayersImpl,
  copySelectedLayers as copySelectedLayersImpl,
  pasteLayers as pasteLayersImpl,
  cutSelectedLayers as cutSelectedLayersImpl,
} from "./clipboard";

// Hierarchy operations
import {
  setLayerParent as setLayerParentImpl,
  toggleLayer3D as toggleLayer3DImpl,
  selectLayer as selectLayerImpl,
  deselectLayer as deselectLayerImpl,
  clearSelection as clearSelectionImpl,
  getLayerById as getLayerByIdImpl,
  getLayerChildren as getLayerChildrenImpl,
  getLayerDescendants as getLayerDescendantsImpl,
  getVisibleLayers as getVisibleLayersImpl,
  getDisplayedLayers as getDisplayedLayersImpl,
  getRootLayers as getRootLayersImpl,
  getCameraLayers as getCameraLayersImpl,
  getSelectedLayers as getSelectedLayersImpl,
  getSelectedLayer as getSelectedLayerImpl,
  selectAllLayers as selectAllLayersImpl,
  deleteSelectedLayers as deleteSelectedLayersImpl,
  duplicateSelectedLayers as duplicateSelectedLayersImpl,
} from "./hierarchy";

// Specialized operations
import {
  createTextLayer as createTextLayerImpl,
  createSplineLayer as createSplineLayerImpl,
  createShapeLayer as createShapeLayerImpl,
  createCameraLayer as createCameraLayerImpl,
  createVideoLayer as createVideoLayerImpl,
  createNestedCompLayer as createNestedCompLayerImpl,
  updateNestedCompLayerData as updateNestedCompLayerDataImpl,
  replaceLayerSource as replaceLayerSourceImpl,
} from "./specialized";

// Time operations
import {
  timeStretchLayer as timeStretchLayerImpl,
  reverseLayer as reverseLayerImpl,
  freezeFrameAtPlayhead as freezeFrameAtPlayheadImpl,
  splitLayerAtPlayhead as splitLayerAtPlayheadImpl,
  enableSpeedMap as enableSpeedMapImpl,
  disableSpeedMap as disableSpeedMapImpl,
  toggleSpeedMap as toggleSpeedMapImpl,
} from "./time";

// Batch operations
import {
  sequenceLayers as sequenceLayersImpl,
  applyExponentialScale as applyExponentialScaleImpl,
} from "./batch";

// Spline operations
import {
  addSplineControlPoint as addSplineControlPointImpl,
  insertSplineControlPoint as insertSplineControlPointImpl,
  updateSplineControlPoint as updateSplineControlPointImpl,
  deleteSplineControlPoint as deleteSplineControlPointImpl,
  enableSplineAnimation as enableSplineAnimationImpl,
  addSplinePointKeyframe as addSplinePointKeyframeImpl,
  addSplinePointPositionKeyframe as addSplinePointPositionKeyframeImpl,
  updateSplinePointWithKeyframe as updateSplinePointWithKeyframeImpl,
  getEvaluatedSplinePoints as getEvaluatedSplinePointsImpl,
  isSplineAnimated as isSplineAnimatedImpl,
  hasSplinePointKeyframes as hasSplinePointKeyframesImpl,
  simplifySpline as simplifySplineImpl,
  smoothSplineHandles as smoothSplineHandlesImpl,
} from "./spline";
export type { SplineControlPoint } from "./spline";

// Text conversion
import { convertTextLayerToSplines as convertTextLayerToSplinesImpl } from "./textConversion";
export type { ConvertTextToSplinesOptions } from "./textConversion";

// Path operations
import { copyPathToPosition as copyPathToPositionImpl } from "./pathOperations";
export type { CopyPathToPositionOptions } from "./pathOperations";

// Types for internal use
import type {
  LayerState,
  CompositorStoreAccess,
  DeleteLayerOptions,
  SequenceLayersOptions,
  ExponentialScaleOptions,
  TimeStretchOptions,
  LayerSourceReplacement,
} from "./types";
import type { Layer, ClipboardKeyframe, AnyLayerData, EvaluatedControlPoint, NestedCompData } from "@/types/project";
import type { SplineControlPoint } from "./spline";
import type { ConvertTextToSplinesOptions } from "./textConversion";
import type { CopyPathToPositionOptions } from "./pathOperations";

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useLayerStore = defineStore("layer", {
  state: (): LayerState => ({
    clipboard: {
      layers: [],
      keyframes: [],
    },
  }),

  getters: {
    /** Check if clipboard has layers */
    hasLayersInClipboard: (state) => state.clipboard.layers.length > 0,

    /** Check if clipboard has keyframes */
    hasKeyframesInClipboard: (state) => state.clipboard.keyframes.length > 0,
  },

  actions: {
    // ========================================================================
    // CLIPBOARD STATE
    // ========================================================================

    setClipboard(layers: Layer[], keyframes: ClipboardKeyframe[] = []): void {
      setClipboardImpl(this.$state, layers, keyframes);
    },

    clearClipboard(): void {
      clearClipboardImpl(this.$state);
    },

    getClipboardLayers(): Layer[] {
      return getClipboardLayersImpl(this.$state);
    },

    // ========================================================================
    // LAYER CRUD
    // ========================================================================

    createLayer(
      compositorStore: CompositorStoreAccess,
      type: Layer["type"],
      name?: string,
    ): Layer {
      return createLayerImpl(compositorStore, type, name);
    },

    deleteLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      options?: DeleteLayerOptions,
    ): void {
      deleteLayerImpl(compositorStore, layerId, options);
    },

    updateLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      updates: Partial<Layer>,
    ): void {
      updateLayerImpl(compositorStore, layerId, updates);
    },

    updateLayerData(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      dataUpdates: Partial<AnyLayerData> & Record<string, unknown>,
    ): void {
      updateLayerDataImpl(compositorStore, layerId, dataUpdates);
    },

    duplicateLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): Layer | null {
      return duplicateLayerImpl(compositorStore, layerId);
    },

    moveLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      newIndex: number,
    ): void {
      moveLayerImpl(compositorStore, layerId, newIndex);
    },

    renameLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      newName: string,
    ): void {
      renameLayerImpl(compositorStore, layerId, newName);
    },

    updateLayerTransform(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      updates: {
        position?: { x: number; y: number; z?: number };
        scale?: { x: number; y: number; z?: number };
        rotation?: number;
        opacity?: number;
        origin?: { x: number; y: number; z?: number };
        anchor?: { x: number; y: number; z?: number };
      },
    ): void {
      updateLayerTransformImpl(compositorStore, layerId, updates);
    },

    toggleLayerLock(compositorStore: CompositorStoreAccess): void {
      toggleLayerLockImpl(compositorStore);
    },

    toggleLayerVisibility(compositorStore: CompositorStoreAccess): void {
      toggleLayerVisibilityImpl(compositorStore);
    },

    toggleLayerSolo(compositorStore: CompositorStoreAccess): void {
      toggleLayerSoloImpl(compositorStore);
    },

    bringToFront(compositorStore: CompositorStoreAccess): void {
      bringToFrontImpl(compositorStore);
    },

    sendToBack(compositorStore: CompositorStoreAccess): void {
      sendToBackImpl(compositorStore);
    },

    bringForward(compositorStore: CompositorStoreAccess): void {
      bringForwardImpl(compositorStore);
    },

    sendBackward(compositorStore: CompositorStoreAccess): void {
      sendBackwardImpl(compositorStore);
    },

    /** @internal Used by clipboard operations */
    _regenerateKeyframeIds(layer: Layer): void {
      regenerateKeyframeIds(layer);
    },

    // ========================================================================
    // CLIPBOARD OPERATIONS
    // ========================================================================

    copySelectedLayers(compositorStore: CompositorStoreAccess): void {
      copySelectedLayersImpl(this.$state, compositorStore);
    },

    pasteLayers(compositorStore: CompositorStoreAccess): Layer[] {
      return pasteLayersImpl(this.$state, compositorStore);
    },

    cutSelectedLayers(compositorStore: CompositorStoreAccess): void {
      cutSelectedLayersImpl(this.$state, compositorStore);
    },

    // ========================================================================
    // HIERARCHY
    // ========================================================================

    setLayerParent(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      parentId: string | null,
    ): void {
      setLayerParentImpl(compositorStore, layerId, parentId);
    },

    toggleLayer3D(compositorStore: CompositorStoreAccess, layerId: string): void {
      toggleLayer3DImpl(compositorStore, layerId);
    },

    // ========================================================================
    // SELECTION HELPERS
    // ========================================================================

    selectLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      addToSelection = false,
    ): void {
      selectLayerImpl(compositorStore, layerId, addToSelection);
    },

    deselectLayer(compositorStore: CompositorStoreAccess, layerId: string): void {
      deselectLayerImpl(compositorStore, layerId);
    },

    clearSelection(compositorStore: CompositorStoreAccess): void {
      clearSelectionImpl(compositorStore);
    },

    selectAllLayers(compositorStore: CompositorStoreAccess): void {
      selectAllLayersImpl(compositorStore);
    },

    deleteSelectedLayers(compositorStore: CompositorStoreAccess): void {
      deleteSelectedLayersImpl(compositorStore);
    },

    duplicateSelectedLayers(compositorStore: CompositorStoreAccess): string[] {
      return duplicateSelectedLayersImpl(compositorStore);
    },

    // ========================================================================
    // SPECIALIZED LAYER CREATION
    // ========================================================================

    createTextLayer(
      compositorStore: CompositorStoreAccess,
      text: string = "Text",
    ): Layer {
      return createTextLayerImpl(compositorStore, text);
    },

    createSplineLayer(compositorStore: CompositorStoreAccess): Layer {
      return createSplineLayerImpl(compositorStore);
    },

    createShapeLayer(
      compositorStore: CompositorStoreAccess,
      name: string = "Shape Layer",
    ): Layer {
      return createShapeLayerImpl(compositorStore, name);
    },

    /**
     * Create a camera layer
     * Requires camera store access (cameras Map, activeCameraId, selectLayer)
     */
    createCameraLayer(
      compositorStore: CompositorStoreAccess & {
        cameras: Map<string, any>;
        activeCameraId: string | null;
        selectLayer: (layerId: string) => void;
      },
      name?: string,
    ): Layer {
      return createCameraLayerImpl(compositorStore, name);
    },

    /**
     * Create a video layer from a file
     * Requires video store access (assets Record)
     * Delegates to videoActions for metadata extraction and asset management
     */
    async createVideoLayer(
      compositorStore: CompositorStoreAccess & {
        assets: Record<string, any>;
      },
      file: File,
      autoResizeComposition: boolean = true,
    ): Promise<{ status: string; layer?: Layer; error?: string; [key: string]: any }> {
      return createVideoLayerImpl(compositorStore, file, autoResizeComposition);
    },

    /**
     * Create a nested comp layer referencing another composition
     */
    createNestedCompLayer(
      compositorStore: CompositorStoreAccess,
      compositionId: string,
      name?: string,
    ): Layer {
      return createNestedCompLayerImpl(compositorStore, compositionId, name);
    },

    /**
     * Update nested comp layer data
     */
    updateNestedCompLayerData(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      updates: Partial<NestedCompData>,
    ): void {
      updateNestedCompLayerDataImpl(compositorStore, layerId, updates);
    },

    // ========================================================================
    // SOURCE REPLACEMENT
    // ========================================================================

    replaceLayerSource(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      newSource: LayerSourceReplacement,
    ): void {
      replaceLayerSourceImpl(compositorStore, layerId, newSource);
    },

    // ========================================================================
    // BATCH OPERATIONS
    // ========================================================================

    sequenceLayers(
      compositorStore: CompositorStoreAccess,
      layerIds: string[],
      options: SequenceLayersOptions = {},
    ): number {
      return sequenceLayersImpl(compositorStore, layerIds, options);
    },

    applyExponentialScale(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      options: ExponentialScaleOptions = {},
    ): number {
      return applyExponentialScaleImpl(compositorStore, layerId, options);
    },

    // ========================================================================
    // TIME MANIPULATION
    // ========================================================================

    timeStretchLayer(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      options: TimeStretchOptions,
    ): void {
      timeStretchLayerImpl(compositorStore, layerId, options);
    },

    reverseLayer(compositorStore: CompositorStoreAccess, layerId: string): void {
      reverseLayerImpl(compositorStore, layerId);
    },

    freezeFrameAtPlayhead(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): void {
      freezeFrameAtPlayheadImpl(compositorStore, layerId);
    },

    splitLayerAtPlayhead(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): Layer | null {
      return splitLayerAtPlayheadImpl(compositorStore, layerId);
    },

    enableSpeedMap(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      fps?: number,
    ): void {
      enableSpeedMapImpl(compositorStore, layerId, fps);
    },

    disableSpeedMap(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): void {
      disableSpeedMapImpl(compositorStore, layerId);
    },

    toggleSpeedMap(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      fps?: number,
    ): boolean {
      return toggleSpeedMapImpl(compositorStore, layerId, fps);
    },

    // ========================================================================
    // UTILITY METHODS
    // ========================================================================

    getLayerById(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): Layer | null {
      return getLayerByIdImpl(compositorStore, layerId);
    },

    getLayerChildren(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): Layer[] {
      return getLayerChildrenImpl(compositorStore, layerId);
    },

    getLayerDescendants(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): Layer[] {
      return getLayerDescendantsImpl(compositorStore, layerId);
    },

    getVisibleLayers(compositorStore: CompositorStoreAccess): Layer[] {
      return getVisibleLayersImpl(compositorStore);
    },

    getDisplayedLayers(
      compositorStore: CompositorStoreAccess,
      hideMinimized = false,
    ): Layer[] {
      return getDisplayedLayersImpl(compositorStore, hideMinimized);
    },

    getRootLayers(compositorStore: CompositorStoreAccess): Layer[] {
      return getRootLayersImpl(compositorStore);
    },

    getCameraLayers(compositorStore: CompositorStoreAccess): Layer[] {
      return getCameraLayersImpl(compositorStore);
    },

    getSelectedLayers(compositorStore: CompositorStoreAccess): Layer[] {
      return getSelectedLayersImpl(compositorStore);
    },

    getSelectedLayer(compositorStore: CompositorStoreAccess): Layer | null {
      return getSelectedLayerImpl(compositorStore);
    },

    // ========================================================================
    // SPLINE OPERATIONS
    // ========================================================================

    addSplineControlPoint(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      point: SplineControlPoint,
    ): void {
      addSplineControlPointImpl(compositorStore, layerId, point);
    },

    insertSplineControlPoint(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      point: SplineControlPoint,
      index: number,
    ): void {
      insertSplineControlPointImpl(compositorStore, layerId, point, index);
    },

    updateSplineControlPoint(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
      updates: Partial<SplineControlPoint>,
    ): void {
      updateSplineControlPointImpl(compositorStore, layerId, pointId, updates);
    },

    deleteSplineControlPoint(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
    ): void {
      deleteSplineControlPointImpl(compositorStore, layerId, pointId);
    },

    enableSplineAnimation(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): void {
      enableSplineAnimationImpl(compositorStore, layerId);
    },

    addSplinePointKeyframe(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
      property:
        | "x"
        | "y"
        | "depth"
        | "handleIn.x"
        | "handleIn.y"
        | "handleOut.x"
        | "handleOut.y",
      frame: number,
    ): void {
      addSplinePointKeyframeImpl(compositorStore, layerId, pointId, property, frame);
    },

    addSplinePointPositionKeyframe(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
      frame: number,
    ): void {
      addSplinePointPositionKeyframeImpl(compositorStore, layerId, pointId, frame);
    },

    updateSplinePointWithKeyframe(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
      x: number,
      y: number,
      frame: number,
      addKeyframe: boolean = false,
    ): void {
      updateSplinePointWithKeyframeImpl(
        compositorStore,
        layerId,
        pointId,
        x,
        y,
        frame,
        addKeyframe,
      );
    },

    getEvaluatedSplinePoints(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      frame: number,
    ): EvaluatedControlPoint[] {
      return getEvaluatedSplinePointsImpl(compositorStore, layerId, frame);
    },

    isSplineAnimated(
      compositorStore: CompositorStoreAccess,
      layerId: string,
    ): boolean {
      return isSplineAnimatedImpl(compositorStore, layerId);
    },

    hasSplinePointKeyframes(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      pointId: string,
    ): boolean {
      return hasSplinePointKeyframesImpl(compositorStore, layerId, pointId);
    },

    simplifySpline(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      tolerance: number,
    ): void {
      simplifySplineImpl(compositorStore, layerId, tolerance);
    },

    smoothSplineHandles(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      amount: number,
    ): void {
      smoothSplineHandlesImpl(compositorStore, layerId, amount);
    },

    // ========================================================================
    // TEXT CONVERSION
    // ========================================================================

    async convertTextLayerToSplines(
      compositorStore: CompositorStoreAccess,
      layerId: string,
      options: ConvertTextToSplinesOptions = {},
    ): Promise<string[] | null> {
      return convertTextLayerToSplinesImpl(compositorStore, layerId, options);
    },

    // ========================================================================
    // PATH OPERATIONS
    // ========================================================================

    copyPathToPosition(
      compositorStore: CompositorStoreAccess,
      sourceSplineLayerId: string,
      targetLayerId: string,
      options: CopyPathToPositionOptions = {},
    ): number | null {
      return copyPathToPositionImpl(
        compositorStore,
        sourceSplineLayerId,
        targetLayerId,
        options,
      );
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type LayerStoreType = ReturnType<typeof useLayerStore>;
