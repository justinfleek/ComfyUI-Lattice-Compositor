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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // module // imports
// ═══════════════════════════════════════════════════════════════════════════

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
  DeleteLayerOptions,
  SequenceLayersOptions,
  ExponentialScaleOptions,
  TimeStretchOptions,
  LayerSourceReplacement,
} from "./types";
import type { AssetReference, Layer, ClipboardKeyframe, LayerDataUnion, EvaluatedControlPoint, NestedCompData } from "@/types/project";
import type { VideoImportResult } from "@/stores/videoStore";
import type { SplineControlPoint } from "./spline";
import type { ConvertTextToSplinesOptions } from "./textConversion";
import type { CopyPathToPositionOptions } from "./pathOperations";

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // store // definition
// ═══════════════════════════════════════════════════════════════════════════

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
    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // clipboard // state
    // ═══════════════════════════════════════════════════════════════════════════

    setClipboard(layers: Layer[], keyframes: ClipboardKeyframe[] = []): void {
      setClipboardImpl(this.$state, layers, keyframes);
    },

    clearClipboard(): void {
      clearClipboardImpl(this.$state);
    },

    getClipboardLayers(): Layer[] {
      return getClipboardLayersImpl(this.$state);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                            // layer // crud
    // ═══════════════════════════════════════════════════════════════════════════

    createLayer(
      type: Layer["type"],
      name?: string,
    ): Layer {
      return createLayerImpl(type, name);
    },

    deleteLayer(
      layerId: string,
      options?: DeleteLayerOptions,
    ): void {
      deleteLayerImpl(layerId, options);
    },

    updateLayer(
      layerId: string,
      updates: Partial<Layer>,
    ): void {
      updateLayerImpl(layerId, updates);
    },

    updateLayerData(
      layerId: string,
      dataUpdates: Partial<LayerDataUnion & { physics?: import("@/types/physics").PhysicsLayerData }>,
    ): void {
      updateLayerDataImpl(layerId, dataUpdates);
    },

    duplicateLayer(
      layerId: string,
    ): Layer | null {
      return duplicateLayerImpl(layerId);
    },

    moveLayer(
      layerId: string,
      newIndex: number,
    ): void {
      moveLayerImpl(layerId, newIndex);
    },

    renameLayer(
      layerId: string,
      newName: string,
    ): void {
      renameLayerImpl(layerId, newName);
    },

    updateLayerTransform(
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
      updateLayerTransformImpl(layerId, updates);
    },

    toggleLayerLock(): void {
      toggleLayerLockImpl();
    },

    toggleLayerVisibility(): void {
      toggleLayerVisibilityImpl();
    },

    toggleLayerSolo(): void {
      toggleLayerSoloImpl();
    },

    bringToFront(): void {
      bringToFrontImpl();
    },

    sendToBack(): void {
      sendToBackImpl();
    },

    bringForward(): void {
      bringForwardImpl();
    },

    sendBackward(): void {
      sendBackwardImpl();
    },

    /** @internal Used by clipboard operations */
    _regenerateKeyframeIds(layer: Layer): void {
      regenerateKeyframeIds(layer);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                  // clipboard // operations
    // ═══════════════════════════════════════════════════════════════════════════

    copySelectedLayers(): void {
      copySelectedLayersImpl(this.$state);
    },

    pasteLayers(): Layer[] {
      return pasteLayersImpl(this.$state);
    },

    cutSelectedLayers(): void {
      cutSelectedLayersImpl(this.$state);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                                // hierarchy
    // ═══════════════════════════════════════════════════════════════════════════

    setLayerParent(
      layerId: string,
      parentId: string | null,
    ): void {
      setLayerParentImpl(layerId, parentId);
    },

    toggleLayer3D(layerId: string): void {
      toggleLayer3DImpl(layerId);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                     // selection // helpers
    // ═══════════════════════════════════════════════════════════════════════════

    selectLayer(
      layerId: string,
      addToSelection = false,
    ): void {
      selectLayerImpl(layerId, addToSelection);
    },

    deselectLayer(layerId: string): void {
      deselectLayerImpl(layerId);
    },

    clearSelection(): void {
      clearSelectionImpl();
    },

    selectAllLayers(): void {
      selectAllLayersImpl();
    },

    deleteSelectedLayers(): void {
      deleteSelectedLayersImpl();
    },

    duplicateSelectedLayers(): string[] {
      return duplicateSelectedLayersImpl();
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                         // specialized // layer // creation
    // ═══════════════════════════════════════════════════════════════════════════

    createTextLayer(
      text: string = "Text",
    ): Layer {
      return createTextLayerImpl(text);
    },

    createSplineLayer(): Layer {
      return createSplineLayerImpl();
    },

    createShapeLayer(
      name: string = "Shape Layer",
    ): Layer {
      return createShapeLayerImpl(name);
    },

    /**
     * Create a camera layer
     * Creates both the camera object and the layer, managing camera state
     */
    createCameraLayer(
      name?: string,
    ): Layer {
      return createCameraLayerImpl(name);
    },

    /**
     * Create a video layer from a file
     * Delegates to videoStore for metadata extraction and asset management
     */
    async createVideoLayer(
      file: File,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
      return createVideoLayerImpl(file, autoResizeComposition);
    },

    /**
     * Create a nested comp layer referencing another composition
     */
    createNestedCompLayer(
      compositionId: string,
      name?: string,
    ): Layer {
      return createNestedCompLayerImpl(compositionId, name);
    },

    /**
     * Update nested comp layer data
     */
    updateNestedCompLayerData(
      layerId: string,
      updates: Partial<NestedCompData>,
    ): void {
      updateNestedCompLayerDataImpl(layerId, updates);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                    // source // replacement
    // ═══════════════════════════════════════════════════════════════════════════

    replaceLayerSource(
      layerId: string,
      newSource: LayerSourceReplacement,
    ): void {
      replaceLayerSourceImpl(layerId, newSource);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                      // batch // operations
    // ═══════════════════════════════════════════════════════════════════════════

    sequenceLayers(
      layerIds: string[],
      options: SequenceLayersOptions = {},
    ): number {
      return sequenceLayersImpl(layerIds, options);
    },

    applyExponentialScale(
      layerId: string,
      options: ExponentialScaleOptions = {},
    ): number {
      return applyExponentialScaleImpl(layerId, options);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                     // time // manipulation
    // ═══════════════════════════════════════════════════════════════════════════

    timeStretchLayer(
      layerId: string,
      options: TimeStretchOptions,
    ): void {
      timeStretchLayerImpl(layerId, options);
    },

    reverseLayer(layerId: string): void {
      reverseLayerImpl(layerId);
    },

    freezeFrameAtPlayhead(
      layerId: string,
    ): void {
      freezeFrameAtPlayheadImpl(layerId);
    },

    splitLayerAtPlayhead(
      layerId: string,
    ): Layer | null {
      return splitLayerAtPlayheadImpl(layerId);
    },

    enableSpeedMap(
      layerId: string,
      fps?: number,
    ): void {
      enableSpeedMapImpl(layerId, fps);
    },

    disableSpeedMap(
      layerId: string,
    ): void {
      disableSpeedMapImpl(layerId);
    },

    toggleSpeedMap(
      layerId: string,
      fps?: number,
    ): boolean {
      return toggleSpeedMapImpl(layerId, fps);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // utility // methods
    // ═══════════════════════════════════════════════════════════════════════════

    getLayerById(
      layerId: string,
    ): Layer | null {
      return getLayerByIdImpl(layerId);
    },

    getLayerChildren(
      layerId: string,
    ): Layer[] {
      return getLayerChildrenImpl(layerId);
    },

    getLayerDescendants(
      layerId: string,
    ): Layer[] {
      return getLayerDescendantsImpl(layerId);
    },

    getVisibleLayers(): Layer[] {
      return getVisibleLayersImpl();
    },

    getDisplayedLayers(
      hideMinimized = false,
    ): Layer[] {
      return getDisplayedLayersImpl(hideMinimized);
    },

    getRootLayers(): Layer[] {
      return getRootLayersImpl();
    },

    getCameraLayers(): Layer[] {
      return getCameraLayersImpl();
    },

    getSelectedLayers(): Layer[] {
      return getSelectedLayersImpl();
    },

    getSelectedLayer(): Layer | null {
      return getSelectedLayerImpl();
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                     // spline // operations
    // ═══════════════════════════════════════════════════════════════════════════

    addSplineControlPoint(
      layerId: string,
      point: SplineControlPoint,
    ): void {
      addSplineControlPointImpl(layerId, point);
    },

    insertSplineControlPoint(
      layerId: string,
      point: SplineControlPoint,
      index: number,
    ): void {
      insertSplineControlPointImpl(layerId, point, index);
    },

    updateSplineControlPoint(
      layerId: string,
      pointId: string,
      updates: Partial<SplineControlPoint>,
    ): void {
      updateSplineControlPointImpl(layerId, pointId, updates);
    },

    deleteSplineControlPoint(
      layerId: string,
      pointId: string,
    ): void {
      deleteSplineControlPointImpl(layerId, pointId);
    },

    enableSplineAnimation(
      layerId: string,
    ): void {
      enableSplineAnimationImpl(layerId);
    },

    addSplinePointKeyframe(
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
      addSplinePointKeyframeImpl(layerId, pointId, property, frame);
    },

    addSplinePointPositionKeyframe(
      layerId: string,
      pointId: string,
      frame: number,
    ): void {
      addSplinePointPositionKeyframeImpl(layerId, pointId, frame);
    },

    updateSplinePointWithKeyframe(
      layerId: string,
      pointId: string,
      x: number,
      y: number,
      frame: number,
      addKeyframe: boolean = false,
    ): void {
      updateSplinePointWithKeyframeImpl(
        layerId,
        pointId,
        x,
        y,
        frame,
        addKeyframe,
      );
    },

    getEvaluatedSplinePoints(
      layerId: string,
      frame: number,
    ): EvaluatedControlPoint[] {
      return getEvaluatedSplinePointsImpl(layerId, frame);
    },

    isSplineAnimated(
      layerId: string,
    ): boolean {
      return isSplineAnimatedImpl(layerId);
    },

    hasSplinePointKeyframes(
      layerId: string,
      pointId: string,
    ): boolean {
      return hasSplinePointKeyframesImpl(layerId, pointId);
    },

    simplifySpline(
      layerId: string,
      tolerance: number,
    ): void {
      simplifySplineImpl(layerId, tolerance);
    },

    smoothSplineHandles(
      layerId: string,
      amount: number,
    ): void {
      smoothSplineHandlesImpl(layerId, amount);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // text // conversion
    // ═══════════════════════════════════════════════════════════════════════════

    async convertTextLayerToSplines(
      layerId: string,
      options: ConvertTextToSplinesOptions = {},
    ): Promise<string[] | null> {
      return convertTextLayerToSplinesImpl(layerId, options);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // path // operations
    // ═══════════════════════════════════════════════════════════════════════════

    copyPathToPosition(
      sourceSplineLayerId: string,
      targetLayerId: string,
      options: CopyPathToPositionOptions = {},
    ): number | null {
      return copyPathToPositionImpl(
        sourceSplineLayerId,
        targetLayerId,
        options,
      );
    },
  },
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // type // exports
// ═══════════════════════════════════════════════════════════════════════════

export type LayerStoreType = ReturnType<typeof useLayerStore>;
