/**
 * Main Compositor Store
 *
 * Manages project state, layers, playback, and ComfyUI communication.
 *
 * ARCHITECTURAL NOTE - Time Authority:
 * ====================================
 * This store maintains `currentFrame` as UI STATE ONLY.
 * The store does NOT evaluate frame state - that responsibility belongs
 * to MotionEngine.
 *
 * The correct data flow is:
 *   1. UI sets `currentFrame` via setFrame(), play(), nextFrame(), etc.
 *   2. Components call `motionEngine.evaluate(currentFrame, project)` to get FrameState
 *   3. FrameState is passed to renderer via `engine.applyFrameState()`
 *
 * This store should NEVER:
 *   - Call interpolateProperty() for rendering purposes
 *   - Mutate layer state during playback
 *   - Be the source of truth for evaluated values
 */
import { defineStore } from 'pinia';
import { motionEngine } from '@/engine/MotionEngine';
import type { FrameState } from '@/engine/MotionEngine';
import { particleSimulationRegistry } from '@/engine/ParticleSimulationController';
import type { ParticleSnapshot } from '@/engine/ParticleSimulationController';
import { storeLogger } from '@/utils/logger';
import type {
  LatticeProject,
  Layer,
  Composition,
  CompositionSettings,
  AssetReference,
  AnimatableProperty,
  Keyframe,
  BezierHandle,
  TextData,
  SplineData,
  ParticleLayerData,
  DepthflowLayerData,
  ParticleEmitterConfig,
  AudioParticleMapping,
  CameraLayerData,
  ImageLayerData,
  VideoData,
  NestedCompData,
  InterpolationType,
  PropertyValue,
  ClipboardKeyframe,
  AnyLayerData
} from '@/types/project';
import type { VideoMetadata } from '@/engine/layers/VideoLayer';
import { extractVideoMetadata, calculateCompositionFromVideo } from '@/engine/layers/VideoLayer';
import type { Camera3D, CameraKeyframe, ViewportState, ViewOptions } from '@/types/camera';
import { createDefaultCamera, createDefaultViewportState, createDefaultViewOptions } from '@/types/camera';
import { interpolateCameraAtFrame } from '@/services/export/cameraExportFormats';
import type { AudioAnalysis, PeakData, PeakDetectionConfig } from '@/services/audioFeatures';
import { getFeatureAtFrame, detectPeaks, isBeatAtFrame } from '@/services/audioFeatures';
import { loadAndAnalyzeAudio, cancelAnalysis } from '@/services/audioWorkerClient';
import { createEmptyProject, createDefaultTransform, createAnimatableProperty } from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';
import { markLayerDirty } from '@/services/layerEvaluationCache';
import type { AudioMapping, TargetParameter } from '@/services/audioReactiveMapping';
import { AudioReactiveMapper } from '@/services/audioReactiveMapping';
import { AudioPathAnimator, type PathAnimatorConfig } from '@/services/audioPathAnimator';
// Effect creation delegated to effectActions
import {
  PropertyDriverSystem,
  type PropertyDriver,
  type PropertyPath,
  createPropertyDriver,
  createAudioDriver,
  createPropertyLink
} from '@/services/propertyDriver';
import {
  type SnapConfig,
  type SnapResult,
  findNearestSnap,
  DEFAULT_SNAP_CONFIG,
  getBeatFrames,
  getPeakFrames
} from '@/services/timelineSnap';
import { type SegmentationPoint } from '@/services/segmentation';
import { type CacheStats } from '@/services/frameCache';
// Extracted action modules
import * as layerActions from './actions/layerActions';
import * as playbackActions from './actions/playbackActions';
import type { LayerSourceReplacement } from './actions/layerActions';
import * as keyframeActions from './actions/keyframeActions';
import * as projectActions from './actions/projectActions';
import * as audioActions from './actions/audioActions';
import * as propertyDriverActions from './actions/propertyDriverActions';
import * as cacheActions from './actions/cacheActions';
import * as cameraActions from './actions/cameraActions';
import * as segmentationActions from './actions/segmentationActions';
import * as effectActions from './actions/effectActions';
import * as compositionActions from './actions/compositionActions';
import * as particleLayerActions from './actions/particleLayerActions';
import * as depthflowActions from './actions/depthflowActions';
import * as videoActions from './actions/videoActions';
import type { VideoImportResult } from './actions/videoActions';
import * as textAnimatorActions from './actions/textAnimatorActions';
import * as markerActions from './actions/markerActions';

// Domain-specific stores (for delegation)
import { usePlaybackStore } from './playbackStore';
import { useAudioStore } from './audioStore';
import { useSelectionStore } from './selectionStore';

interface CompositorState {
  // Project data
  project: LatticeProject;

  // Active composition (for multi-composition support)
  activeCompositionId: string;
  openCompositionIds: string[];  // Tabs - which comps are open
  compositionBreadcrumbs: string[];  // Navigation history for nested compositions

  // ComfyUI connection
  comfyuiNodeId: string | null;

  // Input data from ComfyUI
  sourceImage: string | null;
  depthMap: string | null;

  // Playback state (delegated to playbackStore, kept here for backwards compat)
  isPlaying: boolean;

  // Selection state is now in selectionStore (accessed via getters)
  // Tool 'segment' is compositor-specific, handled separately
  segmentToolActive: boolean;

  // Segmentation state
  segmentMode: 'point' | 'box';
  segmentPendingMask: {
    mask: string;
    bounds: { x: number; y: number; width: number; height: number };
    area: number;
    score: number;
  } | null;
  segmentBoxStart: { x: number; y: number } | null;
  segmentIsLoading: boolean;

  // Shape tool options
  shapeToolOptions: {
    fromCenter: boolean;
    constrain: boolean;
    polygonSides: number;
    starPoints: number;
    starInnerRadius: number;
  };

  // UI state
  curveEditorVisible: boolean;
  hideMinimizedLayers: boolean;  // Toggle to hide layers marked as minimized

  // History for undo/redo
  historyStack: LatticeProject[];
  historyIndex: number;

  // Audio state
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;
  audioVolume: number;  // 0-100
  audioMuted: boolean;

  // Audio loading state (for Web Worker progress)
  audioLoadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  audioLoadingProgress: number;  // 0-1
  audioLoadingPhase: string;     // Human-readable phase name
  audioLoadingError: string | null;

  // Audio-particle mappings (legacy)
  audioMappings: Map<string, AudioParticleMapping[]>;

  // New audio reactive system
  peakData: PeakData | null;
  audioReactiveMappings: AudioMapping[];
  audioReactiveMapper: AudioReactiveMapper | null;
  pathAnimators: Map<string, AudioPathAnimator>;

  // Camera system
  cameras: Map<string, Camera3D>;           // All cameras by ID
  cameraKeyframes: Map<string, CameraKeyframe[]>; // Keyframes per camera
  activeCameraId: string | null;            // Which camera is currently active
  viewportState: ViewportState;             // Multi-view layout state
  viewOptions: ViewOptions;                 // Display options (wireframes, etc.)

  // Property driver system (expressions/links)
  propertyDriverSystem: PropertyDriverSystem | null;
  propertyDrivers: PropertyDriver[];        // Serializable driver configs

  // Timeline snapping
  snapConfig: SnapConfig;

  // Clipboard for copy/paste
  clipboard: {
    layers: Layer[];
    keyframes: ClipboardKeyframe[];
  };

  // Autosave state
  autosaveEnabled: boolean;
  autosaveIntervalMs: number;
  autosaveTimerId: number | null;
  lastSaveTime: number | null;
  lastSaveProjectId: string | null;
  hasUnsavedChanges: boolean;

  // Frame cache state
  frameCacheEnabled: boolean;
  projectStateHash: string;

  // Timeline UI state
  timelineZoom: number;
  selectedAssetId: string | null;
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => {
    // Create initial project and pre-populate history with it
    // This ensures undo works for the very first action
    const initialProject = createEmptyProject(1280, 720);  // 720p HD default
    return {
      project: initialProject,
      activeCompositionId: 'main',
      openCompositionIds: ['main'],
      compositionBreadcrumbs: ['main'],  // Start with main comp in breadcrumb path
      comfyuiNodeId: null,
      sourceImage: null,
      depthMap: null,
      isPlaying: false,
      segmentToolActive: false,
      segmentMode: 'point',
      segmentPendingMask: null,
      segmentBoxStart: null,
      segmentIsLoading: false,
      shapeToolOptions: {
        fromCenter: false,
        constrain: false,
        polygonSides: 6,
        starPoints: 5,
        starInnerRadius: 0.5,
      },
      curveEditorVisible: false,
      hideMinimizedLayers: false,
      // Initialize history with initial project state so first action can be undone
      historyStack: [structuredClone(initialProject)],
      historyIndex: 0,
    audioBuffer: null,
    audioAnalysis: null,
    audioFile: null,
    audioVolume: 100,
    audioMuted: false,
    audioLoadingState: 'idle',
    audioLoadingProgress: 0,
    audioLoadingPhase: '',
    audioLoadingError: null,
    audioMappings: new Map(),
    peakData: null,
    audioReactiveMappings: [],
    audioReactiveMapper: null,
    pathAnimators: new Map(),

    // Camera system
    cameras: new Map(),
    cameraKeyframes: new Map(),
    activeCameraId: null,
    viewportState: createDefaultViewportState(),
    viewOptions: createDefaultViewOptions(),

    // Property driver system
    propertyDriverSystem: null,
    propertyDrivers: [],

    // Timeline snapping
    snapConfig: { ...DEFAULT_SNAP_CONFIG },

    // Clipboard
    clipboard: {
      layers: [],
      keyframes: []
    },

    // Autosave (enabled by default, every 60 seconds)
    autosaveEnabled: true,
    autosaveIntervalMs: 60000,
    autosaveTimerId: null,
    lastSaveTime: null,
    lastSaveProjectId: null,
    hasUnsavedChanges: false,

    // Frame cache (enabled by default)
    frameCacheEnabled: true,
    projectStateHash: '',

    // Timeline UI state
    timelineZoom: 1,
    selectedAssetId: null
    };
  },

  getters: {
    // Active composition helper
    activeComposition: (state): Composition | null => {
      return state.project.compositions[state.activeCompositionId] || null;
    },

    // Project info - now uses active composition
    hasProject: (state): boolean => state.sourceImage !== null,
    width(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.width || 1024;
    },
    height(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.height || 1024;
    },
    frameCount(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.frameCount || 81;
    },
    fps(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.fps || 16;
    },
    duration(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.duration || 5;
    },
    backgroundColor(state): string {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.settings.backgroundColor || '#050505';
    },

    // Current frame - per composition
    currentFrame(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.currentFrame || 0;
    },
    currentTime(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      if (!comp) return 0;
      return comp.currentFrame / comp.settings.fps;
    },

    // Layers - from active composition
    layers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.layers || [];
    },
    visibleLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      return (comp?.layers || []).filter((l: Layer) => l.visible);
    },
    // Layers displayed in timeline (respects minimized filter)
    displayedLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      const allLayers = comp?.layers || [];
      if (state.hideMinimizedLayers) {
        return allLayers.filter((l: Layer) => !l.minimized);
      }
      return allLayers;
    },

    // Selection (delegated to selectionStore)
    selectedLayerIds(): string[] {
      return useSelectionStore().selectedLayerIds;
    },
    selectedKeyframeIds(): string[] {
      return useSelectionStore().selectedKeyframeIds;
    },
    selectedPropertyPath(): string | null {
      return useSelectionStore().selectedPropertyPath;
    },
    currentTool(state): 'select' | 'pen' | 'text' | 'hand' | 'zoom' | 'segment' {
      if (state.segmentToolActive) return 'segment';
      return useSelectionStore().currentTool;
    },
    selectedLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      const selectionStore = useSelectionStore();
      return (comp?.layers || []).filter((l: Layer) => selectionStore.selectedLayerIds.includes(l.id));
    },
    selectedLayer(state): Layer | null {
      const selectionStore = useSelectionStore();
      if (selectionStore.selectedLayerIds.length !== 1) return null;
      const comp = state.project.compositions[state.activeCompositionId];
      return (comp?.layers || []).find((l: Layer) => l.id === selectionStore.selectedLayerIds[0]) || null;
    },

    // All compositions for tabs
    allCompositions: (state): Composition[] => {
      return Object.values(state.project.compositions);
    },
    openCompositions(state): Composition[] {
      return state.openCompositionIds
        .map((id: string) => state.project.compositions[id])
        .filter(Boolean);
    },

    // Breadcrumb navigation path for nested compositions
    breadcrumbPath(state): Array<{ id: string; name: string }> {
      return state.compositionBreadcrumbs
        .map((id: string) => {
          const comp = state.project.compositions[id];
          return comp ? { id, name: comp.name } : null;
        })
        .filter(Boolean) as Array<{ id: string; name: string }>;
    },

    // Assets
    assets: (state): Record<string, AssetReference> => state.project.assets,

    // History
    canUndo: (state): boolean => state.historyIndex > 0,
    canRedo: (state): boolean => state.historyIndex < state.historyStack.length - 1,

    // Camera
    activeCamera: (state): Camera3D | null => {
      if (!state.activeCameraId) return null;
      return state.cameras.get(state.activeCameraId) || null;
    },
    allCameras: (state): Camera3D[] => Array.from(state.cameras.values()),
    cameraLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      return (comp?.layers || []).filter((l: Layer) => l.type === 'camera');
    }
  },

  actions: {
    // ============================================================
    // HELPER METHODS
    // ============================================================

    /**
     * Get the layers array for the active composition (mutable reference)
     */
    getActiveCompLayers(): Layer[] {
      const comp = this.project.compositions[this.activeCompositionId];
      return comp?.layers || [];
    },

    /**
     * Get the active composition (mutable reference)
     */
    getActiveComp(): Composition | null {
      return this.project.compositions[this.activeCompositionId] || null;
    },
    // ============================================================
    // COMPOSITION MANAGEMENT (delegated to compositionActions)
    // ============================================================

    createComposition(
      name: string,
      settings?: Partial<CompositionSettings>,
      isNestedComp: boolean = false
    ): Composition {
      return compositionActions.createComposition(this, name, settings, isNestedComp);
    },

    deleteComposition(compId: string): boolean {
      return compositionActions.deleteComposition(this, compId);
    },

    switchComposition(compId: string): void {
      compositionActions.switchComposition(this, compId);
    },

    closeCompositionTab(compId: string): void {
      compositionActions.closeCompositionTab(this, compId);
    },

    enterNestedComp(compId: string): void {
      compositionActions.enterNestedComp(this, compId);
    },

    navigateBack(): void {
      compositionActions.navigateBack(this);
    },

    navigateToBreadcrumb(index: number): void {
      compositionActions.navigateToBreadcrumb(this, index);
    },

    resetBreadcrumbs(): void {
      compositionActions.resetBreadcrumbs(this);
    },

    renameComposition(compId: string, newName: string): void {
      compositionActions.renameComposition(this, compId, newName);
    },

    updateCompositionSettings(compId: string, settings: Partial<CompositionSettings>): void {
      compositionActions.updateCompositionSettings(this, compId, settings);
    },

    getComposition(compId: string): Composition | null {
      return compositionActions.getComposition(this, compId);
    },

    enableFrameBlending(compId: string): void {
      compositionActions.enableFrameBlending(this, compId);
    },

    disableFrameBlending(compId: string): void {
      compositionActions.disableFrameBlending(this, compId);
    },

    toggleFrameBlending(compId: string): void {
      compositionActions.toggleFrameBlending(this, compId);
    },

    nestSelectedLayers(name?: string): Composition | null {
      return compositionActions.nestSelectedLayers(this, name);
    },

    // ============================================================
    // COMFYUI INTEGRATION
    // ============================================================

    /**
     * Load inputs from ComfyUI node
     */
    loadInputs(inputs: {
      node_id: string;
      source_image: string;
      depth_map: string;
      width: number;
      height: number;
      frame_count: number;
    }): void {
      this.comfyuiNodeId = inputs.node_id;
      this.sourceImage = inputs.source_image;
      this.depthMap = inputs.depth_map;

      // Update active composition
      const comp = this.project.compositions[this.activeCompositionId];
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      // Update composition settings
      comp.settings.width = inputs.width;
      comp.settings.height = inputs.height;
      comp.settings.frameCount = inputs.frame_count;
      comp.settings.duration = inputs.frame_count / comp.settings.fps;

      // Keep legacy alias in sync
      this.project.composition.width = inputs.width;
      this.project.composition.height = inputs.height;
      this.project.composition.frameCount = inputs.frame_count;
      this.project.composition.duration = inputs.frame_count / this.project.composition.fps;

      // Extend layer outPoints if frameCount increased
      if (inputs.frame_count > oldFrameCount) {
        for (const layer of comp.layers) {
          if (layer.outPoint === oldFrameCount - 1) {
            layer.outPoint = inputs.frame_count - 1;
          }
        }
      }

      // Store as assets
      if (inputs.source_image) {
        this.project.assets['source_image'] = {
          id: 'source_image',
          type: 'image',
          source: 'comfyui_node',
          nodeId: inputs.node_id,
          width: inputs.width,
          height: inputs.height,
          data: inputs.source_image
        };
      }

      if (inputs.depth_map) {
        this.project.assets['depth_map'] = {
          id: 'depth_map',
          type: 'depth_map',
          source: 'comfyui_node',
          nodeId: inputs.node_id,
          width: inputs.width,
          height: inputs.height,
          data: inputs.depth_map
        };
      }

      if (comp) comp.currentFrame = 0;
      this.project.meta.modified = new Date().toISOString();

      storeLogger.debug('Loaded inputs from ComfyUI:', {
        width: inputs.width,
        height: inputs.height,
        frameCount: inputs.frame_count
      });

      // Save initial state to history
      this.pushHistory();
    },

    /**
     * Create a new layer
     */
    createLayer(type: Layer['type'], name?: string): Layer {
      return layerActions.createLayer(this, type, name);
    },

    /**
     * Alias for createLayer - used by keyboard shortcuts
     */
    addLayer(type: Layer['type'], name?: string): Layer {
      return layerActions.createLayer(this, type, name);
    },

    /**
     * Get a layer by ID
     */
    getLayerById(layerId: string): Layer | null {
      return layerActions.getLayerById(this, layerId);
    },

    /**
     * Delete a layer
     */
    deleteLayer(layerId: string): void {
      layerActions.deleteLayer(this, layerId);
    },

    /**
     * Duplicate a layer
     */
    duplicateLayer(layerId: string): Layer | null {
      return layerActions.duplicateLayer(this, layerId);
    },

    /**
     * Copy selected layers to clipboard
     */
    copySelectedLayers(): void {
      layerActions.copySelectedLayers(this);
    },

    /**
     * Paste layers from clipboard
     */
    pasteLayers(): Layer[] {
      return layerActions.pasteLayers(this);
    },

    /**
     * Cut selected layers (copy + delete)
     */
    cutSelectedLayers(): void {
      layerActions.cutSelectedLayers(this);
    },

    /**
     * Select all layers in the active composition
     */
    selectAllLayers(): void {
      const layers = this.getActiveCompLayers();
      const selection = useSelectionStore();
      selection.selectLayers(layers.map(l => l.id));
    },

    /**
     * Delete all selected layers
     */
    deleteSelectedLayers(): void {
      const selection = useSelectionStore();
      const layerIds = [...selection.selectedLayerIds];
      layerIds.forEach(id => this.deleteLayer(id));
      selection.clearLayerSelection();
    },

    /**
     * Duplicate all selected layers
     */
    duplicateSelectedLayers(): void {
      const selection = useSelectionStore();
      const newLayerIds: string[] = [];
      selection.selectedLayerIds.forEach(id => {
        const newLayer = layerActions.duplicateLayer(this, id);
        if (newLayer) {
          newLayerIds.push(newLayer.id);
        }
      });
      // Select the duplicated layers
      if (newLayerIds.length > 0) {
        selection.selectLayers(newLayerIds);
      }
    },

    /**
     * Update layer properties
     */
    updateLayer(layerId: string, updates: Partial<Layer>): void {
      layerActions.updateLayer(this, layerId, updates);
    },

    /**
     * Update layer-specific data (e.g., text content, image path, etc.)
     * Accepts both common AnyLayerData properties and layer-type-specific properties.
     */
    updateLayerData(layerId: string, dataUpdates: Partial<AnyLayerData> & Record<string, unknown>): void {
      layerActions.updateLayerData(this, layerId, dataUpdates);
    },

    /**
     * Add a control point to a spline layer
     */
    addSplineControlPoint(layerId: string, point: layerActions.SplineControlPoint): void {
      layerActions.addSplineControlPoint(this, layerId, point);
    },

    /**
     * Insert a control point at a specific index in a spline layer
     */
    insertSplineControlPoint(layerId: string, point: layerActions.SplineControlPoint, index: number): void {
      layerActions.insertSplineControlPoint(this, layerId, point, index);
    },

    /**
     * Update a spline control point
     */
    updateSplineControlPoint(layerId: string, pointId: string, updates: Partial<layerActions.SplineControlPoint>): void {
      layerActions.updateSplineControlPoint(this, layerId, pointId, updates);
    },

    /**
     * Delete a spline control point
     */
    deleteSplineControlPoint(layerId: string, pointId: string): void {
      layerActions.deleteSplineControlPoint(this, layerId, pointId);
    },

    /**
     * Enable animation mode on a spline layer (converts to keyframeable control points)
     */
    enableSplineAnimation(layerId: string): void {
      layerActions.enableSplineAnimation(this, layerId);
    },

    /**
     * Add keyframe to a spline control point property
     */
    addSplinePointKeyframe(
      layerId: string,
      pointId: string,
      property: 'x' | 'y' | 'depth' | 'handleIn.x' | 'handleIn.y' | 'handleOut.x' | 'handleOut.y',
      frame: number
    ): void {
      layerActions.addSplinePointKeyframe(this, layerId, pointId, property, frame);
    },

    /**
     * Add keyframes to all position properties of a control point
     */
    addSplinePointPositionKeyframe(layerId: string, pointId: string, frame: number): void {
      layerActions.addSplinePointPositionKeyframe(this, layerId, pointId, frame);
    },

    /**
     * Update spline control point with optional keyframe
     */
    updateSplinePointWithKeyframe(
      layerId: string,
      pointId: string,
      x: number,
      y: number,
      frame: number,
      addKeyframe: boolean = false
    ): void {
      layerActions.updateSplinePointWithKeyframe(this, layerId, pointId, x, y, frame, addKeyframe);
    },

    /**
     * Get evaluated control points at a specific frame
     */
    getEvaluatedSplinePoints(layerId: string, frame: number): import('@/types/project').EvaluatedControlPoint[] {
      return layerActions.getEvaluatedSplinePoints(this, layerId, frame);
    },

    /**
     * Check if spline has animation enabled
     */
    isSplineAnimated(layerId: string): boolean {
      return layerActions.isSplineAnimated(this, layerId);
    },

    /**
     * Check if a control point has any keyframes
     */
    hasSplinePointKeyframes(layerId: string, pointId: string): boolean {
      return layerActions.hasSplinePointKeyframes(this, layerId, pointId);
    },

    /**
     * Simplify a spline by reducing control points (Douglas-Peucker)
     * @param tolerance - Distance threshold in pixels (higher = more simplification)
     */
    simplifySpline(layerId: string, tolerance: number): void {
      layerActions.simplifySpline(this, layerId, tolerance);
    },

    /**
     * Smooth spline handles to create smoother curves
     * @param amount - Smoothing amount 0-100 (100 = fully smooth)
     */
    smoothSplineHandles(layerId: string, amount: number): void {
      layerActions.smoothSplineHandles(this, layerId, amount);
    },

    /**
     * Copy a path from a spline layer and paste it as position keyframes on a target layer.
     * This creates a motion path where the layer follows the spline's shape over time.
     *
     * @param sourceSplineLayerId - The spline layer to copy the path from
     * @param targetLayerId - The layer to apply position keyframes to
     * @param options - Configuration options
     * @returns Number of keyframes created, or null if failed
     */
    copyPathToPosition(
      sourceSplineLayerId: string,
      targetLayerId: string,
      options?: {
        useFullDuration?: boolean;
        startFrame?: number;
        endFrame?: number;
        keyframeCount?: number;
        interpolation?: 'linear' | 'bezier' | 'hold';
        useSpatialTangents?: boolean;
        reversed?: boolean;
      }
    ): number | null {
      return layerActions.copyPathToPosition(this, sourceSplineLayerId, targetLayerId, options);
    },

    /**
     * Toggle 3D mode for a layer
     */
    toggleLayer3D(layerId: string): void {
      layerActions.toggleLayer3D(this, layerId);
    },

    /**
     * Reorder layers
     */
    moveLayer(layerId: string, newIndex: number): void {
      layerActions.moveLayer(this, layerId, newIndex);
    },

    /**
     * Replace layer source with a new asset (Alt+drag replacement)
     * Keeps all keyframes, effects, and transforms
     */
    replaceLayerSource(layerId: string, newSource: LayerSourceReplacement): void {
      layerActions.replaceLayerSource(this, layerId, newSource);
    },

    /**
     * Selection
     */
    selectLayer(layerId: string, addToSelection = false): void {
      layerActions.selectLayer(this, layerId, addToSelection);
    },

    deselectLayer(layerId: string): void {
      layerActions.deselectLayer(this, layerId);
    },

    /**
     * Set a layer's parent for parenting/hierarchy
     */
    setLayerParent(layerId: string, parentId: string | null): void {
      layerActions.setLayerParent(this, layerId, parentId);
    },

    // ============================================================
    // TIME MANIPULATION
    // ============================================================

    /**
     * Apply time stretch to a video or nested comp layer
     * @param layerId - Target layer ID
     * @param options - Time stretch options including stretchFactor, holdInPlace, reverse
     */
    timeStretchLayer(layerId: string, options: layerActions.TimeStretchOptions): void {
      layerActions.timeStretchLayer(this, layerId, options);
    },

    /**
     * Reverse layer playback by negating speed
     * @param layerId - Target layer ID
     */
    reverseLayer(layerId: string): void {
      layerActions.reverseLayer(this, layerId);
    },

    /**
     * Create freeze frame at current playhead
     * Uses speedMap with hold keyframes
     * @param layerId - Target layer ID
     */
    freezeFrameAtPlayhead(layerId: string): void {
      const comp = this.getActiveComp();
      const storeWithFrame = {
        ...this,
        currentFrame: comp?.currentFrame ?? 0,
        fps: comp?.settings.fps ?? 30,
        // Explicitly bind pushHistory to preserve 'this' context
        pushHistory: this.pushHistory.bind(this)
      };
      layerActions.freezeFrameAtPlayhead(storeWithFrame, layerId);
    },

    /**
     * Split layer at current playhead
     * Creates two layers: one ending at playhead, one starting at playhead
     * @param layerId - Target layer ID
     * @returns The new layer created after the split point
     */
    splitLayerAtPlayhead(layerId: string): Layer | null {
      const comp = this.getActiveComp();
      const storeWithFrame = {
        ...this,
        currentFrame: comp?.currentFrame ?? 0,
        // Explicitly bind pushHistory to preserve 'this' context
        pushHistory: this.pushHistory.bind(this)
      };
      return layerActions.splitLayerAtPlayhead(storeWithFrame, layerId);
    },

    clearSelection(): void {
      const selection = useSelectionStore();
      selection.clearAll();
    },

    /**
     * Select a property path for graph editor focus
     */
    selectProperty(propertyPath: string | null): void {
      useSelectionStore().setSelectedPropertyPath(propertyPath);
    },

    // ============================================================
    // MOTION ENGINE INTEGRATION
    // ============================================================

    /**
     * Get evaluated FrameState for the current frame
     *
     * This is the CANONICAL way to get evaluated state for rendering.
     * Uses MotionEngine.evaluate() which is PURE and deterministic.
     *
     * @param frame - Optional frame override (defaults to currentFrame)
     * @returns Immutable FrameState snapshot
     */
    getFrameState(frame?: number): FrameState {
      const comp = this.getActiveComp();
      const targetFrame = frame ?? (comp?.currentFrame ?? 0);

      // Get audio reactive data from audioStore
      const audioStore = useAudioStore();
      const audioReactive = audioStore.audioAnalysis && audioStore.reactiveMappings.length > 0
        ? {
            analysis: audioStore.audioAnalysis,
            mappings: audioStore.reactiveMappings
          }
        : null;

      return motionEngine.evaluate(
        targetFrame,
        this.project,
        this.audioAnalysis,
        this.activeCameraId,
        true, // useCache
        audioReactive
      );
    },

    // ============================================================
    // PLAYBACK CONTROLS (delegated to playbackActions)
    // ============================================================

    play(): void {
      playbackActions.play(this);
    },

    pause(): void {
      playbackActions.pause(this);
    },

    togglePlayback(): void {
      playbackActions.togglePlayback(this);
    },

    setFrame(frame: number): void {
      playbackActions.setFrame(this, frame);
    },

    nextFrame(): void {
      playbackActions.nextFrame(this);
    },

    prevFrame(): void {
      playbackActions.prevFrame(this);
    },

    goToStart(): void {
      playbackActions.goToStart(this);
    },

    goToEnd(): void {
      playbackActions.goToEnd(this);
    },

    jumpFrames(n: number): void {
      playbackActions.jumpFrames(this, n);
    },

    /**
     * Tool selection
     */
    setTool(tool: 'select' | 'pen' | 'text' | 'hand' | 'zoom' | 'segment'): void {
      if (tool === 'segment') {
        // Segment tool is compositor-specific
        this.segmentToolActive = true;
      } else {
        // Regular tools are handled by selectionStore
        this.segmentToolActive = false;
        useSelectionStore().setTool(tool);
        this.clearSegmentPendingMask();
      }
    },

    /**
     * Set segmentation mode (point or box)
     */
    setSegmentMode(mode: 'point' | 'box'): void {
      this.segmentMode = mode;
      this.clearSegmentPendingMask();
    },

    /**
     * Clear pending segmentation mask
     */
    clearSegmentPendingMask(): void {
      this.segmentPendingMask = null;
      this.segmentBoxStart = null;
    },

    /**
     * Set pending segmentation mask (preview before creating layer)
     */
    setSegmentPendingMask(mask: CompositorState['segmentPendingMask']): void {
      this.segmentPendingMask = mask;
    },

    /**
     * Set box selection start point
     */
    setSegmentBoxStart(point: { x: number; y: number } | null): void {
      this.segmentBoxStart = point;
    },

    /**
     * Set segmentation loading state
     */
    setSegmentLoading(loading: boolean): void {
      this.segmentIsLoading = loading;
    },

    /**
     * Confirm pending mask and create layer from it
     */
    async confirmSegmentMask(layerName?: string): Promise<Layer | null> {
      if (!this.segmentPendingMask || !this.sourceImage) {
        return null;
      }

      const layer = await segmentationActions.createLayerFromMask(
        this,
        this.sourceImage,
        this.segmentPendingMask,
        layerName,
        false
      );

      // Clear pending mask after creating layer
      this.clearSegmentPendingMask();

      return layer;
    },

    /**
     * Set shape tool options (from toolbar)
     */
    setShapeToolOptions(options: CompositorState['shapeToolOptions']): void {
      this.shapeToolOptions = { ...options };
    },

    /**
     * History management
     */
    pushHistory(): void {
      projectActions.pushHistory(this);
    },

    undo(): void {
      projectActions.undo(this);
    },

    redo(): void {
      projectActions.redo(this);
    },

    /**
     * Project serialization
     */
    exportProject(): string {
      return projectActions.exportProject(this);
    },

    importProject(json: string): boolean {
      return projectActions.importProject(this, json, () => this.pushHistory());
    },

    /**
     * Load project from a File object (e.g., from file input or drag-drop)
     */
    async loadProjectFromFile(file: File): Promise<boolean> {
      return projectActions.loadProjectFromFile(this, file, () => this.pushHistory());
    },

    /**
     * Save project to server (ComfyUI backend)
     */
    async saveProjectToServer(projectId?: string): Promise<string | null> {
      return projectActions.saveProjectToServer(this, projectId);
    },

    /**
     * Load project from server (ComfyUI backend)
     */
    async loadProjectFromServer(projectId: string): Promise<boolean> {
      return projectActions.loadProjectFromServer(this, projectId, () => this.pushHistory());
    },

    /**
     * List all projects saved on server
     */
    async listServerProjects(): Promise<Array<{ id: string; name: string; modified?: string }>> {
      return projectActions.listServerProjects();
    },

    /**
     * Delete a project from server
     */
    async deleteServerProject(projectId: string): Promise<boolean> {
      return projectActions.deleteServerProject(projectId);
    },

    /**
     * Remove unused assets from the project (Reduce Project)
     * Returns info about removed assets
     */
    removeUnusedAssets(): { removed: number; assetNames: string[] } {
      return projectActions.removeUnusedAssets(this);
    },

    /**
     * Get statistics about asset usage
     */
    getAssetUsageStats(): { total: number; used: number; unused: number; unusedNames: string[] } {
      return projectActions.getAssetUsageStats(this);
    },

    /**
     * Collect Files - Package project and assets into a downloadable ZIP
     * @param includeUnused - Whether to include assets not used by any layer
     */
    async collectFiles(options: { includeUnused?: boolean } = {}): Promise<void> {
      return projectActions.downloadCollectedFiles(this, options);
    },

    /**
     * Toggle curve editor visibility
     */
    toggleCurveEditor(): void {
      this.curveEditorVisible = !this.curveEditorVisible;
    },

    /**
     * Set curve editor visibility directly
     */
    setCurveEditorVisible(visible: boolean): void {
      this.curveEditorVisible = visible;
    },

    /**
     * Toggle hide minimized layers in timeline
     */
    toggleHideMinimizedLayers(): void {
      this.hideMinimizedLayers = !this.hideMinimizedLayers;
    },

    /** @deprecated Use toggleHideMinimizedLayers instead */
    toggleHideShyLayers(): void {
      this.toggleHideMinimizedLayers();
    },

    /**
     * Set hide minimized layers state
     */
    setHideMinimizedLayers(hide: boolean): void {
      this.hideMinimizedLayers = hide;
    },

    /** @deprecated Use setHideMinimizedLayers instead */
    setHideShyLayers(hide: boolean): void {
      this.setHideMinimizedLayers(hide);
    },

    /**
     * Get interpolated value for any animatable property at current frame
     * BUG-040/041 FIX: Pass fps and duration from composition settings
     */
    getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
      const comp = this.getActiveComp();
      const frame = comp?.currentFrame ?? 0;
      const fps = this.fps;
      const duration = comp ? comp.settings.frameCount / comp.settings.fps : undefined;
      return interpolateProperty(property, frame, fps, '', duration);
    },

    /**
     * Add a keyframe to a property
     */
    addKeyframe<T>(
      layerId: string,
      propertyName: string,
      value: T,
      atFrame?: number
    ): Keyframe<T> | null {
      return keyframeActions.addKeyframe(this, layerId, propertyName, value, atFrame);
    },

    /**
     * Remove a keyframe
     */
    removeKeyframe(layerId: string, propertyName: string, keyframeId: string): void {
      keyframeActions.removeKeyframe(this, layerId, propertyName, keyframeId);
    },

    /**
     * Set a property's value (for direct editing in timeline)
     */
    setPropertyValue(layerId: string, propertyPath: string, value: PropertyValue): void {
      keyframeActions.setPropertyValue(this, layerId, propertyPath, value);
    },

    /**
     * Update an entire property including keyframes (for batch operations)
     */
    updateLayerProperty(layerId: string, propertyPath: string, propertyData: Partial<AnimatableProperty<any>>): boolean {
      return keyframeActions.updateLayerProperty(this, layerId, propertyPath, propertyData);
    },

    /**
     * Set a property's animated state
     */
    setPropertyAnimated(layerId: string, propertyPath: string, animated: boolean): void {
      keyframeActions.setPropertyAnimated(this, layerId, propertyPath, animated, () => {
        this.addKeyframe(layerId, propertyPath, keyframeActions.findPropertyByPath(
          this.getActiveCompLayers().find(l => l.id === layerId)!,
          propertyPath
        )?.value);
      });
    },

    /**
     * Move a keyframe to a new frame
     */
    moveKeyframe(layerId: string, propertyPath: string, keyframeId: string, newFrame: number): void {
      keyframeActions.moveKeyframe(this, layerId, propertyPath, keyframeId, newFrame);
    },

    /**
     * Set keyframe value (for graph editor numeric input)
     */
    setKeyframeValue(layerId: string, propertyPath: string, keyframeId: string, newValue: number): void {
      keyframeActions.setKeyframeValue(this, layerId, propertyPath, keyframeId, newValue);
    },

    /**
     * Set keyframe interpolation type
     */
    setKeyframeInterpolation(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      interpolation: InterpolationType
    ): void {
      keyframeActions.setKeyframeInterpolation(this, layerId, propertyPath, keyframeId, interpolation);
    },

    /**
     * Apply easing preset to multiple keyframes at once
     * @param keyframeSelections Array of keyframe selections with layerId, propertyPath, keyframeId
     * @param interpolation The interpolation type to apply
     * @returns Number of keyframes updated
     */
    applyEasingPresetToKeyframes(
      keyframeSelections: Array<{ layerId: string; propertyPath: string; keyframeId: string }>,
      interpolation: InterpolationType
    ): number {
      let count = 0;
      for (const sel of keyframeSelections) {
        keyframeActions.setKeyframeInterpolation(this, sel.layerId, sel.propertyPath, sel.keyframeId, interpolation);
        count++;
      }
      return count;
    },

    /**
     * Update keyframe frame position and/or value
     */
    updateKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      updates: { frame?: number; value?: PropertyValue }
    ): void {
      keyframeActions.updateKeyframe(this, layerId, propertyPath, keyframeId, updates);
    },

    /**
     * Set keyframe bezier handle
     */
    setKeyframeHandle(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: 'in' | 'out',
      handle: BezierHandle
    ): void {
      keyframeActions.setKeyframeHandle(this, layerId, propertyPath, keyframeId, handleType, handle);
    },

    /**
     * Update both keyframe handles at once (convenience method for easing presets)
     */
    updateKeyframeHandles(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handles: { inHandle?: { x: number; y: number }; outHandle?: { x: number; y: number } }
    ): void {
      if (handles.inHandle) {
        keyframeActions.setKeyframeHandle(this, layerId, propertyPath, keyframeId, 'in', {
          frame: handles.inHandle.x * 10, // Convert normalized x to frame offset
          value: handles.inHandle.y * 100, // Convert normalized y to value offset
          enabled: true
        });
      }
      if (handles.outHandle) {
        keyframeActions.setKeyframeHandle(this, layerId, propertyPath, keyframeId, 'out', {
          frame: handles.outHandle.x * 10,
          value: handles.outHandle.y * 100,
          enabled: true
        });
      }
    },

    /**
     * Set keyframe control mode (smooth, corner, symmetric)
     */
    setKeyframeControlMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      controlMode: 'smooth' | 'corner' | 'symmetric'
    ): void {
      keyframeActions.setKeyframeControlMode(this, layerId, propertyPath, keyframeId, controlMode);
    },

    /**
     * Insert a keyframe on the motion path at the current frame
     * Uses interpolated values from existing keyframes
     * @returns The created keyframe ID or null if failed
     */
    insertKeyframeOnPath(layerId: string, frame: number): string | null {
      return keyframeActions.insertKeyframeOnPath(this, layerId, frame);
    },

    /**
     * Set keyframe handle with control mode awareness (supports breaking handles)
     * @param breakHandle - If true, sets controlMode to 'corner' (Ctrl+drag behavior)
     */
    setKeyframeHandleWithMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: 'in' | 'out',
      handle: BezierHandle,
      breakHandle: boolean = false
    ): void {
      keyframeActions.setKeyframeHandleWithMode(this, layerId, propertyPath, keyframeId, handleType, handle, breakHandle);
    },

    /**
     * Auto-calculate bezier tangents for a single keyframe
     */
    autoCalculateBezierTangents(
      layerId: string,
      propertyPath: string,
      keyframeId: string
    ): boolean {
      return keyframeActions.autoCalculateBezierTangents(this, layerId, propertyPath, keyframeId);
    },

    /**
     * Auto-calculate bezier tangents for ALL keyframes on a property
     */
    autoCalculateAllBezierTangents(
      layerId: string,
      propertyPath: string
    ): number {
      return keyframeActions.autoCalculateAllBezierTangents(this, layerId, propertyPath);
    },

    /**
     * Separate position into individual X, Y, Z properties for independent keyframing.
     */
    separatePositionDimensions(layerId: string): boolean {
      return keyframeActions.separatePositionDimensionsAction(this, layerId);
    },

    /**
     * Link position dimensions back into a combined property.
     */
    linkPositionDimensions(layerId: string): boolean {
      return keyframeActions.linkPositionDimensionsAction(this, layerId);
    },

    /**
     * Separate scale into individual X, Y, Z properties.
     */
    separateScaleDimensions(layerId: string): boolean {
      return keyframeActions.separateScaleDimensionsAction(this, layerId);
    },

    /**
     * Link scale dimensions back into a combined property.
     */
    linkScaleDimensions(layerId: string): boolean {
      return keyframeActions.linkScaleDimensionsAction(this, layerId);
    },

    /**
     * Check if position dimensions are separated.
     */
    hasPositionSeparated(layerId: string): boolean {
      return keyframeActions.hasPositionSeparated(this, layerId);
    },

    /**
     * Check if scale dimensions are separated.
     */
    hasScaleSeparated(layerId: string): boolean {
      return keyframeActions.hasScaleSeparated(this, layerId);
    },

    /**
     * Sequence layers - arrange selected layers one after another.
     * @param layerIds - Array of layer IDs to sequence (in order)
     * @param options - Sequence options (gap, startFrame, reverse)
     */
    sequenceLayers(layerIds: string[], options?: layerActions.SequenceLayersOptions): number {
      return layerActions.sequenceLayers(this, layerIds, options);
    },

    /**
     * Apply exponential scale animation to a layer.
     * Creates keyframes with exponential curve for natural zoom effect.
     */
    applyExponentialScale(layerId: string, options?: layerActions.ExponentialScaleOptions): number {
      return layerActions.applyExponentialScale(this, layerId, options);
    },

    /**
     * Create a text layer with proper data structure
     */
    createTextLayer(text: string = 'Text'): Layer {
      return layerActions.createTextLayer(this, text);
    },

    /**
     * Create a spline layer with proper data structure
     */
    createSplineLayer(): Layer {
      return layerActions.createSplineLayer(this);
    },

    /**
     * Create a shape layer with proper data structure
     */
    createShapeLayer(name: string = 'Shape Layer'): Layer {
      return layerActions.createShapeLayer(this, name);
    },

    /**
     * Rename a layer by ID
     */
    renameLayer(layerId: string, newName: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (layer) {
        layer.name = newName;
        this.pushHistory();
      }
    },

    // ============================================================
    // PARTICLE SYSTEM LAYER ACTIONS (delegated to particleLayerActions)
    // ============================================================

    createParticleLayer(): Layer {
      return particleLayerActions.createParticleLayer(this);
    },

    updateParticleLayerData(layerId: string, updates: Partial<ParticleLayerData>): void {
      particleLayerActions.updateParticleLayerData(this, layerId, updates);
    },

    addParticleEmitter(layerId: string, config: ParticleEmitterConfig): void {
      particleLayerActions.addParticleEmitter(this, layerId, config);
    },

    updateParticleEmitter(layerId: string, emitterId: string, updates: Partial<ParticleEmitterConfig>): void {
      particleLayerActions.updateParticleEmitter(this, layerId, emitterId, updates);
    },

    removeParticleEmitter(layerId: string, emitterId: string): void {
      particleLayerActions.removeParticleEmitter(this, layerId, emitterId);
    },

    // ============================================================
    // DEPTHFLOW LAYER ACTIONS (delegated to depthflowActions)
    // ============================================================

    createDepthflowLayer(sourceLayerId: string = '', depthLayerId: string = ''): Layer {
      return depthflowActions.createDepthflowLayer(this, sourceLayerId, depthLayerId);
    },

    updateDepthflowConfig(layerId: string, updates: Partial<DepthflowLayerData['config']>): void {
      depthflowActions.updateDepthflowConfig(this, layerId, updates);
    },

    // ============================================================
    // VIDEO LAYER ACTIONS (delegated to videoActions)
    // ============================================================

    async createVideoLayer(file: File, autoResizeComposition: boolean = true): Promise<VideoImportResult> {
      return videoActions.createVideoLayer(this, file, autoResizeComposition);
    },

    updateVideoLayerData(layerId: string, updates: Partial<VideoData>): void {
      videoActions.updateVideoLayerData(this, layerId, updates);
    },

    onVideoMetadataLoaded(layerId: string, metadata: VideoMetadata): void {
      videoActions.onVideoMetadataLoaded(this, layerId, metadata);
    },

    resizeComposition(width: number, height: number, frameCount?: number): void {
      videoActions.resizeComposition(this, width, height, frameCount);
    },

    // NESTED COMP LAYER ACTIONS
    // ============================================================

    /**
     * Create a nested comp layer referencing another composition
     */
    createNestedCompLayer(compositionId: string, name?: string): Layer {
      const layer = this.createLayer('nestedComp', name || 'Nested Comp');

      const nestedCompData: NestedCompData = {
        compositionId,
        // Speed map (new naming)
        speedMapEnabled: false,
        speedMap: undefined,
        // Backwards compatibility
        timeRemapEnabled: false,
        timeRemap: undefined,
        flattenTransform: false,
        overrideFrameRate: false,
        frameRate: undefined
      };

      layer.data = nestedCompData;

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      return layer;
    },

    /**
     * Update nested comp layer data
     */
    updateNestedCompLayerData(layerId: string, updates: Partial<NestedCompData>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'nestedComp') return;

      const data = layer.data as NestedCompData;
      Object.assign(data, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    // ============================================================
    // SEGMENTATION ACTIONS (delegated to segmentationActions)
    // ============================================================

    async segmentToLayerByPoint(
      point: SegmentationPoint,
      options: { model?: 'sam2' | 'matseg'; layerName?: string; positionAtCenter?: boolean } = {}
    ): Promise<Layer | null> {
      return segmentationActions.segmentToLayerByPoint(this, point, options);
    },
    async segmentToLayerByBox(
      box: [number, number, number, number],
      options: { model?: 'sam2' | 'matseg'; layerName?: string; positionAtCenter?: boolean } = {}
    ): Promise<Layer | null> {
      return segmentationActions.segmentToLayerByBox(this, box, options);
    },
    async segmentToLayerByMultiplePoints(
      foregroundPoints: SegmentationPoint[],
      backgroundPoints: SegmentationPoint[] = [],
      options: { model?: 'sam2' | 'matseg'; layerName?: string; positionAtCenter?: boolean } = {}
    ): Promise<Layer | null> {
      return segmentationActions.segmentToLayerByMultiplePoints(this, foregroundPoints, backgroundPoints, options);
    },
    async autoSegmentToLayers(
      options: { model?: 'sam2' | 'matseg'; minArea?: number; maxMasks?: number; namePrefix?: string } = {}
    ): Promise<Layer[]> {
      return segmentationActions.autoSegmentToLayers(this, options);
    },

    // ============================================================
    // EFFECT ACTIONS (delegated to effectActions)
    // ============================================================

    addEffectToLayer(layerId: string, effectKey: string): void {
      effectActions.addEffectToLayer(this, layerId, effectKey);
    },
    removeEffectFromLayer(layerId: string, effectId: string): void {
      effectActions.removeEffectFromLayer(this, layerId, effectId);
    },
    updateEffectParameter(layerId: string, effectId: string, paramKey: string, value: PropertyValue): void {
      effectActions.updateEffectParameter(this, layerId, effectId, paramKey, value);
    },
    setEffectParamAnimated(layerId: string, effectId: string, paramKey: string, animated: boolean): void {
      effectActions.setEffectParamAnimated(this, layerId, effectId, paramKey, animated);
    },
    toggleEffect(layerId: string, effectId: string): void {
      effectActions.toggleEffect(this, layerId, effectId);
    },
    reorderEffects(layerId: string, fromIndex: number, toIndex: number): void {
      effectActions.reorderEffects(this, layerId, fromIndex, toIndex);
    },
    getEffectParameterValue(layerId: string, effectId: string, paramKey: string, frame?: number): PropertyValue | undefined {
      return effectActions.getEffectParameterValue(this, layerId, effectId, paramKey, frame);
    },

    // ============================================================
    // TEXT ANIMATOR ACTIONS (Tutorial 06)
    // ============================================================

    addTextAnimator(layerId: string, config: textAnimatorActions.AddTextAnimatorConfig = {}) {
      return textAnimatorActions.addTextAnimator(this, layerId, config);
    },
    removeTextAnimator(layerId: string, animatorId: string): boolean {
      return textAnimatorActions.removeTextAnimator(this, layerId, animatorId);
    },
    updateTextAnimator(layerId: string, animatorId: string, updates: Partial<import('@/types/text').TextAnimator>): boolean {
      return textAnimatorActions.updateTextAnimator(this, layerId, animatorId, updates);
    },
    getTextAnimator(layerId: string, animatorId: string) {
      return textAnimatorActions.getTextAnimator(this, layerId, animatorId);
    },
    getTextAnimators(layerId: string) {
      return textAnimatorActions.getTextAnimators(this, layerId);
    },
    configureRangeSelector(layerId: string, animatorId: string, config: textAnimatorActions.RangeSelectorConfig): boolean {
      return textAnimatorActions.configureRangeSelector(this, layerId, animatorId, config);
    },
    configureExpressionSelector(layerId: string, animatorId: string, config: textAnimatorActions.ExpressionSelectorConfig): boolean {
      return textAnimatorActions.configureExpressionSelector(this, layerId, animatorId, config);
    },
    removeExpressionSelector(layerId: string, animatorId: string): boolean {
      return textAnimatorActions.removeExpressionSelector(this, layerId, animatorId);
    },
    configureWigglySelector(layerId: string, animatorId: string, config: textAnimatorActions.WigglySelectorConfig): boolean {
      return textAnimatorActions.configureWigglySelector(this, layerId, animatorId, config);
    },
    removeWigglySelector(layerId: string, animatorId: string): boolean {
      return textAnimatorActions.removeWigglySelector(this, layerId, animatorId);
    },
    getCharacterTransforms(layerId: string, frame: number): textAnimatorActions.CharacterTransform[] {
      return textAnimatorActions.getCharacterTransforms(this, layerId, frame);
    },
    getSelectionValues(layerId: string, animatorId: string, frame: number): number[] {
      return textAnimatorActions.getSelectionValues(this, layerId, animatorId, frame);
    },
    getRangeSelectionValue(layerId: string, animatorId: string, charIndex: number, frame: number): number {
      return textAnimatorActions.getRangeSelectionValue(this, layerId, animatorId, charIndex, frame);
    },
    setAnimatorPropertyValue(layerId: string, animatorId: string, propertyName: string, value: any): boolean {
      return textAnimatorActions.setAnimatorPropertyValue(this, layerId, animatorId, propertyName as any, value);
    },
    hasTextAnimators(layerId: string): boolean {
      return textAnimatorActions.hasTextAnimators(this, layerId);
    },
    getTextContent(layerId: string): string {
      return textAnimatorActions.getTextContent(this, layerId);
    },
    setTextContent(layerId: string, text: string): boolean {
      return textAnimatorActions.setTextContent(this, layerId, text);
    },

    // TEXT ON PATH ACTIONS (Tutorial 06: Section 7)
    setTextPath(layerId: string, config: textAnimatorActions.TextPathConfig): boolean {
      return textAnimatorActions.setTextPath(this, layerId, config);
    },
    getTextPathConfig(layerId: string) {
      return textAnimatorActions.getTextPathConfig(this, layerId);
    },
    updateTextPath(layerId: string, updates: Partial<textAnimatorActions.TextPathConfig>): boolean {
      return textAnimatorActions.updateTextPath(this, layerId, updates);
    },
    getCharacterPathPlacements(layerId: string, frame: number) {
      return textAnimatorActions.getCharacterPathPlacements(this, layerId, frame);
    },
    getPathLength(layerId: string): number {
      return textAnimatorActions.getPathLength(this, layerId);
    },
    hasTextPath(layerId: string): boolean {
      return textAnimatorActions.hasTextPath(this, layerId);
    },
    clearTextPath(layerId: string): boolean {
      return textAnimatorActions.clearTextPath(this, layerId);
    },

    // ============================================================
    // CAMERA ACTIONS (delegated to cameraActions module)
    // ============================================================

    createCameraLayer(name?: string): { camera: Camera3D; layer: Layer } {
      return cameraActions.createCameraLayer(this, name);
    },
    getCamera(cameraId: string): Camera3D | null {
      return cameraActions.getCamera(this, cameraId);
    },
    updateCamera(cameraId: string, updates: Partial<Camera3D>): void {
      cameraActions.updateCamera(this, cameraId, updates);
    },
    setActiveCamera(cameraId: string): void {
      cameraActions.setActiveCamera(this, cameraId);
    },
    deleteCamera(cameraId: string): void {
      cameraActions.deleteCamera(this, cameraId);
    },
    getCameraKeyframes(cameraId: string): CameraKeyframe[] {
      return cameraActions.getCameraKeyframes(this, cameraId);
    },
    addCameraKeyframe(cameraId: string, keyframe: CameraKeyframe): void {
      cameraActions.addCameraKeyframe(this, cameraId, keyframe);
    },
    removeCameraKeyframe(cameraId: string, frame: number): void {
      cameraActions.removeCameraKeyframe(this, cameraId, frame);
    },
    getCameraAtFrame(cameraId: string, frame: number): Camera3D | null {
      return cameraActions.getCameraAtFrame(this, cameraId, frame);
    },
    getActiveCameraAtFrame(frame?: number): Camera3D | null {
      return cameraActions.getActiveCameraAtFrame(this, frame);
    },
    updateViewportState(updates: Partial<ViewportState>): void {
      cameraActions.updateViewportState(this, updates);
    },
    updateViewOptions(updates: Partial<ViewOptions>): void {
      cameraActions.updateViewOptions(this, updates);
    },

    // ============================================================
    // AUDIO ACTIONS (delegated to audioActions module)
    // ============================================================

    async loadAudio(file: File): Promise<void> {
      return audioActions.loadAudio(this, file);
    },
    cancelAudioLoad(): void {
      audioActions.cancelAudioLoad(this);
    },
    clearAudio(): void {
      audioActions.clearAudio(this);
    },
    setAudioVolume(volume: number): void {
      this.audioVolume = Math.max(0, Math.min(100, volume));
    },
    setAudioMuted(muted: boolean): void {
      this.audioMuted = muted;
    },
    toggleAudioMute(): void {
      this.audioMuted = !this.audioMuted;
    },
    getAudioFeatureAtFrame(feature: string, frame?: number): number {
      return audioActions.getAudioFeatureAtFrame(this, feature, frame);
    },
    applyAudioToParticles(layerId: string, mapping: AudioParticleMapping): void {
      audioActions.applyAudioToParticles(this, layerId, mapping);
    },
    removeLegacyAudioMapping(layerId: string, index: number): void {
      audioActions.removeLegacyAudioMapping(this, layerId, index);
    },
    getAudioMappingsForLayer(layerId: string): AudioParticleMapping[] {
      return audioActions.getAudioMappingsForLayer(this, layerId);
    },
    setPeakData(peakData: PeakData): void {
      audioActions.setPeakData(this, peakData);
    },
    detectAudioPeaks(config: PeakDetectionConfig): PeakData | null {
      return audioActions.detectAudioPeaks(this, config);
    },
    addAudioMapping(mapping: AudioMapping): void {
      audioActions.addAudioMapping(this, mapping);
    },
    removeAudioMapping(mappingId: string): void {
      audioActions.removeAudioMapping(this, mappingId);
    },
    updateAudioMapping(mappingId: string, updates: Partial<AudioMapping>): void {
      audioActions.updateAudioMapping(this, mappingId, updates);
    },
    getAudioMappings(): AudioMapping[] {
      return this.audioReactiveMappings;
    },
    getMappedValueAtFrame(mappingId: string, frame: number): number {
      return audioActions.getMappedValueAtFrame(this, mappingId, frame);
    },
    getAllMappedValuesAtFrame(frame?: number): Map<TargetParameter, number> {
      return audioActions.getAllMappedValuesAtFrame(this, frame);
    },
    getActiveMappingsForLayer(layerId: string): AudioMapping[] {
      return audioActions.getActiveMappingsForLayer(this, layerId);
    },
    getAudioReactiveValuesForLayer(layerId: string, frame: number): Map<TargetParameter, number> {
      return audioActions.getAudioReactiveValuesForLayer(this, layerId, frame);
    },
    isBeatAtCurrentFrame(): boolean {
      return audioActions.isBeatAtCurrentFrame(this);
    },
    convertAudioToKeyframes(options: { name?: string; amplitudeScale?: number; smoothing?: number } = {}) {
      return audioActions.convertAudioToKeyframes(this, options);
    },
    getAudioAmplitudeAtFrame(channel: 'both' | 'left' | 'right', frame: number): number {
      return audioActions.getAudioAmplitudeAtFrame(this, channel, frame);
    },
    convertFrequencyBandsToKeyframes(options: {
      name?: string;
      scale?: number;
      smoothing?: number;
      bands?: audioActions.FrequencyBandName[];
    } = {}) {
      return audioActions.convertFrequencyBandsToKeyframes(this, options);
    },
    convertAllAudioFeaturesToKeyframes(options: {
      name?: string;
      scale?: number;
      smoothing?: number;
    } = {}) {
      return audioActions.convertAllAudioFeaturesToKeyframes(this, options);
    },
    getFrequencyBandAtFrame(band: audioActions.FrequencyBandName, frame: number): number {
      return audioActions.getFrequencyBandAtFrame(this, band, frame);
    },

    // Timeline snapping (simple inline - no need for delegation)
    findSnapPoint(frame: number, pixelsPerFrame: number, selectedLayerId?: string | null): SnapResult | null {
      return findNearestSnap(frame, this.snapConfig, pixelsPerFrame, {
        layers: this.layers, selectedLayerId,
        currentFrame: (this.getActiveComp()?.currentFrame ?? 0),
        audioAnalysis: this.audioAnalysis, peakData: this.peakData,
      });
    },
    getAudioBeatFrames(): number[] { return getBeatFrames(this.audioAnalysis); },
    getAudioPeakFrames(): number[] { return getPeakFrames(this.peakData); },
    setSnapConfig(config: Partial<SnapConfig>): void { this.snapConfig = { ...this.snapConfig, ...config }; },
    toggleSnapping(): void { this.snapConfig.enabled = !this.snapConfig.enabled; },
    toggleSnapType(type: 'grid' | 'keyframes' | 'beats' | 'peaks' | 'layerBounds' | 'playhead'): void {
      // Type-safe snap toggle mapping
      type BooleanSnapKey = 'snapToGrid' | 'snapToKeyframes' | 'snapToBeats' | 'snapToPeaks' | 'snapToLayerBounds' | 'snapToPlayhead';
      const typeMap: Record<typeof type, BooleanSnapKey> = {
        'grid': 'snapToGrid', 'keyframes': 'snapToKeyframes', 'beats': 'snapToBeats',
        'peaks': 'snapToPeaks', 'layerBounds': 'snapToLayerBounds', 'playhead': 'snapToPlayhead',
      };
      const key = typeMap[type];
      this.snapConfig[key] = !this.snapConfig[key];
    },

    // Path animator (delegated to audioActions module)
    createPathAnimator(layerId: string, config: Partial<PathAnimatorConfig> = {}): void {
      audioActions.createPathAnimator(this, layerId, config);
    },
    setPathAnimatorPath(layerId: string, pathData: string): void {
      audioActions.setPathAnimatorPath(this, layerId, pathData);
    },
    updatePathAnimatorConfig(layerId: string, config: Partial<PathAnimatorConfig>): void {
      audioActions.updatePathAnimatorConfig(this, layerId, config);
    },
    removePathAnimator(layerId: string): void {
      audioActions.removePathAnimator(this, layerId);
    },
    getPathAnimator(layerId: string): AudioPathAnimator | undefined {
      return audioActions.getPathAnimator(this, layerId);
    },
    updatePathAnimators(): void {
      audioActions.updatePathAnimators(this);
    },
    resetPathAnimators(): void {
      audioActions.resetPathAnimators(this);
    },
    initializeAudioReactiveMapper(): void {
      audioActions.initializeAudioReactiveMapper(this);
    },

    // ============================================================
    // TIMELINE MARKERS (delegated to markerActions)
    // ============================================================

    addMarker(marker: Omit<import('@/types/project').Marker, 'id'> & { id?: string }): import('@/types/project').Marker | null {
      return markerActions.addMarker(this, marker);
    },
    removeMarker(markerId: string): boolean {
      return markerActions.removeMarker(this, markerId);
    },
    removeMarkerAtFrame(frame: number): boolean {
      return markerActions.removeMarkerAtFrame(this, frame);
    },
    updateMarker(markerId: string, updates: Partial<Omit<import('@/types/project').Marker, 'id'>>): boolean {
      return markerActions.updateMarker(this, markerId, updates);
    },
    clearMarkers(): void {
      markerActions.clearMarkers(this);
    },
    getMarkers(): import('@/types/project').Marker[] {
      return markerActions.getMarkers(this);
    },
    getMarker(markerId: string): import('@/types/project').Marker | null {
      return markerActions.getMarker(this, markerId);
    },
    getMarkerAtFrame(frame: number): import('@/types/project').Marker | null {
      return markerActions.getMarkerAtFrame(this, frame);
    },
    getMarkersInRange(startFrame: number, endFrame: number): import('@/types/project').Marker[] {
      return markerActions.getMarkersInRange(this, startFrame, endFrame);
    },
    getNextMarker(frame: number): import('@/types/project').Marker | null {
      return markerActions.getNextMarker(this, frame);
    },
    getPreviousMarker(frame: number): import('@/types/project').Marker | null {
      return markerActions.getPreviousMarker(this, frame);
    },
    jumpToNextMarker(): void {
      const nextFrame = markerActions.jumpToNextMarker(this, this.currentFrame);
      if (nextFrame !== null) this.setFrame(nextFrame);
    },
    jumpToPreviousMarker(): void {
      const prevFrame = markerActions.jumpToPreviousMarker(this, this.currentFrame);
      if (prevFrame !== null) this.setFrame(prevFrame);
    },
    addMarkers(markers: Array<Omit<import('@/types/project').Marker, 'id'>>): import('@/types/project').Marker[] {
      return markerActions.addMarkers(this, markers);
    },
    removeMarkersByColor(color: string): number {
      return markerActions.removeMarkersByColor(this, color);
    },

    // ============================================================
    // PROPERTY DRIVER SYSTEM (delegated to propertyDriverActions)
    // ============================================================

    initializePropertyDriverSystem(): void {
      this.propertyDriverSystem = new PropertyDriverSystem();
      this.propertyDriverSystem.setPropertyGetter((layerId, propertyPath, frame) => {
        return this.getPropertyValueAtFrame(layerId, propertyPath, frame);
      });
      if (this.audioAnalysis) this.propertyDriverSystem.setAudioAnalysis(this.audioAnalysis);
      for (const driver of this.propertyDrivers) this.propertyDriverSystem.addDriver(driver);
    },
    // BUG-040/041 FIX: Pass fps and duration from composition settings
    getPropertyValueAtFrame(layerId: string, propertyPath: PropertyPath, frame: number): number | null {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return null;

      // Get composition context for expressions
      const comp = this.getActiveComp();
      const fps = this.fps;
      const duration = comp ? comp.settings.frameCount / comp.settings.fps : undefined;

      const parts = propertyPath.split('.');
      if (parts[0] === 'transform') {
        const t = layer.transform;
        if (parts[1] === 'position') {
          const p = interpolateProperty(t.position, frame, fps, layerId, duration);
          return parts[2] === 'x' ? p.x : parts[2] === 'y' ? p.y : (p.z ?? 0);
        }
        if (parts[1] === 'anchorPoint' || parts[1] === 'origin') {
          // Use origin (new name) with fallback to anchorPoint
          const originProp = t.origin || t.anchorPoint;
          if (!originProp) return 0;
          const a = interpolateProperty(originProp, frame, fps, layerId, duration);
          return parts[2] === 'x' ? a.x : parts[2] === 'y' ? a.y : (a.z ?? 0);
        }
        if (parts[1] === 'scale') {
          const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
          return parts[2] === 'x' ? s.x : parts[2] === 'y' ? s.y : (s.z ?? 100);
        }
        if (parts[1] === 'rotation') return interpolateProperty(t.rotation, frame, fps, layerId, duration);
        if (parts[1] === 'rotationX' && t.rotationX) return interpolateProperty(t.rotationX, frame, fps, layerId, duration);
        if (parts[1] === 'rotationY' && t.rotationY) return interpolateProperty(t.rotationY, frame, fps, layerId, duration);
        if (parts[1] === 'rotationZ' && t.rotationZ) return interpolateProperty(t.rotationZ, frame, fps, layerId, duration);
      }
      return parts[0] === 'opacity' ? interpolateProperty(layer.opacity, frame, fps, layerId, duration) : null;
    },

    /**
     * Evaluate a property at a specific frame and return the full value
     * Returns the interpolated value as an array for position/scale/origin types,
     * or a single value for scalar types (rotation, opacity)
     *
     * Used by MotionPathOverlay to get full position values for path rendering
     */
    evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): number[] | number | null {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return null;

      // Get composition context for expressions
      const comp = this.getActiveComp();
      const fps = this.fps;
      const duration = comp ? comp.settings.frameCount / comp.settings.fps : undefined;

      // Normalize path
      const normalizedPath = propertyPath.replace(/^transform\./, '');

      // Handle transform properties
      const t = layer.transform;

      if (normalizedPath === 'position' && t.position) {
        const p = interpolateProperty(t.position, frame, fps, layerId, duration);
        return [p.x, p.y, p.z ?? 0];
      }

      if ((normalizedPath === 'anchorPoint' || normalizedPath === 'origin') && (t.origin || t.anchorPoint)) {
        const originProp = t.origin || t.anchorPoint;
        if (!originProp) return null;
        const a = interpolateProperty(originProp, frame, fps, layerId, duration);
        return [a.x, a.y, a.z ?? 0];
      }

      if (normalizedPath === 'scale' && t.scale) {
        const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
        return [s.x, s.y, s.z ?? 100];
      }

      if (normalizedPath === 'rotation' && t.rotation) {
        return interpolateProperty(t.rotation, frame, fps, layerId, duration);
      }

      if (normalizedPath === 'rotationX' && t.rotationX) {
        return interpolateProperty(t.rotationX, frame, fps, layerId, duration);
      }

      if (normalizedPath === 'rotationY' && t.rotationY) {
        return interpolateProperty(t.rotationY, frame, fps, layerId, duration);
      }

      if (normalizedPath === 'rotationZ' && t.rotationZ) {
        return interpolateProperty(t.rotationZ, frame, fps, layerId, duration);
      }

      if (normalizedPath === 'orientation' && t.orientation) {
        const o = interpolateProperty(t.orientation, frame, fps, layerId, duration);
        return [o.x, o.y, o.z ?? 0];
      }

      if (propertyPath === 'opacity' && layer.opacity) {
        return interpolateProperty(layer.opacity, frame, fps, layerId, duration);
      }

      // Check custom properties
      const customProp = layer.properties.find(p => p.name === propertyPath || p.id === propertyPath);
      if (customProp) {
        const value = interpolateProperty(customProp, frame, fps, layerId, duration);
        // If it's a position-like value with x/y, return as array
        if (value && typeof value === 'object' && 'x' in value && 'y' in value) {
          return [(value as any).x, (value as any).y, (value as any).z ?? 0];
        }
        return value;
      }

      return null;
    },

    getDrivenValuesForLayer(layerId: string): Map<PropertyPath, number> {
      return propertyDriverActions.getEvaluatedLayerProperties(this, layerId, this.getActiveComp()?.currentFrame ?? 0);
    },
    addPropertyDriver(driver: PropertyDriver): boolean {
      return propertyDriverActions.addPropertyDriver(this, driver);
    },
    createAudioPropertyDriver(
      targetLayerId: string, targetProperty: PropertyPath,
      audioFeature: 'amplitude' | 'bass' | 'mid' | 'high' | 'rms',
      options: { threshold?: number; scale?: number; offset?: number; smoothing?: number } = {}
    ): PropertyDriver {
      return propertyDriverActions.createAudioPropertyDriver(this, targetLayerId, targetProperty, audioFeature, options);
    },
    createPropertyLink(
      targetLayerId: string, targetProperty: PropertyPath,
      sourceLayerId: string, sourceProperty: PropertyPath,
      options: { scale?: number; offset?: number; blendMode?: 'replace' | 'add' | 'multiply' } = {}
    ): PropertyDriver | null {
      return propertyDriverActions.createPropertyLinkDriver(this, targetLayerId, targetProperty, sourceLayerId, sourceProperty, options);
    },
    removePropertyDriver(driverId: string): void {
      propertyDriverActions.removePropertyDriver(this, driverId);
    },
    updatePropertyDriver(driverId: string, updates: Partial<PropertyDriver>): void {
      propertyDriverActions.updatePropertyDriver(this, driverId, updates);
    },
    getDriversForLayer(layerId: string): PropertyDriver[] {
      return propertyDriverActions.getDriversForLayer(this, layerId);
    },
    togglePropertyDriver(driverId: string): void {
      propertyDriverActions.togglePropertyDriver(this, driverId);
    },

    // ============================================================
    // PARTICLE SIMULATION ACTIONS
    // ============================================================

    /**
     * Reset a particle layer's simulation
     * Called when particle configuration changes
     */
    resetParticleSimulation(layerId: string): void {
      particleSimulationRegistry.resetLayer(layerId);
      storeLogger.debug('Reset particle simulation for layer:', layerId);
    },

    /**
     * Clear all particle simulations
     * Called on project load/new
     */
    clearAllParticleSimulations(): void {
      particleSimulationRegistry.clear();
      storeLogger.debug('Cleared all particle simulations');
    },

    /**
     * Get particle snapshot for a layer at a specific frame
     * Evaluates the frame state to get the deterministic snapshot
     */
    getParticleSnapshot(layerId: string, frame?: number): ParticleSnapshot | null {
      const frameState = this.getFrameState(frame);
      return frameState.particleSnapshots[layerId] ?? null;
    },

    /**
     * Get all particle snapshots from current frame
     */
    getAllParticleSnapshots(frame?: number): Readonly<Record<string, ParticleSnapshot>> {
      const frameState = this.getFrameState(frame);
      return frameState.particleSnapshots;
    },

    // ============================================================
    // AUTOSAVE/PROJECT ACTIONS (delegated to projectActions)
    // ============================================================

    enableAutosave(intervalMs?: number): void {
      projectActions.configureAutosave(this, { enabled: true, intervalMs }, () => this.performAutosave());
    },
    disableAutosave(): void {
      projectActions.stopAutosave(this);
      this.autosaveEnabled = false;
    },
    startAutosaveTimer(): void {
      projectActions.startAutosave(this, () => this.performAutosave());
    },
    stopAutosaveTimer(): void {
      projectActions.stopAutosave(this);
    },
    async performAutosave(): Promise<void> {
      return projectActions.performAutosave(this);
    },
    markUnsavedChanges(): void {
      projectActions.markUnsavedChanges(this);
      this.invalidateFrameCache();
    },
    async saveProjectToBackend(): Promise<string> {
      const result = await projectActions.saveProjectToServer(this);
      if (!result) throw new Error('Save failed');
      return result;
    },
    async loadProjectFromBackend(projectId: string): Promise<void> {
      const success = await projectActions.loadProjectFromServer(this, projectId, () => this.pushHistory());
      if (!success) throw new Error('Load failed');
    },
    async listSavedProjects(): Promise<Array<{ id: string; name: string; modified?: string }>> {
      return projectActions.listServerProjects();
    },

    // ============================================================
    // FRAME CACHE ACTIONS (delegated to cacheActions)
    // ============================================================

    async initializeFrameCache(): Promise<void> {
      return cacheActions.initializeCache(this);
    },
    setFrameCacheEnabled(enabled: boolean): void {
      cacheActions.setFrameCacheEnabled(this, enabled);
    },
    getCachedFrame(frame: number): ImageData | null {
      return cacheActions.getCachedFrame(this, frame);
    },
    async cacheFrame(frame: number, imageData: ImageData): Promise<void> {
      return cacheActions.cacheFrame(this, frame, imageData);
    },
    isFrameCached(frame: number): boolean {
      return cacheActions.isFrameCached(this, frame);
    },
    async startPreCache(currentFrame: number, direction: 'forward' | 'backward' | 'both' = 'both'): Promise<void> {
      return cacheActions.startPreCache(this, currentFrame, direction);
    },
    invalidateFrameCache(): void {
      cacheActions.invalidateFrameCache(this);
    },
    clearFrameCache(): void {
      cacheActions.clearFrameCache();
    },
    getFrameCacheStats(): CacheStats {
      return cacheActions.getFrameCacheStats();
    },
    computeProjectHash(): string {
      return cacheActions.computeProjectHash(this);
    },

    // ============================================================
    // UI STATE ACTIONS (timeline, asset selection)
    // ============================================================

    /**
     * Set timeline zoom level
     */
    setTimelineZoom(zoom: number): void {
      this.timelineZoom = Math.max(0.1, Math.min(10, zoom));
    },

    /**
     * Select an asset by ID
     */
    selectAsset(assetId: string | null): void {
      this.selectedAssetId = assetId;
    },

    /**
     * Select multiple layers (delegates to selectionStore)
     */
    selectLayers(layerIds: string[]): void {
      const selection = useSelectionStore();
      selection.selectLayers(layerIds);
    },

    /**
     * Time reverse keyframes - reverses keyframe timing order
     * @param layerId The layer ID
     * @param propertyPath Optional specific property, otherwise reverses all transform properties
     * @returns Number of keyframes reversed
     */
    timeReverseKeyframes(layerId: string, propertyPath?: string): number {
      return keyframeActions.timeReverseKeyframes(this, layerId, propertyPath);
    },

    /**
     * Apply velocity settings to a keyframe
     */
    applyKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      settings: keyframeActions.VelocitySettings
    ): boolean {
      return keyframeActions.applyKeyframeVelocity(this, layerId, propertyPath, keyframeId, settings);
    },

    /**
     * Get velocity settings from a keyframe
     */
    getKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string
    ): keyframeActions.VelocitySettings | null {
      return keyframeActions.getKeyframeVelocity(this, layerId, propertyPath, keyframeId);
    },

    /**
     * Convert expression to keyframes (bake expression)
     */
    convertExpressionToKeyframes(
      layerId: string,
      propertyPath: string,
      startFrame?: number,
      endFrame?: number,
      sampleRate?: number
    ): number {
      return keyframeActions.convertExpressionToKeyframes(
        this as unknown as keyframeActions.BakeExpressionStore,
        layerId,
        propertyPath,
        startFrame,
        endFrame,
        sampleRate
      );
    },

    /**
     * Check if a property has a bakeable expression
     */
    canBakeExpression(layerId: string, propertyPath: string): boolean {
      return keyframeActions.canBakeExpression(this, layerId, propertyPath);
    },

    /**
     * Get all keyframe frames for a layer across all animated properties
     * @param layerId The layer ID
     * @returns Sorted array of unique frame numbers where keyframes exist
     */
    getAllKeyframeFrames(layerId: string): number[] {
      return keyframeActions.getAllKeyframeFrames(this, layerId);
    },

    /**
     * Jump to the next keyframe (K key behavior)
     * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
     */
    jumpToNextKeyframe(layerId?: string): void {
      const layerIds = layerId
        ? [layerId]
        : useSelectionStore().selectedLayerIds.length > 0
          ? useSelectionStore().selectedLayerIds
          : [];
      const nextFrame = keyframeActions.findNextKeyframeFrame(this, this.currentFrame, layerIds);
      if (nextFrame !== null) {
        this.setFrame(nextFrame);
      }
    },

    /**
     * Jump to the previous keyframe (J key behavior)
     * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
     */
    jumpToPrevKeyframe(layerId?: string): void {
      const layerIds = layerId
        ? [layerId]
        : useSelectionStore().selectedLayerIds.length > 0
          ? useSelectionStore().selectedLayerIds
          : [];
      const prevFrame = keyframeActions.findPrevKeyframeFrame(this, this.currentFrame, layerIds);
      if (prevFrame !== null) {
        this.setFrame(prevFrame);
      }
    },

    /**
     * Copy keyframes to clipboard
     * @param keyframeSelections Array of keyframe selections with layerId, propertyPath, and keyframeId
     * @returns Number of keyframes copied
     */
    copyKeyframes(
      keyframeSelections: Array<{ layerId: string; propertyPath: string; keyframeId: string }>
    ): number {
      return keyframeActions.copyKeyframes(this, keyframeSelections);
    },

    /**
     * Paste keyframes from clipboard to a target layer/property
     * @param targetLayerId Target layer ID to paste to
     * @param targetPropertyPath Optional target property path (uses original if not specified)
     * @returns Array of newly created keyframes
     */
    pasteKeyframes(
      targetLayerId: string,
      targetPropertyPath?: string
    ): Keyframe<any>[] {
      return keyframeActions.pasteKeyframes(this, targetLayerId, targetPropertyPath);
    },

    /**
     * Check if clipboard has keyframes
     */
    hasKeyframesInClipboard(): boolean {
      return keyframeActions.hasKeyframesInClipboard(this);
    },

    // ============================================================
    // EXPRESSION METHODS
    // ============================================================

    /**
     * Set a property expression
     */
    setPropertyExpression(
      layerId: string,
      propertyPath: string,
      expression: import('@/types/animation').PropertyExpression
    ): boolean {
      return keyframeActions.setPropertyExpression(this, layerId, propertyPath, expression);
    },

    /**
     * Enable expression on a property
     */
    enablePropertyExpression(
      layerId: string,
      propertyPath: string,
      expressionName: string = 'custom',
      params: Record<string, number | string | boolean> = {}
    ): boolean {
      return keyframeActions.enablePropertyExpression(this, layerId, propertyPath, expressionName, params);
    },

    /**
     * Disable expression on a property
     */
    disablePropertyExpression(layerId: string, propertyPath: string): boolean {
      return keyframeActions.disablePropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Toggle expression enabled state
     */
    togglePropertyExpression(layerId: string, propertyPath: string): boolean {
      return keyframeActions.togglePropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Remove expression from property
     */
    removePropertyExpression(layerId: string, propertyPath: string): boolean {
      return keyframeActions.removePropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Get expression for a property
     */
    getPropertyExpression(
      layerId: string,
      propertyPath: string
    ): import('@/types/animation').PropertyExpression | undefined {
      return keyframeActions.getPropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Check if property has an expression
     */
    hasPropertyExpression(layerId: string, propertyPath: string): boolean {
      return keyframeActions.hasPropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Update expression parameters
     */
    updateExpressionParams(
      layerId: string,
      propertyPath: string,
      params: Record<string, number | string | boolean>
    ): boolean {
      return keyframeActions.updateExpressionParams(this, layerId, propertyPath, params);
    },

    /**
     * Update layer transform properties (convenience method)
     * Supports both single property updates and batch updates with an object
     * @param layerId The layer ID
     * @param updates Object with transform properties to update (position, scale, rotation, opacity, origin/anchor)
     */
    updateLayerTransform(
      layerId: string,
      updates: {
        position?: { x: number; y: number; z?: number };
        scale?: { x: number; y: number; z?: number };
        rotation?: number;
        opacity?: number;
        origin?: { x: number; y: number; z?: number };
        anchor?: { x: number; y: number; z?: number }; // Alias for origin
      }
    ): void {
      const layer = this.getLayerById(layerId);
      if (!layer?.transform) return;

      if (updates.position !== undefined && layer.transform.position) {
        layer.transform.position.value = updates.position;
      }
      if (updates.scale !== undefined && layer.transform.scale) {
        layer.transform.scale.value = updates.scale;
      }
      if (updates.rotation !== undefined && layer.transform.rotation) {
        layer.transform.rotation.value = updates.rotation;
      }
      if (updates.opacity !== undefined) {
        // Opacity is at layer level (layer.opacity), not transform level
        if (layer.opacity && typeof layer.opacity === 'object' && 'value' in layer.opacity) {
          layer.opacity.value = updates.opacity;
        }
      }
      // Handle origin/anchor (anchor is alias for origin)
      const originUpdate = updates.origin ?? updates.anchor;
      if (originUpdate !== undefined && layer.transform.origin) {
        layer.transform.origin.value = originUpdate;
      }

      markLayerDirty(layerId);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    }
  }
});
