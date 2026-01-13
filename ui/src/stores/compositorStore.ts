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
import { defineStore } from "pinia";
import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import type { FrameState } from "@/engine/MotionEngine";
import { motionEngine } from "@/engine/MotionEngine";
import type { ParticleSnapshot } from "@/engine/ParticleSimulationController";
import { particleSimulationRegistry } from "@/engine/ParticleSimulationController";
import type {
  AudioAnalysis,
  PeakData,
  PeakDetectionConfig,
} from "@/services/audioFeatures";
import type { PathAnimatorConfig } from "@/services/audioPathAnimator";
import type { PathAnimatorAccess } from "./audioKeyframeStore";
import type {
  AudioMapping,
  TargetParameter,
} from "@/services/audioReactiveMapping";
import type { CacheStats } from "@/services/frameCache";
import { interpolateProperty } from "@/services/interpolation";
import { markLayerDirty } from "@/services/layerEvaluationCache";
// Effect creation delegated to effectActions
import {
  type PropertyDriver,
  PropertyDriverSystem,
  type PropertyPath,
} from "@/services/propertyDriver";
import type { SegmentationPoint } from "@/services/segmentation";
import {
  DEFAULT_SNAP_CONFIG,
  findNearestSnap,
  getBeatFrames,
  getPeakFrames,
  type SnapConfig,
  type SnapResult,
} from "@/services/timelineSnap";
import type {
  Camera3D,
  CameraKeyframe,
  ViewOptions,
  ViewportState,
} from "@/types/camera";
import {
  createDefaultViewOptions,
  createDefaultViewportState,
} from "@/types/camera";
import type {
  AnimatableProperty,
  AnyLayerData,
  AssetReference,
  AudioParticleMapping,
  BezierHandle,
  ClipboardKeyframe,
  Composition,
  CompositionSettings,
  DepthflowLayerData,
  InterpolationType,
  Keyframe,
  LatticeProject,
  Layer,
  NestedCompData,
  ParticleEmitterConfig,
  ParticleLayerData,
  PropertyValue,
  VideoData,
} from "@/types/project";
import { createEmptyProject } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useAudioKeyframeStore, type FrequencyBandName } from "./audioKeyframeStore";
import { useCacheStore } from "./cacheStore";
import { useCameraStore } from "./cameraStore";
import { useCompositionStore } from "./compositionStore";
import { useDepthflowStore } from "./depthflowStore";
// Domain stores
import {
  useLayerStore,
  type LayerSourceReplacement,
  type SplineControlPoint,
  type TimeStretchOptions,
  type SequenceLayersOptions,
  type ExponentialScaleOptions,
  type CompositorStoreAccess,
} from "./layerStore";
import {
  useKeyframeStore,
  findPropertyByPath,
  type VelocitySettings,
  type BakeExpressionStoreAccess,
} from "./keyframeStore";
import { useMarkerStore } from "./markerStore";
import { useParticleStore } from "./particleStore";
import { useAnimationStore } from "./animationStore";
import { useExpressionStore } from "./expressionStore";
import { useSegmentationStore } from "./segmentationStore";
import {
  useTextAnimatorStore,
  type AddTextAnimatorConfig,
  type RangeSelectorConfig,
  type ExpressionSelectorConfig,
  type WigglySelectorConfig,
  type CharacterTransform,
  type TextPathConfig,
} from "./textAnimatorStore";
import { useVideoStore, type VideoImportResult } from "./videoStore";
import { useAudioStore } from "./audioStore";
import { useEffectStore } from "./effectStore";
import { useSelectionStore } from "./selectionStore";
import { useUIStore } from "./uiStore";
import { useProjectStore } from "./projectStore";

interface CompositorState {
  // Project data
  project: LatticeProject;

  // Active composition (for multi-composition support)
  activeCompositionId: string;
  openCompositionIds: string[]; // Tabs - which comps are open
  compositionBreadcrumbs: string[]; // Navigation history for nested compositions

  // ComfyUI connection
  comfyuiNodeId: string | null;

  // Input data from ComfyUI
  sourceImage: string | null;
  depthMap: string | null;

  // Playback state (isPlaying migrated to playbackStore, accessed via getter)

  // Selection state is now in selectionStore (accessed via getters)
  // Tool 'segment' is compositor-specific, handled separately
  segmentToolActive: boolean;

  // Segmentation state
  segmentMode: "point" | "box";
  segmentPendingMask: {
    mask: string;
    bounds: { x: number; y: number; width: number; height: number };
    area: number;
    score: number;
  } | null;
  segmentBoxStart: { x: number; y: number } | null;
  segmentIsLoading: boolean;

  // UI state (migrated to uiStore - accessed via getters/delegation)

  // History for undo/redo
  historyStack: LatticeProject[];
  historyIndex: number;

  // Path animators for audio-driven motion (only state still managed here)
  pathAnimators: Map<string, PathAnimatorAccess>;

  // Camera system
  cameras: Map<string, Camera3D>; // All cameras by ID
  cameraKeyframes: Map<string, CameraKeyframe[]>; // Keyframes per camera
  activeCameraId: string | null; // Which camera is currently active
  viewportState: ViewportState; // Multi-view layout state
  viewOptions: ViewOptions; // Display options (wireframes, etc.)

  // Property driver system (propertyDriverSystem and propertyDrivers migrated to expressionStore)

  // Timeline snapping (snapConfig migrated to animationStore)

  // Clipboard for copy/paste
  clipboard: {
    layers: Layer[];
    keyframes: ClipboardKeyframe[];
  };

  // Autosave state
  autosaveEnabled: boolean;
  autosaveIntervalMs: number;
  autosaveTimerId: number | null;
  lastSaveTime: number; // 0 = never saved, Date.now() = last save time
  lastSaveProjectId: string | null;
  hasUnsavedChanges: boolean;

  // Frame cache state
  frameCacheEnabled: boolean;
  projectStateHash: string;

  // Timeline UI state (timelineZoom migrated to animationStore)
  selectedAssetId: string | null;
}

export const useCompositorStore = defineStore("compositor", {
  state: (): CompositorState => {
    // Create initial project and pre-populate history with it
    // This ensures undo works for the very first action
    const initialProject = createEmptyProject(1280, 720); // 720p HD default
    return {
      project: initialProject,
      activeCompositionId: "main",
      openCompositionIds: ["main"],
      compositionBreadcrumbs: ["main"], // Start with main comp in breadcrumb path
      comfyuiNodeId: null,
      sourceImage: null,
      depthMap: null,
      // isPlaying migrated to playbackStore (accessed via getter)
      segmentToolActive: false,
      segmentMode: "point",
      segmentPendingMask: null,
      segmentBoxStart: null,
      segmentIsLoading: false,
      // UI state migrated to uiStore (curveEditorVisible, hideMinimizedLayers, shapeToolOptions)
      // Initialize history with initial project state so first action can be undone
      historyStack: [structuredClone(initialProject)],
      historyIndex: 0,
      pathAnimators: new Map(),

      // Camera system
      cameras: new Map(),
      cameraKeyframes: new Map(),
      activeCameraId: null,
      viewportState: createDefaultViewportState(),
      viewOptions: createDefaultViewOptions(),

      // Property driver system (migrated to expressionStore)

      // Timeline snapping (snapConfig migrated to animationStore)

      // Clipboard
      clipboard: {
        layers: [],
        keyframes: [],
      },

      // Autosave (enabled by default, every 60 seconds)
      autosaveEnabled: true,
      autosaveIntervalMs: 60000,
      autosaveTimerId: null,
      lastSaveTime: 0, // 0 = never saved
      lastSaveProjectId: null,
      hasUnsavedChanges: false,

      // Frame cache (enabled by default)
      frameCacheEnabled: true,
      projectStateHash: "",

      // Timeline UI state (timelineZoom migrated to animationStore)
      selectedAssetId: null,
    };
  },

  getters: {
    // Active composition helper
    activeComposition: (state): Composition | null => {
      return state.project.compositions[state.activeCompositionId] || null;
    },

    // Project info - computed from active composition
    hasProject(): boolean {
      return this.sourceImage !== null;
    },
    width(): number {
      return this.activeComposition?.settings.width || 1024;
    },
    height(): number {
      return this.activeComposition?.settings.height || 1024;
    },
    frameCount(): number {
      return this.activeComposition?.settings.frameCount || 81;
    },
    fps(): number {
      return this.activeComposition?.settings.fps || 16;
    },
    duration(): number {
      return this.activeComposition?.settings.duration || 5;
    },
    backgroundColor(): string {
      return this.activeComposition?.settings.backgroundColor || "#050505";
    },

    // Timeline zoom (delegated to animationStore)
    timelineZoom(): number {
      return useAnimationStore().timelineZoom;
    },

    // Snap config (delegated to animationStore)
    snapConfig(): SnapConfig {
      return useAnimationStore().snapConfig;
    },

    // Playback state (delegated to animationStore -> playbackStore)
    isPlaying(): boolean {
      return useAnimationStore().isPlaying;
    },

    // Current frame - per composition
    currentFrame(state): number {
      const comp = state.project.compositions[state.activeCompositionId];
      return comp?.currentFrame || 0;
    },
    currentTime(): number {
      const comp = this.activeComposition;
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
      const layers = comp?.layers || [];
      return layers.filter((l: Layer) => l.visible);
    },
    // Layers displayed in timeline (respects minimized filter)
    displayedLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      const layers = comp?.layers || [];
      const uiStore = useUIStore();
      if (uiStore.hideMinimizedLayers) {
        return layers.filter((l: Layer) => !l.minimized);
      }
      return layers;
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
    currentTool(
      state,
    ): "select" | "pen" | "text" | "hand" | "zoom" | "segment" {
      if (state.segmentToolActive) return "segment";
      return useSelectionStore().currentTool;
    },
    selectedLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      const selectionStore = useSelectionStore();
      return (comp?.layers || []).filter((l: Layer) =>
        selectionStore.selectedLayerIds.includes(l.id),
      );
    },
    selectedLayer(state): Layer | null {
      const selectionStore = useSelectionStore();
      if (selectionStore.selectedLayerIds.length !== 1) return null;
      const comp = state.project.compositions[state.activeCompositionId];
      return (
        (comp?.layers || []).find(
          (l: Layer) => l.id === selectionStore.selectedLayerIds[0],
        ) || null
      );
    },

    // All compositions for tabs
    allCompositions: (state): Composition[] => {
      return Object.values(state.project.compositions);
    },
    openCompositions(): Composition[] {
      return this.openCompositionIds
        .map((id: string) => this.project.compositions[id])
        .filter((comp): comp is Composition => comp !== undefined);
    },

    // Breadcrumb navigation path for nested compositions
    breadcrumbPath(): Array<{ id: string; name: string }> {
      return this.compositionBreadcrumbs.map((id: string) => {
        const comp = this.project.compositions[id];
        return { id, name: comp?.name || "Unknown" };
      });
    },

    // Assets
    assets: (state): Record<string, AssetReference> => state.project.assets,

    // History
    canUndo: (state): boolean => state.historyIndex > 0,
    canRedo: (state): boolean =>
      state.historyIndex < state.historyStack.length - 1,

    // Camera
    activeCamera: (state): Camera3D | null => {
      if (!state.activeCameraId) return null;
      return state.cameras.get(state.activeCameraId) || null;
    },
    allCameras: (state): Camera3D[] => Array.from(state.cameras.values()),
    cameraLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      const layers = comp?.layers || [];
      return layers.filter((l: Layer) => l.type === "camera");
    },

    // UI State (delegated to uiStore)
    hideMinimizedLayers(): boolean {
      return useUIStore().hideMinimizedLayers;
    },
    curveEditorVisible(): boolean {
      return useUIStore().curveEditorVisible;
    },
    shapeToolOptions() {
      return useUIStore().shapeToolOptions;
    },
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
      isNestedComp: boolean = false,
    ): Composition {
      return useCompositionStore().createComposition(this, name, settings, isNestedComp);
    },

    deleteComposition(compId: string): boolean {
      return useCompositionStore().deleteComposition(this, compId);
    },

    switchComposition(compId: string): void {
      useCompositionStore().switchComposition(this, compId);
    },

    closeCompositionTab(compId: string): void {
      useCompositionStore().closeCompositionTab(this, compId);
    },

    enterNestedComp(compId: string): void {
      useCompositionStore().enterNestedComp(this, compId);
    },

    navigateBack(): void {
      useCompositionStore().navigateBack(this);
    },

    navigateToBreadcrumb(index: number): void {
      useCompositionStore().navigateToBreadcrumb(this, index);
    },

    resetBreadcrumbs(): void {
      useCompositionStore().resetBreadcrumbs(this);
    },

    renameComposition(compId: string, newName: string): void {
      useCompositionStore().renameComposition(this, compId, newName);
    },

    updateCompositionSettings(
      compId: string,
      settings: Partial<CompositionSettings>,
    ): void {
      useCompositionStore().updateCompositionSettings(this, compId, settings);
    },

    getComposition(compId: string): Composition | null {
      return useCompositionStore().getComposition(this, compId);
    },

    enableFrameBlending(compId: string): void {
      useCompositionStore().enableFrameBlending(this, compId);
    },

    disableFrameBlending(compId: string): void {
      useCompositionStore().disableFrameBlending(this, compId);
    },

    toggleFrameBlending(compId: string): void {
      useCompositionStore().toggleFrameBlending(this, compId);
    },

    nestSelectedLayers(name?: string): Composition | null {
      return useCompositionStore().nestSelectedLayers(this, name);
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
      useProjectStore().loadInputs(this, inputs);

      // Save initial state to history
      this.pushHistory();
    },

    /**
     * Create a new layer

     */
    createLayer(type: Layer["type"], name?: string): Layer {
      return useLayerStore().createLayer(this, type, name);
    },

    /**
     * Alias for createLayer - used by keyboard shortcuts

     */
    addLayer(type: Layer["type"], name?: string): Layer {
      return useLayerStore().createLayer(this, type, name);
    },

    /**
     * Get a layer by ID
     */
    getLayerById(layerId: string): Layer | null {
      return useLayerStore().getLayerById(this, layerId);
    },

    /**
     * Delete a layer

     */
    deleteLayer(layerId: string): void {
      useLayerStore().deleteLayer(this, layerId);
    },

    /**
     * Duplicate a layer

     */
    duplicateLayer(layerId: string): Layer | null {
      return useLayerStore().duplicateLayer(this, layerId);
    },

    /**
     * Copy selected layers to clipboard
     */
    copySelectedLayers(): void {
      useLayerStore().copySelectedLayers(this);
    },

    /**
     * Paste layers from clipboard
     */
    pasteLayers(): Layer[] {
      return useLayerStore().pasteLayers(this);
    },

    /**
     * Cut selected layers (copy + delete)
     */
    cutSelectedLayers(): void {
      useLayerStore().cutSelectedLayers(this);
    },

    /**
     * Select all layers in the active composition
     */
    selectAllLayers(): void {
      useLayerStore().selectAllLayers(this);
    },

    /**
     * Delete all selected layers
     */
    deleteSelectedLayers(): void {
      useLayerStore().deleteSelectedLayers(this);
    },

    /**
     * Duplicate all selected layers
     */
    duplicateSelectedLayers(): string[] {
      return useLayerStore().duplicateSelectedLayers(this);
    },

    /**
     * Update layer properties

     */
    updateLayer(layerId: string, updates: Partial<Layer>): void {
      useLayerStore().updateLayer(this, layerId, updates);
    },

    /**
     * Update layer-specific data (e.g., text content, image path, etc.)
     * Accepts both common AnyLayerData properties and layer-type-specific properties.

     */
    updateLayerData(
      layerId: string,
      dataUpdates: Partial<AnyLayerData> & Record<string, unknown>,
    ): void {
      useLayerStore().updateLayerData(this, layerId, dataUpdates);
    },

    /**
     * Add a control point to a spline layer

     */
    addSplineControlPoint(
      layerId: string,
      point: SplineControlPoint,
    ): void {
      useLayerStore().addSplineControlPoint(this, layerId, point);
    },

    /**
     * Insert a control point at a specific index in a spline layer

     */
    insertSplineControlPoint(
      layerId: string,
      point: SplineControlPoint,
      index: number,
    ): void {
      useLayerStore().insertSplineControlPoint(this, layerId, point, index);
    },

    /**
     * Update a spline control point

     */
    updateSplineControlPoint(
      layerId: string,
      pointId: string,
      updates: Partial<SplineControlPoint>,
    ): void {
      useLayerStore().updateSplineControlPoint(this, layerId, pointId, updates);
    },

    /**
     * Delete a spline control point

     */
    deleteSplineControlPoint(layerId: string, pointId: string): void {
      useLayerStore().deleteSplineControlPoint(this, layerId, pointId);
    },

    /**
     * Enable animation mode on a spline layer (converts to keyframeable control points)

     */
    enableSplineAnimation(layerId: string): void {
      useLayerStore().enableSplineAnimation(this, layerId);
    },

    /**
     * Add keyframe to a spline control point property

     */
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
      useLayerStore().addSplinePointKeyframe(
        this,
        layerId,
        pointId,
        property,
        frame,
      );
    },

    /**
     * Add keyframes to all position properties of a control point

     */
    addSplinePointPositionKeyframe(
      layerId: string,
      pointId: string,
      frame: number,
    ): void {
      useLayerStore().addSplinePointPositionKeyframe(
        this,
        layerId,
        pointId,
        frame,
      );
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
      addKeyframe: boolean = false,
    ): void {
      useLayerStore().updateSplinePointWithKeyframe(
        this,
        layerId,
        pointId,
        x,
        y,
        frame,
        addKeyframe,
      );
    },

    /**
     * Get evaluated control points at a specific frame

     */
    getEvaluatedSplinePoints(
      layerId: string,
      frame: number,
    ): import("@/types/project").EvaluatedControlPoint[] {
      return useLayerStore().getEvaluatedSplinePoints(this, layerId, frame);
    },

    /**
     * Check if spline has animation enabled

     */
    isSplineAnimated(layerId: string): boolean {
      return useLayerStore().isSplineAnimated(this, layerId);
    },

    /**
     * Check if a control point has any keyframes

     */
    hasSplinePointKeyframes(layerId: string, pointId: string): boolean {
      return useLayerStore().hasSplinePointKeyframes(this, layerId, pointId);
    },

    /**
     * Simplify a spline by reducing control points (Douglas-Peucker)
     * @param tolerance - Distance threshold in pixels (higher = more simplification)

     */
    simplifySpline(layerId: string, tolerance: number): void {
      useLayerStore().simplifySpline(this, layerId, tolerance);
    },

    /**
     * Smooth spline handles to create smoother curves
     * @param amount - Smoothing amount 0-100 (100 = fully smooth)

     */
    smoothSplineHandles(layerId: string, amount: number): void {
      useLayerStore().smoothSplineHandles(this, layerId, amount);
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
        interpolation?: "linear" | "bezier" | "hold";
        useSpatialTangents?: boolean;
        reversed?: boolean;
      },
    ): number | null {
      return useLayerStore().copyPathToPosition(
        this,
        sourceSplineLayerId,
        targetLayerId,
        options,
      );
    },

    /**
     * Toggle 3D mode for a layer
     */
    toggleLayer3D(layerId: string): void {
      useLayerStore().toggleLayer3D(this, layerId);
    },

    /**
     * Reorder layers
     */
    moveLayer(layerId: string, newIndex: number): void {
      useLayerStore().moveLayer(this, layerId, newIndex);
    },

    /**
     * Replace layer source with a new asset (Alt+drag replacement)
     * Keeps all keyframes, effects, and transforms
     */
    replaceLayerSource(
      layerId: string,
      newSource: LayerSourceReplacement,
    ): void {
      useLayerStore().replaceLayerSource(this, layerId, newSource);
    },

    /**
     * Toggle locked state for selected layers
     */
    toggleLayerLock(): void {
      useLayerStore().toggleLayerLock(this);
    },

    /**
     * Toggle visibility for selected layers
     */
    toggleLayerVisibility(): void {
      useLayerStore().toggleLayerVisibility(this);
    },

    /**
     * Toggle solo state for selected layers
     */
    toggleLayerSolo(): void {
      useLayerStore().toggleLayerSolo(this);
    },

    /**
     * Move selected layers to the front (top of stack)
     */
    bringToFront(): void {
      useLayerStore().bringToFront(this);
    },

    /**
     * Move selected layers to the back (bottom of stack)
     */
    sendToBack(): void {
      useLayerStore().sendToBack(this);
    },

    /**
     * Move selected layers forward by one position
     */
    bringForward(): void {
      useLayerStore().bringForward(this);
    },

    /**
     * Move selected layers backward by one position
     */
    sendBackward(): void {
      useLayerStore().sendBackward(this);
    },

    /**
     * Selection
     */
    selectLayer(layerId: string, addToSelection = false): void {
      useLayerStore().selectLayer(this, layerId, addToSelection);
    },

    deselectLayer(layerId: string): void {
      useLayerStore().deselectLayer(this, layerId);
    },

    /**
     * Set a layer's parent for parenting/hierarchy
     */
    setLayerParent(layerId: string, parentId: string | null): void {
      useLayerStore().setLayerParent(this, layerId, parentId);
    },

    // ============================================================
    // TIME MANIPULATION
    // ============================================================

    /**
     * Apply time stretch to a video or nested comp layer
     * @param layerId - Target layer ID
     * @param options - Time stretch options including stretchFactor, holdInPlace, reverse
     */
    timeStretchLayer(
      layerId: string,
      options: TimeStretchOptions,
    ): void {
      useLayerStore().timeStretchLayer(this, layerId, options);
    },

    /**
     * Reverse layer playback by negating speed
     * @param layerId - Target layer ID
     */
    reverseLayer(layerId: string): void {
      useLayerStore().reverseLayer(this, layerId);
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
        pushHistory: this.pushHistory.bind(this),
      };
      useLayerStore().freezeFrameAtPlayhead(storeWithFrame, layerId);
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
        fps: comp?.settings.fps ?? 30,
        // Explicitly bind pushHistory to preserve 'this' context
        pushHistory: this.pushHistory.bind(this),
      };
      return useLayerStore().splitLayerAtPlayhead(storeWithFrame, layerId);
    },

    clearSelection(): void {
      useLayerStore().clearSelection(this);
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
      return useAnimationStore().getFrameState(this, frame);
    },

    // ============================================================
    // PLAYBACK CONTROLS (delegated to animationStore)
    // ============================================================

    play(): void {
      useAnimationStore().play(this);
    },

    pause(): void {
      useAnimationStore().pause(this);
    },

    togglePlayback(): void {
      useAnimationStore().togglePlayback(this);
    },

    setFrame(frame: number): void {
      useAnimationStore().setFrame(this, frame);
    },

    nextFrame(): void {
      useAnimationStore().nextFrame(this);
    },

    prevFrame(): void {
      useAnimationStore().prevFrame(this);
    },

    goToStart(): void {
      useAnimationStore().goToStart(this);
    },

    goToEnd(): void {
      useAnimationStore().goToEnd(this);
    },

    jumpFrames(n: number): void {
      useAnimationStore().jumpFrames(this, n);
    },

    /**
     * Tool selection
     */
    setTool(
      tool: "select" | "pen" | "text" | "hand" | "zoom" | "segment",
    ): void {
      if (tool === "segment") {
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
    setSegmentMode(mode: "point" | "box"): void {
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
    setSegmentPendingMask(mask: CompositorState["segmentPendingMask"]): void {
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

      const layer = await useSegmentationStore().createLayerFromMask(
        this,
        this.sourceImage,
        this.segmentPendingMask,
        layerName,
        false,
      );

      // Clear pending mask after creating layer
      this.clearSegmentPendingMask();

      return layer;
    },

    /**
     * Set shape tool options (from toolbar)
     */
    setShapeToolOptions(options: Parameters<ReturnType<typeof useUIStore>["setShapeToolOptions"]>[0]): void {
      useUIStore().setShapeToolOptions(options);
    },

    /**
     * History management (delegated to projectStore)
     */
    pushHistory(): void {
      useProjectStore().pushHistory(this);
    },

    undo(): void {
      useProjectStore().undo(this);
    },

    redo(): void {
      useProjectStore().redo(this);
    },

    /**
     * Project serialization (delegated to projectStore)
     */
    exportProject(): string {
      return useProjectStore().exportProject(this);
    },

    importProject(json: string): boolean {
      return useProjectStore().importProject(this, json, () => this.pushHistory());
    },

    /**
     * Load project from a File object (e.g., from file input or drag-drop)
     */
    async loadProjectFromFile(file: File): Promise<boolean> {
      return useProjectStore().loadProjectFromFile(this, file, () =>
        this.pushHistory(),
      );
    },

    /**
     * Save project to server (ComfyUI backend)
     */
    async saveProjectToServer(projectId?: string): Promise<string | null> {
      return useProjectStore().saveProjectToServer(this, projectId);
    },

    /**
     * Load project from server (ComfyUI backend)
     */
    async loadProjectFromServer(projectId: string): Promise<boolean> {
      return useProjectStore().loadProjectFromServer(this, projectId, () =>
        this.pushHistory(),
      );
    },

    /**
     * List all projects saved on server
     */
    async listServerProjects(): Promise<
      Array<{ id: string; name: string; modified?: string }>
    > {
      return useProjectStore().listServerProjects();
    },

    /**
     * Delete a project from server
     */
    async deleteServerProject(projectId: string): Promise<boolean> {
      return useProjectStore().deleteServerProject(projectId);
    },

    /**
     * Remove unused assets from the project (Reduce Project)
     * Returns info about removed assets
     */
    removeUnusedAssets(): { removed: number; assetNames: string[] } {
      return useProjectStore().removeUnusedAssets(this);
    },

    /**
     * Get statistics about asset usage
     */
    getAssetUsageStats(): {
      total: number;
      used: number;
      unused: number;
      unusedNames: string[];
    } {
      return useProjectStore().getAssetUsageStats(this);
    },

    /**
     * Collect Files - Package project and assets into a downloadable ZIP
     * @param includeUnused - Whether to include assets not used by any layer
     */
    async collectFiles(
      options: { includeUnused?: boolean } = {},
    ): Promise<void> {
      return useProjectStore().downloadCollectedFiles(this, options);
    },

    /**
     * Toggle curve editor visibility
     */
    toggleCurveEditor(): void {
      useUIStore().toggleCurveEditorVisible();
    },

    /**
     * Set curve editor visibility directly
     */
    setCurveEditorVisible(visible: boolean): void {
      useUIStore().setCurveEditorVisible(visible);
    },

    /**
     * Toggle hide minimized layers in timeline
     */
    toggleHideMinimizedLayers(): void {
      useUIStore().toggleHideMinimizedLayers();
    },

    /** @deprecated Use toggleHideMinimizedLayers instead */
    toggleHideShyLayers(): void {
      useUIStore().toggleHideMinimizedLayers();
    },

    /**
     * Set hide minimized layers state
     */
    setHideMinimizedLayers(hide: boolean): void {
      useUIStore().setHideMinimizedLayers(hide);
    },

    /** @deprecated Use setHideMinimizedLayers instead */
    setHideShyLayers(hide: boolean): void {
      useUIStore().setHideMinimizedLayers(hide);
    },

    /**
     * Get interpolated value for any animatable property at current frame.
     * Passes fps and duration from composition settings.
     */
    getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
      return useKeyframeStore().getInterpolatedValue(this, property);
    },

    /**
     * Add a keyframe to a property
     */
    addKeyframe<T>(
      layerId: string,
      propertyName: string,
      value: T,
      atFrame?: number,
    ): Keyframe<T> | null {
      return useKeyframeStore().addKeyframe(
        this,
        layerId,
        propertyName,
        value,
        atFrame,
      );
    },

    /**
     * Remove a keyframe
     */
    removeKeyframe(
      layerId: string,
      propertyName: string,
      keyframeId: string,
    ): void {
      useKeyframeStore().removeKeyframe(this, layerId, propertyName, keyframeId);
    },

    /**
     * Set a property's value (for direct editing in timeline)
     */
    setPropertyValue(
      layerId: string,
      propertyPath: string,
      value: PropertyValue,
    ): void {
      useKeyframeStore().setPropertyValue(this, layerId, propertyPath, value);
    },

    /**
     * Update an entire property including keyframes (for batch operations)
     */
    updateLayerProperty(
      layerId: string,
      propertyPath: string,
      propertyData: Partial<AnimatableProperty<any>>,
    ): boolean {
      return useKeyframeStore().updateLayerProperty(
        this,
        layerId,
        propertyPath,
        propertyData,
      );
    },

    /**
     * Set a property's animated state
     */
    setPropertyAnimated(
      layerId: string,
      propertyPath: string,
      animated: boolean,
    ): void {
      useKeyframeStore().setPropertyAnimated(
        this,
        layerId,
        propertyPath,
        animated,
        () => {
          this.addKeyframe(
            layerId,
            propertyPath,
            findPropertyByPath(
              this.getActiveCompLayers().find((l) => l.id === layerId)!,
              propertyPath,
            )?.value,
          );
        },
      );
    },

    /**
     * Move a keyframe to a new frame
     */
    moveKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newFrame: number,
    ): void {
      useKeyframeStore().moveKeyframe(
        this,
        layerId,
        propertyPath,
        keyframeId,
        newFrame,
      );
    },

    /**
     * Move multiple keyframes by a frame delta (for marquee selection bulk moves).
     * All keyframes move together by the same delta, maintaining relative positions.
     */
    moveKeyframes(
      keyframes: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
      frameDelta: number,
    ): void {
      useKeyframeStore().moveKeyframes(this, keyframes, frameDelta);
    },

    /**
     * Set keyframe value (for graph editor numeric input)
     */
    setKeyframeValue(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newValue: number,
    ): void {
      useKeyframeStore().setKeyframeValue(
        this,
        layerId,
        propertyPath,
        keyframeId,
        newValue,
      );
    },

    /**
     * Set keyframe interpolation type
     */
    setKeyframeInterpolation(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      interpolation: InterpolationType,
    ): void {
      useKeyframeStore().setKeyframeInterpolation(
        this,
        layerId,
        propertyPath,
        keyframeId,
        interpolation,
      );
    },

    /**
     * Apply easing preset to multiple keyframes at once
     * @param keyframeSelections Array of keyframe selections with layerId, propertyPath, keyframeId
     * @param interpolation The interpolation type to apply
     * @returns Number of keyframes updated
     */
    applyEasingPresetToKeyframes(
      keyframeSelections: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
      interpolation: InterpolationType,
    ): number {
      let count = 0;
      for (const sel of keyframeSelections) {
        useKeyframeStore().setKeyframeInterpolation(
          this,
          sel.layerId,
          sel.propertyPath,
          sel.keyframeId,
          interpolation,
        );
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
      updates: { frame?: number; value?: PropertyValue },
    ): void {
      useKeyframeStore().updateKeyframe(
        this,
        layerId,
        propertyPath,
        keyframeId,
        updates,
      );
    },

    /**
     * Set keyframe bezier handle
     */
    setKeyframeHandle(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
    ): void {
      useKeyframeStore().setKeyframeHandle(
        this,
        layerId,
        propertyPath,
        keyframeId,
        handleType,
        handle,
      );
    },

    /**
     * Update both keyframe handles at once (convenience method for easing presets)
     */
    updateKeyframeHandles(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handles: {
        inHandle?: { x: number; y: number };
        outHandle?: { x: number; y: number };
      },
    ): void {
      if (handles.inHandle) {
        useKeyframeStore().setKeyframeHandle(
          this,
          layerId,
          propertyPath,
          keyframeId,
          "in",
          {
            frame: handles.inHandle.x * 10, // Convert normalized x to frame offset
            value: handles.inHandle.y * 100, // Convert normalized y to value offset
            enabled: true,
          },
        );
      }
      if (handles.outHandle) {
        useKeyframeStore().setKeyframeHandle(
          this,
          layerId,
          propertyPath,
          keyframeId,
          "out",
          {
            frame: handles.outHandle.x * 10,
            value: handles.outHandle.y * 100,
            enabled: true,
          },
        );
      }
    },

    /**
     * Set keyframe control mode (smooth, corner, symmetric)
     */
    setKeyframeControlMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      controlMode: "smooth" | "corner" | "symmetric",
    ): void {
      useKeyframeStore().setKeyframeControlMode(
        this,
        layerId,
        propertyPath,
        keyframeId,
        controlMode,
      );
    },

    /**
     * Insert a keyframe on the motion path at the current frame
     * Uses interpolated values from existing keyframes
     * @returns The created keyframe ID or null if failed
     */
    insertKeyframeOnPath(layerId: string, frame: number): string | null {
      return useKeyframeStore().insertKeyframeOnPath(this, layerId, frame);
    },

    /**
     * Set keyframe handle with control mode awareness (supports breaking handles)
     * @param breakHandle - If true, sets controlMode to 'corner' (Ctrl+drag behavior)
     */
    setKeyframeHandleWithMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
      breakHandle: boolean = false,
    ): void {
      useKeyframeStore().setKeyframeHandleWithMode(
        this,
        layerId,
        propertyPath,
        keyframeId,
        handleType,
        handle,
        breakHandle,
      );
    },

    /**
     * Auto-calculate bezier tangents for a single keyframe
     */
    autoCalculateBezierTangents(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): boolean {
      return useKeyframeStore().autoCalculateBezierTangents(
        this,
        layerId,
        propertyPath,
        keyframeId,
      );
    },

    /**
     * Auto-calculate bezier tangents for ALL keyframes on a property
     */
    autoCalculateAllBezierTangents(
      layerId: string,
      propertyPath: string,
    ): number {
      return useKeyframeStore().autoCalculateAllBezierTangents(
        this,
        layerId,
        propertyPath,
      );
    },

    /**
     * Separate position into individual X, Y, Z properties for independent keyframing.
     */
    separatePositionDimensions(layerId: string): boolean {
      return useKeyframeStore().separatePositionDimensionsAction(this, layerId);
    },

    /**
     * Link position dimensions back into a combined property.
     */
    linkPositionDimensions(layerId: string): boolean {
      return useKeyframeStore().linkPositionDimensionsAction(this, layerId);
    },

    /**
     * Separate scale into individual X, Y, Z properties.
     */
    separateScaleDimensions(layerId: string): boolean {
      return useKeyframeStore().separateScaleDimensionsAction(this, layerId);
    },

    /**
     * Link scale dimensions back into a combined property.
     */
    linkScaleDimensions(layerId: string): boolean {
      return useKeyframeStore().linkScaleDimensionsAction(this, layerId);
    },

    /**
     * Check if position dimensions are separated.
     */
    hasPositionSeparated(layerId: string): boolean {
      return useKeyframeStore().hasPositionSeparated(this, layerId);
    },

    /**
     * Check if scale dimensions are separated.
     */
    hasScaleSeparated(layerId: string): boolean {
      return useKeyframeStore().hasScaleSeparated(this, layerId);
    },

    /**
     * Sequence layers - arrange selected layers one after another.
     * @param layerIds - Array of layer IDs to sequence (in order)
     * @param options - Sequence options (gap, startFrame, reverse)
     */
    sequenceLayers(
      layerIds: string[],
      options?: SequenceLayersOptions,
    ): number {
      return useLayerStore().sequenceLayers(this, layerIds, options);
    },

    /**
     * Apply exponential scale animation to a layer.
     * Creates keyframes with exponential curve for natural zoom effect.
     */
    applyExponentialScale(
      layerId: string,
      options?: ExponentialScaleOptions,
    ): number {
      return useLayerStore().applyExponentialScale(this, layerId, options);
    },

    /**
     * Create a text layer with proper data structure
     */
    createTextLayer(text: string = "Text"): Layer {
      return useLayerStore().createTextLayer(this, text);
    },

    /**
     * Create a spline layer with proper data structure
     */
    createSplineLayer(): Layer {
      return useLayerStore().createSplineLayer(this);
    },

    /**
     * Create a shape layer with proper data structure
     */
    createShapeLayer(name: string = "Shape Layer"): Layer {
      return useLayerStore().createShapeLayer(this, name);
    },

    /**
     * Convert a text layer to spline layer(s)
     */
    async convertTextLayerToSplines(
      layerId: string,
      options: {
        perCharacter?: boolean;
        fontUrl?: string;
        keepOriginal?: boolean;
        groupCharacters?: boolean;
      } = {},
    ): Promise<string[] | null> {
      return useLayerStore().convertTextLayerToSplines(this, layerId, options);
    },

    /**
     * Rename a layer by ID
     */
    renameLayer(layerId: string, newName: string): void {
      return useLayerStore().renameLayer(this, layerId, newName);
    },

    // ============================================================
    // PARTICLE SYSTEM LAYER ACTIONS (delegated to particleLayerActions)
    // ============================================================

    createParticleLayer(): Layer {
      return useParticleStore().createParticleLayer(this);
    },

    updateParticleLayerData(
      layerId: string,
      updates: Partial<ParticleLayerData>,
    ): void {
      useParticleStore().updateParticleLayerData(this, layerId, updates);
    },

    addParticleEmitter(layerId: string, config: ParticleEmitterConfig): void {
      useParticleStore().addParticleEmitter(this, layerId, config);
    },

    updateParticleEmitter(
      layerId: string,
      emitterId: string,
      updates: Partial<ParticleEmitterConfig>,
    ): void {
      useParticleStore().updateParticleEmitter(this, layerId, emitterId, updates);
    },

    removeParticleEmitter(layerId: string, emitterId: string): void {
      useParticleStore().removeParticleEmitter(this, layerId, emitterId);
    },

    // ============================================================
    // DEPTHFLOW LAYER ACTIONS (delegated to depthflowStore)
    // ============================================================

    createDepthflowLayer(
      sourceLayerId: string = "",
      depthLayerId: string = "",
    ): Layer {
      return useDepthflowStore().createDepthflowLayer(this, sourceLayerId, depthLayerId);
    },

    updateDepthflowConfig(
      layerId: string,
      updates: Partial<DepthflowLayerData["config"]>,
    ): void {
      useDepthflowStore().updateDepthflowConfig(this, layerId, updates);
    },

    // ============================================================
    // VIDEO LAYER ACTIONS (delegated to videoStore)
    // ============================================================

    async createVideoLayer(
      file: File,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
      return useVideoStore().createVideoLayer(this, file, autoResizeComposition);
    },

    updateVideoLayerData(layerId: string, updates: Partial<VideoData>): void {
      useVideoStore().updateVideoLayerData(this, layerId, updates);
    },

    onVideoMetadataLoaded(layerId: string, metadata: VideoMetadata): void {
      useVideoStore().onVideoMetadataLoaded(this, layerId, metadata);
    },

    resizeComposition(
      width: number,
      height: number,
      frameCount?: number,
    ): void {
      useVideoStore().resizeComposition(this, width, height, frameCount);
    },

    // NESTED COMP LAYER ACTIONS (delegated to layerStore)
    // ============================================================

    /**
     * Create a nested comp layer referencing another composition
     */
    createNestedCompLayer(compositionId: string, name?: string): Layer {
      return useLayerStore().createNestedCompLayer(this, compositionId, name);
    },

    /**
     * Update nested comp layer data
     */
    updateNestedCompLayerData(
      layerId: string,
      updates: Partial<NestedCompData>,
    ): void {
      useLayerStore().updateNestedCompLayerData(this, layerId, updates);
    },

    // ============================================================
    // SEGMENTATION ACTIONS (delegated to segmentationActions)
    // ============================================================

    async segmentToLayerByPoint(
      point: SegmentationPoint,
      options: {
        model?: "sam2" | "matseg";
        layerName?: string;
        positionAtCenter?: boolean;
      } = {},
    ): Promise<Layer | null> {
      return useSegmentationStore().segmentToLayerByPoint(this, point, options);
    },
    async segmentToLayerByBox(
      box: [number, number, number, number],
      options: {
        model?: "sam2" | "matseg";
        layerName?: string;
        positionAtCenter?: boolean;
      } = {},
    ): Promise<Layer | null> {
      return useSegmentationStore().segmentToLayerByBox(this, box, options);
    },
    async segmentToLayerByMultiplePoints(
      foregroundPoints: SegmentationPoint[],
      backgroundPoints: SegmentationPoint[] = [],
      options: {
        model?: "sam2" | "matseg";
        layerName?: string;
        positionAtCenter?: boolean;
      } = {},
    ): Promise<Layer | null> {
      return useSegmentationStore().segmentToLayerByMultiplePoints(
        this,
        foregroundPoints,
        backgroundPoints,
        options,
      );
    },
    async autoSegmentToLayers(
      options: {
        model?: "sam2" | "matseg";
        minArea?: number;
        maxMasks?: number;
        namePrefix?: string;
      } = {},
    ): Promise<Layer[]> {
      return useSegmentationStore().autoSegmentToLayers(this, options);
    },

    // ============================================================
    // EFFECT ACTIONS (delegated to effectStore)
    // ============================================================

    addEffectToLayer(layerId: string, effectKey: string): void {
      useEffectStore().addEffectToLayer(this, layerId, effectKey);
    },
    removeEffectFromLayer(layerId: string, effectId: string): void {
      useEffectStore().removeEffectFromLayer(this, layerId, effectId);
    },
    updateEffectParameter(
      layerId: string,
      effectId: string,
      paramKey: string,
      value: PropertyValue,
    ): void {
      useEffectStore().updateEffectParameter(
        this,
        layerId,
        effectId,
        paramKey,
        value,
      );
    },
    setEffectParamAnimated(
      layerId: string,
      effectId: string,
      paramKey: string,
      animated: boolean,
    ): void {
      useEffectStore().setEffectParamAnimated(
        this,
        layerId,
        effectId,
        paramKey,
        animated,
      );
    },
    toggleEffect(layerId: string, effectId: string): void {
      useEffectStore().toggleEffect(this, layerId, effectId);
    },
    reorderEffects(layerId: string, fromIndex: number, toIndex: number): void {
      useEffectStore().reorderEffects(this, layerId, fromIndex, toIndex);
    },
    getEffectParameterValue(
      layerId: string,
      effectId: string,
      paramKey: string,
      frame?: number,
    ): PropertyValue | undefined {
      return useEffectStore().getEffectParameterValue(
        this,
        layerId,
        effectId,
        paramKey,
        frame,
      ) as PropertyValue | undefined;
    },

    // ============================================================
    // TEXT ANIMATOR ACTIONS (delegated to textAnimatorStore)
    // ============================================================

    addTextAnimator(
      layerId: string,
      config: AddTextAnimatorConfig = {},
    ) {
      return useTextAnimatorStore().addTextAnimator(this, layerId, config);
    },
    removeTextAnimator(layerId: string, animatorId: string): boolean {
      return useTextAnimatorStore().removeTextAnimator(this, layerId, animatorId);
    },
    updateTextAnimator(
      layerId: string,
      animatorId: string,
      updates: Partial<import("@/types/text").TextAnimator>,
    ): boolean {
      return useTextAnimatorStore().updateTextAnimator(this, layerId, animatorId, updates);
    },
    getTextAnimator(layerId: string, animatorId: string) {
      return useTextAnimatorStore().getTextAnimator(this, layerId, animatorId);
    },
    getTextAnimators(layerId: string) {
      return useTextAnimatorStore().getTextAnimators(this, layerId);
    },
    configureRangeSelector(
      layerId: string,
      animatorId: string,
      config: RangeSelectorConfig,
    ): boolean {
      return useTextAnimatorStore().configureRangeSelector(this, layerId, animatorId, config);
    },
    configureExpressionSelector(
      layerId: string,
      animatorId: string,
      config: ExpressionSelectorConfig,
    ): Promise<boolean> {
      return useTextAnimatorStore().configureExpressionSelector(this, layerId, animatorId, config);
    },
    removeExpressionSelector(layerId: string, animatorId: string): boolean {
      return useTextAnimatorStore().removeExpressionSelector(this, layerId, animatorId);
    },
    configureWigglySelector(
      layerId: string,
      animatorId: string,
      config: WigglySelectorConfig,
    ): boolean {
      return useTextAnimatorStore().configureWigglySelector(this, layerId, animatorId, config);
    },
    removeWigglySelector(layerId: string, animatorId: string): boolean {
      return useTextAnimatorStore().removeWigglySelector(this, layerId, animatorId);
    },
    getCharacterTransforms(
      layerId: string,
      frame?: number,
    ): CharacterTransform[] {
      return useTextAnimatorStore().getCharacterTransforms(this, layerId, frame ?? this.currentFrame);
    },
    getSelectionValues(
      layerId: string,
      animatorId: string,
      frame?: number,
    ): number[] {
      return useTextAnimatorStore().getSelectionValues(this, layerId, animatorId, frame ?? this.currentFrame);
    },
    getRangeSelectionValue(
      layerId: string,
      animatorId: string,
      charIndex: number,
      frame?: number,
    ): number {
      return useTextAnimatorStore().getRangeSelectionValue(this, layerId, animatorId, charIndex, frame ?? this.currentFrame);
    },
    setAnimatorPropertyValue(
      layerId: string,
      animatorId: string,
      propertyName: string,
      value: number,
    ): boolean {
      return useTextAnimatorStore().setAnimatorPropertyValue(
        this,
        layerId,
        animatorId,
        propertyName as keyof import("@/types/text").TextAnimatorProperties,
        value,
      );
    },
    hasTextAnimators(layerId: string): boolean {
      return useTextAnimatorStore().hasTextAnimators(this, layerId);
    },
    getTextContent(layerId: string): string | null {
      return useTextAnimatorStore().getTextContent(this, layerId);
    },
    setTextContent(layerId: string, text: string): boolean {
      return useTextAnimatorStore().setTextContent(this, layerId, text);
    },

    // TEXT ON PATH ACTIONS (delegated to textAnimatorStore)
    setTextPath(
      layerId: string,
      config: TextPathConfig,
    ): boolean {
      return useTextAnimatorStore().setTextPath(this, layerId, config);
    },
    getTextPathConfig(layerId: string) {
      return useTextAnimatorStore().getTextPathConfig(this, layerId);
    },
    updateTextPath(
      layerId: string,
      updates: Partial<TextPathConfig>,
    ): boolean {
      return useTextAnimatorStore().updateTextPath(this, layerId, updates);
    },
    getCharacterPathPlacements(layerId: string, frame?: number) {
      return useTextAnimatorStore().getCharacterPathPlacements(this, layerId, frame ?? this.currentFrame);
    },
    getPathLength(layerId: string): number {
      return useTextAnimatorStore().getPathLength(this, layerId);
    },
    hasTextPath(layerId: string): boolean {
      return useTextAnimatorStore().hasTextPath(this, layerId);
    },
    clearTextPath(layerId: string): boolean {
      return useTextAnimatorStore().clearTextPath(this, layerId);
    },

    // ============================================================
    // CAMERA ACTIONS (delegated to cameraStore)
    // ============================================================

    createCameraLayer(name?: string): { camera: Camera3D; layer: Layer } {
      return useCameraStore().createCameraLayer(this, name);
    },
    getCamera(cameraId: string): Camera3D | null {
      return useCameraStore().getCamera(this, cameraId);
    },
    updateCamera(cameraId: string, updates: Partial<Camera3D>): void {
      useCameraStore().updateCamera(this, cameraId, updates);
    },
    setActiveCamera(cameraId: string): void {
      useCameraStore().setActiveCamera(this, cameraId);
    },
    deleteCamera(cameraId: string): void {
      useCameraStore().deleteCamera(this, cameraId);
    },
    getCameraKeyframes(cameraId: string): CameraKeyframe[] {
      return useCameraStore().getCameraKeyframes(this, cameraId);
    },
    addCameraKeyframe(cameraId: string, keyframe: CameraKeyframe): void {
      useCameraStore().addCameraKeyframe(this, cameraId, keyframe);
    },
    removeCameraKeyframe(cameraId: string, frame: number): void {
      useCameraStore().removeCameraKeyframe(this, cameraId, frame);
    },
    getCameraAtFrame(cameraId: string, frame: number): Camera3D | null {
      return useCameraStore().getCameraAtFrame(this, cameraId, frame);
    },
    getActiveCameraAtFrame(frame?: number): Camera3D | null {
      return useCameraStore().getActiveCameraAtFrame(this, frame ?? this.currentFrame);
    },
    updateViewportState(updates: Partial<ViewportState>): void {
      useCameraStore().updateViewportState(this, updates);
    },
    updateViewOptions(updates: Partial<ViewOptions>): void {
      useCameraStore().updateViewOptions(this, updates);
    },

    // ============================================================
    // AUDIO ACTIONS (delegated to audioStore - source of truth)
    // ============================================================

    async loadAudio(file: File): Promise<void> {
      await useAudioStore().loadAudio(file, this.project.composition.fps);
    },
    cancelAudioLoad(): void {
      useAudioStore().cancelLoad();
    },
    clearAudio(): void {
      useAudioStore().clear();
      this.pathAnimators.clear();
    },
    setAudioVolume(volume: number): void {
      useAudioStore().setVolume(volume);
    },
    setAudioMuted(muted: boolean): void {
      useAudioStore().setMuted(muted);
    },
    toggleAudioMute(): void {
      useAudioStore().toggleMuted();
    },
    getAudioFeatureAtFrame(feature: string, frame?: number): number {
      return useAudioStore().getFeatureAtFrame(this, feature, frame);
    },
    applyAudioToParticles(
      layerId: string,
      mapping: AudioParticleMapping,
    ): void {
      useAudioStore().addLegacyMapping(layerId, mapping);
    },
    removeLegacyAudioMapping(layerId: string, index: number): void {
      useAudioStore().removeLegacyMapping(layerId, index);
    },
    getAudioMappingsForLayer(layerId: string): AudioParticleMapping[] {
      return useAudioStore().getLegacyMappings(layerId);
    },
    setPeakData(peakData: PeakData): void {
      useAudioStore().setPeakData(peakData);
    },
    detectAudioPeaks(config: PeakDetectionConfig): PeakData | null {
      return useAudioStore().detectPeaks(config);
    },
    addAudioMapping(mapping: AudioMapping): void {
      useAudioStore().addMapping(mapping);
    },
    removeAudioMapping(mappingId: string): void {
      useAudioStore().removeMapping(mappingId);
    },
    updateAudioMapping(
      mappingId: string,
      updates: Partial<AudioMapping>,
    ): void {
      useAudioStore().updateMapping(mappingId, updates);
    },
    getAudioMappings(): AudioMapping[] {
      return useAudioStore().getMappings();
    },
    getMappedValueAtFrame(mappingId: string, frame: number): number {
      return useAudioStore().getMappedValueAtFrame(mappingId, frame);
    },
    getAllMappedValuesAtFrame(frame?: number): Map<TargetParameter, number> {
      const targetFrame = frame ?? this.getActiveComp()?.currentFrame ?? 0;
      return useAudioStore().getAllMappedValuesAtFrame(targetFrame);
    },
    getActiveMappingsForLayer(layerId: string): AudioMapping[] {
      return useAudioStore().getActiveMappingsForLayer(layerId);
    },
    getAudioReactiveValuesForLayer(
      layerId: string,
      frame: number,
    ): Map<TargetParameter, number> {
      return useAudioStore().getValuesForLayerAtFrame(layerId, frame);
    },
    isBeatAtCurrentFrame(): boolean {
      const frame = this.getActiveComp()?.currentFrame ?? 0;
      return useAudioStore().isBeatAtFrame(frame);
    },
    convertAudioToKeyframes(
      options: {
        name?: string;
        amplitudeScale?: number;
        smoothing?: number;
      } = {},
    ) {
      return useAudioKeyframeStore().convertAudioToKeyframes(this, options);
    },
    getAudioAmplitudeAtFrame(
      channel: "both" | "left" | "right",
      frame: number,
    ): number {
      return useAudioKeyframeStore().getAudioAmplitudeAtFrame(this, channel, frame);
    },
    convertFrequencyBandsToKeyframes(
      options: {
        name?: string;
        scale?: number;
        smoothing?: number;
        bands?: FrequencyBandName[];
      } = {},
    ) {
      return useAudioKeyframeStore().convertFrequencyBandsToKeyframes(this, options);
    },
    convertAllAudioFeaturesToKeyframes(
      options: { name?: string; scale?: number; smoothing?: number } = {},
    ) {
      return useAudioKeyframeStore().convertAllAudioFeaturesToKeyframes(this, options);
    },
    getFrequencyBandAtFrame(
      band: FrequencyBandName,
      frame: number,
    ): number {
      return useAudioKeyframeStore().getFrequencyBandAtFrame(this, band, frame);
    },

    // Timeline snapping (delegated to animationStore)
    findSnapPoint(
      frame: number,
      pixelsPerFrame: number,
      selectedLayerId?: string | null,
    ): SnapResult | null {
      return useAnimationStore().findSnapPoint(this, frame, pixelsPerFrame, selectedLayerId);
    },
    getAudioBeatFrames(): number[] {
      return getBeatFrames(useAudioStore().audioAnalysis);
    },
    getAudioPeakFrames(): number[] {
      return getPeakFrames(useAudioStore().peakData);
    },
    setSnapConfig(config: Partial<SnapConfig>): void {
      useAnimationStore().setSnapConfig(config);
    },
    toggleSnapping(): void {
      useAnimationStore().toggleSnapping();
    },
    toggleSnapType(
      type:
        | "grid"
        | "keyframes"
        | "beats"
        | "peaks"
        | "layerBounds"
        | "playhead",
    ): void {
      useAnimationStore().toggleSnapType(type);
    },

    // Path animator (delegated to audioKeyframeStore)
    createPathAnimator(
      layerId: string,
      config: Partial<PathAnimatorConfig> = {},
    ): void {
      useAudioKeyframeStore().createPathAnimator(this, layerId, config);
    },
    setPathAnimatorPath(layerId: string, pathData: string): void {
      useAudioKeyframeStore().setPathAnimatorPath(this, layerId, pathData);
    },
    updatePathAnimatorConfig(
      layerId: string,
      config: Partial<PathAnimatorConfig>,
    ): void {
      useAudioKeyframeStore().updatePathAnimatorConfig(this, layerId, config);
    },
    removePathAnimator(layerId: string): void {
      useAudioKeyframeStore().removePathAnimator(this, layerId);
    },
    getPathAnimator(layerId: string): PathAnimatorAccess | undefined {
      return useAudioKeyframeStore().getPathAnimator(this, layerId);
    },
    updatePathAnimators(): void {
      useAudioKeyframeStore().updatePathAnimators(this);
    },
    resetPathAnimators(): void {
      useAudioKeyframeStore().resetPathAnimators(this);
    },
    initializeAudioReactiveMapper(): void {
      useAudioStore().initializeReactiveMapper();
    },

    // ============================================================
    // TIMELINE MARKERS (delegated to markerStore)
    // ============================================================

    addMarker(
      marker: Omit<import("@/types/project").Marker, "id"> & { id?: string },
    ): import("@/types/project").Marker | null {
      return useMarkerStore().addMarker(this, marker);
    },
    removeMarker(markerId: string): boolean {
      return useMarkerStore().removeMarker(this, markerId);
    },
    removeMarkerAtFrame(frame: number): boolean {
      return useMarkerStore().removeMarkerAtFrame(this, frame);
    },
    updateMarker(
      markerId: string,
      updates: Partial<Omit<import("@/types/project").Marker, "id">>,
    ): boolean {
      return useMarkerStore().updateMarker(this, markerId, updates);
    },
    clearMarkers(): void {
      useMarkerStore().clearMarkers(this);
    },
    getMarkers(): import("@/types/project").Marker[] {
      return useMarkerStore().getMarkers(this);
    },
    getMarker(markerId: string): import("@/types/project").Marker | null {
      return useMarkerStore().getMarker(this, markerId);
    },
    getMarkerAtFrame(frame: number): import("@/types/project").Marker | null {
      return useMarkerStore().getMarkerAtFrame(this, frame);
    },
    getMarkersInRange(
      startFrame: number,
      endFrame: number,
    ): import("@/types/project").Marker[] {
      return useMarkerStore().getMarkersInRange(this, startFrame, endFrame);
    },
    getNextMarker(frame: number): import("@/types/project").Marker | null {
      return useMarkerStore().getNextMarker(this, frame);
    },
    getPreviousMarker(frame: number): import("@/types/project").Marker | null {
      return useMarkerStore().getPreviousMarker(this, frame);
    },
    jumpToNextMarker(): void {
      useMarkerStore().jumpToNextMarker(this);
    },
    jumpToPreviousMarker(): void {
      useMarkerStore().jumpToPreviousMarker(this);
    },
    addMarkers(
      markers: Array<Omit<import("@/types/project").Marker, "id">>,
    ): import("@/types/project").Marker[] {
      return useMarkerStore().addMarkers(this, markers);
    },
    removeMarkersByColor(color: string): number {
      return useMarkerStore().removeMarkersByColor(this, color);
    },

    // ============================================================
    // PROPERTY DRIVER SYSTEM (delegated to expressionStore)
    // ============================================================

    initializePropertyDriverSystem(): void {
      useExpressionStore().initializePropertyDriverSystem(this);
    },
    // Evaluates property at frame, using composition's fps and duration for expressions
    getPropertyValueAtFrame(
      layerId: string,
      propertyPath: string,
      frame: number,
    ): number | null {
      return useKeyframeStore().getPropertyValueAtFrame(
        this,
        layerId,
        propertyPath,
        frame,
      );
    },

    /**
     * Evaluate a property at a specific frame and return the full value
     * Returns the interpolated value as an array for position/scale/origin types,
     * or a single value for scalar types (rotation, opacity)
     *
     * Used by MotionPathOverlay to get full position values for path rendering
     */
    evaluatePropertyAtFrame(
      layerId: string,
      propertyPath: string,
      frame: number,
    ): number[] | number | null {
      return useKeyframeStore().evaluatePropertyAtFrame(
        this,
        layerId,
        propertyPath,
        frame,
      );
    },

    getDrivenValuesForLayer(layerId: string): Map<PropertyPath, number> {
      return useExpressionStore().getEvaluatedLayerProperties(
        this,
        layerId,
        this.getActiveComp()?.currentFrame ?? 0,
      );
    },
    addPropertyDriver(driver: PropertyDriver): boolean {
      return useExpressionStore().addPropertyDriver(this, driver);
    },
    createAudioPropertyDriver(
      targetLayerId: string,
      targetProperty: PropertyPath,
      audioFeature: "amplitude" | "bass" | "mid" | "high" | "rms",
      options: {
        threshold?: number;
        scale?: number;
        offset?: number;
        smoothing?: number;
      } = {},
    ): PropertyDriver {
      return useExpressionStore().createAudioPropertyDriver(
        this,
        targetLayerId,
        targetProperty,
        audioFeature,
        options,
      );
    },
    createPropertyLink(
      targetLayerId: string,
      targetProperty: PropertyPath,
      sourceLayerId: string,
      sourceProperty: PropertyPath,
      options: {
        scale?: number;
        offset?: number;
        blendMode?: "replace" | "add" | "multiply";
      } = {},
    ): PropertyDriver | null {
      return useExpressionStore().createPropertyLinkDriver(
        this,
        targetLayerId,
        targetProperty,
        sourceLayerId,
        sourceProperty,
        options,
      );
    },
    removePropertyDriver(driverId: string): void {
      useExpressionStore().removePropertyDriver(this, driverId);
    },
    updatePropertyDriver(
      driverId: string,
      updates: Partial<PropertyDriver>,
    ): void {
      useExpressionStore().updatePropertyDriver(this, driverId, updates);
    },
    getDriversForLayer(layerId: string): PropertyDriver[] {
      return useExpressionStore().getDriversForLayer(this, layerId);
    },
    togglePropertyDriver(driverId: string): void {
      useExpressionStore().togglePropertyDriver(this, driverId);
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
      storeLogger.debug("Reset particle simulation for layer:", layerId);
    },

    /**
     * Clear all particle simulations
     * Called on project load/new
     */
    clearAllParticleSimulations(): void {
      particleSimulationRegistry.clear();
      storeLogger.debug("Cleared all particle simulations");
    },

    /**
     * Get particle snapshot for a layer at a specific frame
     * Evaluates the frame state to get the deterministic snapshot
     */
    getParticleSnapshot(
      layerId: string,
      frame?: number,
    ): ParticleSnapshot | null {
      const frameState = this.getFrameState(frame);
      return frameState.particleSnapshots[layerId] ?? null;
    },

    /**
     * Get all particle snapshots from current frame
     */
    getAllParticleSnapshots(
      frame?: number,
    ): Readonly<Record<string, ParticleSnapshot>> {
      const frameState = this.getFrameState(frame);
      return frameState.particleSnapshots;
    },

    // ============================================================
    // AUTOSAVE/PROJECT ACTIONS (delegated to projectStore)
    // ============================================================

    enableAutosave(intervalMs?: number): void {
      useProjectStore().configureAutosave(
        this,
        { enabled: true, intervalMs },
        () => this.performAutosave(),
      );
    },
    disableAutosave(): void {
      useProjectStore().stopAutosave(this);
      this.autosaveEnabled = false;
    },
    startAutosaveTimer(): void {
      useProjectStore().startAutosave(this, () => this.performAutosave());
    },
    stopAutosaveTimer(): void {
      useProjectStore().stopAutosave(this);
    },
    async performAutosave(): Promise<void> {
      return useProjectStore().performAutosave(this);
    },
    markUnsavedChanges(): void {
      useProjectStore().markUnsavedChanges(this);
      this.invalidateFrameCache();
    },
    async saveProjectToBackend(): Promise<string> {
      const result = await useProjectStore().saveProjectToServer(this);
      if (!result) throw new Error("Save failed");
      return result;
    },
    async loadProjectFromBackend(projectId: string): Promise<void> {
      const success = await useProjectStore().loadProjectFromServer(
        this,
        projectId,
        () => this.pushHistory(),
      );
      if (!success) throw new Error("Load failed");
    },
    async listSavedProjects(): Promise<
      Array<{ id: string; name: string; modified?: string }>
    > {
      return useProjectStore().listServerProjects();
    },

    // ============================================================
    // FRAME CACHE ACTIONS (delegated to cacheStore)
    // ============================================================

    async initializeFrameCache(): Promise<void> {
      return useCacheStore().initializeCache(this);
    },
    setFrameCacheEnabled(enabled: boolean): void {
      useCacheStore().setFrameCacheEnabled(this, enabled);
    },
    getCachedFrame(frame: number): ImageData | null {
      return useCacheStore().getCachedFrame(this, frame);
    },
    async cacheFrame(frame: number, imageData: ImageData): Promise<void> {
      return useCacheStore().cacheFrame(this, frame, imageData);
    },
    isFrameCached(frame: number): boolean {
      return useCacheStore().isFrameCached(this, frame);
    },
    async startPreCache(
      currentFrame: number,
      direction: "forward" | "backward" | "both" = "both",
    ): Promise<void> {
      return useCacheStore().startPreCache(this, currentFrame, direction);
    },
    invalidateFrameCache(): void {
      useCacheStore().invalidateFrameCache(this);
    },
    clearFrameCache(): void {
      useCacheStore().clearFrameCache();
    },
    getFrameCacheStats(): CacheStats {
      return useCacheStore().getFrameCacheStats();
    },
    computeProjectHash(): string {
      return useCacheStore().computeProjectHash(this);
    },

    // ============================================================
    // UI STATE ACTIONS (timeline, asset selection)
    // ============================================================

    /**
     * Set timeline zoom level
     */
    setTimelineZoom(zoom: number): void {
      useAnimationStore().setTimelineZoom(zoom);
    },

    /**
     * Select an asset by ID
     */
    selectAsset(assetId: string | null): void {
      useProjectStore().selectAsset(this, assetId);
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
      return useKeyframeStore().timeReverseKeyframes(this, layerId, propertyPath);
    },

    /**
     * Scale keyframe timing around an anchor frame
     * @param layerId The layer ID
     * @param propertyPath Optional specific property, otherwise scales all transform properties
     * @param scaleFactor Scale factor (0.5 = double speed, 2.0 = half speed)
     * @param anchorFrame The frame to anchor scaling around (default: 0)
     * @returns Number of keyframes scaled
     */
    scaleKeyframeTiming(
      layerId: string,
      propertyPath: string | undefined,
      scaleFactor: number,
      anchorFrame: number = 0,
    ): number {
      return useKeyframeStore().scaleKeyframeTiming(
        this,
        layerId,
        propertyPath,
        scaleFactor,
        anchorFrame,
      );
    },

    /**
     * Apply roving keyframes to position property
     * Roving automatically adjusts keyframe timing based on spatial distance
     * so motion appears at constant speed between keyframes.
     * @param layerId The layer ID
     * @returns True if roving was applied successfully
     */
    applyRovingToPosition(layerId: string): boolean {
      return useKeyframeStore().applyRovingToPosition(this, layerId);
    },

    /**
     * Check if roving would have any impact on a layer's position keyframes
     * @param layerId The layer ID
     * @returns True if roving would modify keyframe timing
     */
    checkRovingImpact(layerId: string): boolean {
      return useKeyframeStore().checkRovingImpact(this, layerId);
    },

    /**
     * Clear all keyframes from a property (single undo entry)
     * @param layerId The layer ID
     * @param propertyPath Path to the property (e.g., 'transform.position')
     */
    clearKeyframes(layerId: string, propertyPath: string): void {
      useKeyframeStore().clearKeyframes(this, layerId, propertyPath);
    },

    /**
     * Apply velocity settings to a keyframe
     */
    applyKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      settings: VelocitySettings,
    ): boolean {
      return useKeyframeStore().applyKeyframeVelocity(
        this,
        layerId,
        propertyPath,
        keyframeId,
        settings,
      );
    },

    /**
     * Get velocity settings from a keyframe
     */
    getKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): VelocitySettings | null {
      return useKeyframeStore().getKeyframeVelocity(
        this,
        layerId,
        propertyPath,
        keyframeId,
      );
    },

    /**
     * Convert expression to keyframes (bake expression)
     */
    convertExpressionToKeyframes(
      layerId: string,
      propertyPath: string,
      startFrame?: number,
      endFrame?: number,
      sampleRate?: number,
    ): number {
      return useExpressionStore().convertExpressionToKeyframes(
        this,
        layerId,
        propertyPath,
        startFrame,
        endFrame,
        sampleRate,
      );
    },

    /**
     * Check if a property has a bakeable expression
     */
    canBakeExpression(layerId: string, propertyPath: string): boolean {
      return useExpressionStore().canBakeExpression(this, layerId, propertyPath);
    },

    /**
     * Get all keyframe frames for a layer across all animated properties
     * @param layerId The layer ID
     * @returns Sorted array of unique frame numbers where keyframes exist
     */
    getAllKeyframeFrames(layerId: string): number[] {
      return useKeyframeStore().getAllKeyframeFrames(this, layerId);
    },

    /**
     * Jump to the next keyframe (K key behavior)
     * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
     */
    jumpToNextKeyframe(layerId?: string): void {
      useAnimationStore().jumpToNextKeyframe(this, layerId);
    },

    /**
     * Jump to the previous keyframe (J key behavior)
     * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
     */
    jumpToPrevKeyframe(layerId?: string): void {
      useAnimationStore().jumpToPrevKeyframe(this, layerId);
    },

    /**
     * Copy keyframes to clipboard
     * @param keyframeSelections Array of keyframe selections with layerId, propertyPath, and keyframeId
     * @returns Number of keyframes copied
     */
    copyKeyframes(
      keyframeSelections: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
    ): number {
      return useKeyframeStore().copyKeyframes(this, keyframeSelections);
    },

    /**
     * Paste keyframes from clipboard to a target layer/property
     * @param targetLayerId Target layer ID to paste to
     * @param targetPropertyPath Optional target property path (uses original if not specified)
     * @returns Array of newly created keyframes
     */
    pasteKeyframes(
      targetLayerId: string,
      targetPropertyPath?: string,
    ): Keyframe<any>[] {
      return useKeyframeStore().pasteKeyframes(
        this,
        targetLayerId,
        targetPropertyPath,
      );
    },

    /**
     * Check if clipboard has keyframes
     */
    hasKeyframesInClipboard(): boolean {
      return this.clipboard.keyframes.length > 0;
    },

    // ============================================================
    // EXPRESSION METHODS (delegated to expressionStore)
    // ============================================================

    /**
     * Set a property expression
     */
    setPropertyExpression(
      layerId: string,
      propertyPath: string,
      expression: import("@/types/animation").PropertyExpression,
    ): boolean {
      return useExpressionStore().setPropertyExpression(
        this,
        layerId,
        propertyPath,
        expression,
      );
    },

    /**
     * Enable expression on a property
     */
    enablePropertyExpression(
      layerId: string,
      propertyPath: string,
      expressionName: string = "custom",
      params: Record<string, number | string | boolean> = {},
    ): boolean {
      return useExpressionStore().enablePropertyExpression(
        this,
        layerId,
        propertyPath,
        expressionName,
        params,
      );
    },

    /**
     * Disable expression on a property
     */
    disablePropertyExpression(layerId: string, propertyPath: string): boolean {
      return useExpressionStore().disablePropertyExpression(
        this,
        layerId,
        propertyPath,
      );
    },

    /**
     * Toggle expression enabled state
     */
    togglePropertyExpression(layerId: string, propertyPath: string): boolean {
      return useExpressionStore().togglePropertyExpression(
        this,
        layerId,
        propertyPath,
      );
    },

    /**
     * Remove expression from property
     */
    removePropertyExpression(layerId: string, propertyPath: string): boolean {
      return useExpressionStore().removePropertyExpression(
        this,
        layerId,
        propertyPath,
      );
    },

    /**
     * Get expression for a property
     */
    getPropertyExpression(
      layerId: string,
      propertyPath: string,
    ): import("@/types/animation").PropertyExpression | undefined {
      return useExpressionStore().getPropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Check if property has an expression
     */
    hasPropertyExpression(layerId: string, propertyPath: string): boolean {
      return useExpressionStore().hasPropertyExpression(this, layerId, propertyPath);
    },

    /**
     * Update expression parameters
     */
    updateExpressionParams(
      layerId: string,
      propertyPath: string,
      params: Record<string, number | string | boolean>,
    ): boolean {
      return useExpressionStore().updateExpressionParams(
        this,
        layerId,
        propertyPath,
        params,
      );
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
      },
    ): void {
      return useLayerStore().updateLayerTransform(this, layerId, updates);
    },
  },
});
