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
  WeylProject,
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
  InterpolationType
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
import * as keyframeActions from './actions/keyframeActions';
import * as projectActions from './actions/projectActions';
import * as audioActions from './actions/audioActions';
import * as propertyDriverActions from './actions/propertyDriverActions';
import * as cacheActions from './actions/cacheActions';
import * as cameraActions from './actions/cameraActions';
import * as segmentationActions from './actions/segmentationActions';
import * as effectActions from './actions/effectActions';

// Domain-specific stores (for delegation)
import { usePlaybackStore } from './playbackStore';
import { useAudioStore } from './audioStore';
import { useSelectionStore } from './selectionStore';

interface CompositorState {
  // Project data
  project: WeylProject;

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
  historyStack: WeylProject[];
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
    keyframes: { layerId: string; propertyPath: string; keyframes: Keyframe<any>[] }[];
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
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => {
    // Create initial project and pre-populate history with it
    // This ensures undo works for the very first action
    const initialProject = createEmptyProject(832, 480);  // Wan 2.1 480p default
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
    projectStateHash: ''
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
    // COMPOSITION MANAGEMENT
    // ============================================================

    /**
     * Create a new composition
     */
    createComposition(
      name: string,
      settings?: Partial<CompositionSettings>,
      isNestedComp: boolean = false
    ): Composition {
      const id = `comp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

      // Get settings from active comp or use defaults
      const activeComp = this.project.compositions[this.activeCompositionId];
      const defaultSettings: CompositionSettings = {
        width: settings?.width ?? activeComp?.settings.width ?? 1024,
        height: settings?.height ?? activeComp?.settings.height ?? 1024,
        frameCount: settings?.frameCount ?? activeComp?.settings.frameCount ?? 81,
        fps: settings?.fps ?? activeComp?.settings.fps ?? 16,
        duration: 0,
        backgroundColor: settings?.backgroundColor ?? '#050505',
        autoResizeToContent: settings?.autoResizeToContent ?? true
      };
      defaultSettings.duration = defaultSettings.frameCount / defaultSettings.fps;

      const composition: Composition = {
        id,
        name,
        settings: defaultSettings,
        layers: [],
        currentFrame: 0,
        isNestedComp
      };

      this.project.compositions[id] = composition;

      // Open and switch to new composition
      if (!this.openCompositionIds.includes(id)) {
        this.openCompositionIds.push(id);
      }
      this.activeCompositionId = id;

      storeLogger.debug('Created composition:', name, id);
      return composition;
    },

    /**
     * Delete a composition
     */
    deleteComposition(compId: string): boolean {
      // Can't delete main composition
      if (compId === this.project.mainCompositionId) {
        storeLogger.warn('Cannot delete main composition');
        return false;
      }

      const comp = this.project.compositions[compId];
      if (!comp) return false;

      // Remove from compositions
      delete this.project.compositions[compId];

      // Remove from open tabs
      const openIdx = this.openCompositionIds.indexOf(compId);
      if (openIdx >= 0) {
        this.openCompositionIds.splice(openIdx, 1);
      }

      // If this was active, switch to another
      if (this.activeCompositionId === compId) {
        this.activeCompositionId = this.openCompositionIds[0] || this.project.mainCompositionId;
      }

      storeLogger.debug('Deleted composition:', compId);
      return true;
    },

    /**
     * Switch to a different composition (tab)
     */
    switchComposition(compId: string): void {
      if (!this.project.compositions[compId]) {
        storeLogger.warn('Composition not found:', compId);
        return;
      }

      // Add to open tabs if not already
      if (!this.openCompositionIds.includes(compId)) {
        this.openCompositionIds.push(compId);
      }

      // Clear selection when switching
      const selection = useSelectionStore();
      selection.clearLayerSelection();
      selection.clearKeyframeSelection();

      this.activeCompositionId = compId;
      storeLogger.debug('Switched to composition:', compId);
    },

    /**
     * Close a composition tab
     */
    closeCompositionTab(compId: string): void {
      // Can't close if it's the only open tab
      if (this.openCompositionIds.length <= 1) {
        storeLogger.warn('Cannot close the last tab');
        return;
      }

      const idx = this.openCompositionIds.indexOf(compId);
      if (idx >= 0) {
        this.openCompositionIds.splice(idx, 1);
      }

      // If closing active, switch to another
      if (this.activeCompositionId === compId) {
        this.activeCompositionId = this.openCompositionIds[Math.max(0, idx - 1)];
      }
    },

    /**
     * Enter a nested comp (e.g., double-click on nested comp layer)
     * Pushes the composition to the breadcrumb trail
     */
    enterNestedComp(compId: string): void {
      if (!this.project.compositions[compId]) {
        storeLogger.warn('Nested comp not found:', compId);
        return;
      }

      // Add to breadcrumb trail
      this.compositionBreadcrumbs.push(compId);

      // Switch to the composition
      this.switchComposition(compId);

      storeLogger.debug('Entered nested comp:', compId, 'breadcrumbs:', this.compositionBreadcrumbs);
    },

    /**
     * Navigate back one level in the breadcrumb trail
     */
    navigateBack(): void {
      if (this.compositionBreadcrumbs.length <= 1) {
        storeLogger.warn('Already at root composition');
        return;
      }

      // Pop current and switch to previous
      this.compositionBreadcrumbs.pop();
      const prevId = this.compositionBreadcrumbs[this.compositionBreadcrumbs.length - 1];

      if (prevId) {
        this.switchComposition(prevId);
      }

      storeLogger.debug('Navigated back, breadcrumbs:', this.compositionBreadcrumbs);
    },

    /**
     * Navigate to a specific breadcrumb index
     * Truncates the breadcrumb trail to that point
     */
    navigateToBreadcrumb(index: number): void {
      if (index < 0 || index >= this.compositionBreadcrumbs.length) {
        return;
      }

      // Already at this breadcrumb
      if (index === this.compositionBreadcrumbs.length - 1) {
        return;
      }

      // Truncate to the selected index
      this.compositionBreadcrumbs = this.compositionBreadcrumbs.slice(0, index + 1);
      const targetId = this.compositionBreadcrumbs[index];

      if (targetId) {
        this.switchComposition(targetId);
      }

      storeLogger.debug('Navigated to breadcrumb', index, 'breadcrumbs:', this.compositionBreadcrumbs);
    },

    /**
     * Reset breadcrumbs to main composition (e.g., when loading a new project)
     */
    resetBreadcrumbs(): void {
      this.compositionBreadcrumbs = [this.project.mainCompositionId];
      this.switchComposition(this.project.mainCompositionId);
    },

    /**
     * Rename a composition
     */
    renameComposition(compId: string, newName: string): void {
      const comp = this.project.compositions[compId];
      if (comp) {
        comp.name = newName;
      }
    },

    /**
     * Update composition settings
     */
    updateCompositionSettings(compId: string, settings: Partial<CompositionSettings>): void {
      const comp = this.project.compositions[compId];
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      // Update settings
      Object.assign(comp.settings, settings);

      // Recalculate duration
      comp.settings.duration = comp.settings.frameCount / comp.settings.fps;

      // Extend layer outPoints if frameCount increased
      if (settings.frameCount && settings.frameCount > oldFrameCount) {
        for (const layer of comp.layers) {
          if (layer.outPoint === oldFrameCount - 1) {
            layer.outPoint = settings.frameCount - 1;
          }
        }
      }

      // Keep legacy alias in sync for main comp
      if (compId === this.project.mainCompositionId) {
        Object.assign(this.project.composition, comp.settings);
      }
    },

    /**
     * Get a composition by ID
     */
    getComposition(compId: string): Composition | null {
      return this.project.compositions[compId] || null;
    },

    /**
     * Nest selected layers into a new composition
     */
    nestSelectedLayers(name?: string): Composition | null {
      if (this.selectedLayerIds.length === 0) {
        storeLogger.warn('No layers selected for nesting');
        return null;
      }

      const activeComp = this.project.compositions[this.activeCompositionId];
      if (!activeComp) return null;

      // Create new composition with same settings
      const nestedComp = this.createComposition(
        name || 'Nested Comp',
        activeComp.settings,
        true
      );

      // Move selected layers to nested comp
      const selectedLayers = activeComp.layers.filter(l =>
        this.selectedLayerIds.includes(l.id)
      );

      // Find earliest startFrame to normalize timing
      const earliestIn = Math.min(...selectedLayers.map(l => l.startFrame ?? l.inPoint ?? 0));

      // Move layers to nested comp and adjust timing
      for (const layer of selectedLayers) {
        // Adjust timing relative to nested comp start (update both new and legacy properties)
        const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
        const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
        layer.startFrame = layerStart - earliestIn;
        layer.endFrame = layerEnd - earliestIn;
        layer.inPoint = layer.startFrame;
        layer.outPoint = layer.endFrame;

        // Remove from parent
        const idx = activeComp.layers.indexOf(layer);
        if (idx >= 0) {
          activeComp.layers.splice(idx, 1);
        }

        // Add to nested comp
        nestedComp.layers.push(layer);
      }

      // Update nested comp duration to fit layers
      const maxOut = Math.max(...nestedComp.layers.map(l => l.endFrame ?? l.outPoint ?? 80));
      nestedComp.settings.frameCount = maxOut + 1;
      nestedComp.settings.duration = nestedComp.settings.frameCount / nestedComp.settings.fps;

      // Create nested comp layer in parent composition
      const nestedEndFrame = earliestIn + nestedComp.settings.frameCount - 1;
      const nestedCompLayer: Layer = {
        id: `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        name: nestedComp.name,
        type: 'nestedComp',
        visible: true,
        locked: false,
        isolate: false,
        threeD: false,
        // Timing (primary properties)
        startFrame: earliestIn,
        endFrame: nestedEndFrame,
        // Backwards compatibility aliases
        inPoint: earliestIn,
        outPoint: nestedEndFrame,
        parentId: null,
        transform: createDefaultTransform(),
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        properties: [],
        effects: [],
        blendMode: 'normal',
        motionBlur: false,
        data: {
          compositionId: nestedComp.id,
          // Speed map (new naming)
          speedMapEnabled: false,
          // Backwards compatibility
          timeRemapEnabled: false,
          flattenTransform: false
        } as NestedCompData
      };

      activeComp.layers.push(nestedCompLayer);

      // Clear selection
      useSelectionStore().clearLayerSelection();

      // Switch back to parent composition
      this.activeCompositionId = activeComp.id;

      storeLogger.debug('Nested layers into:', nestedComp.name);
      return nestedComp;
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
      const id = `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

      // Initialize type-specific data
      let layerData: any = null;

      switch (type) {
        case 'text':
          layerData = {
            text: 'Text',
            fontFamily: 'Arial',
            fontSize: 72,
            fontWeight: '400',
            fontStyle: 'normal',
            fill: '#ffffff',
            stroke: '',
            strokeWidth: 0,
            tracking: 0,
            letterSpacing: 0,
            lineHeight: 1.2,
            textAlign: 'left',
            pathLayerId: null,
            pathReversed: false,
            pathPerpendicularToPath: true,
            pathForceAlignment: false,
            pathFirstMargin: 0,
            pathLastMargin: 0,
            pathOffset: 0,
            pathAlign: 'left'
          };
          break;

        case 'solid': {
          // Use active composition dimensions, not main project composition
          const activeComp = this.getActiveComp();
          layerData = {
            color: '#808080',
            width: activeComp?.settings.width || this.project.composition.width,
            height: activeComp?.settings.height || this.project.composition.height
          };
          break;
        }

        case 'null':
          layerData = {
            size: 40
          };
          break;

        case 'spline':
          layerData = {
            pathData: '',
            controlPoints: [],
            closed: false,
            stroke: '#00ff00',
            strokeWidth: 2,
            // Stroke options (shown in More Options group)
            lineCap: 'round',    // butt, round, square
            lineJoin: 'round',   // miter, round, bevel
            dashArray: '',       // e.g., "10, 5" for dashed lines
            dashOffset: 0
          };
          break;

        case 'particles': {
          // Get active composition dimensions for emitter positioning
          const activeComp = this.getActiveComp();
          const compWidth = activeComp?.settings.width || this.project.composition.width;
          const compHeight = activeComp?.settings.height || this.project.composition.height;

          layerData = {
            systemConfig: {
              maxParticles: 10000,
              gravity: 0,
              windStrength: 0,
              windDirection: 0,
              warmupPeriod: 0,
              respectMaskBoundary: false,
              boundaryBehavior: 'kill',
              friction: 0.01
            },
            emitters: [{
              id: 'emitter_1',
              name: 'Emitter 1',
              // Use pixel coordinates - center of composition
              x: compWidth / 2,
              y: compHeight / 2,
              direction: 270, // Up direction (degrees, 270 = upward)
              spread: 30,
              speed: 150, // Pixels per second
              speedVariance: 30,
              size: 8,
              sizeVariance: 2,
              color: [255, 200, 100] as [number, number, number], // Orange-ish for visibility
              emissionRate: 30, // Particles per second
              initialBurst: 0,
              particleLifetime: 90, // Frames
              lifetimeVariance: 15,
              enabled: true,
              burstOnBeat: false,
              burstCount: 20,
              // Geometric emitter shape defaults
              shape: 'point' as const,
              shapeRadius: 50,
              shapeWidth: 100,
              shapeHeight: 100,
              shapeDepth: 100,
              shapeInnerRadius: 25,
              emitFromEdge: false,
              emitFromVolume: false,
              splinePath: null,
              sprite: {
                enabled: false,
                imageUrl: null,
                imageData: null,
                isSheet: false,
                columns: 1,
                rows: 1,
                totalFrames: 1,
                frameRate: 30,
                playMode: 'loop' as const,
                billboard: true,
                rotationEnabled: false,
                rotationSpeed: 0,
                rotationSpeedVariance: 0,
                alignToVelocity: false
              }
            }],
            gravityWells: [],
            vortices: [],
            modulations: [{
              id: 'mod_opacity_1',
              emitterId: '*',
              property: 'opacity',
              startValue: 1,
              endValue: 0,
              easing: 'linear'
            }],
            renderOptions: {
              blendMode: 'additive',
              renderTrails: false,
              trailLength: 5,
              trailOpacityFalloff: 0.7,
              particleShape: 'circle',
              glowEnabled: true,
              glowRadius: 8,
              glowIntensity: 0.6,
              motionBlur: false,
              motionBlurStrength: 0.5,
              motionBlurSamples: 8,
              connections: {
                enabled: false,
                maxDistance: 100,
                maxConnections: 3,
                lineWidth: 1,
                lineOpacity: 0.5,
                fadeByDistance: true
              }
            },
            turbulenceFields: [],
            subEmitters: []
          };
          break;
        }

        case 'depthflow':
          layerData = {
            sourceLayerId: null,
            depthLayerId: null,
            config: {
              preset: 'static',
              zoom: 1,
              offsetX: 0,
              offsetY: 0,
              rotation: 0,
              depthScale: 1,
              focusDepth: 0.5,
              dollyZoom: 0,
              orbitRadius: 0,
              orbitSpeed: 1,
              swingAmplitude: 0,
              swingFrequency: 1,
              edgeDilation: 0,
              inpaintEdges: false
            }
          };
          break;

        case 'light':
          layerData = {
            lightType: 'point',
            color: '#ffffff',
            intensity: 100,
            radius: 500,
            falloff: 'none',
            falloffDistance: 500,
            castShadows: false,
            shadowDarkness: 100,
            shadowDiffusion: 0
          };
          break;

        case 'camera':
          // Camera layers are created via createCameraLayer(), but handle here too
          layerData = {
            cameraId: null,
            isActiveCamera: false
          };
          break;

        case 'image':
          layerData = {
            assetId: null,
            fit: 'contain'
          };
          break;

        case 'video':
          layerData = {
            assetId: null,
            loop: false,
            startTime: 0,
            speed: 1.0
          };
          break;

        case 'shape':
          layerData = {
            contents: [],
            blendMode: 'normal',
            quality: 'normal',
            gpuAccelerated: false
          };
          break;

        case 'adjustment':
          // Adjustment/Effect layer - applies effects to layers below
          layerData = {
            color: '#808080',
            effectLayer: true,
            adjustmentLayer: true  // Backwards compatibility
          };
          break;

        case 'group':
          // Layer group/folder
          layerData = {
            collapsed: false,
            color: null,
            passThrough: true,
            isolate: false
          };
          break;
      }

      // Initialize audio props for video/audio layers
      let audioProps = undefined;
      if (type === 'video' || type === 'audio') {
        audioProps = {
          level: createAnimatableProperty('Audio Levels', 0, 'number') // 0dB default
        };
      }

      const comp = this.getActiveComp();
      const layers = this.getActiveCompLayers();

      // Get composition dimensions for centering
      const compWidth = comp?.settings.width || this.project.composition.width;
      const compHeight = comp?.settings.height || this.project.composition.height;

      // Create transform with layer centered in composition
      const layerTransform = createDefaultTransform();

      // Set position to composition center
      // Anchor point should be at layer's own origin (0,0 for text/shapes, layer center for solids)
      layerTransform.position.value = { x: compWidth / 2, y: compHeight / 2, z: 0 };

      // Use origin (new name) for the transform pivot point
      const originProp = layerTransform.origin || layerTransform.anchorPoint;
      if (type === 'solid' && layerData) {
        // Solid layers: origin at layer's own center
        const layerWidth = layerData.width || compWidth;
        const layerHeight = layerData.height || compHeight;
        if (originProp) originProp.value = { x: layerWidth / 2, y: layerHeight / 2, z: 0 };
      } else {
        // Text, shape, spline, particles, image, video, etc.: origin at (0,0)
        // Position directly controls where the layer's origin appears in composition
        if (originProp) originProp.value = { x: 0, y: 0, z: 0 };
      }

      // Initialize layer-specific properties
      let layerProperties: AnimatableProperty<any>[] = [];

      // Spline layer properties for timeline
      // Note: Splines don't have Fill (only shapes/text do) - they only have stroke
      if (type === 'spline') {
        layerProperties = [
          createAnimatableProperty('Stroke Width', layerData?.strokeWidth ?? 2, 'number', 'Stroke'),
          createAnimatableProperty('Stroke Opacity', layerData?.strokeOpacity ?? 100, 'number', 'Stroke'),
          // Line Cap, Line Join, Dashes are stored in layer.data and shown in More Options
          createAnimatableProperty('Trim Start', 0, 'number', 'Trim Paths'),
          createAnimatableProperty('Trim End', 100, 'number', 'Trim Paths'),
          createAnimatableProperty('Trim Offset', 0, 'number', 'Trim Paths'),
          // Note: "Closed" is stored in layer.data.closed as a boolean, not animatable
          // It's displayed in the timeline via the Path Options group in EnhancedLayerTrack
        ];
      }

      const endFrameValue = (comp?.settings.frameCount || 81) - 1;
      const layer: Layer = {
        id,
        name: name || `${type.charAt(0).toUpperCase() + type.slice(1)} ${layers.length + 1}`,
        type,
        visible: true,
        locked: false,
        isolate: false,
        threeD: false,
        motionBlur: false,
        // Timing (primary properties)
        startFrame: 0,
        endFrame: endFrameValue,
        // Backwards compatibility aliases
        inPoint: 0,
        outPoint: endFrameValue,
        parentId: null,
        blendMode: 'normal',
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        transform: layerTransform,
        audio: audioProps,
        properties: layerProperties,
        effects: [],
        data: layerData
      };

      // Camera layers should use createCameraLayer() instead
      if (type === 'camera') {
        storeLogger.warn('Use createCameraLayer() for camera layers');
      }

      layers.unshift(layer);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      return layer;
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
     */
    updateLayerData(layerId: string, dataUpdates: Record<string, any>): void {
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
    replaceLayerSource(layerId: string, newSource: { type: string; name: string; path?: string; id?: string; data?: any }): void {
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
        fps: comp?.settings.fps ?? 30
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
        currentFrame: comp?.currentFrame ?? 0
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
    // PLAYBACK CONTROLS
    // ============================================================

    /**
     * Start playback
     * NOTE: This only updates UI state (currentFrame).
     * Actual frame evaluation happens via getFrameState().
     */
    play(): void {
      const playback = usePlaybackStore();
      if (playback.isPlaying) return;

      const comp = this.getActiveComp();
      if (!comp) return;

      // Delegate to playbackStore with callback to update frame
      playback.play(
        comp.settings.fps,
        comp.settings.frameCount,
        comp.currentFrame,
        (frame: number) => { comp.currentFrame = frame; }
      );

      // Sync state for backwards compatibility
      this.isPlaying = true;
    },

    /**
     * Pause playback
     */
    pause(): void {
      const playback = usePlaybackStore();
      playback.stop();
      this.isPlaying = false;
    },

    /**
     * Toggle playback state
     */
    togglePlayback(): void {
      const playback = usePlaybackStore();
      if (playback.isPlaying) {
        this.pause();
      } else {
        this.play();
      }
    },

    /**
     * Set current frame (UI state only)
     * Components watching currentFrame should call getFrameState() to evaluate.
     */
    setFrame(frame: number): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      comp.currentFrame = Math.max(0, Math.min(frame, comp.settings.frameCount - 1));
    },

    /**
     * Advance to next frame (UI state only)
     */
    nextFrame(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      if (comp.currentFrame < comp.settings.frameCount - 1) {
        comp.currentFrame++;
      }
    },

    /**
     * Go to previous frame (UI state only)
     */
    prevFrame(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      if (comp.currentFrame > 0) {
        comp.currentFrame--;
      }
    },

    /**
     * Jump to first frame (UI state only)
     */
    goToStart(): void {
      const comp = this.getActiveComp();
      if (comp) comp.currentFrame = 0;
    },

    /**
     * Jump to last frame (UI state only)
     */
    goToEnd(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      // Frame indices are 0-based, so last frame is frameCount - 1
      comp.currentFrame = comp.settings.frameCount - 1;
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

    importProject(json: string): void {
      projectActions.importProject(this, json, () => this.pushHistory());
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
     */
    getInterpolatedValue<T>(property: AnimatableProperty<T>): T {
      return interpolateProperty(property, (this.getActiveComp()?.currentFrame ?? 0));
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
    setPropertyValue(layerId: string, propertyPath: string, value: any): void {
      keyframeActions.setPropertyValue(this, layerId, propertyPath, value);
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
     * Update keyframe frame position and/or value
     */
    updateKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      updates: { frame?: number; value?: any }
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
     * Create a text layer with proper data structure
     */
    createTextLayer(text: string = 'Text'): Layer {
      const layer = this.createLayer('text', text.substring(0, 20));

      // Set up text data with full AE parity
      const textData: TextData = {
        text,
        fontFamily: 'Arial',
        fontSize: 72,
        fontWeight: '400',
        fontStyle: 'normal',
        fill: '#ffffff',
        stroke: '',
        strokeWidth: 0,

        // Character Properties (AE Animator defaults)
        tracking: 0,
        lineSpacing: 0,
        lineAnchor: 0,
        characterOffset: 0,
        characterValue: 0,
        blur: { x: 0, y: 0 },

        // Paragraph (legacy aliases)
        letterSpacing: 0,
        lineHeight: 1.2,
        textAlign: 'left',

        // Path Options (Full AE Parity)
        pathLayerId: null,
        pathReversed: false,
        pathPerpendicularToPath: true,
        pathForceAlignment: false,
        pathFirstMargin: 0,
        pathLastMargin: 0,
        pathOffset: 0,
        pathAlign: 'left',

        // More Options (AE Advanced)
        anchorPointGrouping: 'character',
        groupingAlignment: { x: 0, y: 0 },
        fillAndStroke: 'fill-over-stroke',
        interCharacterBlending: 'normal',

        // 3D Text
        perCharacter3D: false
      };

      layer.data = textData;

      // --- TEXT PROPERTIES (Timeline) ---

      // Text Section
      layer.properties.push(createAnimatableProperty('Font Size', 72, 'number', 'Text'));
      layer.properties.push(createAnimatableProperty('Fill Color', '#ffffff', 'color', 'Text'));
      layer.properties.push(createAnimatableProperty('Stroke Color', '#000000', 'color', 'Text'));
      layer.properties.push(createAnimatableProperty('Stroke Width', 0, 'number', 'Text'));

      // Path Options (Full AE Parity)
      layer.properties.push(createAnimatableProperty('Path Offset', 0, 'number', 'Path Options'));
      layer.properties.push(createAnimatableProperty('First Margin', 0, 'number', 'Path Options'));
      layer.properties.push(createAnimatableProperty('Last Margin', 0, 'number', 'Path Options'));

      // More Options
      // Grouping Alignment must be 'position' type for X/Y
      layer.properties.push(createAnimatableProperty('Grouping Alignment', { x: 0, y: 0 }, 'position', 'More Options'));

      // Advanced / Animators
      layer.properties.push(createAnimatableProperty('Tracking', 0, 'number', 'Advanced'));
      layer.properties.push(createAnimatableProperty('Line Spacing', 0, 'number', 'Advanced'));
      layer.properties.push(createAnimatableProperty('Character Offset', 0, 'number', 'Advanced'));
      layer.properties.push(createAnimatableProperty('Character Value', 0, 'number', 'Advanced'));
      layer.properties.push(createAnimatableProperty('Blur', { x: 0, y: 0 }, 'position', 'Advanced')); // 2D Blur

      return layer;
    },

    /**
     * Create a spline layer with proper data structure
     */
    createSplineLayer(): Layer {
      const layer = this.createLayer('spline');

      // Set up spline data
      const splineData: SplineData = {
        pathData: '',
        controlPoints: [],
        closed: false,
        stroke: '#00ff00',
        strokeWidth: 2,
        fill: ''
      };

      layer.data = splineData;

      return layer;
    },

    /**
     * Create a shape layer with proper data structure
     */
    createShapeLayer(name: string = 'Shape Layer'): Layer {
      const layer = this.createLayer('shape', name);

      // Shape layer data is already set by createLayer switch
      // Add any additional default properties here if needed

      return layer;
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
    // PARTICLE SYSTEM LAYER ACTIONS
    // ============================================================

    /**
     * Create a particle system layer
     */
    createParticleLayer(): Layer {
      const layer = this.createLayer('particles', 'Particle System');

      // Get active composition dimensions for emitter positioning
      const activeComp = this.getActiveComp();
      const compWidth = activeComp?.settings.width || this.project.composition.width;
      const compHeight = activeComp?.settings.height || this.project.composition.height;

      // Set up particle layer data
      const particleData: ParticleLayerData = {
        systemConfig: {
          maxParticles: 10000,
          gravity: 0,
          windStrength: 0,
          windDirection: 0,
          warmupPeriod: 0,
          respectMaskBoundary: false,
          boundaryBehavior: 'kill',
          friction: 0.01
        },
        emitters: [{
          id: `emitter_${Date.now()}`,
          name: 'Emitter 1',
          // Use pixel coordinates - center of composition
          x: compWidth / 2,
          y: compHeight / 2,
          direction: 270, // Up direction (270 degrees)
          spread: 30,
          speed: 150, // Pixels per second
          speedVariance: 30,
          size: 8,
          sizeVariance: 2,
          color: [255, 200, 100] as [number, number, number],
          emissionRate: 30, // Particles per second
          initialBurst: 0,
          particleLifetime: 90,
          lifetimeVariance: 15,
          enabled: true,
          burstOnBeat: false,
          burstCount: 20,
          // Geometric emitter shape defaults (in pixels)
          shape: 'point' as const,
          shapeRadius: 50,
          shapeWidth: 100,
          shapeHeight: 100,
          shapeDepth: 100,
          shapeInnerRadius: 25,
          emitFromEdge: false,
          emitFromVolume: false,
          // Spline path emission (null = disabled)
          splinePath: null,
          // Sprite configuration
          sprite: {
            enabled: false,
            imageUrl: null,
            imageData: null,
            isSheet: false,
            columns: 1,
            rows: 1,
            totalFrames: 1,
            frameRate: 30,
            playMode: 'loop' as const,
            billboard: true,
            rotationEnabled: false,
            rotationSpeed: 0,
            rotationSpeedVariance: 0,
            alignToVelocity: false
          }
        }],
        gravityWells: [],
        vortices: [],
        modulations: [{
          id: `mod_${Date.now()}`,
          emitterId: '*',
          property: 'opacity',
          startValue: 1,
          endValue: 0,
          easing: 'linear'
        }],
        renderOptions: {
          blendMode: 'additive',
          renderTrails: false,
          trailLength: 5,
          trailOpacityFalloff: 0.7,
          particleShape: 'circle',
          glowEnabled: false,
          glowRadius: 10,
          glowIntensity: 0.5,
          motionBlur: false,
          motionBlurStrength: 0.5,
          motionBlurSamples: 8,
          connections: {
            enabled: false,
            maxDistance: 100,
            maxConnections: 3,
            lineWidth: 1,
            lineOpacity: 0.5,
            fadeByDistance: true
          }
        },
        turbulenceFields: [],
        subEmitters: []
      };

      layer.data = particleData;

      return layer;
    },

    /**
     * Update particle layer data
     */
    updateParticleLayerData(layerId: string, updates: Partial<ParticleLayerData>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      Object.assign(data, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Add emitter to particle layer
     */
    addParticleEmitter(layerId: string, config: ParticleEmitterConfig): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      data.emitters.push(config);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Update particle emitter
     */
    updateParticleEmitter(layerId: string, emitterId: string, updates: Partial<ParticleEmitterConfig>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      const emitter = data.emitters.find(e => e.id === emitterId);
      if (emitter) {
        Object.assign(emitter, updates);
        this.project.meta.modified = new Date().toISOString();
      }
    },

    /**
     * Remove particle emitter
     */
    removeParticleEmitter(layerId: string, emitterId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      data.emitters = data.emitters.filter(e => e.id !== emitterId);
      this.project.meta.modified = new Date().toISOString();
    },

    // ============================================================
    // DEPTHFLOW LAYER ACTIONS
    // ============================================================

    /**
     * Create a depthflow parallax layer
     */
    createDepthflowLayer(sourceLayerId: string = '', depthLayerId: string = ''): Layer {
      const layer = this.createLayer('depthflow', 'Depthflow');

      // Set up depthflow layer data
      const depthflowData: DepthflowLayerData = {
        sourceLayerId,
        depthLayerId,
        config: {
          preset: 'zoom_in',
          zoom: 1.0,
          offsetX: 0,
          offsetY: 0,
          rotation: 0,
          depthScale: 1.0,
          focusDepth: 0.5,
          dollyZoom: 0,
          orbitRadius: 0.1,
          orbitSpeed: 360,
          swingAmplitude: 0.1,
          swingFrequency: 1,
          edgeDilation: 5,
          inpaintEdges: true
        },
        animatedZoom: createAnimatableProperty('zoom', 1.0, 'number'),
        animatedOffsetX: createAnimatableProperty('offsetX', 0, 'number'),
        animatedOffsetY: createAnimatableProperty('offsetY', 0, 'number'),
        animatedRotation: createAnimatableProperty('rotation', 0, 'number'),
        animatedDepthScale: createAnimatableProperty('depthScale', 1.0, 'number')
      };

      layer.data = depthflowData;

      return layer;
    },

    /**
     * Update depthflow config
     */
    updateDepthflowConfig(layerId: string, updates: Partial<DepthflowLayerData['config']>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'depthflow') return;

      const data = layer.data as DepthflowLayerData;
      Object.assign(data.config, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    // ============================================================
    // VIDEO LAYER ACTIONS
    // ============================================================

    /**
     * Create a video layer from a file
     * Automatically resizes composition to match video dimensions and duration
     *
     * @param file - Video file to import
     * @param autoResizeComposition - If true, resize composition to match video (default: true for first video)
     * @returns The created layer
     */
    async createVideoLayer(file: File, autoResizeComposition: boolean = true): Promise<Layer> {
      // First extract metadata to determine dimensions and duration
      let videoUrl: string;
      try {
        videoUrl = URL.createObjectURL(file);
      } catch {
        throw new Error('Failed to create URL for video file');
      }

      let metadata: VideoMetadata;
      try {
        metadata = await extractVideoMetadata(videoUrl);
      } catch (error) {
        URL.revokeObjectURL(videoUrl);
        throw new Error(`Failed to load video metadata: ${(error as Error).message}`);
      }

      // Create asset reference
      const assetId = `video_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
      const asset: AssetReference = {
        id: assetId,
        type: 'video',
        source: 'file',
        width: metadata.width,
        height: metadata.height,
        data: videoUrl,
        // Video-specific metadata
        duration: metadata.duration,
        frameCount: metadata.frameCount,
        fps: metadata.fps,
        hasAudio: metadata.hasAudio
      };

      this.project.assets[assetId] = asset;

      // Auto-resize composition if requested
      if (autoResizeComposition) {
        const compSettings = calculateCompositionFromVideo(metadata, this.project.composition.fps);

        storeLogger.debug('Auto-resizing composition for video:', {
          originalWidth: this.project.composition.width,
          originalHeight: this.project.composition.height,
          originalFrameCount: this.project.composition.frameCount,
          newWidth: compSettings.width,
          newHeight: compSettings.height,
          newFrameCount: compSettings.frameCount,
          videoDuration: metadata.duration
        });

        this.project.composition.width = compSettings.width;
        this.project.composition.height = compSettings.height;
        this.project.composition.frameCount = compSettings.frameCount;
        this.project.composition.duration = compSettings.frameCount / this.project.composition.fps;
      }

      // Create the layer
      const layer = this.createLayer('video', file.name.replace(/\.[^.]+$/, ''));

      // Set video data
      const videoData: VideoData = {
        assetId,
        loop: false,
        pingPong: false,
        startTime: 0,
        endTime: undefined,
        speed: 1,
        // Speed map (new naming)
        speedMapEnabled: false,
        speedMap: undefined,
        // Backwards compatibility
        timeRemapEnabled: false,
        timeRemap: undefined,
        frameBlending: 'none',
        audioEnabled: metadata.hasAudio,
        audioLevel: 100,
        posterFrame: 0
      };

      layer.data = videoData;

      // Set layer duration to match video (in frames)
      if (!autoResizeComposition) {
        // If not auto-resizing, set layer out point to video duration
        const videoFrameCount = Math.ceil(metadata.duration * this.project.composition.fps);
        layer.outPoint = Math.min(videoFrameCount - 1, this.project.composition.frameCount - 1);
      }

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      storeLogger.debug('Created video layer:', {
        layerId: layer.id,
        assetId,
        dimensions: `${metadata.width}x${metadata.height}`,
        duration: `${metadata.duration.toFixed(2)}s`,
        frameCount: metadata.frameCount,
        hasAudio: metadata.hasAudio
      });

      return layer;
    },

    /**
     * Update video layer data
     */
    updateVideoLayerData(layerId: string, updates: Partial<VideoData>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'video') return;

      const data = layer.data as VideoData;
      Object.assign(data, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Handle video metadata loaded callback from engine
     * Called by LayerManager when a video finishes loading
     */
    onVideoMetadataLoaded(layerId: string, metadata: VideoMetadata): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'video') return;

      const videoData = layer.data as VideoData;
      if (!videoData.assetId) return;

      // Update asset with accurate metadata
      const asset = this.project.assets[videoData.assetId];
      if (asset) {
        asset.width = metadata.width;
        asset.height = metadata.height;
        asset.duration = metadata.duration;
        asset.frameCount = metadata.frameCount;
        asset.fps = metadata.fps;
        asset.hasAudio = metadata.hasAudio;
      }

      storeLogger.debug('Video metadata loaded:', { layerId, metadata });
    },

    /**
     * Resize composition settings
     * Used for manual resize or when importing video
     */
    resizeComposition(width: number, height: number, frameCount?: number): void {
      const comp = this.getActiveComp();
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      comp.settings.width = width;
      comp.settings.height = height;

      // Keep legacy alias in sync
      this.project.composition.width = width;
      this.project.composition.height = height;

      if (frameCount !== undefined) {
        comp.settings.frameCount = frameCount;
        comp.settings.duration = frameCount / comp.settings.fps;

        // Keep legacy alias in sync
        this.project.composition.frameCount = frameCount;
        this.project.composition.duration = frameCount / this.project.composition.fps;

        // Extend layer outPoints if frameCount increased
        // Only extend layers that were at the old max frame
        if (frameCount > oldFrameCount) {
          for (const layer of comp.layers) {
            // If layer ended at the old composition end, extend it to new end
            if (layer.outPoint === oldFrameCount - 1) {
              layer.outPoint = frameCount - 1;
            }
          }
        }
      }

      // Update current frame if it's now out of bounds
      if (comp.currentFrame >= comp.settings.frameCount) {
        comp.currentFrame = comp.settings.frameCount - 1;
      }

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      storeLogger.debug('Composition resized:', {
        width,
        height,
        frameCount: comp.settings.frameCount
      });
    },

    // ============================================================
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
    updateEffectParameter(layerId: string, effectId: string, paramKey: string, value: any): void {
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
    getEffectParameterValue(layerId: string, effectId: string, paramKey: string, frame?: number): any {
      return effectActions.getEffectParameterValue(this, layerId, effectId, paramKey, frame);
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
      const typeMap: Record<string, keyof SnapConfig> = {
        'grid': 'snapToGrid', 'keyframes': 'snapToKeyframes', 'beats': 'snapToBeats',
        'peaks': 'snapToPeaks', 'layerBounds': 'snapToLayerBounds', 'playhead': 'snapToPlayhead',
      };
      const key = typeMap[type];
      if (key && typeof this.snapConfig[key] === 'boolean') {
        (this.snapConfig as any)[key] = !(this.snapConfig as any)[key];
      }
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
    getPropertyValueAtFrame(layerId: string, propertyPath: PropertyPath, frame: number): number | null {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return null;
      const parts = propertyPath.split('.');
      if (parts[0] === 'transform') {
        const t = layer.transform;
        if (parts[1] === 'position') {
          const p = interpolateProperty(t.position, frame);
          return parts[2] === 'x' ? p.x : parts[2] === 'y' ? p.y : (p.z ?? 0);
        }
        if (parts[1] === 'anchorPoint' || parts[1] === 'origin') {
          // Use origin (new name) with fallback to anchorPoint
          const originProp = t.origin || t.anchorPoint;
          if (!originProp) return 0;
          const a = interpolateProperty(originProp, frame);
          return parts[2] === 'x' ? a.x : parts[2] === 'y' ? a.y : (a.z ?? 0);
        }
        if (parts[1] === 'scale') {
          const s = interpolateProperty(t.scale, frame);
          return parts[2] === 'x' ? s.x : parts[2] === 'y' ? s.y : (s.z ?? 100);
        }
        if (parts[1] === 'rotation') return interpolateProperty(t.rotation, frame);
        if (parts[1] === 'rotationX' && t.rotationX) return interpolateProperty(t.rotationX, frame);
        if (parts[1] === 'rotationY' && t.rotationY) return interpolateProperty(t.rotationY, frame);
        if (parts[1] === 'rotationZ' && t.rotationZ) return interpolateProperty(t.rotationZ, frame);
      }
      return parts[0] === 'opacity' ? interpolateProperty(layer.opacity, frame) : null;
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
    }
  }
});
