/**
 * Main Compositor Store
 *
 * Manages project state, layers, playback, and ComfyUI communication.
 */
import { defineStore } from 'pinia';
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
  VideoData,
  PrecompData,
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
import { createEffectInstance } from '@/types/effects';
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

interface CompositorState {
  // Project data
  project: WeylProject;

  // Active composition (for multi-composition support)
  activeCompositionId: string;
  openCompositionIds: string[];  // Tabs - which comps are open

  // ComfyUI connection
  comfyuiNodeId: string | null;

  // Input data from ComfyUI
  sourceImage: string | null;
  depthMap: string | null;

  // Playback state
  isPlaying: boolean;
  playbackRequestId: number | null;
  playbackStartTime: number | null;
  playbackStartFrame: number;

  // Selection state
  selectedLayerIds: string[];
  selectedKeyframeIds: string[];
  selectedPropertyPath: string | null;  // e.g. "transform.position" for graph editor focus

  // Tool state
  currentTool: 'select' | 'pen' | 'text' | 'hand' | 'zoom';

  // UI state
  graphEditorVisible: boolean;

  // History for undo/redo
  historyStack: WeylProject[];
  historyIndex: number;

  // Audio state
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;

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
    keyframes: { layerId: string; propertyPath: string; keyframes: Keyframe[] }[];
  };
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => ({
    project: createEmptyProject(1024, 1024),
    activeCompositionId: 'main',
    openCompositionIds: ['main'],
    comfyuiNodeId: null,
    sourceImage: null,
    depthMap: null,
    isPlaying: false,
    playbackRequestId: null,
    playbackStartTime: null,
    playbackStartFrame: 0,
    selectedLayerIds: [],
    selectedKeyframeIds: [],
    selectedPropertyPath: null,
    currentTool: 'select',
    graphEditorVisible: false,
    historyStack: [],
    historyIndex: -1,
    audioBuffer: null,
    audioAnalysis: null,
    audioFile: null,
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
    }
  }),

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

    // Selection
    selectedLayers(state): Layer[] {
      const comp = state.project.compositions[state.activeCompositionId];
      return (comp?.layers || []).filter((l: Layer) => state.selectedLayerIds.includes(l.id));
    },
    selectedLayer(state): Layer | null {
      if (state.selectedLayerIds.length !== 1) return null;
      const comp = state.project.compositions[state.activeCompositionId];
      return (comp?.layers || []).find((l: Layer) => l.id === state.selectedLayerIds[0]) || null;
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
      isPrecomp: boolean = false
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
        backgroundColor: settings?.backgroundColor ?? '#000000',
        autoResizeToContent: settings?.autoResizeToContent ?? true
      };
      defaultSettings.duration = defaultSettings.frameCount / defaultSettings.fps;

      const composition: Composition = {
        id,
        name,
        settings: defaultSettings,
        layers: [],
        currentFrame: 0,
        isPrecomp
      };

      this.project.compositions[id] = composition;

      // Open and switch to new composition
      if (!this.openCompositionIds.includes(id)) {
        this.openCompositionIds.push(id);
      }
      this.activeCompositionId = id;

      console.log('[Weyl] Created composition:', name, id);
      return composition;
    },

    /**
     * Delete a composition
     */
    deleteComposition(compId: string): boolean {
      // Can't delete main composition
      if (compId === this.project.mainCompositionId) {
        console.warn('[Weyl] Cannot delete main composition');
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

      console.log('[Weyl] Deleted composition:', compId);
      return true;
    },

    /**
     * Switch to a different composition (tab)
     */
    switchComposition(compId: string): void {
      if (!this.project.compositions[compId]) {
        console.warn('[Weyl] Composition not found:', compId);
        return;
      }

      // Add to open tabs if not already
      if (!this.openCompositionIds.includes(compId)) {
        this.openCompositionIds.push(compId);
      }

      // Clear selection when switching
      this.selectedLayerIds = [];
      this.selectedKeyframeIds = [];

      this.activeCompositionId = compId;
      console.log('[Weyl] Switched to composition:', compId);
    },

    /**
     * Close a composition tab
     */
    closeCompositionTab(compId: string): void {
      // Can't close if it's the only open tab
      if (this.openCompositionIds.length <= 1) {
        console.warn('[Weyl] Cannot close the last tab');
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
     * Pre-compose selected layers into a new composition
     */
    precomposeSelectedLayers(name?: string): Composition | null {
      if (this.selectedLayerIds.length === 0) {
        console.warn('[Weyl] No layers selected for pre-compose');
        return null;
      }

      const activeComp = this.project.compositions[this.activeCompositionId];
      if (!activeComp) return null;

      // Create new composition with same settings
      const precomp = this.createComposition(
        name || 'Pre-comp',
        activeComp.settings,
        true
      );

      // Move selected layers to precomp
      const selectedLayers = activeComp.layers.filter(l =>
        this.selectedLayerIds.includes(l.id)
      );

      // Find earliest inPoint to normalize timing
      const earliestIn = Math.min(...selectedLayers.map(l => l.inPoint));

      // Move layers to precomp and adjust timing
      for (const layer of selectedLayers) {
        // Adjust timing relative to precomp start
        layer.inPoint -= earliestIn;
        layer.outPoint -= earliestIn;

        // Remove from parent
        const idx = activeComp.layers.indexOf(layer);
        if (idx >= 0) {
          activeComp.layers.splice(idx, 1);
        }

        // Add to precomp
        precomp.layers.push(layer);
      }

      // Update precomp duration to fit layers
      const maxOut = Math.max(...precomp.layers.map(l => l.outPoint));
      precomp.settings.frameCount = maxOut + 1;
      precomp.settings.duration = precomp.settings.frameCount / precomp.settings.fps;

      // Create precomp layer in parent composition
      const precompLayer: Layer = {
        id: `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        name: precomp.name,
        type: 'precomp',
        visible: true,
        locked: false,
        solo: false,
        threeD: false,
        inPoint: earliestIn,
        outPoint: earliestIn + precomp.settings.frameCount - 1,
        parentId: null,
        transform: createDefaultTransform(),
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        properties: [],
        effects: [],
        blendMode: 'normal',
        motionBlur: false,
        data: {
          compositionId: precomp.id,
          timeRemapEnabled: false,
          collapseTransformations: false
        } as PrecompData
      };

      activeComp.layers.push(precompLayer);

      // Clear selection
      this.selectedLayerIds = [];

      // Switch back to parent composition
      this.activeCompositionId = activeComp.id;

      console.log('[Weyl] Pre-composed layers into:', precomp.name);
      return precomp;
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

      console.log('[Weyl] Loaded inputs from ComfyUI:', {
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

        case 'solid':
          layerData = {
            color: '#808080',
            width: this.project.composition.width,
            height: this.project.composition.height
          };
          break;

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
            fill: ''
          };
          break;

        case 'particles':
          layerData = {
            systemConfig: {
              maxParticles: 1000,
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
              x: this.project.composition.width / 2,
              y: this.project.composition.height / 2,
              direction: -90,
              spread: 30,
              speed: 5,
              speedVariance: 0.2,
              size: 10,
              sizeVariance: 0.3,
              color: [255, 255, 255],
              emissionRate: 10,
              initialBurst: 0,
              particleLifetime: 60,
              lifetimeVariance: 0.2,
              enabled: true,
              burstOnBeat: false,
              burstCount: 20
            }],
            gravityWells: [],
            vortices: [],
            modulations: [],
            renderOptions: {
              blendMode: 'additive',
              renderTrails: false,
              trailLength: 10,
              trailOpacityFalloff: 0.9,
              particleShape: 'circle',
              glowEnabled: false,
              glowRadius: 5,
              glowIntensity: 0.5,
              motionBlur: false,
              motionBlurStrength: 0.5,
              motionBlurSamples: 4,
              connections: {
                enabled: false,
                maxDistance: 100,
                maxConnections: 3,
                lineWidth: 1,
                lineOpacity: 0.5,
                fadeByDistance: true
              }
            }
          };
          break;

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

      const layer: Layer = {
        id,
        name: name || `${type.charAt(0).toUpperCase() + type.slice(1)} ${layers.length + 1}`,
        type,
        visible: true,
        locked: false,
        solo: false,
        threeD: false,
        motionBlur: false,
        inPoint: 0,
        outPoint: (comp?.settings.frameCount || 81) - 1, // Last frame index (0-indexed)
        parentId: null,
        blendMode: 'normal',
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        transform: createDefaultTransform(),
        audio: audioProps,
        properties: [],
        effects: [],
        data: layerData
      };

      // Camera layers should use createCameraLayer() instead
      if (type === 'camera') {
        console.warn('Use createCameraLayer() for camera layers');
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
      const layers = this.getActiveCompLayers();
      const index = layers.findIndex(l => l.id === layerId);
      if (index === -1) return;

      layers.splice(index, 1);
      this.selectedLayerIds = this.selectedLayerIds.filter(id => id !== layerId);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Duplicate a layer
     */
    duplicateLayer(layerId: string): Layer | null {
      const layers = this.getActiveCompLayers();
      const original = layers.find(l => l.id === layerId);
      if (!original) return null;

      // Deep clone the layer
      const duplicate: Layer = JSON.parse(JSON.stringify(original));

      // Generate new IDs
      duplicate.id = crypto.randomUUID();
      duplicate.name = original.name + ' Copy';

      // Generate new keyframe IDs to avoid conflicts
      if (duplicate.transform) {
        for (const key of Object.keys(duplicate.transform)) {
          const prop = (duplicate.transform as any)[key];
          if (prop?.keyframes) {
            prop.keyframes = prop.keyframes.map((kf: any) => ({
              ...kf,
              id: crypto.randomUUID()
            }));
          }
        }
      }
      if (duplicate.properties) {
        for (const prop of duplicate.properties) {
          if (prop.keyframes) {
            prop.keyframes = prop.keyframes.map((kf: any) => ({
              ...kf,
              id: crypto.randomUUID()
            }));
          }
        }
      }

      // Insert after the original
      const index = layers.findIndex(l => l.id === layerId);
      layers.splice(index, 0, duplicate);

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      return duplicate;
    },

    /**
     * Copy selected layers to clipboard
     */
    copySelectedLayers(): void {
      const layers = this.getActiveCompLayers();
      const selectedLayers = layers.filter(l => this.selectedLayerIds.includes(l.id));
      if (selectedLayers.length === 0) return;

      // Deep clone layers to clipboard
      this.clipboard.layers = selectedLayers.map(layer => JSON.parse(JSON.stringify(layer)));
      console.log(`[Store] Copied ${this.clipboard.layers.length} layer(s) to clipboard`);
    },

    /**
     * Paste layers from clipboard
     */
    pasteLayers(): Layer[] {
      if (this.clipboard.layers.length === 0) return [];

      const layers = this.getActiveCompLayers();
      const pastedLayers: Layer[] = [];

      for (const clipboardLayer of this.clipboard.layers) {
        // Deep clone from clipboard
        const newLayer: Layer = JSON.parse(JSON.stringify(clipboardLayer));

        // Generate new IDs
        newLayer.id = crypto.randomUUID();
        newLayer.name = clipboardLayer.name + ' Copy';

        // Generate new keyframe IDs
        if (newLayer.transform) {
          for (const key of Object.keys(newLayer.transform)) {
            const prop = (newLayer.transform as any)[key];
            if (prop?.keyframes) {
              prop.keyframes = prop.keyframes.map((kf: any) => ({
                ...kf,
                id: crypto.randomUUID()
              }));
            }
          }
        }
        if (newLayer.properties) {
          for (const prop of newLayer.properties) {
            if (prop.keyframes) {
              prop.keyframes = prop.keyframes.map((kf: any) => ({
                ...kf,
                id: crypto.randomUUID()
              }));
            }
          }
        }

        // Clear parent reference (may not exist in this comp)
        newLayer.parentId = null;

        layers.unshift(newLayer);
        pastedLayers.push(newLayer);
      }

      // Select pasted layers
      this.selectedLayerIds = pastedLayers.map(l => l.id);

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      console.log(`[Store] Pasted ${pastedLayers.length} layer(s)`);
      return pastedLayers;
    },

    /**
     * Cut selected layers (copy + delete)
     */
    cutSelectedLayers(): void {
      this.copySelectedLayers();
      const layerIds = [...this.selectedLayerIds];
      for (const id of layerIds) {
        this.deleteLayer(id);
      }
    },

    /**
     * Update layer properties
     */
    updateLayer(layerId: string, updates: Partial<Layer>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      Object.assign(layer, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Update layer-specific data (e.g., text content, image path, etc.)
     */
    updateLayerData(layerId: string, dataUpdates: Record<string, any>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.data) return;

      Object.assign(layer.data, dataUpdates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Add a control point to a spline layer
     */
    addSplineControlPoint(layerId: string, point: { id: string; x: number; y: number; handleIn?: { x: number; y: number } | null; handleOut?: { x: number; y: number } | null; type: 'corner' | 'smooth' | 'symmetric' }): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'spline' || !layer.data) return;

      const splineData = layer.data as any;
      if (!splineData.controlPoints) {
        splineData.controlPoints = [];
      }
      splineData.controlPoints.push(point);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Update a spline control point
     */
    updateSplineControlPoint(layerId: string, pointId: string, updates: Partial<{ x: number; y: number; handleIn: { x: number; y: number } | null; handleOut: { x: number; y: number } | null; type: 'corner' | 'smooth' | 'symmetric' }>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'spline' || !layer.data) return;

      const splineData = layer.data as any;
      const point = splineData.controlPoints?.find((p: any) => p.id === pointId);
      if (!point) return;

      Object.assign(point, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Delete a spline control point
     */
    deleteSplineControlPoint(layerId: string, pointId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'spline' || !layer.data) return;

      const splineData = layer.data as any;
      if (!splineData.controlPoints) return;

      const index = splineData.controlPoints.findIndex((p: any) => p.id === pointId);
      if (index >= 0) {
        splineData.controlPoints.splice(index, 1);
        this.project.meta.modified = new Date().toISOString();
      }
    },

    /**
     * Toggle 3D mode for a layer
     */
    toggleLayer3D(layerId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      layer.threeD = !layer.threeD;

      if (layer.threeD) {
        const t = layer.transform;

        // Force reactivity by replacing the entire value objects
        // Position - always create new object with z
        const pos = t.position.value;
        t.position.value = { x: pos.x, y: pos.y, z: pos.z ?? 0 };
        t.position.type = 'vector3';

        // Anchor Point
        const anch = t.anchorPoint.value;
        t.anchorPoint.value = { x: anch.x, y: anch.y, z: anch.z ?? 0 };
        t.anchorPoint.type = 'vector3';

        // Scale
        const scl = t.scale.value;
        t.scale.value = { x: scl.x, y: scl.y, z: scl.z ?? 100 };
        t.scale.type = 'vector3';

        // Initialize 3D rotations
        if (!t.orientation) {
          t.orientation = createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3');
        }
        if (!t.rotationX) {
          t.rotationX = createAnimatableProperty('rotationX', 0, 'number');
        }
        if (!t.rotationY) {
          t.rotationY = createAnimatableProperty('rotationY', 0, 'number');
        }
        if (!t.rotationZ) {
          t.rotationZ = createAnimatableProperty('rotationZ', 0, 'number');
          // Copy existing 2D rotation to Z rotation
          t.rotationZ.value = t.rotation.value;
        }
      } else {
        // Reverting to 2D
        // Map Z rotation back to standard rotation
        if (layer.transform.rotationZ) {
          layer.transform.rotation.value = layer.transform.rotationZ.value;
        }
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Reorder layers
     */
    moveLayer(layerId: string, newIndex: number): void {
      const layers = this.getActiveCompLayers();
      const currentIndex = layers.findIndex(l => l.id === layerId);
      if (currentIndex === -1) return;

      const [layer] = layers.splice(currentIndex, 1);
      layers.splice(newIndex, 0, layer);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Selection
     */
    selectLayer(layerId: string, addToSelection = false): void {
      if (addToSelection) {
        if (!this.selectedLayerIds.includes(layerId)) {
          this.selectedLayerIds.push(layerId);
        }
      } else {
        this.selectedLayerIds = [layerId];
      }
    },

    deselectLayer(layerId: string): void {
      this.selectedLayerIds = this.selectedLayerIds.filter(id => id !== layerId);
    },

    /**
     * Set a layer's parent for parenting/hierarchy
     */
    setLayerParent(layerId: string, parentId: string | null): void {
      const layers = this.getActiveCompLayers();
      const layer = layers.find(l => l.id === layerId);
      if (!layer) return;

      // Prevent self-parenting
      if (parentId === layerId) return;

      // Prevent circular parenting (parent can't be a descendant)
      if (parentId) {
        const getDescendantIds = (id: string): string[] => {
          const children = layers.filter(l => l.parentId === id);
          let ids = children.map(c => c.id);
          for (const child of children) {
            ids = ids.concat(getDescendantIds(child.id));
          }
          return ids;
        };

        const descendants = new Set(getDescendantIds(layerId));
        if (descendants.has(parentId)) {
          console.warn('[Store] Cannot set parent: would create circular reference');
          return;
        }
      }

      layer.parentId = parentId;
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    clearSelection(): void {
      this.selectedLayerIds = [];
      this.selectedKeyframeIds = [];
      this.selectedPropertyPath = null;
    },

    /**
     * Select a property path for graph editor focus
     */
    selectProperty(propertyPath: string | null): void {
      this.selectedPropertyPath = propertyPath;
    },

    /**
     * Playback controls
     */
    play(): void {
      if (this.isPlaying) return;

      const comp = this.getActiveComp();
      if (!comp) return;

      this.isPlaying = true;
      this.playbackStartTime = performance.now();
      this.playbackStartFrame = comp.currentFrame;

      this.playbackLoop();
    },

    pause(): void {
      this.isPlaying = false;
      if (this.playbackRequestId !== null) {
        cancelAnimationFrame(this.playbackRequestId);
        this.playbackRequestId = null;
      }
    },

    togglePlayback(): void {
      if (this.isPlaying) {
        this.pause();
      } else {
        this.play();
      }
    },

    /**
     * Animation loop for playback
     */
    playbackLoop(): void {
      if (!this.isPlaying) return;

      const comp = this.getActiveComp();
      if (!comp) return;

      const elapsed = performance.now() - (this.playbackStartTime || 0);
      const fps = comp.settings.fps;
      const frameCount = comp.settings.frameCount;

      const elapsedFrames = Math.floor((elapsed / 1000) * fps);
      let newFrame = this.playbackStartFrame + elapsedFrames;

      // Loop playback
      if (newFrame >= frameCount) {
        newFrame = 0;
        this.playbackStartFrame = 0;
        this.playbackStartTime = performance.now();
      }

      comp.currentFrame = newFrame;

      this.playbackRequestId = requestAnimationFrame(() => this.playbackLoop());
    },

    setFrame(frame: number): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      comp.currentFrame = Math.max(0, Math.min(frame, comp.settings.frameCount - 1));
    },

    nextFrame(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      if (comp.currentFrame < comp.settings.frameCount - 1) {
        comp.currentFrame++;
      }
    },

    prevFrame(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      if (comp.currentFrame > 0) {
        comp.currentFrame--;
      }
    },

    goToStart(): void {
      const comp = this.getActiveComp();
      if (comp) comp.currentFrame = 0;
    },

    goToEnd(): void {
      const comp = this.getActiveComp();
      if (!comp) return;
      // Frame indices are 0-based, so last frame is frameCount - 1
      comp.currentFrame = comp.settings.frameCount - 1;
    },

    /**
     * Tool selection
     */
    setTool(tool: CompositorState['currentTool']): void {
      this.currentTool = tool;
    },

    /**
     * History management
     */
    pushHistory(): void {
      // Remove any future history if we're not at the end
      if (this.historyIndex < this.historyStack.length - 1) {
        this.historyStack = this.historyStack.slice(0, this.historyIndex + 1);
      }

      // Deep clone the project
      const snapshot = JSON.parse(JSON.stringify(this.project));
      this.historyStack.push(snapshot);
      this.historyIndex = this.historyStack.length - 1;

      // Limit history size
      const maxHistory = 50;
      if (this.historyStack.length > maxHistory) {
        this.historyStack = this.historyStack.slice(-maxHistory);
        this.historyIndex = this.historyStack.length - 1;
      }
    },

    undo(): void {
      if (this.historyIndex <= 0) return;

      this.historyIndex--;
      this.project = JSON.parse(JSON.stringify(this.historyStack[this.historyIndex]));
    },

    redo(): void {
      if (this.historyIndex >= this.historyStack.length - 1) return;

      this.historyIndex++;
      this.project = JSON.parse(JSON.stringify(this.historyStack[this.historyIndex]));
    },

    /**
     * Project serialization
     */
    exportProject(): string {
      return JSON.stringify(this.project, null, 2);
    },

    importProject(json: string): void {
      try {
        const project = JSON.parse(json) as WeylProject;
        this.project = project;
        this.pushHistory();
      } catch (err) {
        console.error('[Weyl] Failed to import project:', err);
      }
    },

    /**
     * Toggle graph editor visibility
     */
    toggleGraphEditor(): void {
      this.graphEditorVisible = !this.graphEditorVisible;
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
      const frame = atFrame ?? (this.getActiveComp()?.currentFrame ?? 0);
      console.log('[Store] addKeyframe called:', { layerId, propertyName, value, frame });
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) {
        console.log('[Store] addKeyframe: layer not found');
        return null;
      }

      // Find the property
      let property: AnimatableProperty<T> | undefined;

      // Check transform properties (support both 'position' and 'transform.position' formats)
      if (propertyName === 'position' || propertyName === 'transform.position') {
        property = layer.transform.position as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'scale' || propertyName === 'transform.scale') {
        property = layer.transform.scale as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'rotation' || propertyName === 'transform.rotation') {
        property = layer.transform.rotation as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'anchorPoint' || propertyName === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'opacity') {
        property = layer.opacity as unknown as AnimatableProperty<T>;
      } else {
        // Check custom properties
        property = layer.properties.find(p => p.name === propertyName) as AnimatableProperty<T> | undefined;
      }

      if (!property) {
        console.log('[Store] addKeyframe: property not found:', propertyName);
        return null;
      }

      // Enable animation
      property.animated = true;

      // Create keyframe with new handle structure
      // Default handles are disabled (linear interpolation until graph editor enables them)
      const keyframe: Keyframe<T> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        frame,
        value,
        interpolation: 'linear',
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: 'smooth'
      };

      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(k => k.frame === frame);
      if (existingIndex >= 0) {
        property.keyframes[existingIndex] = keyframe;
        console.log('[Store] addKeyframe: replaced existing keyframe at frame', (this.getActiveComp()?.currentFrame ?? 0));
      } else {
        property.keyframes.push(keyframe);
        property.keyframes.sort((a, b) => a.frame - b.frame);
        console.log('[Store] addKeyframe: added new keyframe at frame', (this.getActiveComp()?.currentFrame ?? 0), 'total keyframes:', property.keyframes.length);
      }

      this.project.meta.modified = new Date().toISOString();
      return keyframe;
    },

    /**
     * Remove a keyframe
     */
    removeKeyframe(layerId: string, propertyName: string, keyframeId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      // Find the property (support both 'position' and 'transform.position' formats)
      let property: AnimatableProperty<any> | undefined;

      if (propertyName === 'position' || propertyName === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyName === 'scale' || propertyName === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyName === 'rotation' || propertyName === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyName === 'anchorPoint' || propertyName === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyName === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyName);
      }

      if (!property) return;

      const index = property.keyframes.findIndex(k => k.id === keyframeId);
      if (index >= 0) {
        property.keyframes.splice(index, 1);

        // Disable animation if no keyframes left
        if (property.keyframes.length === 0) {
          property.animated = false;
        }
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Set a property's value (for direct editing in timeline)
     */
    setPropertyValue(layerId: string, propertyPath: string, value: any): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      // Find the property
      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      property.value = value;

      // If animated and at a keyframe, update that keyframe's value too
      if (property.animated && property.keyframes.length > 0) {
        const existingKf = property.keyframes.find(kf => kf.frame === (this.getActiveComp()?.currentFrame ?? 0));
        if (existingKf) {
          existingKf.value = value;
        }
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Set a property's animated state
     */
    setPropertyAnimated(layerId: string, propertyPath: string, animated: boolean): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      property.animated = animated;

      // If enabling animation and no keyframes, add one at current frame
      if (animated && property.keyframes.length === 0) {
        this.addKeyframe(layerId, propertyPath, property.value);
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Move a keyframe to a new frame
     */
    moveKeyframe(layerId: string, propertyPath: string, keyframeId: string, newFrame: number): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
      if (!keyframe) return;

      // Check if there's already a keyframe at the target frame
      const existingAtTarget = property.keyframes.find(kf => kf.frame === newFrame && kf.id !== keyframeId);
      if (existingAtTarget) {
        // Remove the existing keyframe at target
        property.keyframes = property.keyframes.filter(kf => kf.id !== existingAtTarget.id);
      }

      keyframe.frame = newFrame;

      // Re-sort keyframes by frame
      property.keyframes.sort((a, b) => a.frame - b.frame);

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Set keyframe value (for graph editor numeric input)
     */
    setKeyframeValue(layerId: string, propertyPath: string, keyframeId: string, newValue: number): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
      if (!keyframe) return;

      // Handle vector values (Position X/Y are separated in graph editor)
      if (typeof keyframe.value === 'object' && keyframe.value !== null) {
        // For graph editor, the curve name tells us which dimension
        // This is a simplified update - for full support, we'd need curve dimension info
        // For now, just update scalar values directly
        console.warn('[Store] setKeyframeValue: Cannot directly update vector keyframes from graph editor. Use separate dimension curves.');
      } else {
        keyframe.value = newValue;
      }

      this.project.meta.modified = new Date().toISOString();
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
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
      if (!keyframe) return;

      keyframe.interpolation = interpolation;

      this.project.meta.modified = new Date().toISOString();
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
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else {
        property = layer.properties.find(p => p.id === propertyPath || p.name === propertyPath);
      }

      if (!property) return;

      const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
      if (!keyframe) return;

      if (updates.frame !== undefined) {
        keyframe.frame = updates.frame;
        // Re-sort keyframes by frame
        property.keyframes.sort((a, b) => a.frame - b.frame);
      }

      if (updates.value !== undefined) {
        keyframe.value = updates.value;
      }

      this.project.meta.modified = new Date().toISOString();
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
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      if (propertyPath === 'position' || propertyPath === 'transform.position') {
        property = layer.transform.position;
      } else if (propertyPath === 'scale' || propertyPath === 'transform.scale') {
        property = layer.transform.scale;
      } else if (propertyPath === 'rotation' || propertyPath === 'transform.rotation') {
        property = layer.transform.rotation;
      } else if (propertyPath === 'opacity') {
        property = layer.opacity;
      } else if (propertyPath === 'anchorPoint' || propertyPath === 'transform.anchorPoint') {
        property = layer.transform.anchorPoint;
      } else {
        property = layer.properties.find(p => p.id === propertyPath || p.name === propertyPath);
      }

      if (!property) return;

      const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
      if (!keyframe) return;

      if (handleType === 'in') {
        keyframe.inHandle = { ...handle };
      } else {
        keyframe.outHandle = { ...handle };
      }

      // Enable bezier interpolation when handles are modified
      if (handle.enabled && keyframe.interpolation === 'linear') {
        keyframe.interpolation = 'bezier';
      }

      this.project.meta.modified = new Date().toISOString();
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

    // ============================================================
    // PARTICLE SYSTEM LAYER ACTIONS
    // ============================================================

    /**
     * Create a particle system layer
     */
    createParticleLayer(): Layer {
      const layer = this.createLayer('particles', 'Particle System');

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
          x: 0.5,
          y: 0.5,
          direction: 270,
          spread: 30,
          speed: 330,
          speedVariance: 50,
          size: 17,
          sizeVariance: 5,
          color: [255, 255, 255],
          emissionRate: 10,
          initialBurst: 0,
          particleLifetime: 60,
          lifetimeVariance: 10,
          enabled: true,
          burstOnBeat: false,
          burstCount: 20
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

        console.log('[Weyl] Auto-resizing composition for video:', {
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

      console.log('[Weyl] Created video layer:', {
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

      console.log('[Weyl] Video metadata loaded:', { layerId, metadata });
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

      console.log('[Weyl] Composition resized:', {
        width,
        height,
        frameCount: comp.settings.frameCount
      });
    },

    // ============================================================
    // PRECOMP LAYER ACTIONS
    // ============================================================

    /**
     * Create a precomp layer referencing another composition
     * (For future multi-composition architecture)
     */
    createPrecompLayer(compositionId: string, name?: string): Layer {
      const layer = this.createLayer('precomp', name || 'Precomp');

      const precompData: PrecompData = {
        compositionId,
        timeRemapEnabled: false,
        timeRemap: undefined,
        collapseTransformations: false,
        overrideFrameRate: false,
        frameRate: undefined
      };

      layer.data = precompData;

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      return layer;
    },

    /**
     * Update precomp layer data
     */
    updatePrecompLayerData(layerId: string, updates: Partial<PrecompData>): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || layer.type !== 'precomp') return;

      const data = layer.data as PrecompData;
      Object.assign(data, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    // ============================================================
    // EFFECT ACTIONS
    // ============================================================

    /**
     * Add effect to layer
     */
    addEffectToLayer(layerId: string, effectKey: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return;

      const effect = createEffectInstance(effectKey);
      if (!effect) return;

      if (!layer.effects) {
        layer.effects = [];
      }
      layer.effects.push(effect);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Remove effect from layer
     */
    removeEffectFromLayer(layerId: string, effectId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return;

      const index = layer.effects.findIndex(e => e.id === effectId);
      if (index >= 0) {
        layer.effects.splice(index, 1);
        this.project.meta.modified = new Date().toISOString();
        this.pushHistory();
      }
    },

    /**
     * Update effect parameter value
     */
    updateEffectParameter(layerId: string, effectId: string, paramKey: string, value: any): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find(e => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) return;

      effect.parameters[paramKey].value = value;
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Toggle effect parameter animation state
     */
    setEffectParamAnimated(layerId: string, effectId: string, paramKey: string, animated: boolean): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find(e => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) return;

      const param = effect.parameters[paramKey];
      param.animated = animated;

      // If enabling animation and no keyframes exist, add one at current frame
      if (animated && (!param.keyframes || param.keyframes.length === 0)) {
        param.keyframes = [{
          id: `kf_${Date.now()}`,
          frame: this.currentFrame,
          value: param.value,
          interpolation: 'linear' as InterpolationType,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: 'smooth' as const,
        }];
      }

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Toggle effect enabled state
     */
    toggleEffect(layerId: string, effectId: string): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find(e => e.id === effectId);
      if (!effect) return;

      effect.enabled = !effect.enabled;
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Reorder effects in stack
     */
    reorderEffects(layerId: string, fromIndex: number, toIndex: number): void {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return;
      if (fromIndex < 0 || fromIndex >= layer.effects.length) return;
      if (toIndex < 0 || toIndex >= layer.effects.length) return;

      const [effect] = layer.effects.splice(fromIndex, 1);
      layer.effects.splice(toIndex, 0, effect);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Get evaluated effect parameter value at a given frame
     */
    getEffectParameterValue(layerId: string, effectId: string, paramKey: string, frame?: number): any {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer || !layer.effects) return null;

      const effect = layer.effects.find(e => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) return null;

      const param = effect.parameters[paramKey];
      const targetFrame = frame ?? (this.getActiveComp()?.currentFrame ?? 0);

      // Use interpolation if animated
      if (param.animated && param.keyframes.length > 0) {
        return interpolateProperty(param, targetFrame);
      }

      return param.value;
    },

    // ============================================================
    // CAMERA ACTIONS
    // ============================================================

    /**
     * Create a new camera and corresponding layer
     * Returns both the camera and the layer
     */
    createCameraLayer(name?: string): { camera: Camera3D; layer: Layer } {
      const comp = this.getActiveComp();
      const layers = this.getActiveCompLayers();

      const cameraId = `camera_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
      const cameraName = name || `Camera ${this.cameras.size + 1}`;

      // Create the camera object
      const camera = createDefaultCamera(
        cameraId,
        comp?.settings.width || 1024,
        comp?.settings.height || 1024
      );
      camera.name = cameraName;

      // Add to cameras map
      this.cameras.set(cameraId, camera);

      // If this is the first camera, make it active
      if (!this.activeCameraId) {
        this.activeCameraId = cameraId;
      }

      // Create the layer
      const layerId = `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
      const layer: Layer = {
        id: layerId,
        name: cameraName,
        type: 'camera',
        visible: true,
        locked: false,
        solo: false,
        threeD: true,  // Cameras are always 3D
        motionBlur: false,
        inPoint: 0,
        outPoint: (comp?.settings.frameCount || 81) - 1, // Last frame index (0-indexed)
        parentId: null,
        blendMode: 'normal',
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        transform: createDefaultTransform(),
        properties: [],
        effects: [],
        data: {
          cameraId,
          isActiveCamera: !this.activeCameraId || this.activeCameraId === cameraId
        } as CameraLayerData
      };

      layers.unshift(layer);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      // Auto-select the new camera layer
      this.selectLayer(layerId);

      return { camera, layer };
    },

    /**
     * Get a camera by ID
     */
    getCamera(cameraId: string): Camera3D | null {
      return this.cameras.get(cameraId) || null;
    },

    /**
     * Update camera properties
     */
    updateCamera(cameraId: string, updates: Partial<Camera3D>): void {
      const camera = this.cameras.get(cameraId);
      if (!camera) return;

      Object.assign(camera, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Set the active camera
     */
    setActiveCamera(cameraId: string): void {
      if (!this.cameras.has(cameraId)) return;

      this.activeCameraId = cameraId;

      // Update all camera layers' isActiveCamera flag
      const layers = this.getActiveCompLayers();
      for (const layer of layers) {
        if (layer.type === 'camera' && layer.data) {
          const cameraData = layer.data as CameraLayerData;
          cameraData.isActiveCamera = cameraData.cameraId === cameraId;
        }
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Delete a camera (and its layer)
     */
    deleteCamera(cameraId: string): void {
      const layers = this.getActiveCompLayers();

      // Find the associated layer
      const layerIndex = layers.findIndex(
        l => l.type === 'camera' && (l.data as CameraLayerData)?.cameraId === cameraId
      );

      // Remove the layer if found
      if (layerIndex !== -1) {
        const layerId = layers[layerIndex].id;
        layers.splice(layerIndex, 1);
        this.selectedLayerIds = this.selectedLayerIds.filter(id => id !== layerId);
      }

      // Remove the camera
      this.cameras.delete(cameraId);

      // If this was the active camera, select another or set to null
      if (this.activeCameraId === cameraId) {
        const remaining = Array.from(this.cameras.keys());
        this.activeCameraId = remaining.length > 0 ? remaining[0] : null;

        // Update layer flags
        if (this.activeCameraId) {
          this.setActiveCamera(this.activeCameraId);
        }
      }

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Get camera keyframes for a specific camera
     */
    getCameraKeyframes(cameraId: string): CameraKeyframe[] {
      return this.cameraKeyframes.get(cameraId) || [];
    },

    /**
     * Add a keyframe to a camera
     */
    addCameraKeyframe(cameraId: string, keyframe: CameraKeyframe): void {
      let keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes) {
        keyframes = [];
        this.cameraKeyframes.set(cameraId, keyframes);
      }

      // Remove existing keyframe at same frame
      const existingIndex = keyframes.findIndex(k => k.frame === keyframe.frame);
      if (existingIndex >= 0) {
        keyframes[existingIndex] = keyframe;
      } else {
        keyframes.push(keyframe);
        // Keep sorted by frame
        keyframes.sort((a, b) => a.frame - b.frame);
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Remove a keyframe from a camera
     */
    removeCameraKeyframe(cameraId: string, frame: number): void {
      const keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes) return;

      const index = keyframes.findIndex(k => k.frame === frame);
      if (index >= 0) {
        keyframes.splice(index, 1);
        this.project.meta.modified = new Date().toISOString();
      }
    },

    /**
     * Get camera with keyframe interpolation applied at a specific frame
     * This is the main method for getting animated camera values
     */
    getCameraAtFrame(cameraId: string, frame: number): Camera3D | null {
      const camera = this.cameras.get(cameraId);
      if (!camera) return null;

      const keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes || keyframes.length === 0) {
        return camera; // No animation, return base camera
      }

      // Use the interpolation function from camera export service
      const interpolated = interpolateCameraAtFrame(camera, keyframes, frame);

      // Merge interpolated values back onto camera (return modified copy, not original)
      return {
        ...camera,
        position: interpolated.position,
        orientation: interpolated.rotation,
        focalLength: interpolated.focalLength,
        zoom: interpolated.zoom,
        depthOfField: {
          ...camera.depthOfField,
          focusDistance: interpolated.focusDistance,
        },
      };
    },

    /**
     * Get the active camera with interpolation at current frame
     */
    getActiveCameraAtFrame(frame?: number): Camera3D | null {
      if (!this.activeCameraId) return null;
      return this.getCameraAtFrame(this.activeCameraId, frame ?? this.currentFrame);
    },

    /**
     * Update viewport state
     */
    updateViewportState(updates: Partial<ViewportState>): void {
      Object.assign(this.viewportState, updates);
    },

    /**
     * Update view options
     */
    updateViewOptions(updates: Partial<ViewOptions>): void {
      Object.assign(this.viewOptions, updates);
    },

    // ============================================================
    // AUDIO ACTIONS
    // ============================================================

    /**
     * Load audio file using Web Worker (non-blocking)
     */
    async loadAudio(file: File): Promise<void> {
      // Reset state
      this.audioFile = file;
      this.audioBuffer = null;
      this.audioAnalysis = null;
      this.audioLoadingState = 'decoding';
      this.audioLoadingProgress = 0;
      this.audioLoadingPhase = 'Preparing...';
      this.audioLoadingError = null;

      try {
        const result = await loadAndAnalyzeAudio(
          file,
          this.project.composition.fps,
          {
            onProgress: (progress) => {
              // Update loading state based on phase
              if (progress.phase === 'decoding') {
                this.audioLoadingState = 'decoding';
              } else {
                this.audioLoadingState = 'analyzing';
              }
              this.audioLoadingProgress = progress.progress;
              this.audioLoadingPhase = progress.message;
            }
          }
        );

        this.audioBuffer = result.buffer;
        this.audioAnalysis = result.analysis;
        this.audioLoadingState = 'complete';
        this.audioLoadingProgress = 1;
        this.audioLoadingPhase = 'Complete';

        // Initialize the audio reactive mapper
        this.initializeAudioReactiveMapper();

        // Update property driver system with new audio data
        if (this.propertyDriverSystem && this.audioAnalysis) {
          this.propertyDriverSystem.setAudioAnalysis(this.audioAnalysis);
        }

        console.log('[Weyl] Audio loaded:', {
          duration: this.audioBuffer.duration,
          bpm: this.audioAnalysis.bpm,
          frameCount: this.audioAnalysis.frameCount
        });
      } catch (error) {
        console.error('[Weyl] Failed to load audio:', error);
        this.audioFile = null;
        this.audioBuffer = null;
        this.audioAnalysis = null;
        this.audioReactiveMapper = null;
        this.audioLoadingState = 'error';
        this.audioLoadingError = (error as Error).message;
      }
    },

    /**
     * Cancel ongoing audio analysis
     */
    cancelAudioLoad(): void {
      cancelAnalysis();
      this.audioLoadingState = 'idle';
      this.audioLoadingProgress = 0;
      this.audioLoadingPhase = '';
      this.audioLoadingError = null;
    },

    /**
     * Clear loaded audio
     */
    clearAudio(): void {
      this.cancelAudioLoad();
      this.audioFile = null;
      this.audioBuffer = null;
      this.audioAnalysis = null;
      this.audioMappings.clear();
    },

    /**
     * Get audio feature value at current frame
     */
    getAudioFeatureAtFrame(feature: string, frame?: number): number {
      if (!this.audioAnalysis) return 0;
      return getFeatureAtFrame(this.audioAnalysis, feature, frame ?? (this.getActiveComp()?.currentFrame ?? 0));
    },

    /**
     * Apply audio reactivity mapping to particle layer
     */
    applyAudioToParticles(layerId: string, mapping: AudioParticleMapping): void {
      const existing = this.audioMappings.get(layerId) || [];
      existing.push(mapping);
      this.audioMappings.set(layerId, existing);
    },

    /**
     * Remove audio mapping (legacy)
     */
    removeLegacyAudioMapping(layerId: string, index: number): void {
      const mappings = this.audioMappings.get(layerId);
      if (mappings) {
        mappings.splice(index, 1);
        if (mappings.length === 0) {
          this.audioMappings.delete(layerId);
        }
      }
    },

    /**
     * Get audio mappings for a layer (legacy)
     */
    getAudioMappingsForLayer(layerId: string): AudioParticleMapping[] {
      return this.audioMappings.get(layerId) || [];
    },

    // ============================================================
    // NEW AUDIO REACTIVE SYSTEM
    // ============================================================

    /**
     * Set peak data
     */
    setPeakData(peakData: PeakData): void {
      this.peakData = peakData;
      if (this.audioReactiveMapper) {
        this.audioReactiveMapper.setPeakData(peakData);
      }
    },

    /**
     * Detect peaks with config
     */
    detectAudioPeaks(config: PeakDetectionConfig): PeakData | null {
      if (!this.audioAnalysis) return null;

      const weights = this.audioAnalysis.amplitudeEnvelope;
      const peakData = detectPeaks(weights, config);
      this.peakData = peakData;

      if (this.audioReactiveMapper) {
        this.audioReactiveMapper.setPeakData(peakData);
      }

      return peakData;
    },

    /**
     * Add new audio mapping
     */
    addAudioMapping(mapping: AudioMapping): void {
      this.audioReactiveMappings.push(mapping);

      if (this.audioReactiveMapper) {
        this.audioReactiveMapper.addMapping(mapping);
      }
    },

    /**
     * Remove audio mapping by ID
     */
    removeAudioMapping(mappingId: string): void {
      const index = this.audioReactiveMappings.findIndex(m => m.id === mappingId);
      if (index >= 0) {
        this.audioReactiveMappings.splice(index, 1);
      }

      if (this.audioReactiveMapper) {
        this.audioReactiveMapper.removeMapping(mappingId);
      }
    },

    /**
     * Update audio mapping
     */
    updateAudioMapping(mappingId: string, updates: Partial<AudioMapping>): void {
      const mapping = this.audioReactiveMappings.find(m => m.id === mappingId);
      if (mapping) {
        Object.assign(mapping, updates);
      }

      if (this.audioReactiveMapper) {
        this.audioReactiveMapper.updateMapping(mappingId, updates);
      }
    },

    /**
     * Get all audio mappings
     */
    getAudioMappings(): AudioMapping[] {
      return this.audioReactiveMappings;
    },

    /**
     * Get mapped value at frame
     */
    getMappedValueAtFrame(mappingId: string, frame: number): number {
      if (!this.audioReactiveMapper) return 0;
      return this.audioReactiveMapper.getValueAtFrame(mappingId, frame);
    },

    /**
     * Get all mapped values at current frame
     */
    getAllMappedValuesAtFrame(frame?: number): Map<TargetParameter, number> {
      if (!this.audioReactiveMapper) return new Map();
      return this.audioReactiveMapper.getAllValuesAtFrame(frame ?? (this.getActiveComp()?.currentFrame ?? 0));
    },

    /**
     * Get active mappings for a specific layer
     */
    getActiveMappingsForLayer(layerId: string): AudioMapping[] {
      return this.audioReactiveMappings.filter(
        m => m.enabled && (m.targetLayerId === layerId || m.targetLayerId === undefined)
      );
    },

    /**
     * Get audio reactive values for a specific layer at a specific frame
     * This is called by the engine during frame evaluation
     */
    getAudioReactiveValuesForLayer(layerId: string, frame: number): Map<TargetParameter, number> {
      if (!this.audioReactiveMapper) return new Map();
      return this.audioReactiveMapper.getValuesForLayerAtFrame(layerId, frame);
    },

    /**
     * Check if current frame is a beat
     */
    isBeatAtCurrentFrame(): boolean {
      if (!this.audioAnalysis) return false;
      return isBeatAtFrame(this.audioAnalysis, (this.getActiveComp()?.currentFrame ?? 0));
    },

    // ============================================================
    // TIMELINE SNAPPING
    // ============================================================

    /**
     * Find nearest snap point for a given frame
     * @param frame - The frame to snap
     * @param pixelsPerFrame - Current zoom level
     * @param selectedLayerId - Currently selected layer (excluded from keyframe snapping)
     */
    findSnapPoint(frame: number, pixelsPerFrame: number, selectedLayerId?: string | null): SnapResult | null {
      return findNearestSnap(frame, this.snapConfig, pixelsPerFrame, {
        layers: this.layers,
        selectedLayerId,
        currentFrame: (this.getActiveComp()?.currentFrame ?? 0),
        audioAnalysis: this.audioAnalysis,
        peakData: this.peakData,
      });
    },

    /**
     * Get all beat frames from audio analysis
     */
    getAudioBeatFrames(): number[] {
      return getBeatFrames(this.audioAnalysis);
    },

    /**
     * Get all peak frames from peak data
     */
    getAudioPeakFrames(): number[] {
      return getPeakFrames(this.peakData);
    },

    /**
     * Update snap configuration
     */
    setSnapConfig(config: Partial<SnapConfig>): void {
      this.snapConfig = { ...this.snapConfig, ...config };
    },

    /**
     * Toggle snapping enabled
     */
    toggleSnapping(): void {
      this.snapConfig.enabled = !this.snapConfig.enabled;
    },

    /**
     * Toggle specific snap type
     */
    toggleSnapType(type: 'grid' | 'keyframes' | 'beats' | 'peaks' | 'layerBounds' | 'playhead'): void {
      const typeMap: Record<string, keyof SnapConfig> = {
        'grid': 'snapToGrid',
        'keyframes': 'snapToKeyframes',
        'beats': 'snapToBeats',
        'peaks': 'snapToPeaks',
        'layerBounds': 'snapToLayerBounds',
        'playhead': 'snapToPlayhead',
      };
      const key = typeMap[type];
      if (key && typeof this.snapConfig[key] === 'boolean') {
        (this.snapConfig as any)[key] = !(this.snapConfig as any)[key];
      }
    },

    // ============================================================
    // PATH ANIMATOR ACTIONS
    // ============================================================

    /**
     * Create path animator for a layer
     */
    createPathAnimator(layerId: string, config: Partial<PathAnimatorConfig> = {}): void {
      const animator = new AudioPathAnimator(config);
      this.pathAnimators.set(layerId, animator);
    },

    /**
     * Set path for an animator
     */
    setPathAnimatorPath(layerId: string, pathData: string): void {
      const animator = this.pathAnimators.get(layerId);
      if (animator) {
        animator.setPath(pathData);
      }
    },

    /**
     * Update path animator config
     */
    updatePathAnimatorConfig(layerId: string, config: Partial<PathAnimatorConfig>): void {
      const animator = this.pathAnimators.get(layerId);
      if (animator) {
        animator.setConfig(config);
      }
    },

    /**
     * Remove path animator
     */
    removePathAnimator(layerId: string): void {
      this.pathAnimators.delete(layerId);
    },

    /**
     * Get path animator for layer
     */
    getPathAnimator(layerId: string): AudioPathAnimator | undefined {
      return this.pathAnimators.get(layerId) as AudioPathAnimator | undefined;
    },

    /**
     * Update all path animators for current frame
     */
    updatePathAnimators(): void {
      if (!this.audioAnalysis) return;

      const frame = (this.getActiveComp()?.currentFrame ?? 0);
      const amplitude = getFeatureAtFrame(this.audioAnalysis, 'amplitude', frame);
      const isBeat = isBeatAtFrame(this.audioAnalysis, frame);

      for (const [_layerId, animator] of this.pathAnimators) {
        animator.update(amplitude, isBeat);
      }
    },

    /**
     * Reset all path animators
     */
    resetPathAnimators(): void {
      for (const animator of this.pathAnimators.values()) {
        animator.reset();
      }
    },

    /**
     * Initialize audio reactive mapper when audio is loaded
     */
    initializeAudioReactiveMapper(): void {
      if (!this.audioAnalysis) return;

      this.audioReactiveMapper = new AudioReactiveMapper(this.audioAnalysis);

      // Add existing mappings
      for (const mapping of this.audioReactiveMappings) {
        this.audioReactiveMapper.addMapping(mapping);
      }

      // Set peak data if available
      if (this.peakData) {
        this.audioReactiveMapper.setPeakData(this.peakData);
      }
    },

    // ============================================================
    // PROPERTY DRIVER SYSTEM (Expressions/Links)
    // ============================================================

    /**
     * Initialize the property driver system
     */
    initializePropertyDriverSystem(): void {
      this.propertyDriverSystem = new PropertyDriverSystem();

      // Set up property getter that reads from store
      this.propertyDriverSystem.setPropertyGetter((layerId, propertyPath, frame) => {
        return this.getPropertyValueAtFrame(layerId, propertyPath, frame);
      });

      // Connect audio if available
      if (this.audioAnalysis) {
        this.propertyDriverSystem.setAudioAnalysis(this.audioAnalysis);
      }

      // Load existing drivers
      for (const driver of this.propertyDrivers) {
        this.propertyDriverSystem.addDriver(driver);
      }
    },

    /**
     * Get a property value at a specific frame
     * Used by the driver system to read source properties
     */
    getPropertyValueAtFrame(layerId: string, propertyPath: PropertyPath, frame: number): number | null {
      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return null;

      // Parse property path
      const parts = propertyPath.split('.');

      if (parts[0] === 'transform') {
        const t = layer.transform;
        if (parts[1] === 'position') {
          const pos = interpolateProperty(t.position, frame);
          if (parts[2] === 'x') return pos.x;
          if (parts[2] === 'y') return pos.y;
          if (parts[2] === 'z') return pos.z ?? 0;
        }
        if (parts[1] === 'anchorPoint') {
          const anchor = interpolateProperty(t.anchorPoint, frame);
          if (parts[2] === 'x') return anchor.x;
          if (parts[2] === 'y') return anchor.y;
          if (parts[2] === 'z') return anchor.z ?? 0;
        }
        if (parts[1] === 'scale') {
          const scale = interpolateProperty(t.scale, frame);
          if (parts[2] === 'x') return scale.x;
          if (parts[2] === 'y') return scale.y;
          if (parts[2] === 'z') return scale.z ?? 100;
        }
        if (parts[1] === 'rotation') {
          return interpolateProperty(t.rotation, frame);
        }
        if (parts[1] === 'rotationX' && t.rotationX) {
          return interpolateProperty(t.rotationX, frame);
        }
        if (parts[1] === 'rotationY' && t.rotationY) {
          return interpolateProperty(t.rotationY, frame);
        }
        if (parts[1] === 'rotationZ' && t.rotationZ) {
          return interpolateProperty(t.rotationZ, frame);
        }
      }

      if (parts[0] === 'opacity') {
        return interpolateProperty(layer.opacity, frame);
      }

      return null;
    },

    /**
     * Get driven property values for a layer at current frame
     */
    getDrivenValuesForLayer(layerId: string): Map<PropertyPath, number> {
      if (!this.propertyDriverSystem) {
        return new Map();
      }

      const layer = this.getActiveCompLayers().find(l => l.id === layerId);
      if (!layer) return new Map();

      // Build base values map
      const baseValues = new Map<PropertyPath, number>();
      const frame = (this.getActiveComp()?.currentFrame ?? 0);

      // Position
      const pos = interpolateProperty(layer.transform.position, frame);
      baseValues.set('transform.position.x', pos.x);
      baseValues.set('transform.position.y', pos.y);
      baseValues.set('transform.position.z', pos.z ?? 0);

      // Anchor point
      const anchor = interpolateProperty(layer.transform.anchorPoint, frame);
      baseValues.set('transform.anchorPoint.x', anchor.x);
      baseValues.set('transform.anchorPoint.y', anchor.y);
      baseValues.set('transform.anchorPoint.z', anchor.z ?? 0);

      // Scale
      const scale = interpolateProperty(layer.transform.scale, frame);
      baseValues.set('transform.scale.x', scale.x);
      baseValues.set('transform.scale.y', scale.y);
      baseValues.set('transform.scale.z', scale.z ?? 100);

      // Rotation
      baseValues.set('transform.rotation', interpolateProperty(layer.transform.rotation, frame));
      if (layer.transform.rotationX) {
        baseValues.set('transform.rotationX', interpolateProperty(layer.transform.rotationX, frame));
      }
      if (layer.transform.rotationY) {
        baseValues.set('transform.rotationY', interpolateProperty(layer.transform.rotationY, frame));
      }
      if (layer.transform.rotationZ) {
        baseValues.set('transform.rotationZ', interpolateProperty(layer.transform.rotationZ, frame));
      }

      // Opacity
      baseValues.set('opacity', interpolateProperty(layer.opacity, frame));

      return this.propertyDriverSystem.evaluateLayerDrivers(layerId, frame, baseValues);
    },

    /**
     * Add a property driver
     * Returns false if adding would create a circular dependency
     */
    addPropertyDriver(driver: PropertyDriver): boolean {
      // Check for cycles before adding
      if (this.propertyDriverSystem) {
        const added = this.propertyDriverSystem.addDriver(driver);
        if (!added) {
          console.warn('[Store] Cannot add property driver: would create circular dependency');
          return false;
        }
      }

      this.propertyDrivers.push(driver);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
      return true;
    },

    /**
     * Create and add an audio-driven property driver
     */
    createAudioPropertyDriver(
      targetLayerId: string,
      targetProperty: PropertyPath,
      audioFeature: 'amplitude' | 'bass' | 'mid' | 'high' | 'rms',
      options: { threshold?: number; scale?: number; offset?: number; smoothing?: number } = {}
    ): PropertyDriver {
      const driver = createAudioDriver(targetLayerId, targetProperty, audioFeature, options);
      this.addPropertyDriver(driver);
      return driver;
    },

    /**
     * Create and add a property-to-property link
     * Returns null if creating would cause a circular dependency
     */
    createPropertyLink(
      targetLayerId: string,
      targetProperty: PropertyPath,
      sourceLayerId: string,
      sourceProperty: PropertyPath,
      options: { scale?: number; offset?: number; blendMode?: 'replace' | 'add' | 'multiply' } = {}
    ): PropertyDriver | null {
      const driver = createPropertyLink(
        targetLayerId,
        targetProperty,
        sourceLayerId,
        sourceProperty,
        options
      );

      const success = this.addPropertyDriver(driver);
      if (!success) {
        return null; // Circular dependency detected
      }

      return driver;
    },

    /**
     * Remove a property driver
     */
    removePropertyDriver(driverId: string): void {
      const index = this.propertyDrivers.findIndex(d => d.id === driverId);
      if (index >= 0) {
        this.propertyDrivers.splice(index, 1);
      }

      if (this.propertyDriverSystem) {
        this.propertyDriverSystem.removeDriver(driverId);
      }

      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Update a property driver
     */
    updatePropertyDriver(driverId: string, updates: Partial<PropertyDriver>): void {
      const driver = this.propertyDrivers.find(d => d.id === driverId);
      if (driver) {
        Object.assign(driver, updates);
      }

      if (this.propertyDriverSystem) {
        this.propertyDriverSystem.updateDriver(driverId, updates);
      }

      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Get all drivers for a layer
     */
    getDriversForLayer(layerId: string): PropertyDriver[] {
      return this.propertyDrivers.filter(d => d.targetLayerId === layerId);
    },

    /**
     * Toggle driver enabled state
     */
    togglePropertyDriver(driverId: string): void {
      const driver = this.propertyDrivers.find(d => d.id === driverId);
      if (driver) {
        driver.enabled = !driver.enabled;
        if (this.propertyDriverSystem) {
          this.propertyDriverSystem.updateDriver(driverId, { enabled: driver.enabled });
        }
        this.project.meta.modified = new Date().toISOString();
      }
    }
  }
});
