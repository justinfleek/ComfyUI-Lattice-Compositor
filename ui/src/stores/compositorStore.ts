/**
 * Main Compositor Store
 *
 * Manages project state, layers, playback, and ComfyUI communication.
 */
import { defineStore } from 'pinia';
import type {
  WeylProject,
  Layer,
  AssetReference,
  AnimatableProperty,
  Keyframe,
  TextData,
  SplineData,
  ParticleLayerData,
  DepthflowLayerData,
  ParticleEmitterConfig,
  AudioParticleMapping
} from '@/types/project';
import type { AudioAnalysis, PeakData, PeakDetectionConfig } from '@/services/audioFeatures';
import { loadAudioFile, analyzeAudio, getFeatureAtFrame, detectPeaks, isBeatAtFrame } from '@/services/audioFeatures';
import { createEmptyProject, createDefaultTransform, createAnimatableProperty } from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';
import type { AudioMapping, TargetParameter } from '@/services/audioReactiveMapping';
import { AudioReactiveMapper } from '@/services/audioReactiveMapping';
import { AudioPathAnimator, type PathAnimatorConfig } from '@/services/audioPathAnimator';

interface CompositorState {
  // Project data
  project: WeylProject;

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

  // Audio-particle mappings (legacy)
  audioMappings: Map<string, AudioParticleMapping[]>;

  // New audio reactive system
  peakData: PeakData | null;
  audioReactiveMappings: AudioMapping[];
  audioReactiveMapper: AudioReactiveMapper | null;
  pathAnimators: Map<string, AudioPathAnimator>;
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => ({
    project: createEmptyProject(1024, 1024),
    comfyuiNodeId: null,
    sourceImage: null,
    depthMap: null,
    isPlaying: false,
    playbackRequestId: null,
    playbackStartTime: null,
    playbackStartFrame: 0,
    selectedLayerIds: [],
    selectedKeyframeIds: [],
    currentTool: 'select',
    graphEditorVisible: false,
    historyStack: [],
    historyIndex: -1,
    audioBuffer: null,
    audioAnalysis: null,
    audioFile: null,
    audioMappings: new Map(),
    peakData: null,
    audioReactiveMappings: [],
    audioReactiveMapper: null,
    pathAnimators: new Map()
  }),

  getters: {
    // Project info
    hasProject: (state): boolean => state.sourceImage !== null,
    width: (state): number => state.project.composition.width,
    height: (state): number => state.project.composition.height,
    frameCount: (state): number => state.project.composition.frameCount,
    fps: (state): number => state.project.composition.fps,
    duration: (state): number => state.project.composition.duration,

    // Current frame
    currentFrame: (state): number => state.project.currentFrame,
    currentTime: (state): number => state.project.currentFrame / state.project.composition.fps,

    // Layers
    layers: (state): Layer[] => state.project.layers,
    visibleLayers: (state): Layer[] => state.project.layers.filter(l => l.visible),

    // Selection
    selectedLayers: (state): Layer[] =>
      state.project.layers.filter(l => state.selectedLayerIds.includes(l.id)),
    selectedLayer: (state): Layer | null => {
      if (state.selectedLayerIds.length !== 1) return null;
      return state.project.layers.find(l => l.id === state.selectedLayerIds[0]) || null;
    },

    // Assets
    assets: (state): Record<string, AssetReference> => state.project.assets,

    // History
    canUndo: (state): boolean => state.historyIndex > 0,
    canRedo: (state): boolean => state.historyIndex < state.historyStack.length - 1
  },

  actions: {
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

      // Update project composition settings
      this.project.composition.width = inputs.width;
      this.project.composition.height = inputs.height;
      this.project.composition.frameCount = inputs.frame_count;
      this.project.composition.duration = inputs.frame_count / this.project.composition.fps;

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

      this.project.currentFrame = 0;
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

      const layer: Layer = {
        id,
        name: name || `${type.charAt(0).toUpperCase() + type.slice(1)} ${this.project.layers.length + 1}`,
        type,
        visible: true,
        locked: false,
        solo: false,
        inPoint: 0,
        outPoint: this.project.composition.frameCount - 1,
        parentId: null,
        blendMode: 'normal',
        opacity: createAnimatableProperty('opacity', 100, 'number'),
        transform: createDefaultTransform(),
        properties: [],
        data: null
      };

      this.project.layers.unshift(layer);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();

      return layer;
    },

    /**
     * Delete a layer
     */
    deleteLayer(layerId: string): void {
      const index = this.project.layers.findIndex(l => l.id === layerId);
      if (index === -1) return;

      this.project.layers.splice(index, 1);
      this.selectedLayerIds = this.selectedLayerIds.filter(id => id !== layerId);
      this.project.meta.modified = new Date().toISOString();
      this.pushHistory();
    },

    /**
     * Update layer properties
     */
    updateLayer(layerId: string, updates: Partial<Layer>): void {
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer) return;

      Object.assign(layer, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Reorder layers
     */
    moveLayer(layerId: string, newIndex: number): void {
      const currentIndex = this.project.layers.findIndex(l => l.id === layerId);
      if (currentIndex === -1) return;

      const [layer] = this.project.layers.splice(currentIndex, 1);
      this.project.layers.splice(newIndex, 0, layer);
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

    clearSelection(): void {
      this.selectedLayerIds = [];
      this.selectedKeyframeIds = [];
    },

    /**
     * Playback controls
     */
    play(): void {
      if (this.isPlaying) return;

      this.isPlaying = true;
      this.playbackStartTime = performance.now();
      this.playbackStartFrame = this.project.currentFrame;

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

      const elapsed = performance.now() - (this.playbackStartTime || 0);
      const fps = this.project.composition.fps;
      const frameCount = this.project.composition.frameCount;

      const elapsedFrames = Math.floor((elapsed / 1000) * fps);
      let newFrame = this.playbackStartFrame + elapsedFrames;

      // Loop playback
      if (newFrame >= frameCount) {
        newFrame = 0;
        this.playbackStartFrame = 0;
        this.playbackStartTime = performance.now();
      }

      this.project.currentFrame = newFrame;

      this.playbackRequestId = requestAnimationFrame(() => this.playbackLoop());
    },

    setFrame(frame: number): void {
      this.project.currentFrame = Math.max(0, Math.min(frame, this.project.composition.frameCount - 1));
    },

    nextFrame(): void {
      if (this.project.currentFrame < this.project.composition.frameCount - 1) {
        this.project.currentFrame++;
      }
    },

    prevFrame(): void {
      if (this.project.currentFrame > 0) {
        this.project.currentFrame--;
      }
    },

    goToStart(): void {
      this.project.currentFrame = 0;
    },

    goToEnd(): void {
      this.project.currentFrame = this.project.composition.frameCount - 1;
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
      return interpolateProperty(property, this.project.currentFrame);
    },

    /**
     * Add a keyframe to a property
     */
    addKeyframe<T>(
      layerId: string,
      propertyName: string,
      value: T
    ): Keyframe<T> | null {
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer) return null;

      // Find the property
      let property: AnimatableProperty<T> | undefined;

      // Check transform properties
      if (propertyName === 'position') {
        property = layer.transform.position as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'scale') {
        property = layer.transform.scale as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'rotation') {
        property = layer.transform.rotation as unknown as AnimatableProperty<T>;
      } else if (propertyName === 'opacity') {
        property = layer.opacity as unknown as AnimatableProperty<T>;
      } else {
        // Check custom properties
        property = layer.properties.find(p => p.name === propertyName) as AnimatableProperty<T> | undefined;
      }

      if (!property) return null;

      // Enable animation
      property.animated = true;

      // Create keyframe
      const keyframe: Keyframe<T> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        frame: this.project.currentFrame,
        value,
        interpolation: 'bezier',
        inHandle: { x: 0.33, y: 0.33 },
        outHandle: { x: 0.33, y: 0.33 },
        handlesBroken: false
      };

      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(k => k.frame === this.project.currentFrame);
      if (existingIndex >= 0) {
        property.keyframes[existingIndex] = keyframe;
      } else {
        property.keyframes.push(keyframe);
        property.keyframes.sort((a, b) => a.frame - b.frame);
      }

      this.project.meta.modified = new Date().toISOString();
      return keyframe;
    },

    /**
     * Remove a keyframe
     */
    removeKeyframe(layerId: string, propertyName: string, keyframeId: string): void {
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer) return;

      // Find the property
      let property: AnimatableProperty<any> | undefined;

      if (propertyName === 'position') {
        property = layer.transform.position;
      } else if (propertyName === 'scale') {
        property = layer.transform.scale;
      } else if (propertyName === 'rotation') {
        property = layer.transform.rotation;
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
     * Create a text layer with proper data structure
     */
    createTextLayer(text: string = 'Text'): Layer {
      const layer = this.createLayer('text', text.substring(0, 20));

      // Set up text data
      const textData: TextData = {
        text,
        fontFamily: 'Arial',
        fontSize: 48,
        fontWeight: '400',
        fontStyle: 'normal',
        fill: '#ffffff',
        stroke: '',
        strokeWidth: 0,
        letterSpacing: 0,
        lineHeight: 1.2,
        textAlign: 'left',
        pathLayerId: null,
        pathOffset: 0,
        pathAlign: 'left'
      };

      layer.data = textData;

      // Add animatable properties for text
      layer.properties.push(createAnimatableProperty('fontSize', 48, 'number'));
      layer.properties.push(createAnimatableProperty('pathOffset', 0, 'number'));
      layer.properties.push(createAnimatableProperty('letterSpacing', 0, 'number'));

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
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      Object.assign(data, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Add emitter to particle layer
     */
    addParticleEmitter(layerId: string, config: ParticleEmitterConfig): void {
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer || layer.type !== 'particles') return;

      const data = layer.data as ParticleLayerData;
      data.emitters.push(config);
      this.project.meta.modified = new Date().toISOString();
    },

    /**
     * Update particle emitter
     */
    updateParticleEmitter(layerId: string, emitterId: string, updates: Partial<ParticleEmitterConfig>): void {
      const layer = this.project.layers.find(l => l.id === layerId);
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
      const layer = this.project.layers.find(l => l.id === layerId);
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
      const layer = this.project.layers.find(l => l.id === layerId);
      if (!layer || layer.type !== 'depthflow') return;

      const data = layer.data as DepthflowLayerData;
      Object.assign(data.config, updates);
      this.project.meta.modified = new Date().toISOString();
    },

    // ============================================================
    // AUDIO ACTIONS
    // ============================================================

    /**
     * Load audio file for analysis
     */
    async loadAudio(file: File): Promise<void> {
      try {
        this.audioFile = file;
        this.audioBuffer = await loadAudioFile(file);
        this.audioAnalysis = await analyzeAudio(this.audioBuffer, this.project.composition.fps);

        // Initialize the audio reactive mapper
        this.initializeAudioReactiveMapper();

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
      }
    },

    /**
     * Clear loaded audio
     */
    clearAudio(): void {
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
      return getFeatureAtFrame(this.audioAnalysis, feature, frame ?? this.project.currentFrame);
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
      return this.audioReactiveMapper.getAllValuesAtFrame(frame ?? this.project.currentFrame);
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
     * Check if current frame is a beat
     */
    isBeatAtCurrentFrame(): boolean {
      if (!this.audioAnalysis) return false;
      return isBeatAtFrame(this.audioAnalysis, this.project.currentFrame);
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

      const frame = this.project.currentFrame;
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
    }
  }
});
