/**
 * WeylEngine - Main Engine Facade
 *
 * The primary interface for the Weyl Compositor rendering engine.
 * Provides a clean API for Vue components to interact with the Three.js rendering system.
 *
 * @example
 * ```typescript
 * const engine = new WeylEngine({
 *   canvas: canvasElement,
 *   width: 1920,
 *   height: 1080,
 * });
 *
 * engine.addLayer(layerData);
 * engine.setFrame(0);
 * engine.render();
 * ```
 */

import * as THREE from 'three';
import { TransformControls } from 'three/examples/jsm/controls/TransformControls.js';
import { SceneManager } from './core/SceneManager';
import { RenderPipeline } from './core/RenderPipeline';
import { LayerManager } from './core/LayerManager';
import { CameraController } from './core/CameraController';
import { ResourceManager } from './core/ResourceManager';
import { PerformanceMonitor } from './utils/PerformanceMonitor';
import type {
  WeylEngineConfig,
  RenderState,
  PerformanceStats,
  EngineEventType,
  EngineEventHandler,
  EngineEvent,
  CaptureResult,
  DepthCaptureResult,
  ExportFrameOptions,
} from './types';
import type { Layer } from '@/types/project';
import type { TargetParameter } from '@/services/audioReactiveMapping';
import { engineLogger } from '@/utils/logger';
import type { FrameState } from './MotionEngine';

// Import 3D services for initialization
import { materialSystem } from '@/services/materialSystem';
import { svgExtrusionService } from '@/services/svgExtrusion';
import { meshParticleManager } from '@/services/meshParticleManager';
import { spriteSheetService } from '@/services/spriteSheet';

/** Callback to get audio reactive values at a frame */
export type AudioReactiveGetter = (frame: number) => Map<TargetParameter, number>;

/** Callback to get audio reactive values for a specific layer */
export type LayerAudioReactiveGetter = (layerId: string, frame: number) => Map<TargetParameter, number>;

/** Layer transform update from TransformControls manipulation */
export interface LayerTransformUpdate {
  position?: { x: number; y: number; z?: number };
  rotation?: number;  // Z rotation in degrees
  rotationX?: number;
  rotationY?: number;
  rotationZ?: number;
  scale?: { x: number; y: number; z?: number };
}

export class WeylEngine {
  // Core subsystems
  private readonly scene: SceneManager;
  private readonly renderer: RenderPipeline;
  private readonly layers: LayerManager;
  private readonly camera: CameraController;
  private readonly resources: ResourceManager;
  private readonly performance: PerformanceMonitor;

  // State
  private state: RenderState;
  private animationFrameId: number | null = null;

  // Background and overlay images
  private backgroundImage: THREE.Mesh | null = null;
  private depthMapMesh: THREE.Mesh | null = null;
  private depthMapSettings: {
    colormap: 'viridis' | 'plasma' | 'grayscale';
    opacity: number;
    visible: boolean;
  } = { colormap: 'viridis', opacity: 0.5, visible: false };

  // Viewport transform for pan/zoom
  private viewportTransform: number[] = [1, 0, 0, 1, 0, 0];

  // Render mode
  private renderMode: 'color' | 'depth' | 'normal' = 'color';

  // Audio reactivity
  private audioReactiveGetter: LayerAudioReactiveGetter | null = null;

  // Transform controls for layer manipulation
  private transformControls: TransformControls | null = null;
  private selectedLayerId: string | null = null;
  private transformMode: 'translate' | 'rotate' | 'scale' = 'translate';

  // Transform change callback
  private onTransformChange: ((layerId: string, transform: LayerTransformUpdate) => void) | null = null;

  // Event system
  private readonly eventHandlers: Map<EngineEventType, Set<EngineEventHandler>>;

  // Configuration
  private readonly config: Required<WeylEngineConfig>;

  constructor(config: WeylEngineConfig) {
    // Validate input
    this.validateConfig(config);

    // Merge with defaults
    this.config = {
      canvas: config.canvas,
      width: config.width,
      height: config.height,
      compositionWidth: config.compositionWidth ?? config.width,
      compositionHeight: config.compositionHeight ?? config.height,
      pixelRatio: config.pixelRatio ?? Math.min(window.devicePixelRatio, 2),
      antialias: config.antialias ?? true,
      alpha: config.alpha ?? true,
      backgroundColor: config.backgroundColor ?? null,
      debug: config.debug ?? false,
      powerPreference: config.powerPreference ?? 'high-performance',
    };

    // Initialize state
    // NOTE: state.currentFrame is DEPRECATED as time authority
    // The sole authority is now MotionEngine.evaluate(frame)
    // This field is kept for backwards compatibility but should not be
    // used as source of truth. Use applyFrameState() instead of setFrame().
    this.state = {
      currentFrame: 0, // DEPRECATED: Use MotionEngine as time authority
      isRendering: false,
      isDisposed: false,
      viewport: {
        width: this.config.width,
        height: this.config.height,
      },
    };

    // Initialize event system
    this.eventHandlers = new Map();

    // Initialize subsystems in dependency order
    this.resources = new ResourceManager();
    this.scene = new SceneManager(this.config.backgroundColor);
    // Camera is initialized with COMPOSITION dimensions for position/target calculation
    // but we'll update the aspect ratio to match viewport
    this.camera = new CameraController(
      this.config.compositionWidth!,
      this.config.compositionHeight!
    );
    // Update camera aspect ratio to match viewport (required for correct rendering)
    this.camera.camera.aspect = this.config.width / this.config.height;
    this.camera.camera.updateProjectionMatrix();

    this.renderer = new RenderPipeline({
      canvas: this.config.canvas,
      width: this.config.width,
      height: this.config.height,
      pixelRatio: this.config.pixelRatio,
      antialias: this.config.antialias,
      alpha: this.config.alpha,
    }, this.scene, this.camera);
    this.layers = new LayerManager(this.scene, this.resources);
    this.performance = new PerformanceMonitor();

    // Set composition size for bounds
    this.scene.setCompositionSize(
      this.config.compositionWidth!,
      this.config.compositionHeight!
    );

    // Handle WebGL context loss
    this.setupContextLossHandling();

    if (this.config.debug) {
      engineLogger.debug('Initialized', this.config);
    }
  }

  // ============================================================================
  // CONFIGURATION VALIDATION
  // ============================================================================

  private validateConfig(config: WeylEngineConfig): void {
    if (!(config.canvas instanceof HTMLCanvasElement)) {
      throw new Error('WeylEngine requires a valid HTMLCanvasElement');
    }

    if (config.width <= 0 || config.height <= 0) {
      throw new Error('WeylEngine requires positive width and height');
    }

    if (config.width > 8192 || config.height > 8192) {
      throw new Error('WeylEngine maximum dimension is 8192 pixels');
    }
  }

  // ============================================================================
  // LAYER MANAGEMENT
  // ============================================================================

  /**
   * Add a layer to the composition
   * @param layerData - The layer data from the project schema
   */
  addLayer(layerData: Layer): void {
    this.assertNotDisposed();

    this.layers.create(layerData);
    this.emit('layerAdded', { layerId: layerData.id });

    if (this.config.debug) {
      engineLogger.debug('Layer added:', layerData.id, layerData.type);
    }
  }

  /**
   * Update a layer's properties
   * @param layerId - The layer ID to update
   * @param properties - Partial layer properties to update
   */
  updateLayer(layerId: string, properties: Partial<Layer>): void {
    this.assertNotDisposed();

    this.layers.update(layerId, properties);
    this.emit('layerUpdated', { layerId, properties });
  }

  /**
   * Remove a layer from the composition
   * @param layerId - The layer ID to remove
   */
  removeLayer(layerId: string): void {
    this.assertNotDisposed();

    this.layers.remove(layerId);
    this.emit('layerRemoved', { layerId });

    if (this.config.debug) {
      engineLogger.debug('Layer removed:', layerId);
    }
  }

  /**
   * Get all layer IDs currently in the composition
   */
  getLayerIds(): string[] {
    return this.layers.getLayerIds();
  }

  /**
   * Get the Three.js object for a layer (for advanced manipulation)
   * @param layerId - The layer ID
   */
  getLayerObject(layerId: string): THREE.Object3D | null {
    return this.layers.getObject(layerId);
  }

  /**
   * Sync all layers from store data
   * @param layers - Array of layer data from store
   */
  syncLayers(layers: Layer[]): void {
    this.assertNotDisposed();

    const existingIds = new Set(this.layers.getLayerIds());
    const newIds = new Set(layers.map(l => l.id));

    // Remove layers that no longer exist
    for (const id of existingIds) {
      if (!newIds.has(id)) {
        this.layers.remove(id);
      }
    }

    // Add or update layers
    for (const layer of layers) {
      if (existingIds.has(layer.id)) {
        this.layers.update(layer.id, layer);
      } else {
        this.layers.create(layer);
      }
    }
  }

  // ============================================================================
  // CALLBACKS & INTEGRATION
  // ============================================================================

  /**
   * Set the asset getter callback for ResourceManager
   * This allows layers to access project assets
   * @param getter - Function that retrieves assets by ID
   */
  setAssetGetter(getter: (assetId: string) => import('@/types/project').AssetReference | undefined): void {
    this.resources.setAssetGetter(getter);
  }

  /**
   * Set the video metadata callback for LayerManager
   * Called when a video layer finishes loading its metadata
   * @param callback - Function called with layer ID and video metadata
   */
  setVideoMetadataCallback(callback: (layerId: string, metadata: import('./layers/VideoLayer').VideoMetadata) => void): void {
    this.layers.setVideoMetadataCallback(callback);
  }

  /**
   * Set the precomp render context for LayerManager
   * Allows precomp layers to render nested compositions
   * @param context - Render context with composition access
   */
  setPrecompRenderContext(context: import('./layers/PrecompLayer').PrecompRenderContext): void {
    this.layers.setPrecompRenderContext(context);
  }

  /**
   * Set camera callbacks for LayerManager
   * Allows camera layers to access Camera3D data from store
   * @param getter - Function to get Camera3D by ID
   * @param updater - Function to update Camera3D properties
   * @param atFrameGetter - Function to get Camera3D with keyframe interpolation at a specific frame
   */
  setCameraCallbacks(
    getter: import('./layers/CameraLayer').CameraGetter,
    updater: import('./layers/CameraLayer').CameraUpdater,
    atFrameGetter?: import('./layers/CameraLayer').CameraAtFrameGetter
  ): void {
    this.layers.setCameraCallbacks(getter, updater, atFrameGetter);
    // Store getter for active camera sync
    this.activeCameraGetter = getter;
  }

  // Active camera tracking
  private activeCameraGetter?: import('./layers/CameraLayer').CameraGetter;
  private activeCameraId: string | null = null;

  /**
   * Set the active camera layer that drives the render view
   * @param cameraLayerId - The camera layer ID, or null to use default camera
   */
  setActiveCameraLayer(cameraLayerId: string | null): void {
    this.activeCameraId = cameraLayerId;
  }

  /**
   * Sync render camera from active CameraLayer
   * Called during frame evaluation to update the actual render camera
   */
  private syncActiveCamera(): void {
    if (!this.activeCameraId || !this.activeCameraGetter) {
      return;
    }

    // Get the CameraLayer instance
    const cameraLayer = this.layers.getLayer(this.activeCameraId);
    if (!cameraLayer || cameraLayer.type !== 'camera') {
      return;
    }

    // Get Camera3D data from store via the layer
    const typedLayer = cameraLayer as import('./layers/CameraLayer').CameraLayer;
    const exportData = typedLayer.getExportData();
    if (!exportData) {
      return;
    }

    // Update the render camera from Camera3D data
    // Position
    this.camera.setPosition(exportData.position.x, exportData.position.y, exportData.position.z);

    // Rotation (Camera3D uses degrees)
    this.camera.setRotation(exportData.rotation.x, exportData.rotation.y, exportData.rotation.z);

    // FOV
    this.camera.setFOV(exportData.fov);

    // Clip planes
    this.camera.setClipPlanes(exportData.nearClip, exportData.farClip);

    // Sync DOF settings from camera
    const camera3d = typedLayer.getCameraAtCurrentFrame();
    if (camera3d && camera3d.depthOfField) {
      this.setDOFFromCamera(camera3d.depthOfField);
    }
  }

  /**
   * Set composition FPS for particle timing
   * @param fps - Frames per second
   */
  setCompositionFPS(fps: number): void {
    this.layers.setCompositionFPS(fps);
  }

  /**
   * Initialize particle systems with WebGL renderer
   * Must be called after engine initialization to enable GPU particles
   */
  initializeParticleSystems(): void {
    this.layers.setRenderer(this.renderer.getWebGLRenderer());
    this.layers.setCamera(this.camera.camera);
  }

  /**
   * Initialize all 3D services with WebGL renderer
   * This enables:
   * - Material system PMREM for environment map prefiltering
   * - Environment map support in SceneManager
   * Call this after engine construction for full 3D pipeline support
   */
  initialize3DServices(): void {
    const renderer = this.renderer.getWebGLRenderer();

    // Initialize material system for PMREM
    materialSystem.initialize(renderer);

    // Initialize environment map support
    this.scene.initializeEnvironmentSupport(renderer);

    // Log initialization
    if (this.config.debug) {
      engineLogger.debug('3D services initialized');
    }
  }

  // ============================================================================
  // 3D SERVICE ACCESS
  // ============================================================================

  /**
   * Get the material system for PBR material management
   */
  getMaterialSystem() {
    return materialSystem;
  }

  /**
   * Get the SVG extrusion service for logo workflows
   */
  getSVGExtrusionService() {
    return svgExtrusionService;
  }

  /**
   * Get the mesh particle manager for custom particle shapes
   */
  getMeshParticleManager() {
    return meshParticleManager;
  }

  /**
   * Get the sprite sheet service for particle animations
   */
  getSpriteSheetService() {
    return spriteSheetService;
  }

  /**
   * Get the current camera position (for particle systems, etc.)
   * Returns world-space position of the active camera
   */
  getCameraPosition(): THREE.Vector3 {
    return this.camera.camera.position.clone();
  }

  /**
   * Get the camera's projection and view matrices
   * Useful for depth calculations and screen-space effects
   */
  getCameraMatrices(): {
    projectionMatrix: THREE.Matrix4;
    viewMatrix: THREE.Matrix4;
    projectionMatrixInverse: THREE.Matrix4;
  } {
    const cam = this.camera.camera;
    return {
      projectionMatrix: cam.projectionMatrix.clone(),
      viewMatrix: cam.matrixWorldInverse.clone(),
      projectionMatrixInverse: cam.projectionMatrixInverse.clone(),
    };
  }

  // ============================================================================
  // PROPERTY DRIVERS (Expressions/Links)
  // ============================================================================

  /**
   * Set driven values for a layer
   * Used by the expression/driver system to override animated properties
   */
  setLayerDrivenValues(layerId: string, values: Map<string, number>): void {
    this.layers.setLayerDrivenValues(layerId, values);
  }

  /**
   * Clear driven values for a layer
   */
  clearLayerDrivenValues(layerId: string): void {
    this.layers.clearLayerDrivenValues(layerId);
  }

  /**
   * Clear all driven values for all layers
   */
  clearAllDrivenValues(): void {
    this.layers.clearAllDrivenValues();
  }

  /**
   * Get the Three.js camera directly (for advanced use)
   */
  getCamera(): THREE.PerspectiveCamera {
    return this.camera.camera;
  }

  // ============================================================================
  // ANIMATION & TIMELINE
  // ============================================================================

  /**
   * Apply a pre-evaluated FrameState from MotionEngine
   *
   * This is the CANONICAL way to update the rendering state.
   * FrameState is computed by MotionEngine.evaluate() which is PURE.
   *
   * ARCHITECTURAL RULE:
   * - Layers receive already-evaluated values via applyEvaluatedState()
   * - NO interpolation or time sampling happens here
   * - Single source of truth: MotionEngine
   *
   * @param frameState - Pre-evaluated state from MotionEngine.evaluate()
   */
  applyFrameState(frameState: FrameState): void {
    this.assertNotDisposed();

    // Update internal frame reference (for events and backwards compat)
    this.state.currentFrame = frameState.frame;

    // Apply evaluated layer states - NO RE-EVALUATION
    // Layers only apply pre-computed values from MotionEngine
    // Pass frame for animated spline evaluation in text-on-path
    this.layers.applyEvaluatedState(frameState.layers, frameState.frame);

    // Apply camera state if present
    if (frameState.camera) {
      this.applyCameraState(frameState.camera);
    } else {
      // Sync render camera from active CameraLayer (if set)
      this.syncActiveCamera();

      // Fallback: evaluate CameraController's own animation
      if (!this.activeCameraId) {
        this.camera.evaluateFrame(frameState.frame);
      }
    }
  }

  /**
   * Apply evaluated camera state directly
   */
  private applyCameraState(cameraState: FrameState['camera']): void {
    if (!cameraState) return;

    // Update camera controller with evaluated values
    this.camera.setPositionDirect(
      cameraState.position.x,
      cameraState.position.y,
      cameraState.position.z
    );
    this.camera.setTargetDirect(
      cameraState.target.x,
      cameraState.target.y,
      cameraState.target.z
    );
    this.camera.setFOV(cameraState.fov);
  }

  /**
   * Set the current frame for animation evaluation
   *
   * @deprecated Use applyFrameState() with MotionEngine.evaluate() instead.
   * This method evaluates frames directly, bypassing the single time authority.
   * It is kept for backwards compatibility but should be phased out.
   *
   * @param frame - The frame number (0-indexed)
   */
  setFrame(frame: number): void {
    this.assertNotDisposed();

    this.state.currentFrame = frame;

    // Evaluate layers with audio reactive values if available
    this.layers.evaluateFrame(frame, this.audioReactiveGetter);

    // Sync render camera from active CameraLayer (if set)
    // This must happen AFTER layer evaluation so camera position is updated
    this.syncActiveCamera();

    // Fallback: evaluate CameraController's own animation (if no active camera layer)
    if (!this.activeCameraId) {
      this.camera.evaluateFrame(frame);
    }
  }

  /**
   * Set the audio reactive getter callback
   * This callback will be called during frame evaluation to get audio-modulated values
   */
  setAudioReactiveCallback(getter: LayerAudioReactiveGetter | null): void {
    this.audioReactiveGetter = getter;
    this.layers.setAudioReactiveCallback(getter);
  }

  /**
   * Get the current frame
   * @deprecated Frame authority is now MotionEngine. This returns cached value.
   */
  getCurrentFrame(): number {
    return this.state.currentFrame;
  }

  // ============================================================================
  // RENDERING
  // ============================================================================

  /**
   * Render the current frame
   */
  render(): void {
    this.assertNotDisposed();

    this.performance.beginFrame();
    this.emit('frameStart', { frame: this.state.currentFrame });

    // Update orbit controls if enabled (for smooth damping)
    this.camera.updateOrbitControls();

    this.renderer.render();

    this.emit('frameEnd', { frame: this.state.currentFrame });
    this.performance.endFrame(this.renderer.getWebGLRenderer());
  }

  /**
   * Start continuous rendering loop
   */
  startRenderLoop(): void {
    this.assertNotDisposed();

    if (this.animationFrameId !== null) {
      return; // Already running
    }

    this.state.isRendering = true;

    const loop = () => {
      if (!this.state.isRendering || this.state.isDisposed) {
        return;
      }

      this.render();
      this.animationFrameId = requestAnimationFrame(loop);
    };

    this.animationFrameId = requestAnimationFrame(loop);
  }

  /**
   * Stop continuous rendering loop
   */
  stopRenderLoop(): void {
    this.state.isRendering = false;

    if (this.animationFrameId !== null) {
      cancelAnimationFrame(this.animationFrameId);
      this.animationFrameId = null;
    }
  }

  /**
   * Check if render loop is active
   */
  isRenderLoopActive(): boolean {
    return this.state.isRendering;
  }

  // ============================================================================
  // VIEWPORT
  // ============================================================================

  /**
   * Resize the viewport
   * @param width - New viewport width in pixels
   * @param height - New viewport height in pixels
   * @param compositionWidth - Optional new composition width
   * @param compositionHeight - Optional new composition height
   */
  resize(
    width: number,
    height: number,
    compositionWidth?: number,
    compositionHeight?: number
  ): void {
    this.assertNotDisposed();

    if (width <= 0 || height <= 0) {
      engineLogger.warn('Invalid resize dimensions:', width, height);
      return;
    }

    this.state.viewport = { width, height };
    this.renderer.resize(width, height);

    // Use composition dimensions for camera if provided
    const camWidth = compositionWidth ?? width;
    const camHeight = compositionHeight ?? height;
    this.camera.resize(camWidth, camHeight);

    this.emit('resize', { width, height, compositionWidth, compositionHeight });
  }

  /**
   * Get current viewport dimensions
   */
  getViewport(): { width: number; height: number } {
    return { ...this.state.viewport };
  }

  // ============================================================================
  // CAMERA
  // ============================================================================

  /**
   * Get the camera controller for advanced camera manipulation
   */
  getCameraController(): CameraController {
    return this.camera;
  }

  /**
   * Enable 3D orbit controls for camera navigation
   * Right-click = orbit, middle-click = pan, scroll = dolly
   */
  enableOrbitControls(): void {
    const domElement = this.renderer.getDomElement();
    this.camera.enableOrbitControls(domElement);
  }

  /**
   * Disable 3D orbit controls
   */
  disableOrbitControls(): void {
    this.camera.disableOrbitControls();
  }

  /**
   * Reset camera to default viewing position
   */
  resetCameraToDefault(): void {
    this.camera.resetToDefault();
  }

  /**
   * Check if orbit controls are enabled
   */
  hasOrbitControls(): boolean {
    return this.camera.hasOrbitControls();
  }

  /**
   * Set camera position
   */
  setCameraPosition(x: number, y: number, z: number): void {
    this.camera.setPosition(x, y, z);
  }

  /**
   * Set camera target (look-at point)
   */
  setCameraTarget(x: number, y: number, z: number): void {
    this.camera.setTarget(x, y, z);
  }

  /**
   * Set camera field of view
   */
  setCameraFOV(fov: number): void {
    this.camera.setFOV(fov);
  }

  // ============================================================================
  // DEPTH OF FIELD
  // ============================================================================

  /**
   * Configure depth of field from Camera3D DOF settings
   * @param dof - Camera3D.depthOfField settings
   */
  setDOFFromCamera(dof: {
    enabled: boolean;
    focusDistance: number;
    aperture: number;
    blurLevel: number;
  }): void {
    this.renderer.setDOF({
      enabled: dof.enabled,
      focusDistance: dof.focusDistance,
      // Convert aperture to BokehPass scale (smaller = more blur)
      aperture: dof.aperture * 0.0001,
      maxBlur: dof.blurLevel * 0.02,
    });
  }

  /**
   * Enable or disable DOF
   */
  setDOFEnabled(enabled: boolean): void {
    this.renderer.setDOFEnabled(enabled);
  }

  /**
   * Set DOF focus distance
   * @param distance - Focus distance in world units
   */
  setDOFFocusDistance(distance: number): void {
    this.renderer.setFocusDistance(distance);
  }

  /**
   * Set DOF aperture
   * @param aperture - Aperture value (higher = more blur)
   */
  setDOFAperture(aperture: number): void {
    this.renderer.setAperture(aperture * 0.0001);
  }

  /**
   * Get current DOF configuration
   */
  getDOF(): import('./core/RenderPipeline').DOFConfig {
    return this.renderer.getDOF();
  }

  // ============================================================================
  // SSAO (Screen Space Ambient Occlusion)
  // ============================================================================

  /**
   * Configure SSAO effect
   * @param config - SSAO configuration options
   */
  setSSAO(config: Partial<import('./core/RenderPipeline').SSAOConfig>): void {
    this.renderer.setSSAO(config);
  }

  /**
   * Enable or disable SSAO
   */
  setSSAOEnabled(enabled: boolean): void {
    this.renderer.setSSAOEnabled(enabled);
  }

  /**
   * Set SSAO intensity
   * @param intensity - Occlusion intensity multiplier
   */
  setSSAOIntensity(intensity: number): void {
    this.renderer.setSSAOIntensity(intensity);
  }

  /**
   * Set SSAO sampling radius
   * @param radius - Kernel radius for occlusion sampling
   */
  setSSAORadius(radius: number): void {
    this.renderer.setSSAORadius(radius);
  }

  /**
   * Get current SSAO configuration
   */
  getSSAO(): import('./core/RenderPipeline').SSAOConfig {
    return this.renderer.getSSAO();
  }

  // ============================================================================
  // BLOOM (Emissive Glow)
  // ============================================================================

  /**
   * Configure bloom effect
   * Makes emissive objects (lights, bright particles) glow
   * @param config - Bloom configuration options
   */
  setBloom(config: Partial<import('./core/RenderPipeline').BloomConfig>): void {
    this.renderer.setBloom(config);
  }

  /**
   * Enable or disable bloom
   */
  setBloomEnabled(enabled: boolean): void {
    this.renderer.setBloomEnabled(enabled);
  }

  /**
   * Set bloom intensity
   * @param strength - Bloom strength multiplier
   */
  setBloomStrength(strength: number): void {
    this.renderer.setBloomStrength(strength);
  }

  /**
   * Set bloom threshold
   * @param threshold - Brightness threshold for bloom (0-1)
   */
  setBloomThreshold(threshold: number): void {
    this.renderer.setBloomThreshold(threshold);
  }

  /**
   * Get current bloom configuration
   */
  getBloom(): import('./core/RenderPipeline').BloomConfig {
    return this.renderer.getBloom();
  }

  // ============================================================================
  // VIEWPORT TRANSFORM (PAN/ZOOM)
  // ============================================================================

  /**
   * Set the viewport transform for pan/zoom operations
   * @param transform - [scaleX, skewX, skewY, scaleY, translateX, translateY]
   */
  setViewportTransform(transform: number[]): void {
    this.viewportTransform = [...transform];

    // Apply to camera for 2D-style panning
    const scale = transform[0];
    const tx = transform[4];
    const ty = transform[5];

    // Update camera position based on viewport transform
    this.camera.setZoom(scale);
    this.camera.setPan(tx, ty);
  }

  /**
   * Get the current viewport transform
   */
  getViewportTransform(): number[] {
    return [...this.viewportTransform];
  }

  // ============================================================================
  // BACKGROUND & OVERLAYS
  // ============================================================================

  /**
   * Set a background image for the composition
   * @param image - HTMLImageElement to use as background
   */
  setBackgroundImage(image: HTMLImageElement): void {
    this.assertNotDisposed();

    // Remove existing background
    if (this.backgroundImage) {
      this.scene.removeFromComposition(this.backgroundImage);
      this.backgroundImage.geometry.dispose();
      (this.backgroundImage.material as THREE.Material).dispose();
    }

    // Create texture from image
    const texture = new THREE.Texture(image);
    texture.needsUpdate = true;
    texture.colorSpace = THREE.SRGBColorSpace;

    // Create plane geometry matching image dimensions
    const geometry = new THREE.PlaneGeometry(image.width, image.height);
    const material = new THREE.MeshBasicMaterial({
      map: texture,
      transparent: true,
      depthWrite: false,
    });

    this.backgroundImage = new THREE.Mesh(geometry, material);
    this.backgroundImage.position.set(image.width / 2, image.height / 2, -1000);
    this.backgroundImage.userData.isBackground = true;

    this.scene.addToComposition(this.backgroundImage);
  }

  /**
   * Set the depth map overlay
   * @param image - HTMLImageElement containing depth data
   * @param options - Display options
   */
  setDepthMap(
    image: HTMLImageElement,
    options: { colormap?: 'viridis' | 'plasma' | 'grayscale'; opacity?: number; visible?: boolean }
  ): void {
    this.assertNotDisposed();

    this.depthMapSettings = {
      colormap: options.colormap ?? this.depthMapSettings.colormap,
      opacity: options.opacity ?? this.depthMapSettings.opacity,
      visible: options.visible ?? this.depthMapSettings.visible,
    };

    // Remove existing depth map mesh
    if (this.depthMapMesh) {
      this.scene.removeFromComposition(this.depthMapMesh);
      this.depthMapMesh.geometry.dispose();
      (this.depthMapMesh.material as THREE.Material).dispose();
    }

    // Create texture from image
    const texture = new THREE.Texture(image);
    texture.needsUpdate = true;

    // Create colormap shader material
    const material = this.createColormapMaterial(texture, this.depthMapSettings);

    const geometry = new THREE.PlaneGeometry(image.width, image.height);
    this.depthMapMesh = new THREE.Mesh(geometry, material);
    this.depthMapMesh.position.set(image.width / 2, image.height / 2, -999);
    this.depthMapMesh.visible = this.depthMapSettings.visible;
    this.depthMapMesh.userData.isDepthOverlay = true;

    this.scene.addToComposition(this.depthMapMesh);
  }

  /**
   * Create a colormap shader material for depth visualization
   */
  private createColormapMaterial(
    texture: THREE.Texture,
    settings: { colormap: string; opacity: number }
  ): THREE.ShaderMaterial {
    const vertexShader = `
      varying vec2 vUv;
      void main() {
        vUv = uv;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `;

    const fragmentShader = `
      uniform sampler2D depthMap;
      uniform float opacity;
      uniform int colormap;
      varying vec2 vUv;

      vec3 viridis(float t) {
        const vec3 c0 = vec3(0.267, 0.004, 0.329);
        const vec3 c1 = vec3(0.282, 0.140, 0.458);
        const vec3 c2 = vec3(0.253, 0.265, 0.529);
        const vec3 c3 = vec3(0.191, 0.407, 0.556);
        const vec3 c4 = vec3(0.127, 0.566, 0.551);
        const vec3 c5 = vec3(0.208, 0.718, 0.472);
        const vec3 c6 = vec3(0.565, 0.843, 0.262);
        const vec3 c7 = vec3(0.993, 0.906, 0.144);

        t = clamp(t, 0.0, 1.0);
        float i = t * 7.0;
        int idx = int(floor(i));
        float f = fract(i);

        if (idx < 1) return mix(c0, c1, f);
        if (idx < 2) return mix(c1, c2, f);
        if (idx < 3) return mix(c2, c3, f);
        if (idx < 4) return mix(c3, c4, f);
        if (idx < 5) return mix(c4, c5, f);
        if (idx < 6) return mix(c5, c6, f);
        return mix(c6, c7, f);
      }

      vec3 plasma(float t) {
        const vec3 c0 = vec3(0.050, 0.030, 0.528);
        const vec3 c1 = vec3(0.327, 0.012, 0.615);
        const vec3 c2 = vec3(0.534, 0.054, 0.553);
        const vec3 c3 = vec3(0.716, 0.215, 0.475);
        const vec3 c4 = vec3(0.863, 0.395, 0.362);
        const vec3 c5 = vec3(0.958, 0.590, 0.233);
        const vec3 c6 = vec3(0.995, 0.812, 0.166);
        const vec3 c7 = vec3(0.940, 0.975, 0.131);

        t = clamp(t, 0.0, 1.0);
        float i = t * 7.0;
        int idx = int(floor(i));
        float f = fract(i);

        if (idx < 1) return mix(c0, c1, f);
        if (idx < 2) return mix(c1, c2, f);
        if (idx < 3) return mix(c2, c3, f);
        if (idx < 4) return mix(c3, c4, f);
        if (idx < 5) return mix(c4, c5, f);
        if (idx < 6) return mix(c5, c6, f);
        return mix(c6, c7, f);
      }

      void main() {
        float depth = texture2D(depthMap, vUv).r;
        vec3 color;

        if (colormap == 0) {
          color = viridis(depth);
        } else if (colormap == 1) {
          color = plasma(depth);
        } else {
          color = vec3(depth);
        }

        gl_FragColor = vec4(color, opacity);
      }
    `;

    const colormapIndex = settings.colormap === 'viridis' ? 0 : settings.colormap === 'plasma' ? 1 : 2;

    return new THREE.ShaderMaterial({
      uniforms: {
        depthMap: { value: texture },
        opacity: { value: settings.opacity },
        colormap: { value: colormapIndex },
      },
      vertexShader,
      fragmentShader,
      transparent: true,
      depthWrite: false,
    });
  }

  /**
   * Set depth overlay visibility
   */
  setDepthOverlayVisible(visible: boolean): void {
    this.depthMapSettings.visible = visible;
    if (this.depthMapMesh) {
      this.depthMapMesh.visible = visible;
    }
  }

  /**
   * Set depth colormap
   */
  setDepthColormap(colormap: 'viridis' | 'plasma' | 'grayscale'): void {
    this.depthMapSettings.colormap = colormap;
    if (this.depthMapMesh) {
      const material = this.depthMapMesh.material as THREE.ShaderMaterial;
      const colormapIndex = colormap === 'viridis' ? 0 : colormap === 'plasma' ? 1 : 2;
      material.uniforms.colormap.value = colormapIndex;
    }
  }

  /**
   * Set depth overlay opacity
   */
  setDepthOpacity(opacity: number): void {
    this.depthMapSettings.opacity = opacity;
    if (this.depthMapMesh) {
      const material = this.depthMapMesh.material as THREE.ShaderMaterial;
      material.uniforms.opacity.value = opacity;
    }
  }

  // ============================================================================
  // RENDER MODE
  // ============================================================================

  /**
   * Set the render mode (color, depth, normal)
   */
  setRenderMode(mode: 'color' | 'depth' | 'normal'): void {
    this.renderMode = mode;
    this.renderer.setRenderMode(mode);
  }

  /**
   * Get the current render mode
   */
  getRenderMode(): 'color' | 'depth' | 'normal' {
    return this.renderMode;
  }

  // ============================================================================
  // ENVIRONMENT MAP (HDRI)
  // ============================================================================

  /**
   * Initialize environment map support
   * Must be called before loading environment maps
   */
  initializeEnvironmentSupport(): void {
    this.scene.initializeEnvironmentSupport(this.renderer.getWebGLRenderer());
  }

  /**
   * Load and set an environment map from URL
   * Supports HDR, EXR, and standard image formats
   * @param url - URL to the environment map file
   * @param config - Optional environment configuration
   */
  async loadEnvironmentMap(
    url: string,
    config?: Partial<import('./core/SceneManager').EnvironmentMapConfig>
  ): Promise<THREE.Texture> {
    // Ensure environment support is initialized
    this.initializeEnvironmentSupport();
    return this.scene.loadEnvironmentMap(url, config);
  }

  /**
   * Set environment map configuration
   * @param config - Partial configuration to update
   */
  setEnvironmentConfig(
    config: Partial<import('./core/SceneManager').EnvironmentMapConfig>
  ): void {
    this.scene.setEnvironmentConfig(config);
  }

  /**
   * Get current environment map configuration
   */
  getEnvironmentConfig(): import('./core/SceneManager').EnvironmentMapConfig {
    return this.scene.getEnvironmentConfig();
  }

  /**
   * Enable or disable environment map
   */
  setEnvironmentEnabled(enabled: boolean): void {
    this.scene.setEnvironmentEnabled(enabled);
  }

  /**
   * Set environment map intensity
   * @param intensity - Intensity multiplier (0-2 typical range)
   */
  setEnvironmentIntensity(intensity: number): void {
    this.scene.setEnvironmentIntensity(intensity);
  }

  /**
   * Set environment map rotation
   * @param degrees - Y-axis rotation in degrees
   */
  setEnvironmentRotation(degrees: number): void {
    this.scene.setEnvironmentRotation(degrees);
  }

  /**
   * Set background blur amount for HDRI background
   * @param blur - Blur amount (0-1)
   */
  setEnvironmentBackgroundBlur(blur: number): void {
    this.scene.setBackgroundBlur(blur);
  }

  /**
   * Toggle whether to use HDRI as scene background
   */
  setEnvironmentAsBackground(use: boolean): void {
    this.scene.setUseAsBackground(use);
  }

  /**
   * Get the current environment map texture
   */
  getEnvironmentMap(): THREE.Texture | null {
    return this.scene.getEnvironmentMap();
  }

  // ============================================================================
  // COMPOSITION GUIDES
  // ============================================================================

  /**
   * Show/hide composition grid
   */
  setCompositionGridVisible(visible: boolean): void {
    this.scene.setCompositionGridVisible(visible);
  }

  /**
   * Show/hide dark overlay outside composition
   */
  setOutsideOverlayVisible(visible: boolean): void {
    this.scene.setOutsideOverlayVisible(visible);
  }

  /**
   * Show/hide composition bounds frame
   */
  setCompositionBoundsVisible(visible: boolean): void {
    this.scene.setCompositionBoundsVisible(visible);
  }

  // ============================================================================
  // RAYCASTING
  // ============================================================================

  /**
   * Raycast to find layers at a normalized screen position
   * @param x - Normalized X coordinate (-1 to 1)
   * @param y - Normalized Y coordinate (-1 to 1)
   * @returns Layer ID if hit, null otherwise
   */
  raycastLayers(x: number, y: number): string | null {
    const raycaster = new THREE.Raycaster();
    const pointer = new THREE.Vector2(x, y);

    raycaster.setFromCamera(pointer, this.camera.getCamera());

    const intersects = this.scene.raycastComposition(raycaster);

    for (const intersection of intersects) {
      let obj: THREE.Object3D | null = intersection.object;
      while (obj) {
        if (obj.userData.layerId) {
          return obj.userData.layerId;
        }
        if (obj.userData.isBackground || obj.userData.isDepthOverlay) {
          break; // Don't select background or overlay
        }
        obj = obj.parent;
      }
    }

    return null;
  }

  // ============================================================================
  // TRANSFORM CONTROLS
  // ============================================================================

  /**
   * Initialize transform controls for layer manipulation
   */
  initializeTransformControls(): void {
    this.assertNotDisposed();

    if (this.transformControls) {
      return; // Already initialized
    }

    const camera = this.camera.getCamera();
    const domElement = this.renderer.getDomElement();

    this.transformControls = new TransformControls(camera, domElement);
    this.transformControls.setMode(this.transformMode);
    this.transformControls.setSpace('world');

    // Style the controls
    this.transformControls.setSize(1.0);

    // Add to scene (TransformControls extends Object3D internally)
    this.scene.addUIElement(this.transformControls as unknown as THREE.Object3D);

    // Handle transform changes
    this.transformControls.addEventListener('change', () => {
      if (!this.transformControls || !this.selectedLayerId) return;

      const object = this.transformControls.object;
      if (!object) return;

      const transform: LayerTransformUpdate = {
        position: {
          x: object.position.x,
          y: object.position.y,
          z: object.position.z
        },
        rotationX: THREE.MathUtils.radToDeg(object.rotation.x),
        rotationY: THREE.MathUtils.radToDeg(object.rotation.y),
        rotationZ: THREE.MathUtils.radToDeg(object.rotation.z),
        scale: {
          x: object.scale.x * 100, // Convert back to percentage
          y: object.scale.y * 100,
          z: object.scale.z * 100
        }
      };

      // Also set rotation for 2D layers
      transform.rotation = transform.rotationZ;

      if (this.onTransformChange) {
        this.onTransformChange(this.selectedLayerId, transform);
      }
    });

    // Disable orbit/pan during transform
    this.transformControls.addEventListener('dragging-changed', (event: any) => {
      // Could disable other controls here if needed
      this.emit('transform-dragging', { dragging: event.value });
    });

    // Handle mouseup to finalize transform
    this.transformControls.addEventListener('mouseUp', () => {
      this.emit('transform-end', { layerId: this.selectedLayerId });
    });
  }

  /**
   * Set transform change callback
   * Called whenever a layer is transformed via the controls
   */
  setTransformChangeCallback(
    callback: ((layerId: string, transform: LayerTransformUpdate) => void) | null
  ): void {
    this.onTransformChange = callback;
  }

  /**
   * Select a layer and attach transform controls
   * @param layerId - Layer ID to select, or null to deselect
   */
  selectLayer(layerId: string | null): void {
    this.assertNotDisposed();

    // Initialize transform controls if not already done
    if (!this.transformControls) {
      this.initializeTransformControls();
    }

    // Deselect current layer
    if (this.selectedLayerId && this.transformControls) {
      this.transformControls.detach();
    }

    this.selectedLayerId = layerId;

    if (!layerId || !this.transformControls) {
      return;
    }

    // Get the layer object
    const layerObject = this.getLayerObject(layerId);
    if (layerObject) {
      this.transformControls.attach(layerObject);
    }
  }

  /**
   * Get the currently selected layer ID
   */
  getSelectedLayerId(): string | null {
    return this.selectedLayerId;
  }

  /**
   * Set the transform mode
   * @param mode - 'translate' | 'rotate' | 'scale'
   */
  setTransformMode(mode: 'translate' | 'rotate' | 'scale'): void {
    this.transformMode = mode;
    if (this.transformControls) {
      this.transformControls.setMode(mode);
    }
  }

  /**
   * Get the current transform mode
   */
  getTransformMode(): 'translate' | 'rotate' | 'scale' {
    return this.transformMode;
  }

  /**
   * Set transform controls visibility
   */
  setTransformControlsVisible(visible: boolean): void {
    if (this.transformControls) {
      (this.transformControls as any).visible = visible;
      this.transformControls.enabled = visible;
    }
  }

  /**
   * Check if transform controls are dragging
   */
  isTransformDragging(): boolean {
    return this.transformControls?.dragging ?? false;
  }

  // ============================================================================
  // RENDER LOOP ALIASES
  // ============================================================================

  /**
   * Alias for startRenderLoop
   */
  start(): void {
    this.startRenderLoop();
  }

  /**
   * Alias for stopRenderLoop
   */
  stop(): void {
    this.stopRenderLoop();
  }

  // ============================================================================
  // FRAME CAPTURE & EXPORT
  // ============================================================================

  /**
   * Capture the current frame as ImageData
   */
  captureFrame(): CaptureResult {
    this.assertNotDisposed();

    const imageData = this.renderer.captureFrame();

    return {
      imageData,
      width: imageData.width,
      height: imageData.height,
      format: 'rgba',
    };
  }

  /**
   * Capture the current frame as a Blob
   * @param format - Image format ('png' | 'jpeg' | 'webp')
   * @param quality - Quality for lossy formats (0-1)
   */
  async captureFrameAsBlob(
    format: 'png' | 'jpeg' | 'webp' = 'png',
    quality: number = 0.95
  ): Promise<Blob> {
    this.assertNotDisposed();

    const { imageData, width, height } = this.captureFrame();

    const canvas = new OffscreenCanvas(width, height);
    const ctx = canvas.getContext('2d')!;
    ctx.putImageData(imageData, 0, 0);

    return canvas.convertToBlob({
      type: `image/${format}`,
      quality,
    });
  }

  /**
   * Capture the depth buffer
   */
  captureDepth(): DepthCaptureResult {
    this.assertNotDisposed();

    const depthBuffer = this.renderer.captureDepth();
    const cameraState = this.camera.getState();

    return {
      depthBuffer,
      width: this.state.viewport.width,
      height: this.state.viewport.height,
      near: cameraState.near,
      far: cameraState.far,
    };
  }

  // ============================================================================
  // PERFORMANCE
  // ============================================================================

  /**
   * Get current performance statistics
   */
  getPerformanceStats(): PerformanceStats {
    return this.performance.getStats();
  }

  /**
   * Reset performance statistics
   */
  resetPerformanceStats(): void {
    this.performance.reset();
  }

  // ============================================================================
  // EVENTS
  // ============================================================================

  /**
   * Subscribe to engine events
   * @param type - Event type to listen for
   * @param handler - Event handler function
   */
  on(type: EngineEventType, handler: EngineEventHandler): void {
    if (!this.eventHandlers.has(type)) {
      this.eventHandlers.set(type, new Set());
    }
    this.eventHandlers.get(type)!.add(handler);
  }

  /**
   * Unsubscribe from engine events
   * @param type - Event type
   * @param handler - Event handler to remove
   */
  off(type: EngineEventType, handler: EngineEventHandler): void {
    this.eventHandlers.get(type)?.delete(handler);
  }

  private emit(type: EngineEventType, data?: unknown): void {
    const event: EngineEvent = {
      type,
      timestamp: performance.now(),
      data,
    };

    this.eventHandlers.get(type)?.forEach(handler => {
      try {
        handler(event);
      } catch (error) {
        engineLogger.error(`Event handler error for ${type}:`, error);
      }
    });
  }

  // ============================================================================
  // CONTEXT LOSS HANDLING
  // ============================================================================

  private setupContextLossHandling(): void {
    const canvas = this.config.canvas;

    canvas.addEventListener('webglcontextlost', (event) => {
      event.preventDefault();
      this.stopRenderLoop();
      this.emit('contextLost', null);
      engineLogger.warn('WebGL context lost');
    });

    canvas.addEventListener('webglcontextrestored', () => {
      this.emit('contextRestored', null);
      engineLogger.info('WebGL context restored');
    });
  }

  // ============================================================================
  // STATE & UTILITIES
  // ============================================================================

  /**
   * Get current engine state
   */
  getState(): Readonly<RenderState> {
    return { ...this.state };
  }

  /**
   * Check if the engine has been disposed
   */
  isDisposed(): boolean {
    return this.state.isDisposed;
  }

  private assertNotDisposed(): void {
    if (this.state.isDisposed) {
      throw new Error('WeylEngine has been disposed');
    }
  }

  // ============================================================================
  // PRECOMP RENDER-TO-TEXTURE
  // ============================================================================

  /** Cache of layer managers for precomp compositions */
  private precompLayerManagers: Map<string, LayerManager> = new Map();

  /** Cache of scenes for precomp compositions */
  private precompScenes: Map<string, SceneManager> = new Map();

  /** Cache of last rendered frame per composition (for texture caching) */
  private precompLastFrame: Map<string, number> = new Map();

  /**
   * Render a composition to a texture
   * Used by PrecompLayer to render nested compositions
   *
   * @param compositionId - The composition ID to render
   * @param layers - The layers in that composition
   * @param settings - Composition settings (width, height, fps)
   * @param frame - The frame to render
   * @returns The rendered texture, or null if rendering fails
   */
  renderCompositionToTexture(
    compositionId: string,
    layers: Layer[],
    settings: { width: number; height: number; fps: number },
    frame: number
  ): THREE.Texture | null {
    this.assertNotDisposed();

    try {
      // Check if we already rendered this frame (texture caching)
      const lastFrame = this.precompLastFrame.get(compositionId);
      const target = this.renderer.getPrecompRenderTarget(
        compositionId,
        settings.width,
        settings.height
      );

      // If same frame, return cached texture
      if (lastFrame === frame) {
        return target.texture;
      }

      // Get or create scene for this composition
      let precompScene = this.precompScenes.get(compositionId);
      if (!precompScene) {
        precompScene = new SceneManager(null);
        precompScene.setCompositionSize(settings.width, settings.height);
        this.precompScenes.set(compositionId, precompScene);
      }

      // Get or create layer manager for this composition
      let precompLayers = this.precompLayerManagers.get(compositionId);
      if (!precompLayers) {
        precompLayers = new LayerManager(precompScene, this.resources);
        precompLayers.setRenderer(this.renderer.getWebGLRenderer());
        precompLayers.setCompositionFPS(settings.fps);
        precompLayers.setCamera(this.camera.camera);
        this.precompLayerManagers.set(compositionId, precompLayers);
      }

      // Sync layers - add new, update existing, remove deleted
      const currentLayerIds = new Set(precompLayers.getLayerIds());
      const targetLayerIds = new Set(layers.map(l => l.id));

      // Remove layers that are no longer in the composition
      for (const id of currentLayerIds) {
        if (!targetLayerIds.has(id)) {
          precompLayers.remove(id);
        }
      }

      // Add or update layers
      for (const layerData of layers) {
        if (currentLayerIds.has(layerData.id)) {
          precompLayers.update(layerData.id, layerData);
        } else {
          precompLayers.create(layerData);
        }
      }

      // Evaluate layers at the given frame
      precompLayers.evaluateFrame(frame, this.audioReactiveGetter);

      // Create a camera for this composition size
      const precompCamera = new THREE.OrthographicCamera(
        -settings.width / 2,
        settings.width / 2,
        settings.height / 2,
        -settings.height / 2,
        0.1,
        10000
      );
      precompCamera.position.set(0, 0, 1000);
      precompCamera.lookAt(0, 0, 0);

      // Render to texture
      const texture = this.renderer.renderSceneToTexture(
        precompScene.scene,
        precompCamera,
        target
      );

      // Cache the frame number
      this.precompLastFrame.set(compositionId, frame);

      return texture;
    } catch (error) {
      engineLogger.error('Failed to render composition to texture:', compositionId, error);
      return null;
    }
  }

  /**
   * Clear precomp cache for a specific composition
   * Call when a composition is deleted or significantly changed
   */
  clearPrecompCache(compositionId: string): void {
    const precompLayers = this.precompLayerManagers.get(compositionId);
    if (precompLayers) {
      precompLayers.dispose();
      this.precompLayerManagers.delete(compositionId);
    }

    const precompScene = this.precompScenes.get(compositionId);
    if (precompScene) {
      precompScene.dispose();
      this.precompScenes.delete(compositionId);
    }

    this.precompLastFrame.delete(compositionId);
    this.renderer.disposePrecompTarget(compositionId);
  }

  /**
   * Clear all precomp caches
   */
  clearAllPrecompCaches(): void {
    for (const [id] of this.precompLayerManagers) {
      this.clearPrecompCache(id);
    }
    this.renderer.disposeAllPrecompTargets();
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Dispose all engine resources
   * After calling dispose(), the engine cannot be used again.
   */
  dispose(): void {
    if (this.state.isDisposed) {
      return;
    }

    this.stopRenderLoop();

    // Clear precomp caches
    this.clearAllPrecompCaches();

    // Dispose in reverse order of initialization
    this.layers.dispose();
    this.renderer.dispose();
    this.scene.dispose();
    this.resources.dispose();

    // Clear event handlers
    this.eventHandlers.clear();

    this.state.isDisposed = true;
    this.emit('dispose', null);

    if (this.config.debug) {
      engineLogger.debug('Disposed');
    }
  }
}

export default WeylEngine;
