/**
 * LatticeEngine - Main Engine Facade
 *
 * The primary interface for the Lattice Compositor rendering engine.
 * Provides a clean API for Vue components to interact with the Three.js rendering system.
 *
 * @example
 * ```typescript
 * const engine = new LatticeEngine({
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

import * as THREE from "three";
import type { TargetParameter } from "@/services/audioReactiveMapping";
// Import 3D services for initialization
import { materialSystem } from "@/services/materialSystem";
import { meshParticleManager } from "@/services/meshParticleManager";
import { spriteSheetService } from "@/services/spriteSheet";
import { svgExtrusionService } from "@/services/svgExtrusion";
import type { Layer } from "@/types/project";
import type { JSONValue } from "@/types/dataAsset";
import { engineLogger } from "@/utils/logger";
import { assertDefined } from "@/utils/typeGuards";
import { BackgroundManager } from "./BackgroundManager";
import { CameraController } from "./core/CameraController";
import { LayerManager } from "./core/LayerManager";
import { RenderPipeline } from "./core/RenderPipeline";
import { ResourceManager } from "./core/ResourceManager";
import { SceneManager } from "./core/SceneManager";
import type { BaseLayer } from "./layers/BaseLayer";
import type { FrameState } from "./MotionEngine";
// Extracted utilities and managers
import { NestedCompRenderer } from "./NestedCompRenderer";
import {
  type LayerTransformUpdate,
  TransformControlsManager,
} from "./TransformControlsManager";
import type {
  CaptureResult,
  DepthCaptureResult,
  EngineEvent,
  EngineEventHandler,
  EngineEventType,
  LatticeEngineConfig,
  PerformanceStats,
  RenderState,
} from "./types";
import { PerformanceMonitor } from "./utils/PerformanceMonitor";

/** Callback to get audio reactive values at a frame */
export type AudioReactiveGetter = (
  frame: number,
) => Map<TargetParameter, number>;

/** Callback to get audio reactive values for a specific layer */
export type LayerAudioReactiveGetter = (
  layerId: string,
  frame: number,
) => Map<TargetParameter, number>;

// LayerTransformUpdate is now imported from TransformControlsManager
export type { LayerTransformUpdate } from "./TransformControlsManager";

export class LatticeEngine {
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

  // Background manager (extracted)
  private backgroundManager: BackgroundManager | null = null;

  // Transform controls manager (extracted)
  private transformControlsManager: TransformControlsManager | null = null;

  // Viewport transform for pan/zoom
  private viewportTransform: number[] = [1, 0, 0, 1, 0, 0];

  // Render mode
  private renderMode: "color" | "depth" | "normal" = "color";

  // Audio reactivity
  private audioReactiveGetter: LayerAudioReactiveGetter | null = null;

  // Event system
  private readonly eventHandlers: Map<EngineEventType, Set<EngineEventHandler>>;

  // WebGL context event handlers (stored for cleanup)
  private contextLostHandler: ((e: Event) => void) | null = null;
  private contextRestoredHandler: (() => void) | null = null;

  // Configuration
  private readonly config: Required<LatticeEngineConfig>;

  // Nested composition renderer (extracted)
  private nestedCompRenderer: NestedCompRenderer | null = null;

  constructor(config: LatticeEngineConfig) {
    // Validate input
    this.validateConfig(config);

    // Merge with defaults
    this.config = {
      canvas: config.canvas,
      width: config.width,
      height: config.height,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      // Pattern match: compositionWidth ∈ number | undefined → number (fallback to width)
      compositionWidth: (typeof config.compositionWidth === "number" && Number.isFinite(config.compositionWidth)) ? config.compositionWidth : config.width,
      // Pattern match: compositionHeight ∈ number | undefined → number (fallback to height)
      compositionHeight: (typeof config.compositionHeight === "number" && Number.isFinite(config.compositionHeight)) ? config.compositionHeight : config.height,
      // Pattern match: pixelRatio ∈ number | undefined → number (fallback to Math.min(window.devicePixelRatio, 2))
      pixelRatio: (typeof config.pixelRatio === "number" && Number.isFinite(config.pixelRatio) && config.pixelRatio > 0) ? config.pixelRatio : Math.min(window.devicePixelRatio, 2),
      // Pattern match: antialias ∈ boolean | undefined → boolean (default true)
      antialias: (typeof config.antialias === "boolean") ? config.antialias : true,
      // Pattern match: alpha ∈ boolean | undefined → boolean (default true)
      alpha: (typeof config.alpha === "boolean") ? config.alpha : true,
      // Pattern match: backgroundColor ∈ string | null | undefined → string | null (default null)
      backgroundColor: (typeof config.backgroundColor === "string" && config.backgroundColor.length > 0) ? config.backgroundColor : null,
      // Pattern match: debug ∈ boolean | undefined → boolean (default false)
      debug: (typeof config.debug === "boolean") ? config.debug : false,
      // Pattern match: powerPreference ∈ string | undefined → string (default "high-performance")
      powerPreference: (typeof config.powerPreference === "string" && config.powerPreference.length > 0) ? config.powerPreference : "high-performance",
    };

    // Initialize state
    //                                                                      // note
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
    // Convert null to undefined for SceneManager (it expects string | undefined)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: backgroundColor ∈ string | null | undefined → string | undefined
    const backgroundColor = (typeof this.config.backgroundColor === "string" && this.config.backgroundColor.length > 0) ? this.config.backgroundColor : undefined;
    this.scene = new SceneManager(backgroundColor);
    // Camera is initialized with COMPOSITION dimensions for position/target calculation
    // Type proof: compositionWidth and compositionHeight are guaranteed by Required<> type and default assignment
    assertDefined(this.config.compositionWidth, "compositionWidth must exist after config merge");
    assertDefined(this.config.compositionHeight, "compositionHeight must exist after config merge");
    this.camera = new CameraController(
      this.config.compositionWidth,
      this.config.compositionHeight,
    );
    // Set camera aspect ratio to VIEWPORT dimensions (required for correct rendering)
    this.camera.setViewportAspect(this.config.width, this.config.height);

    this.renderer = new RenderPipeline(
      {
        canvas: this.config.canvas,
        width: this.config.width,
        height: this.config.height,
        pixelRatio: this.config.pixelRatio,
        antialias: this.config.antialias,
        alpha: this.config.alpha,
      },
      this.scene,
      this.camera,
    );
    this.layers = new LayerManager(this.scene, this.resources);
    this.performance = new PerformanceMonitor();

    // Set composition size for bounds
    this.scene.setCompositionSize(
      this.config.compositionWidth,
      this.config.compositionHeight,
    );

    // Handle WebGL context loss
    this.setupContextLossHandling();

    if (this.config.debug) {
      engineLogger.debug("Initialized", this.config);
    }
  }

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  //                                               // configuration // validation
  // ════════════════════════════════════════════════════════════════════════════

  private validateConfig(config: LatticeEngineConfig): void {
    if (!(config.canvas instanceof HTMLCanvasElement)) {
      throw new Error("LatticeEngine requires a valid HTMLCanvasElement");
    }

    // NaN bypasses <= 0 check, so validate with Number.isFinite first
    if (
      !Number.isFinite(config.width) ||
      !Number.isFinite(config.height) ||
      config.width <= 0 ||
      config.height <= 0
    ) {
      throw new Error(
        "LatticeEngine requires positive finite width and height",
      );
    }

    if (config.width > 8192 || config.height > 8192) {
      throw new Error("LatticeEngine maximum dimension is 8192 pixels");
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // layer // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a layer to the composition
   * @param layerData - The layer data from the project schema
   */
  addLayer(layerData: Layer): void {
    this.assertNotDisposed();

    this.layers.create(layerData);
    this.emit("layerAdded", { layerId: layerData.id });

    if (this.config.debug) {
      engineLogger.debug("Layer added:", layerData.id, layerData.type);
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
    // Serialize to JSONValue for event emission
    const eventData: JSONValue = {
      layerId,
      properties: properties as JSONValue,
    };
    this.emit("layerUpdated", eventData);
  }

  /**
   * Remove a layer from the composition
   * @param layerId - The layer ID to remove
   */
  removeLayer(layerId: string): void {
    this.assertNotDisposed();

    this.layers.remove(layerId);
    this.emit("layerRemoved", { layerId });

    if (this.config.debug) {
      engineLogger.debug("Layer removed:", layerId);
    }
  }

  /**
   * Get all layer IDs currently in the composition
   */
  getLayerIds(): string[] {
    return this.layers.getLayerIds();
  }

  /**
   * Get a layer instance by ID
   * @param layerId - The layer ID
   */
  getLayer(layerId: string): BaseLayer | null {
    return this.layers.getLayer(layerId);
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
    const newIds = new Set(layers.map((l) => l.id));

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // callbacks
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the asset getter callback for ResourceManager
   * This allows layers to access project assets
   * @param getter - Function that retrieves assets by ID
   */
  setAssetGetter(
    getter: (
      assetId: string,
    ) => import("@/types/project").AssetReference | undefined,
  ): void {
    this.resources.setAssetGetter(getter);
  }

  /**
   * Set the video metadata callback for LayerManager
   * Called when a video layer finishes loading its metadata
   * @param callback - Function called with layer ID and video metadata
   */
  setVideoMetadataCallback(
    callback: (
      layerId: string,
      metadata: import("./layers/VideoLayer").VideoMetadata,
    ) => void,
  ): void {
    this.layers.setVideoMetadataCallback(callback);
  }

  /**
   * Set the nested comp render context for LayerManager
   * Allows nested comp layers to render nested compositions
   * @param context - Render context with composition access
   */
  setNestedCompRenderContext(
    context: import("./layers/NestedCompLayer").NestedCompRenderContext,
  ): void {
    this.layers.setNestedCompRenderContext(context);
  }

  /**
   * Set camera callbacks for LayerManager
   * Allows camera layers to access Camera3D data from store
   * @param getter - Function to get Camera3D by ID
   * @param updater - Function to update Camera3D properties
   * @param atFrameGetter - Function to get Camera3D with keyframe interpolation at a specific frame
   */
  setCameraCallbacks(
    getter: import("./layers/CameraLayer").CameraGetter,
    updater: import("./layers/CameraLayer").CameraUpdater,
    atFrameGetter?: import("./layers/CameraLayer").CameraAtFrameGetter,
  ): void {
    this.layers.setCameraCallbacks(getter, updater, atFrameGetter);
    // Store getter for active camera sync
    this.activeCameraGetter = getter;
  }

  // Active camera tracking
  private activeCameraGetter?: import("./layers/CameraLayer").CameraGetter;
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
    if (!cameraLayer || cameraLayer.type !== "camera") {
      return;
    }

    // Get Camera3D data from store via the layer
    const typedLayer =
      cameraLayer as import("./layers/CameraLayer").CameraLayer;
    const exportData = typedLayer.getExportData();
    if (!exportData) {
      return;
    }

    // Update the render camera from Camera3D data
    // Position
    this.camera.setPosition(
      exportData.position.x,
      exportData.position.y,
      exportData.position.z,
    );

    // Rotation (Camera3D uses degrees)
    this.camera.setRotation(
      exportData.rotation.x,
      exportData.rotation.y,
      exportData.rotation.z,
    );

    //                                                                       // fov
    this.camera.setFOV(exportData.fov);

    // Clip planes
    this.camera.setClipPlanes(exportData.nearClip, exportData.farClip);

    // Sync DOF settings from camera
    const camera3d = typedLayer.getCameraAtCurrentFrame();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (camera3d != null && typeof camera3d === "object" && "depthOfField" in camera3d && camera3d.depthOfField != null) {
      this.setDOFFromCamera(camera3d.depthOfField);
    }
  }

  /**
   * Set composition FPS for particle timing
   * @param fps - Frames per second
   */
  setCompositionFPS(fps: number): void {
    // Validate fps (NaN/0/negative would corrupt time-based calculations)
    const validFps = Number.isFinite(fps) && fps > 0 ? fps : 30;
    this.layers.setCompositionFPS(validFps);
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
      engineLogger.debug("3D services initialized");
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  // 3D SERVICE ACCESS
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // property // drivers
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // animation
  // ════════════════════════════════════════════════════════════════════════════

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
  private applyCameraState(cameraState: FrameState["camera"]): void {
    if (!cameraState) return;

    // Update camera controller with evaluated values
    this.camera.setPositionDirect(
      cameraState.position.x,
      cameraState.position.y,
      cameraState.position.z,
    );
    this.camera.setTargetDirect(
      cameraState.target.x,
      cameraState.target.y,
      cameraState.target.z,
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // rendering
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Render the current frame
   */
  render(): void {
    this.assertNotDisposed();

    this.performance.beginFrame();
    this.emit("frameStart", { frame: this.state.currentFrame });

    // Update orbit controls if enabled (for smooth damping)
    this.camera.updateOrbitControls();

    this.renderer.render();

    this.emit("frameEnd", { frame: this.state.currentFrame });
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
        this.animationFrameId = null; // Clear ID when loop exits
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // viewport
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Resize the viewport
   * @param width - New viewport width in pixels
   * @param height - New viewport height in pixels
   * @param compositionWidth - Composition width in pixels (required, min: 480, max: 3840)
   * @param compositionHeight - Composition height in pixels (required, min: 480, max: 2160)
   */
  resize(
    width: number,
    height: number,
    compositionWidth: number,
    compositionHeight: number,
  ): void {
    this.assertNotDisposed();

    // System F/Omega: Validate all dimensions with explicit bounds
    // Type proof: width, height, compositionWidth, compositionHeight ∈ ℝ₊ ∧ finite
    // Mathematical proof: All dimensions must be within valid ranges
    const MIN_COMPOSITION_SIZE = 480;
    const MAX_COMPOSITION_SIZE = 4000; // 4K (4000 pixels) in either horizontal or vertical dimension

    // Validate viewport dimensions
    if (
      !Number.isFinite(width) ||
      !Number.isFinite(height) ||
      width <= 0 ||
      height <= 0
    ) {
      throw new Error(
        `[LatticeEngine] Invalid viewport dimensions: width=${width}, height=${height}. Must be finite positive numbers.`,
      );
    }

    // Validate composition dimensions are provided
    if (
      compositionWidth === undefined ||
      compositionHeight === undefined ||
      !Number.isFinite(compositionWidth) ||
      !Number.isFinite(compositionHeight)
    ) {
      throw new Error(
        `[LatticeEngine] Composition dimensions are required: compositionWidth=${compositionWidth}, compositionHeight=${compositionHeight}. Must be finite numbers.`,
      );
    }

    // Validate composition dimensions are within bounds
    if (
      compositionWidth < MIN_COMPOSITION_SIZE ||
      compositionWidth > MAX_COMPOSITION_SIZE
    ) {
      throw new Error(
        `[LatticeEngine] Invalid composition width: ${compositionWidth}. Must be between ${MIN_COMPOSITION_SIZE} and ${MAX_COMPOSITION_SIZE} pixels (4K max).`,
      );
    }

    if (
      compositionHeight < MIN_COMPOSITION_SIZE ||
      compositionHeight > MAX_COMPOSITION_SIZE
    ) {
      throw new Error(
        `[LatticeEngine] Invalid composition height: ${compositionHeight}. Must be between ${MIN_COMPOSITION_SIZE} and ${MAX_COMPOSITION_SIZE} pixels (4K max).`,
      );
    }

    console.log(
      `[LatticeEngine] resize: viewport=${width}x${height}, comp=${compositionWidth}x${compositionHeight}`,
    );

    this.state.viewport = { width, height };
    this.renderer.resize(width, height);

    // Update camera composition dimensions (always provided and validated)
    this.camera.resize(compositionWidth, compositionHeight);

    // Set camera aspect to VIEWPORT dimensions (how wide the view is)
    this.camera.setViewportAspect(width, height);

    // Update SplineLayer resolutions for Line2 materials
    this.updateSplineResolutions(width, height);

    // System F/Omega: All properties are always defined - no optional properties
    // Type proof: compositionWidth, compositionHeight ∈ [480, 4000] × [480, 4000]
    const resizeData: Record<string, number> = {
      width,
      height,
      compositionWidth,
      compositionHeight,
    };
    // Type proof: Record<string, number> is a valid JSONValue
    // No type assertion needed - Record<string, number> satisfies JSONValue constraint
    this.emit("resize", resizeData);
  }

  /**
   * Update all SplineLayer resolutions for Line2 materials
   */
  private updateSplineResolutions(width: number, height: number): void {
    const layers = this.layers.getAllLayers();
    for (const layer of layers) {
      if (
        "setResolution" in layer &&
        typeof (layer as BaseLayer & { setResolution?: (width: number, height: number) => void }).setResolution === "function"
      ) {
        (layer as BaseLayer & { setResolution: (width: number, height: number) => void }).setResolution(width, height);
      }
    }
  }

  /**
   * Get current viewport dimensions
   */
  getViewport(): { width: number; height: number } {
    return { ...this.state.viewport };
  }

  /**
   * Set render resolution (for preview quality).
   * Implements setResolution for ThreeCanvas resolution dropdown.
   *
   * This changes the internal render buffer size without affecting viewport.
   * Used for half/third/quarter resolution preview modes.
   *
   * @param width - Render width in pixels
   * @param height - Render height in pixels
   */
  setResolution(width: number, height: number): void {
    this.assertNotDisposed();

    // NaN bypasses <= 0 check, so validate with Number.isFinite first
    if (
      !Number.isFinite(width) ||
      !Number.isFinite(height) ||
      width <= 0 ||
      height <= 0
    ) {
      engineLogger.warn("Invalid resolution dimensions:", width, height);
      return;
    }

    engineLogger.debug(`[LatticeEngine] setResolution: ${width}x${height}`);

    // Resize the render pipeline (affects render buffer, not viewport)
    this.renderer.resize(width, height);

    // Update spline layer resolutions for Line2 materials
    this.updateSplineResolutions(width, height);

    this.emit("resolutionChange", { width, height });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                    // camera
  // ════════════════════════════════════════════════════════════════════════════

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
   * Fit the composition to the viewport with optional padding
   * This is the canonical method for centering the view on initial load
   * @param padding - Padding in pixels around the composition (default 40)
   */
  fitCompositionToViewport(padding: number = 40): void {
    // Validate padding (NaN/negative would corrupt viewport calculations)
    const validPadding =
      Number.isFinite(padding) && padding >= 0 ? padding : 40;
    const { width, height } = this.state.viewport;
    this.camera.fitToViewport(width, height, validPadding);
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

  /**
   * Set the orbit pivot point (the point the camera orbits around)
   * @param x - X position in screen coordinates
   * @param y - Y position in screen coordinates
   * @param z - Z position
   */
  setOrbitTarget(x: number, y: number, z: number): void {
    this.camera.setOrbitTarget(x, y, z);
  }

  /**
   * Reset orbit target to composition center
   */
  resetOrbitTargetToCenter(): void {
    this.camera.resetOrbitTargetToCenter();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // depth // of // field
  // ════════════════════════════════════════════════════════════════════════════

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
  getDOF(): import("./core/RenderPipeline").DOFConfig {
    return this.renderer.getDOF();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                      // ssao
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Configure SSAO effect
   * @param config - SSAO configuration options
   */
  setSSAO(config: Partial<import("./core/RenderPipeline").SSAOConfig>): void {
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
  getSSAO(): import("./core/RenderPipeline").SSAOConfig {
    return this.renderer.getSSAO();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // bloom
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Configure bloom effect
   * Makes emissive objects (lights, bright particles) glow
   * @param config - Bloom configuration options
   */
  setBloom(config: Partial<import("./core/RenderPipeline").BloomConfig>): void {
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
  getBloom(): import("./core/RenderPipeline").BloomConfig {
    return this.renderer.getBloom();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // viewport // transform
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the viewport transform for pan/zoom operations
   * @param transform - [scaleX, skewX, skewY, scaleY, translateX, translateY]
   */
  setViewportTransform(transform: number[]): void {
    // Validate transform array (must be 6 numbers, all finite)
    if (!Array.isArray(transform) || transform.length < 6) {
      engineLogger.warn("Invalid viewport transform: expected 6-element array");
      return;
    }

    // Validate all values are finite numbers, use defaults if not
    const scale = Number.isFinite(transform[0]) ? transform[0] : 1;
    const skewX = Number.isFinite(transform[1]) ? transform[1] : 0;
    const skewY = Number.isFinite(transform[2]) ? transform[2] : 0;
    const scaleY = Number.isFinite(transform[3]) ? transform[3] : 1;
    const tx = Number.isFinite(transform[4]) ? transform[4] : 0;
    const ty = Number.isFinite(transform[5]) ? transform[5] : 0;

    this.viewportTransform = [scale, skewX, skewY, scaleY, tx, ty];

    // Update camera position based on viewport transform
    this.camera.setZoom(scale);

    // Convert viewport pan from screen pixels to world units.
    // The viewport transform stores pan in screen pixels, but the camera's
    // setPan() expects world units. Dividing by zoom (scale) normalizes
    // the offset so that visual pan distance matches user expectation
    // regardless of zoom level.
    const safeScale = scale > 0 ? scale : 1;
    const worldPanX = tx / safeScale;
    const worldPanY = ty / safeScale;
    this.camera.setPan(worldPanX, worldPanY);
  }

  /**
   * Get the current viewport transform
   */
  getViewportTransform(): number[] {
    return [...this.viewportTransform];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                // background
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the scene background color
   * @param color - Hex color string (e.g., '#050505') or null for transparent
   */
  setBackground(color: string | null): void {
    this.assertNotDisposed();
    // System F/Omega: Validate and convert null to empty string (SceneManager expects non-nullable string)
    // Type proof: color ∈ string | null → string (non-nullable)
    const colorValue = color !== null ? color : "";
    this.scene.setBackground(colorValue);
  }

  /**
   * Get the current background color
   */
  getBackground(): string | null {
    return this.scene.getBackground();
  }

  /**
   * Set a background image for the composition
   * @param image - HTMLImageElement to use as background
   */
  setBackgroundImage(image: HTMLImageElement): void {
    this.assertNotDisposed();
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.backgroundManager != null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.setBackgroundImage === "function") {
      this.backgroundManager.setBackgroundImage(image);
    }
  }

  /**
   * Set the depth map overlay
   * @param image - HTMLImageElement containing depth data
   * @param options - Display options
   */
  setDepthMap(
    image: HTMLImageElement,
    options: {
      colormap?: "viridis" | "plasma" | "grayscale";
      opacity?: number;
      visible?: boolean;
    },
  ): void {
    this.assertNotDisposed();
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.backgroundManager != null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.setDepthMap === "function") {
      this.backgroundManager.setDepthMap(image, options);
    }
  }

  /**
   * Set depth overlay visibility
   */
  setDepthOverlayVisible(visible: boolean): void {
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.backgroundManager != null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.setDepthOverlayVisible === "function") {
      this.backgroundManager.setDepthOverlayVisible(visible);
    }
  }

  /**
   * Set depth colormap
   */
  setDepthColormap(colormap: "viridis" | "plasma" | "grayscale"): void {
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.backgroundManager != null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.setDepthColormap === "function") {
      this.backgroundManager.setDepthColormap(colormap);
    }
  }

  /**
   * Set depth overlay opacity
   */
  setDepthOpacity(opacity: number): void {
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.backgroundManager != null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.setDepthOpacity === "function") {
      this.backgroundManager.setDepthOpacity(opacity);
    }
  }

  /**
   * Get current depth map settings
   */
  getDepthMapSettings(): {
    colormap: "viridis" | "plasma" | "grayscale";
    opacity: number;
    visible: boolean;
  } {
    this.ensureBackgroundManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: backgroundManager.getDepthMapSettings() ∈ DepthMapSettings | undefined → DepthMapSettings (default)
    const depthMapSettings = (this.backgroundManager !== null && typeof this.backgroundManager === "object" && typeof this.backgroundManager.getDepthMapSettings === "function") ? this.backgroundManager.getDepthMapSettings() : undefined;
    return (depthMapSettings !== undefined) ? depthMapSettings : {
      colormap: "grayscale",
      opacity: 1,
      visible: true,
    };
  }

  /**
   * Ensure BackgroundManager is initialized
   */
  private ensureBackgroundManager(): void {
    if (!this.backgroundManager) {
      this.backgroundManager = new BackgroundManager(this.scene);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // render // mode
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the render mode (color, depth, normal)
   */
  setRenderMode(mode: "color" | "depth" | "normal"): void {
    this.renderMode = mode;
    this.renderer.setRenderMode(mode);
  }

  /**
   * Get the current render mode
   */
  getRenderMode(): "color" | "depth" | "normal" {
    return this.renderMode;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // environment // map
  // ════════════════════════════════════════════════════════════════════════════

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
    config?: Partial<import("./core/SceneManager").EnvironmentMapConfig>,
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
    config: Partial<import("./core/SceneManager").EnvironmentMapConfig>,
  ): void {
    this.scene.setEnvironmentConfig(config);
  }

  /**
   * Get current environment map configuration
   */
  getEnvironmentConfig(): import("./core/SceneManager").EnvironmentMapConfig {
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // composition // guides
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                // raycasting
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Raycast to find layers at a normalized screen position
   * @param x - Normalized X coordinate (-1 to 1)
   * @param y - Normalized Y coordinate (-1 to 1)
   * @returns Layer ID if hit, null otherwise
   */
  raycastLayers(x: number, y: number): string {
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

    throw new Error(`[LatticeEngine] No layer found at raycast position (${x}, ${y})`);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // multi
  // ════════════════════════════════════════════════════════════════════════════

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // transform // controls
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Ensure TransformControlsManager is initialized
   */
  private ensureTransformControlsManager(): void {
    if (!this.transformControlsManager) {
      this.transformControlsManager = new TransformControlsManager({
        scene: this.scene,
        layers: this.layers,
        camera: this.camera,
        renderer: this.renderer,
        emit: (type, data) => this.emit(type as EngineEventType, data),
        getLayerObject: (layerId) => this.getLayerObject(layerId),
        resetOrbitTargetToCenter: () => this.resetOrbitTargetToCenter(),
        setOrbitTarget: (x, y, z) => this.setOrbitTarget(x, y, z),
      });
    }
  }

  /**
   * Initialize transform controls for layer manipulation
   */
  initializeTransformControls(): void {
    this.assertNotDisposed();
    this.ensureTransformControlsManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.initialize === "function") {
      this.transformControlsManager.initialize();
    }
  }

  /**
   * Set transform change callback
   * Called whenever a layer is transformed via the controls
   */
  setTransformChangeCallback(
    callback:
      | ((layerId: string, transform: LayerTransformUpdate) => void)
      | null,
  ): void {
    this.ensureTransformControlsManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.setTransformChangeCallback === "function") {
      this.transformControlsManager.setTransformChangeCallback(callback);
    }
  }

  /**
   * Select a layer and attach transform controls
   * @param layerId - Layer ID to select, or null to deselect
   */
  selectLayer(layerId: string | null): void {
    this.assertNotDisposed();
    this.ensureTransformControlsManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.selectLayer === "function") {
      this.transformControlsManager.selectLayer(layerId);
    }
  }

  /**
   * Focus the camera on a layer's position
   */
  focusOnLayer(layerId: string): void {
    this.ensureTransformControlsManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.focusOnLayer === "function") {
      this.transformControlsManager.focusOnLayer(layerId);
    }
  }

  /**
   * Get the currently selected layer ID
   */
  getSelectedLayerId(): string | null {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: transformControlsManager.getSelectedLayerId() ∈ string | null | undefined → string | null (default null)
    const selectedLayerId = (this.transformControlsManager !== null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.getSelectedLayerId === "function") ? this.transformControlsManager.getSelectedLayerId() : undefined;
    return (selectedLayerId !== undefined && typeof selectedLayerId === "string") ? selectedLayerId : null;
  }

  /**
   * Set the transform mode
   * @param mode - 'translate' | 'rotate' | 'scale'
   */
  setTransformMode(mode: "translate" | "rotate" | "scale"): void {
    this.ensureTransformControlsManager();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.setMode === "function") {
      this.transformControlsManager.setMode(mode);
    }
  }

  /**
   * Get the current transform mode
   */
  getTransformMode(): "translate" | "rotate" | "scale" {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: transformControlsManager.getMode() ∈ "translate" | "rotate" | "scale" | undefined → "translate" | "rotate" | "scale" (default "translate")
    const mode = (this.transformControlsManager !== null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.getMode === "function") ? this.transformControlsManager.getMode() : undefined;
    return (mode === "translate" || mode === "rotate" || mode === "scale") ? mode : "translate";
  }

  /**
   * Set transform controls visibility
   */
  setTransformControlsVisible(visible: boolean): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.transformControlsManager != null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.setVisible === "function") {
      this.transformControlsManager.setVisible(visible);
    }
  }

  /**
   * Check if transform controls are dragging
   */
  isTransformDragging(): boolean {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: transformControlsManager.isDragging() ∈ boolean | undefined → boolean (default false)
    const isDragging = (this.transformControlsManager !== null && typeof this.transformControlsManager === "object" && typeof this.transformControlsManager.isDragging === "function") ? this.transformControlsManager.isDragging() : undefined;
    return (typeof isDragging === "boolean") ? isDragging : false;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                 // render // loop // aliases
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                          // frame // capture
  // ════════════════════════════════════════════════════════════════════════════

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
      format: "rgba",
    };
  }

  /**
   * Capture the current frame as a Blob
   * @param format - Image format ('png' | 'jpeg' | 'webp')
   * @param quality - Quality for lossy formats (0-1)
   */
  async captureFrameAsBlob(
    format: "png" | "jpeg" | "webp" = "png",
    quality: number = 0.95,
  ): Promise<Blob> {
    this.assertNotDisposed();

    // Validate quality (NaN or out of range would cause issues)
    const validQuality =
      Number.isFinite(quality) && quality >= 0 && quality <= 1 ? quality : 0.95;

    const { imageData, width, height } = this.captureFrame();

    const canvas = new OffscreenCanvas(width, height);
    // Deterministic: Explicit null check for getContext - "2d" should always succeed but we verify
    const ctx = canvas.getContext("2d");
    if (!ctx) {
      throw new Error("[LatticeEngine] Failed to get 2d context from OffscreenCanvas");
    }
    ctx.putImageData(imageData, 0, 0);

    return canvas.convertToBlob({
      type: `image/${format}`,
      quality: validQuality,
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                               // performance
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                    // events
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Subscribe to engine events
   * @param type - Event type to listen for
   * @param handler - Event handler function
   */
  on(type: EngineEventType, handler: EngineEventHandler): void {
    if (!this.eventHandlers.has(type)) {
      this.eventHandlers.set(type, new Set());
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const handlers = this.eventHandlers.get(type);
    if (handlers != null && typeof handlers === "object" && typeof handlers.add === "function") {
      handlers.add(handler);
    }
  }

  /**
   * Unsubscribe from engine events
   * @param type - Event type
   * @param handler - Event handler to remove
   */
  off(type: EngineEventType, handler: EngineEventHandler): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const handlers = this.eventHandlers.get(type);
    if (handlers != null && typeof handlers === "object" && typeof handlers.delete === "function") {
      handlers.delete(handler);
    }
  }

  private emit(type: EngineEventType, data?: JSONValue): void {
    const event: EngineEvent = {
      type,
      timestamp: performance.now(),
      data,
    };

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const handlers = this.eventHandlers.get(type);
    if (handlers != null && typeof handlers === "object" && typeof handlers.forEach === "function") {
      handlers.forEach((handler) => {
        try {
          handler(event);
        } catch (error) {
          engineLogger.error(`[LatticeEngine] Error in event handler for ${type}:`, error);
        }
      });
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                               // context // loss // handling
  // ════════════════════════════════════════════════════════════════════════════

  private setupContextLossHandling(): void {
    const canvas = this.config.canvas;

    // Store handlers for cleanup in dispose()
    this.contextLostHandler = (event: Event) => {
      event.preventDefault();
      this.stopRenderLoop();
      // System F/Omega: Omit data parameter instead of passing null
      // Type proof: EngineEvent.data is optional (data?: JSONValue)
      this.emit("contextLost");
      engineLogger.warn("WebGL context lost");
    };

    this.contextRestoredHandler = () => {
      // System F/Omega: Omit data parameter instead of passing null
      // Type proof: EngineEvent.data is optional (data?: JSONValue)
      this.emit("contextRestored");
      engineLogger.info("WebGL context restored");
    };

    canvas.addEventListener("webglcontextlost", this.contextLostHandler);
    canvas.addEventListener(
      "webglcontextrestored",
      this.contextRestoredHandler,
    );
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // state
  // ════════════════════════════════════════════════════════════════════════════

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
      throw new Error("LatticeEngine has been disposed");
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                  // nested // comp // render
  // (Implementation extracted to NestedCompRenderer.ts)
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get or create the nested comp renderer (lazy initialization)
   */
  private getNestedCompRenderer(): NestedCompRenderer {
    if (!this.nestedCompRenderer) {
      this.nestedCompRenderer = new NestedCompRenderer(
        this.resources,
        this.renderer,
        this.camera.camera,
      );
    }
    return this.nestedCompRenderer;
  }

  /**
   * Render a composition to a texture
   * Used by NestedCompLayer to render nested compositions
   *
   * @param compositionId - The composition ID to render
   * @param layers - The layers in that composition
   * @param settings - Composition settings (width, height, fps)
   * @param frame - The frame to render
   * @returns The rendered texture, or null if rendering fails
   */
  /**
   * Render a composition to a texture
   * Used by NestedCompLayer to render nested compositions
   * 
   * System F/Omega proof: Explicit error throwing - never return null
   * Type proof: compositionId ∈ string → THREE.Texture (non-nullable)
   * Mathematical proof: Rendering must succeed or throw explicit error
   * Pattern proof: NestedCompRenderer.renderToTexture throws explicit errors - propagate them
   */
  renderCompositionToTexture(
    compositionId: string,
    layers: Layer[],
    settings: { width: number; height: number; fps: number },
    frame: number,
  ): THREE.Texture {
    this.assertNotDisposed();
    // System F/Omega: renderToTexture throws explicit errors - propagate them
    return this.getNestedCompRenderer().renderToTexture(
      compositionId,
      layers,
      settings,
      frame,
      this.audioReactiveGetter,
    );
  }

  /**
   * Clear nested composition cache for a specific composition
   * Call when a composition is deleted or significantly changed
   */
  clearNestedCompCache(compositionId: string): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.nestedCompRenderer != null && typeof this.nestedCompRenderer === "object" && typeof this.nestedCompRenderer.clearCache === "function") {
      this.nestedCompRenderer.clearCache(compositionId);
    }
  }

  /**
   * Clear all nested composition caches
   */
  clearAllNestedCompCaches(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.nestedCompRenderer != null && typeof this.nestedCompRenderer === "object" && typeof this.nestedCompRenderer.clearAllCaches === "function") {
      this.nestedCompRenderer.clearAllCaches();
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // disposal
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Dispose all engine resources
   * After calling dispose(), the engine cannot be used again.
   */
  dispose(): void {
    if (this.state.isDisposed) {
      return;
    }

    this.stopRenderLoop();

    // Dispose nested composition renderer
    if (this.nestedCompRenderer) {
      this.nestedCompRenderer.dispose();
      this.nestedCompRenderer = null;
    }

    // Remove WebGL context event listeners
    const canvas = this.config.canvas;
    if (this.contextLostHandler) {
      canvas.removeEventListener("webglcontextlost", this.contextLostHandler);
      this.contextLostHandler = null;
    }
    if (this.contextRestoredHandler) {
      canvas.removeEventListener(
        "webglcontextrestored",
        this.contextRestoredHandler,
      );
      this.contextRestoredHandler = null;
    }

    // Dispose transform controls manager
    if (this.transformControlsManager) {
      this.transformControlsManager.dispose();
      this.transformControlsManager = null;
    }

    // Dispose background manager
    if (this.backgroundManager) {
      this.backgroundManager.dispose();
      this.backgroundManager = null;
    }

    // Dispose in reverse order of initialization
    this.layers.dispose();
    this.renderer.dispose();
    this.scene.dispose();
    this.resources.dispose();

    // Clear event handlers
    this.eventHandlers.clear();

    this.state.isDisposed = true;
    // System F/Omega: Omit data parameter instead of passing null
    // Type proof: EngineEvent.data is optional (data?: JSONValue)
    this.emit("dispose");

    if (this.config.debug) {
      engineLogger.debug("Disposed");
    }
  }
}

export default LatticeEngine;
