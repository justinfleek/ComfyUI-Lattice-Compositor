/**
 * LayerManager - Layer Lifecycle Management
 *
 * Manages creation, updating, and disposal of layer instances.
 * Acts as a factory for different layer types.
 *
 * ARCHITECTURAL NOTE:
 * ===================
 * This manager supports TWO evaluation modes:
 *
 * 1. DEPRECATED: evaluateFrame(frame)
 *    - Layers internally call interpolateProperty()
 *    - VIOLATES single-source-of-truth
 *
 * 2. NEW: applyEvaluatedState(evaluatedLayers)
 *    - Receives pre-evaluated state from MotionEngine
 *    - Layers only APPLY values, never compute them
 *    - ENFORCES single-source-of-truth
 *
 * All new code should use applyEvaluatedState().
 */

import * as THREE from "three";
import type { TargetParameter } from "@/services/audioReactiveMapping";
import type {
  SplinePathProvider,
  SplineQueryResult,
} from "@/services/particleSystem";
import type { Layer, LayerMask, LayerType } from "@/types/project";
import { layerLogger } from "@/utils/logger";
import { AudioLayer } from "../layers/AudioLayer";
import type { BaseLayer } from "../layers/BaseLayer";
import {
  type CameraGetter,
  CameraLayer,
  type CameraUpdater,
} from "../layers/CameraLayer";
import { ControlLayer } from "../layers/ControlLayer";
import { DepthflowLayer } from "../layers/DepthflowLayer";
import { DepthLayer } from "../layers/DepthLayer";
import {
  type AdjustmentRenderContext,
  EffectLayer,
  type EffectLayerRenderContext,
} from "../layers/EffectLayer";
import { GeneratedLayer } from "../layers/GeneratedLayer";
import { GroupLayer } from "../layers/GroupLayer";
import { ImageLayer } from "../layers/ImageLayer";
import { LightLayer } from "../layers/LightLayer";
import { ModelLayer } from "../layers/ModelLayer";
import {
  NestedCompLayer,
  type NestedCompRenderContext,
} from "../layers/NestedCompLayer";
import { NormalLayer } from "../layers/NormalLayer";
import { ParticleLayer } from "../layers/ParticleLayer";
import { PathLayer } from "../layers/PathLayer";
import { PointCloudLayer } from "../layers/PointCloudLayer";
import { PoseLayer } from "../layers/PoseLayer";
import { ProceduralMatteLayer } from "../layers/ProceduralMatteLayer";
import { ShapeLayer } from "../layers/ShapeLayer";
import { SolidLayer } from "../layers/SolidLayer";
import { SplineLayer } from "../layers/SplineLayer";
import { TextLayer } from "../layers/TextLayer";
import { VideoLayer, type VideoMetadata } from "../layers/VideoLayer";
import type { EvaluatedLayer } from "../MotionEngine";
import type { ResourceManager } from "./ResourceManager";
import type { SceneManager } from "./SceneManager";

/** Callback to get audio reactive values for a specific layer at a frame */
export type LayerAudioReactiveGetter = (
  layerId: string,
  frame: number,
) => Map<TargetParameter, number>;

export class LayerManager {
  private readonly scene: SceneManager;
  private readonly resources: ResourceManager;
  private readonly layers: Map<string, BaseLayer>;

  // Callbacks
  private onVideoMetadataLoaded?: (
    layerId: string,
    metadata: VideoMetadata,
  ) => void;
  // Proper optional types - undefined when not set
  private nestedCompRenderContext: NestedCompRenderContext | undefined = undefined;
  private effectLayerRenderContext: EffectLayerRenderContext | undefined = undefined;
  private cameraGetter?: CameraGetter;
  private cameraAtFrameGetter?: import("../layers/CameraLayer").CameraAtFrameGetter;
  private cameraUpdater?: CameraUpdater;

  // Renderer reference for particle systems
  // Proper optional type - undefined when not set
  private rendererRef: THREE.WebGLRenderer | undefined = undefined;

  // Composition FPS for particle timing (WAN standard: 16fps)
  private compositionFPS: number = 16;

  // Camera reference for particles
  // Proper optional type - undefined when not set
  private cameraRef: THREE.PerspectiveCamera | undefined = undefined;

  // Audio reactive callback
  // Proper optional type - undefined when not set
  private audioReactiveGetter: LayerAudioReactiveGetter | undefined = undefined;

  // Matte canvas cache - stores rendered canvases for layers used as matte sources
  private matteCanvases: Map<string, HTMLCanvasElement> = new Map();

  // Current frame number - updated during evaluateFrame() for particle spline queries
  private currentFrame: number = 0;

  // Ordered layer list for render order (respects track matte dependencies)
  private renderOrder: string[] = [];

  // Callback to get cross-composition matte canvas
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Returns HTMLCanvasElement (throws error if not found, never null)
  private crossCompMatteGetter:
    | ((
        compositionId: string,
        layerId: string,
        frame: number,
      ) => HTMLCanvasElement)
    | {} = {};

  constructor(scene: SceneManager, resources: ResourceManager) {
    this.scene = scene;
    this.resources = resources;
    this.layers = new Map();
  }

  // ============================================================================
  // CALLBACKS
  // ============================================================================

  /**
   * Set callback for when a video layer loads its metadata
   * Used by the store to auto-resize composition based on video duration
   */
  setVideoMetadataCallback(
    callback: (layerId: string, metadata: VideoMetadata) => void,
  ): void {
    this.onVideoMetadataLoaded = callback;
  }

  /**
   * Set the nested comp render context
   * This allows nested comp layers to render nested compositions
   */
  setNestedCompRenderContext(context: NestedCompRenderContext): void {
    this.nestedCompRenderContext = context;

    // Update existing nested comp layers
    for (const layer of this.layers.values()) {
      if (layer.type === "nestedComp") {
        (layer as NestedCompLayer).setRenderContext(context);
      }
    }
  }

  /**
   * Set the effect layer render context
   * This allows effect layers to render layers below them
   */
  setEffectLayerRenderContext(context: EffectLayerRenderContext): void {
    this.effectLayerRenderContext = context;

    // Update existing effect layers
    // Type-safe access using getLayerData() method from BaseLayer
    for (const layer of this.layers.values()) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      // Pattern match: layerData ∈ Layer (throws error if not found, never null)
      if ("getLayerData" in layer && typeof layer.getLayerData === "function") {
        const layerDataValue = layer.getLayerData();
        if (
          layer.type === "solid" &&
          typeof layerDataValue === "object" && layerDataValue !== null && "data" in layerDataValue && typeof layerDataValue.data === "object" && layerDataValue.data !== null
        ) {
          const layerData = layerDataValue;
          const solidData = layerData.data as import("@/types/project").SolidLayerData & {
            effectLayer?: boolean;
            adjustmentLayer?: boolean;
          };
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
          const isEffectOrAdjustment = (typeof solidData.effectLayer === "boolean" && solidData.effectLayer === true) || (typeof solidData.adjustmentLayer === "boolean" && solidData.adjustmentLayer === true);
          if (isEffectOrAdjustment) {
            // Check if method exists before calling (SolidLayer doesn't have setRenderContext)
            // Type guard: EffectLayer has setRenderContext method
            if ("setRenderContext" in layer && typeof (layer as EffectLayer).setRenderContext === "function") {
              (layer as EffectLayer).setRenderContext(context);
            }
          }
        }
      }
    }
  }

  /** @deprecated Use setEffectLayerRenderContext instead */
  setAdjustmentRenderContext(context: AdjustmentRenderContext): void {
    this.setEffectLayerRenderContext(context);
  }

  /**
   * Set camera callbacks for CameraLayer access to store
   */
  setCameraCallbacks(
    getter: CameraGetter,
    updater: CameraUpdater,
    atFrameGetter?: import("../layers/CameraLayer").CameraAtFrameGetter,
  ): void {
    this.cameraGetter = getter;
    this.cameraUpdater = updater;
    this.cameraAtFrameGetter = atFrameGetter;

    // Update existing camera layers
    for (const layer of this.layers.values()) {
      if (layer.type === "camera") {
        (layer as CameraLayer).setCameraCallbacks(
          getter,
          updater,
          atFrameGetter,
        );
      }
    }
  }

  /**
   * Set renderer for particle layers
   * Must be called to enable GPU particle rendering
   */
  setRenderer(renderer: THREE.WebGLRenderer): void {
    this.rendererRef = renderer;

    // Update existing particle layers
    for (const layer of this.layers.values()) {
      if (layer.type === "particles") {
        (layer as ParticleLayer).setRenderer(renderer);
      }
    }
  }

  /**
   * Set composition FPS for timing calculations
   */
  setCompositionFPS(fps: number): void {
    this.compositionFPS = fps;

    // Update existing layers that need FPS
    for (const layer of this.layers.values()) {
      // Set FPS on all layers for time-based effects (Echo, Posterize Time, etc.)
      layer.setCompositionFps(fps);

      // Type-specific FPS handling
      if (layer.type === "particles") {
        (layer as ParticleLayer).setFPS(fps);
      }
      if (layer.type === "video") {
        (layer as VideoLayer).setFPS(fps);
      }
      if (layer.type === "nestedComp") {
        (layer as NestedCompLayer).setFPS(fps);
      }
    }
  }

  /**
   * Set camera reference for particle systems
   * Used for camera-relative effects (soft particles, depth culling)
   */
  setCamera(camera: THREE.PerspectiveCamera): void {
    this.cameraRef = camera;
  }

  /**
   * Get camera reference
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
   * Pattern match: Returns THREE.PerspectiveCamera (throws error if not set, never null)
   */
  getCamera(): THREE.PerspectiveCamera {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.cameraRef !== undefined) {
      return this.cameraRef;
    }
    // Pattern match: Camera not set - throw error instead of returning null
    throw new Error("Camera reference not set. Call setCamera() first.");
  }

  // ============================================================================
  // LAYER CREATION
  // ============================================================================

  /**
   * Create a new layer from layer data
   */
  create(layerData: Layer): BaseLayer {
    // Check for duplicate ID
    if (this.layers.has(layerData.id)) {
      layerLogger.warn(
        `LayerManager: Layer ${layerData.id} already exists, updating instead`,
      );
      this.update(layerData.id, layerData);
      return this.layers.get(layerData.id)!;
    }

    console.log("[LayerManager] Creating layer:", {
      id: layerData.id,
      type: layerData.type,
      name: layerData.name,
    });

    // Create layer instance
    const layer = this.createLayerInstance(layerData);

    // Register layer
    this.layers.set(layerData.id, layer);

    // Set up type-specific callbacks after creation
    this.setupLayerCallbacks(layer, layerData);

    // Set up parenting
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    const hasParentId = typeof layerData.parentId === "string" && layerData.parentId.length > 0;
    if (hasParentId && typeof layerData.parentId === "string") {
      const parentLayer = this.layers.get(layerData.parentId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (typeof parentLayer === "object" && parentLayer !== null) {
        // Pattern match: setParent accepts BaseLayer | null, but BaseLayer now uses empty object sentinel internally
        layer.setParent(parentLayer);
      }
    }

    // Add to scene (only if not parented - parented layers are children of their parent's group)
    if (!layer.hasParent()) {
      this.scene.addToComposition(layer.getObject());
      console.log("[LayerManager] Added to scene:", {
        id: layerData.id,
        objectName: layer.getObject().name,
        sceneChildCount: this.scene.compositionGroup.children.length,
      });
    }

    return layer;
  }

  /**
   * Set up type-specific callbacks after layer creation
   */
  private setupLayerCallbacks(layer: BaseLayer, layerData: Layer): void {
    // Set composition FPS on all layers for time-based effects (Echo, Posterize Time, etc.)
    layer.setCompositionFps(this.compositionFPS);

    // Video layer: hook up metadata callback for auto-resize
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (layer.type === "video" && typeof this.onVideoMetadataLoaded === "function") {
      const videoLayer = layer as VideoLayer;
      videoLayer.setMetadataCallback((metadata) => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onVideoMetadataLoaded === "function") {
          this.onVideoMetadataLoaded(layerData.id, metadata);
        }
      });
    }

    // Nested comp layer: provide render context
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (layer.type === "nestedComp" && this.nestedCompRenderContext !== undefined) {
      const nestedCompLayer = layer as NestedCompLayer;
      nestedCompLayer.setRenderContext(this.nestedCompRenderContext);
    }

    // Camera layer: provide camera data access and spline provider
    if (layer.type === "camera" && this.cameraGetter && this.cameraUpdater) {
      const cameraLayer = layer as CameraLayer;
      cameraLayer.setCameraCallbacks(
        this.cameraGetter,
        this.cameraUpdater,
        this.cameraAtFrameGetter,
      );

      // Set up spline provider for path following
      cameraLayer.setSplineProvider(this.createSplineProvider());
    }

    // Particle layer: provide renderer, FPS, and spline provider
    if (layer.type === "particles") {
      const particleLayer = layer as ParticleLayer;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (this.rendererRef !== undefined) {
        particleLayer.setRenderer(this.rendererRef);
      }
      particleLayer.setFPS(this.compositionFPS);
      // Wire up spline provider for spline-based emission
      particleLayer.setSplineProvider(this.createSplineProviderForParticles());
    }

    // Video layer: provide FPS
    if (layer.type === "video") {
      const videoLayer = layer as VideoLayer;
      videoLayer.setFPS(this.compositionFPS);
    }

    // Nested comp layer: provide FPS
    if (layer.type === "nestedComp") {
      const nestedCompLayer = layer as NestedCompLayer;
      nestedCompLayer.setFPS(this.compositionFPS);
    }

    // Any layer with effectLayer/adjustmentLayer flag: provide render context
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR/truthy checks
    const isEffectLayer = (typeof layerData.effectLayer === "boolean" && layerData.effectLayer === true) || (typeof layerData.adjustmentLayer === "boolean" && layerData.adjustmentLayer === true);
    if (
      isEffectLayer &&
      this.effectLayerRenderContext !== undefined
    ) {
      // The layer might be a solid or any other type with effect layer flag
      // Type guard: EffectLayer has setRenderContext method
      if ("setRenderContext" in layer && typeof (layer as EffectLayer).setRenderContext === "function") {
        (layer as EffectLayer).setRenderContext(
          this.effectLayerRenderContext,
        );
      }
    }

    // Light layer: provide layer position getter for POI and spline provider for path
    if (layer.type === "light") {
      const lightLayer = layer as LightLayer;

      // Provide a way to get other layer positions (for POI targeting)
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      lightLayer.setLayerPositionGetter((layerId: string) => {
        const targetLayer = this.layers.get(layerId);
        if (typeof targetLayer === "object" && targetLayer !== null) {
          const obj = targetLayer.getObject();
          return new THREE.Vector3(
            obj.position.x,
            obj.position.y,
            obj.position.z,
          );
        }
        // Pattern match: Layer not found - return zero vector instead of null
        return new THREE.Vector3(0, 0, 0);
      });

      // Set up spline provider for path following
      lightLayer.setPathProvider(this.createSplineProvider());
    }
  }

  /**
   * Create the appropriate layer instance based on type
   */
  private createLayerInstance(layerData: Layer): BaseLayer {
    switch (layerData.type) {
      case "image":
        return new ImageLayer(layerData, this.resources);

      case "solid":
        return new SolidLayer(layerData);

      case "control":
      case "null": // Deprecated, use 'control'
        return new ControlLayer(layerData);

      case "text":
        return new TextLayer(layerData, this.resources);

      case "spline":
        return new SplineLayer(layerData);

      case "path":
        return new PathLayer(layerData);

      case "particles":
        return new ParticleLayer(layerData);

      case "video":
        return new VideoLayer(layerData, this.resources);

      case "nestedComp":
        return new NestedCompLayer(layerData);

      case "camera":
        return new CameraLayer(layerData);

      case "light":
        return new LightLayer(layerData);

      case "depthflow":
        return new DepthflowLayer(layerData, this.resources);

      case "matte":
        return new ProceduralMatteLayer(layerData);

      case "shape":
        return new ShapeLayer(layerData);

      case "model":
        return new ModelLayer(layerData);

      case "pointcloud":
        return new PointCloudLayer(layerData);

      case "depth":
        return new DepthLayer(layerData);

      case "normal":
        return new NormalLayer(layerData);

      case "audio":
        return new AudioLayer(layerData);

      case "generated":
        return new GeneratedLayer(layerData);

      case "group":
        return new GroupLayer(layerData);

      case "particle":
        // Legacy particle type - use ParticleLayer with simplified config
        layerLogger.info(
          "LayerManager: Legacy particle type, using ParticleLayer",
        );
        return new ParticleLayer(layerData);

      case "pose":
        return new PoseLayer(layerData);

      case "effectLayer":
      case "adjustment": // Deprecated, use 'effectLayer'
        return new EffectLayer(layerData);

      default:
        layerLogger.warn(
          `LayerManager: Unknown layer type: ${layerData.type}, creating ControlLayer`,
        );
        return new ControlLayer(layerData);
    }
  }

  // ============================================================================
  // LAYER UPDATES
  // ============================================================================

  /**
   * Update a layer's properties
   */
  update(layerId: string, properties: Partial<Layer>): void {
    const layer = this.layers.get(layerId);

    if (!layer) {
      layerLogger.warn(`LayerManager: Layer ${layerId} not found for update`);
      return;
    }

    layer.update(properties);
  }

  /**
   * Batch update multiple layers
   */
  batchUpdate(
    updates: Array<{ id: string; properties: Partial<Layer> }>,
  ): void {
    for (const { id, properties } of updates) {
      this.update(id, properties);
    }
  }

  // ============================================================================
  // LAYER REMOVAL
  // ============================================================================

  /**
   * Remove a layer by ID
   */
  remove(layerId: string): void {
    const layer = this.layers.get(layerId);

    if (!layer) {
      layerLogger.warn(`LayerManager: Layer ${layerId} not found for removal`);
      return;
    }

    // Remove from scene
    this.scene.removeFromComposition(layer.getObject());

    // Dispose resources
    layer.dispose();

    // Remove from registry
    this.layers.delete(layerId);
  }

  /**
   * Remove multiple layers
   */
  removeMultiple(layerIds: string[]): void {
    for (const id of layerIds) {
      this.remove(id);
    }
  }

  /**
   * Remove all layers
   */
  removeAll(): void {
    for (const [_id, layer] of this.layers) {
      this.scene.removeFromComposition(layer.getObject());
      layer.dispose();
    }
    this.layers.clear();
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  /**
   * Apply pre-evaluated state from MotionEngine
   *
   * This is the NEW canonical way to update layer state.
   * Layers receive already-computed values and only APPLY them.
   * NO interpolation or time sampling happens here.
   *
   * Rendering order:
   * 1. Spline layers (for text-on-path dependencies)
   * 2. Text-on-path connections
   * 3. Track matte source layers (render to canvas)
   * 4. All other layers (with track mattes applied)
   *
   * @param evaluatedLayers - Pre-evaluated layer states from MotionEngine
   * @param frame - Optional frame number for animated spline/mask evaluation
   */
  applyEvaluatedState(
    evaluatedLayers: readonly EvaluatedLayer[],
    frame?: number,
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: frame ∈ number | undefined → number (≥ 0, frame number, never undefined)
    const frameNum: number = (typeof frame === "number" && Number.isFinite(frame) && frame >= 0)
      ? frame
      : 0;
    // Store current frame for particle spline queries
    this.currentFrame = frameNum;

    // First, apply state to spline and path layers so they evaluate their control points
    // This ensures animated paths are ready before text layers query them
    for (const evalLayer of evaluatedLayers) {
      const layer = this.layers.get(evalLayer.id);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical AND/truthy checks
      const hasLayer = typeof layer === "object" && layer !== null;
      const isValidPathType = hasLayer && (layer.type === "spline" || layer.type === "path");
      if (hasLayer && isValidPathType) {
        layer.applyEvaluatedState(evalLayer);
      }
    }

    // Update text-on-path connections (with frame for animated splines/paths)
    this.updateTextPathConnections(frame);

    // Process track mattes - collect matte canvases and distribute to target layers
    // This must happen before applying state to layers that use track mattes
    this.processTrackMattes(frameNum);

    // Apply evaluated state to remaining layers
    for (const evalLayer of evaluatedLayers) {
      const layer = this.layers.get(evalLayer.id);
      if (layer && layer.type !== "spline" && layer.type !== "path") {
        layer.applyEvaluatedState(evalLayer);
      }
    }

    // Update particle shadows from scene lights
    this.updateParticleShadows();

    // Re-sort by Z after evaluation (positions may have changed)
    this.scene.sortByZ();
  }

  /**
   * Update shadow information for all particle layers from scene lights
   * This should be called after lights have been updated
   */
  private updateParticleShadows(): void {
    // Find all light layers that cast shadows
    const shadowLights: THREE.Light[] = [];
    for (const layer of this.layers.values()) {
      if (layer.type === "light") {
        const lightLayer = layer as LightLayer;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
        // Pattern match: light ∈ THREE.Light (throws error if not found, never null)
        let light: THREE.Light;
        if ("getLight" in lightLayer && typeof lightLayer.getLight === "function") {
          const lightValue = lightLayer.getLight();
          if (typeof lightValue === "object" && lightValue !== null) {
            light = lightValue;
          } else {
            continue; // Skip if light is invalid
          }
        } else {
          continue; // Skip if getLight method doesn't exist
        }
        
        if (typeof light === "object" && "castShadow" in light && light.castShadow === true && "shadow" in light) {
          const shadow = light.shadow;
          if (typeof shadow === "object" && shadow !== null && "map" in shadow) {
            const map = shadow.map;
            if (typeof map === "object" && map !== null && "texture" in map) {
              const texture = map.texture;
              if (typeof texture === "object" && texture !== null) {
                shadowLights.push(light);
              }
            }
          }
        }
      }
    }

    // If no shadow lights, nothing to do
    if (shadowLights.length === 0) return;

    // Update all particle layers with shadow information
    for (const layer of this.layers.values()) {
      if (layer.type === "particles") {
        const particleLayer = layer as ParticleLayer;
        // Pass the Three.js scene for shadow map lookups
        particleLayer.updateShadowsFromScene(this.scene.scene);
      }
    }
  }

  /**
   * Evaluate all layers at a given frame
   *
   * @deprecated Use applyEvaluatedState() with pre-evaluated state from MotionEngine.
   * This method causes layers to internally call interpolateProperty(), violating
   * the single-source-of-truth principle.
   *
   * @param frame - The frame number
   * @param audioReactiveGetter - Optional callback to get audio reactive values
   */
  evaluateFrame(
    frame: number,
    audioReactiveGetter?: LayerAudioReactiveGetter | null,
  ): void {
    // Store current frame for particle spline queries
    this.currentFrame = frame;

    // First, update text-on-path connections
    this.updateTextPathConnections(frame);

    // Process track mattes - collect matte canvases and distribute to target layers
    this.processTrackMattes(frame);

    // Use provided getter or fall back to stored one
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: audioReactiveGetter ∈ function | undefined → function (never check undefined)
    let getter: LayerAudioReactiveGetter;
    if (typeof audioReactiveGetter === "function") {
      getter = audioReactiveGetter;
    } else if (this.audioReactiveGetter !== undefined && typeof this.audioReactiveGetter === "function") {
      getter = this.audioReactiveGetter;
    } else {
      // Pattern match: No getter available - skip audio reactive evaluation
      return;
    }

    for (const layer of this.layers.values()) {
      // Get audio reactive values for this layer if available
      // Pattern match: getter is guaranteed to be function here
      const audioValues = getter(layer.id, frame);
      if (audioValues.size > 0) {
        layer.setAudioReactiveValues(audioValues);
      }

      layer.evaluateFrame(frame);
    }

    // Re-sort by Z after evaluation (positions may have changed)
    this.scene.sortByZ();
  }

  /**
   * Set the audio reactive getter callback
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: getter ∈ LayerAudioReactiveGetter | null → undefined when null
  setAudioReactiveCallback(getter: LayerAudioReactiveGetter | null): void {
    // Pattern match: Convert null to undefined (type is LayerAudioReactiveGetter | undefined)
    this.audioReactiveGetter = (typeof getter === "function") ? getter : undefined;
  }

  /**
   * Set driven values for a specific layer
   * Used by the expression/driver system to override animated properties
   */
  setLayerDrivenValues(layerId: string, values: Map<string, number>): void {
    const layer = this.layers.get(layerId);
    if (layer) {
      layer.setDrivenValues(values);
    }
  }

  /**
   * Clear driven values for a layer
   */
  clearLayerDrivenValues(layerId: string): void {
    const layer = this.layers.get(layerId);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (typeof layer === "object" && layer !== null) {
      layer.clearDrivenValues();
    }
  }

  /**
   * Clear all driven values for all layers
   */
  clearAllDrivenValues(): void {
    for (const layer of this.layers.values()) {
      layer.clearDrivenValues();
    }
  }

  /**
   * Update text layer connections to spline/path layers
   * Called before frame evaluation to ensure paths are current
   *
   * For animated splines/paths, this must be called with the current frame
   * to get properly evaluated control points.
   *
   * Supports both 'spline' and 'path' layer types.
   *
   * @param frame - Optional frame number for animated spline/path evaluation
   */
  private updateTextPathConnections(frame?: number): void {
    for (const layer of this.layers.values()) {
      if (layer.type === "text") {
        const textLayer = layer as TextLayer;
        const textData = textLayer.getTextData();

        if (textData.pathLayerId) {
          const pathSourceLayer = this.layers.get(textData.pathLayerId);

          // Support both spline and path layer types
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
          if (
            typeof pathSourceLayer === "object" && pathSourceLayer !== null &&
            (pathSourceLayer.type === "spline" ||
              pathSourceLayer.type === "path")
          ) {
            // Both SplineLayer and PathLayer have the same path interface
            const pathLayer = pathSourceLayer as SplineLayer | PathLayer;

            // Check if path is animated and we have a frame
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
            if (pathLayer.isAnimated() && typeof frame === "number" && Number.isFinite(frame) && frame >= 0) {
              // Get evaluated control points for this frame
              const evaluatedPoints =
                pathLayer.getEvaluatedControlPoints(frame);

              // Convert EvaluatedControlPoint to ControlPoint for TextLayer
              const controlPoints = evaluatedPoints.map((ep) => ({
                id: ep.id,
                x: ep.x,
                y: ep.y,
                depth: ep.depth,
                handleIn: ep.handleIn,
                handleOut: ep.handleOut,
                type: ep.type,
              }));

              // Update text layer with animated path
              textLayer.setPathFromControlPoints(
                controlPoints,
                pathLayer.isClosed(),
              );
            } else {
              // Static path - use cached curve
              const curve = pathLayer.getCurve();
              if (curve) {
                textLayer.setPathFromCurve(curve);
              }
            }
          }
        }
      }
    }
  }

  // ============================================================================
  // SPLINE PATH PROVIDER (for Particle Systems)
  // ============================================================================

  /**
   * Create a SplinePathProvider that can be used by particle systems
   * to query spline positions for path-based emission
   *
   * USAGE:
   * ```typescript
   * const provider = layerManager.createSplineProvider();
   * particleSystem.setSplineProvider(provider);
   * ```
   */
  createSplineProvider(): SplinePathProvider {
    return (
      layerId: string,
      t: number,
      frame: number,
    ): SplineQueryResult | null => {
      return this.querySplinePath(layerId, t, frame);
    };
  }

  /**
   * Create a spline provider adapted for the particle system
   * The particle system's SplineProvider has a simpler signature: (splineId, t) => {x, y, z}
   * This adapter captures the current frame from the layer manager state
   */
  createSplineProviderForParticles(): import("../particles/ParticleEmitterLogic").SplineProvider {
    return (
      splineId: string,
      t: number,
    ): { x: number; y: number; z?: number } | null => {
      // Use the current frame from the layer manager
      // Note: This is evaluated at particle spawn time, so the frame is accurate
      const result = this.querySplinePath(splineId, t, this.currentFrame);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      // Pattern match: result ∈ { point, tangent, length } (throws error if not found, never null)
      if (typeof result !== "object" || result === null) {
        throw new Error(`Spline path query failed for spline ${splineId} at t=${t}`);
      }
      
      return {
        x: result.point.x,
        y: result.point.y,
        z: result.point.z,
      };
    };
  }

  /**
   * Query a spline/path layer for position and tangent at parameter t
   *
   * Supports both 'spline' and 'path' layer types.
   *
   * @param layerId - ID of the spline or path layer
   * @param t - Parameter along the path (0-1)
   * @param frame - Current frame for animated paths
   * @returns Position, tangent, and length or null if layer not found
   */
  querySplinePath(
    layerId: string,
    t: number,
    frame: number,
  ): SplineQueryResult | null {
    const layer = this.layers.get(layerId);

    // Support both spline and path layer types
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR/truthy checks
    const hasLayer = typeof layer === "object" && layer !== null;
    const isValidPathType = hasLayer && (layer.type === "spline" || layer.type === "path");
    if (!hasLayer || !isValidPathType) {
      throw new Error(`Spline/path layer ${layerId} not found or invalid type`);
    }

    const pathLayer = layer as SplineLayer | PathLayer;

    // For animated paths, ensure we have evaluated control points
    // This triggers rebuild if points have changed
    if (pathLayer.isAnimated()) {
      pathLayer.getEvaluatedControlPoints(frame);
    }

    // Query the curve
    const point = pathLayer.getPointAt(t);
    const tangent = pathLayer.getTangentAt(t);
    const length = pathLayer.getLength();

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (typeof point !== "object" || point === null || typeof tangent !== "object" || tangent === null) {
      throw new Error(`Failed to get point or tangent for layer ${layerId} at t=${t}`);
    }

    // Convert Three.js coordinates to normalized coordinates
    // Spline coordinates are in canvas pixels, normalize to 0-1
    // Note: The Y coordinate is negated in SplineLayer/PathLayer, so we negate it back
    // For now, we assume the composition size is available or use raw coordinates
    // In production, this should be normalized based on composition dimensions

    return {
      point: {
        x: point.x,
        y: -point.y, // Negate back from Three.js coordinate system
        z: point.z,
      },
      tangent: {
        x: tangent.x,
        y: -tangent.y, // Negate back
      },
      length,
    };
  }

  /**
   * Get all spline and path layer IDs (useful for UI to list available paths)
   * Returns both 'spline' and 'path' layer types since both can be used as paths.
   */
  getSplineLayerIds(): string[] {
    const ids: string[] = [];
    for (const [id, layer] of this.layers) {
      if (layer.type === "spline" || layer.type === "path") {
        ids.push(id);
      }
    }
    return ids;
  }

  /**
   * Get all path layer IDs only (invisible motion paths)
   */
  getPathLayerIds(): string[] {
    const ids: string[] = [];
    for (const [id, layer] of this.layers) {
      if (layer.type === "path") {
        ids.push(id);
      }
    }
    return ids;
  }

  /**
   * Connect a text layer to a spline or path layer
   * Supports both 'spline' and 'path' layer types.
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: pathLayerId ∈ string (empty string = no path, never null)
  connectTextToPath(textLayerId: string, pathLayerId: string): void {
    const textLayer = this.layers.get(textLayerId) as TextLayer | undefined;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR/truthy checks
    const hasTextLayer = typeof textLayer === "object" && textLayer !== null;
    if (!hasTextLayer || textLayer.type !== "text") {
      throw new Error(`LayerManager: Text layer ${textLayerId} not found`);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (pathLayerId.length === 0) {
      textLayer.clearPath();
      return;
    }

    const pathSourceLayer = this.layers.get(pathLayerId);

    // Support both spline and path layer types
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR/truthy checks
    const hasPathSourceLayer = typeof pathSourceLayer === "object" && pathSourceLayer !== null;
    const isValidPathType = hasPathSourceLayer && (pathSourceLayer.type === "spline" || pathSourceLayer.type === "path");
    if (!hasPathSourceLayer || !isValidPathType) {
      layerLogger.warn(
        `LayerManager: Spline/path layer ${pathLayerId} not found`,
      );
      return;
    }

    const pathLayer = pathSourceLayer as SplineLayer | PathLayer;
    const curve = pathLayer.getCurve();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (typeof curve === "object" && curve !== null) {
      textLayer.setPathFromCurve(curve);
    }
  }

  // ============================================================================
  // LAYER ACCESS
  // ============================================================================

  /**
   * Get a layer's Three.js object
   */
  getObject(layerId: string): THREE.Object3D | null {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
    // Pattern match: layers.get(layerId) ∈ BaseLayer | undefined → THREE.Object3D (throws error if not found, never null)
    const layer = this.layers.get(layerId);
    if (typeof layer === "object" && layer !== null && typeof layer.getObject === "function") {
      return layer.getObject();
    }
    throw new Error(`Layer ${layerId} not found or does not have getObject method`);
  }

  /**
   * Get a layer instance
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
  // Pattern match: layers.get(layerId) ∈ BaseLayer | undefined → BaseLayer (throws error if not found, never null)
  getLayer(layerId: string): BaseLayer {
    const layer = this.layers.get(layerId);
    if (typeof layer === "object" && layer !== null) {
      return layer;
    }
    throw new Error(`Layer ${layerId} not found`);
  }

  /**
   * Get all layer IDs
   */
  getLayerIds(): string[] {
    return Array.from(this.layers.keys());
  }

  /**
   * Get all layers of a specific type
   */
  getLayersByType(type: LayerType): BaseLayer[] {
    return Array.from(this.layers.values()).filter(
      (layer) => layer.type === type,
    );
  }

  /**
   * Check if a layer exists
   */
  hasLayer(layerId: string): boolean {
    return this.layers.has(layerId);
  }

  /**
   * Get layer count
   */
  getLayerCount(): number {
    return this.layers.size;
  }

  /**
   * Get all layers as an array
   */
  getAllLayers(): BaseLayer[] {
    return Array.from(this.layers.values());
  }

  // ============================================================================
  // LAYER ORDERING
  // ============================================================================

  /**
   * Reorder layers in the scene based on their Z positions
   */
  reorderLayers(): void {
    this.scene.sortByZ();
  }

  // ============================================================================
  // PARENTING
  // ============================================================================

  /**
   * Rebuild the parenting hierarchy for all layers
   * Call this after batch-adding layers to ensure proper parent-child relationships
   */
  rebuildParentHierarchy(): void {
    // First pass: clear all parent relationships
    for (const layer of this.layers.values()) {
      if (layer.hasParent()) {
        // Remove from parent's group
        // getParent() throws explicit error if parent is missing (after hasParent() check)
        const parent = layer.getParent();
        parent.getObject().remove(layer.getObject());
      }
    }

    // Second pass: rebuild parent relationships
    for (const layer of this.layers.values()) {
      const parentId = layer.getParentId();
      if (parentId) {
        const parentLayer = this.layers.get(parentId);
        if (parentLayer) {
          layer.setParent(parentLayer);
        } else {
          // Parent not found, add to scene root
          layer.setParent(null);
          this.scene.addToComposition(layer.getObject());
        }
      }
    }
  }

  /**
   * Set parent for a layer
   */
  setLayerParent(layerId: string, parentId: string | null): void {
    const layer = this.layers.get(layerId);
    if (!layer) return;

    // Remove from current parent or scene
    if (layer.hasParent()) {
      // getParent() throws explicit error if parent is missing (after hasParent() check)
      const oldParent = layer.getParent();
      oldParent.getObject().remove(layer.getObject());
    } else {
      this.scene.removeFromComposition(layer.getObject());
    }

    // Set new parent
    if (parentId) {
      const newParent = this.layers.get(parentId);
      if (newParent) {
        layer.setParent(newParent);
      } else {
        layer.setParent(null);
        this.scene.addToComposition(layer.getObject());
      }
    } else {
      layer.setParent(null);
      this.scene.addToComposition(layer.getObject());
    }
  }

  /**
   * Move a layer to a specific Z position
   */
  setLayerZ(layerId: string, z: number): void {
    const layer = this.layers.get(layerId);
    if (layer) {
      layer.getObject().position.z = z;
      this.scene.sortByZ();
    }
  }

  // ============================================================================
  // VISIBILITY
  // ============================================================================

  /**
   * Set layer visibility
   */
  setLayerVisible(layerId: string, visible: boolean): void {
    const layer = this.layers.get(layerId);
    if (layer) {
      layer.setVisible(visible);
    }
  }

  /**
   * Toggle layer visibility
   */
  toggleLayerVisible(layerId: string): boolean {
    const layer = this.layers.get(layerId);
    if (layer) {
      const newVisible = !layer.getObject().visible;
      layer.setVisible(newVisible);
      return newVisible;
    }
    return false;
  }

  /**
   * Isolate a layer (hide all others)
   */
  isolateLayer(layerId: string): void {
    for (const [id, layer] of this.layers) {
      layer.setVisible(id === layerId);
    }
  }

  /** @deprecated Use isolateLayer instead */
  soloLayer(layerId: string): void {
    this.isolateLayer(layerId);
  }

  /**
   * Unisolate all layers (show all)
   */
  unisolateAll(): void {
    for (const layer of this.layers.values()) {
      layer.setVisible(true);
    }
  }

  /** @deprecated Use unisolateAll instead */
  unsoloAll(): void {
    this.unisolateAll();
  }

  // ============================================================================
  // TRACK MATTE PROCESSING
  // ============================================================================

  /**
   * Set callback for retrieving cross-composition matte canvases
   *
   * This enables track mattes from other compositions (nested comps)
   * to be used as matte sources.
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: getter returns HTMLCanvasElement (throws error if not found, never null)
  setCrossCompMatteGetter(
    getter:
      | ((
          compositionId: string,
          layerId: string,
          frame: number,
        ) => HTMLCanvasElement)
      | {},
  ): void {
    // Pattern match: Use empty object sentinel instead of null
    this.crossCompMatteGetter = (typeof getter === "function") ? getter : {};
  }

  /**
   * Process track mattes for all layers
   *
   * Track mattes use one layer's rendered output to control
   * another layer's visibility (alpha or luma).
   *
   * This method:
   * 1. Identifies layers that are used as track mattes
   * 2. Collects their rendered canvases (from same comp or cross-comp)
   * 3. Passes the canvas to layers that use them as mattes
   *
   * @param frame - Current frame number for animated evaluation
   */
  processTrackMattes(frame: number): void {
    // Clear previous frame's matte canvases
    this.matteCanvases.clear();

    // Process each layer that has a track matte
    for (const layer of this.layers.values()) {
      const matteLayerId = layer.getTrackMatteLayerId();
      const matteType = layer.getTrackMatteType();

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR/truthy checks
      const hasMatteLayerId = typeof matteLayerId === "string" && matteLayerId.length > 0;
      if (!hasMatteLayerId || matteType === "none") {
        continue;
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null assignments
      // Pattern match: matteCanvas ∈ HTMLCanvasElement (throws error if not found, never null)
      let matteCanvas: HTMLCanvasElement;

      // Check if this is a cross-composition matte
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (layer.hasCrossCompMatte() && typeof this.crossCompMatteGetter === "object" && this.crossCompMatteGetter !== null && Object.keys(this.crossCompMatteGetter).length > 0 && typeof (this.crossCompMatteGetter as Function) === "function") {
        const compositionIdValue = layer.getTrackMatteCompositionId();
        if (typeof compositionIdValue === "string" && compositionIdValue.length > 0) {
          const compositionId = compositionIdValue;
          const getter = this.crossCompMatteGetter as (compositionId: string, layerId: string, frame: number) => HTMLCanvasElement;
          matteCanvas = getter(
            compositionId,
            matteLayerId,
            frame,
          );
        } else {
          // Pattern match: Invalid composition ID - throw error instead of warning
          throw new Error(`Invalid composition ID for cross-comp matte: ${compositionIdValue}`);
        }
      } else {
        // Same composition matte
        const matteLayer = this.layers.get(matteLayerId);

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
        if (typeof matteLayer === "object" && matteLayer !== null) {
          // Check cache first
          if (this.matteCanvases.has(matteLayerId)) {
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy non-null assertion
            const cachedMatte = this.matteCanvases.get(matteLayerId);
            if (typeof cachedMatte === "object" && cachedMatte !== null) {
              matteCanvas = cachedMatte;
            } else {
              // Pattern match: Cache miss - render matte
              // Pattern match: getLayerRenderedCanvas returns HTMLCanvasElement (never null)
              matteCanvas = this.getLayerRenderedCanvas(matteLayer, frame);
              this.matteCanvases.set(matteLayerId, matteCanvas);
            }
          } else {
            // Render and cache the matte
            // Pattern match: getLayerRenderedCanvas returns HTMLCanvasElement (never null)
            matteCanvas = this.getLayerRenderedCanvas(matteLayer, frame);
            this.matteCanvases.set(matteLayerId, matteCanvas);
          }
        } else {
          // Pattern match: Matte layer not found - throw error instead of warning
          throw new Error(`Matte source layer ${matteLayerId} not found`);
        }
      }

      // Set the matte canvas on the target layer
      layer.setTrackMatteCanvas(matteCanvas);
    }
  }

  /**
   * Get the rendered canvas from a layer (for use as track matte)
   *
   * This gets the layer's visual output as a canvas that can be used
   * for track matte operations.
   *
   * @param layer - The layer to get canvas from
   * @param frame - Current frame for animated content
   * @returns Canvas with layer's rendered content (throws error if unavailable, never null)
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
  // Pattern match: Returns HTMLCanvasElement (throws error if not found, never null)
  private getLayerRenderedCanvas(
    layer: BaseLayer,
    _frame: number,
  ): HTMLCanvasElement {
    // For layers with getSourceCanvas, use that
    // Note: This is a simplified implementation - in production,
    // this would need to render the full layer to an offscreen canvas
    // including transforms, effects, and nested content

    // Try to get the layer's source canvas through a render-to-texture approach
    // For now, we use the internal source canvas method
    // Subclasses like ImageLayer, VideoLayer, TextLayer implement getSourceCanvas()
    // System F/Omega proof: Runtime type guard for protected method access
    // Type proof: BaseLayer.getSourceCanvas() is protected, but we need to call it from LayerManager
    // Solution: Use runtime property check with type narrowing
    
    // Type guard: Check if layer has getSourceCanvas method
    // Type proof: ∀ l: BaseLayer, hasGetSourceCanvas(l) → can call l.getSourceCanvas()
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
    // Pattern match: getSourceCanvas() returns HTMLCanvasElement (throws error if not found, never null)
    // Note: getSourceCanvas is protected, so we use a type guard with proper interface
    interface LayerWithSourceCanvas {
      getSourceCanvas(): HTMLCanvasElement;
    }
    
    // Type guard: Check if layer has getSourceCanvas method (even if protected)
    // We use a type assertion to access the protected method since we've verified it exists
    const layerWithMethod = layer as BaseLayer & { getSourceCanvas?: () => HTMLCanvasElement };
    if (typeof layerWithMethod.getSourceCanvas === "function") {
      // Call the protected method via type assertion (we've verified it exists)
      const sourceCanvas = (layer as unknown as { getSourceCanvas: () => HTMLCanvasElement }).getSourceCanvas();
      
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (typeof sourceCanvas === "object" && sourceCanvas !== null) {
        // Clone the canvas to avoid mutation issues
        const canvas = document.createElement("canvas");
        canvas.width = sourceCanvas.width;
        canvas.height = sourceCanvas.height;
        const ctx = canvas.getContext("2d");
        if (typeof ctx === "object" && ctx !== null) {
          ctx.drawImage(sourceCanvas, 0, 0);
          return canvas;
        } else {
          throw new Error(`Failed to get 2D context for canvas clone`);
        }
      } else {
        throw new Error(`getSourceCanvas() returned invalid canvas for layer ${layer.id}`);
      }
    }

    // Pattern match: Layer does not have getSourceCanvas method - throw error instead of returning null
    throw new Error(`Layer ${layer.id} does not have getSourceCanvas method`);
  }

  /**
   * Update masks for a specific layer
   */
  setLayerMasks(layerId: string, masks: LayerMask[]): void {
    const layer = this.layers.get(layerId);
    if (layer) {
      layer.setMasks(masks);
    }
  }

  /**
   * Clear track matte assignment for a layer
   */
  clearTrackMatte(layerId: string): void {
    const layer = this.layers.get(layerId);
    if (layer) {
      layer.setTrackMatteCanvas(null);
    }
  }

  /**
   * Compute render order respecting track matte dependencies
   *
   * Matte layers must be rendered before the layers that use them.
   * This returns a topologically sorted list of layer IDs.
   */
  computeRenderOrder(): string[] {
    const order: string[] = [];
    const visited = new Set<string>();
    const visiting = new Set<string>(); // For cycle detection

    const visit = (layerId: string): void => {
      if (visited.has(layerId)) return;
      if (visiting.has(layerId)) {
        layerLogger.warn(
          `Circular track matte dependency detected involving layer ${layerId}`,
        );
        return;
      }

      visiting.add(layerId);

      const layer = this.layers.get(layerId);
      if (layer) {
        // Visit matte layer first (dependency)
        const matteLayerId = layer.getTrackMatteLayerId();
        if (matteLayerId && this.layers.has(matteLayerId)) {
          visit(matteLayerId);
        }

        // Visit parent layer first
        const parentId = layer.getParentId();
        if (parentId && this.layers.has(parentId)) {
          visit(parentId);
        }
      }

      visiting.delete(layerId);
      visited.add(layerId);
      order.push(layerId);
    };

    // Visit all layers
    for (const layerId of this.layers.keys()) {
      visit(layerId);
    }

    this.renderOrder = order;
    return order;
  }

  /**
   * Get the computed render order
   */
  getRenderOrder(): string[] {
    return this.renderOrder;
  }

  // ============================================================================
  // SELECTION
  // ============================================================================

  /**
   * Get layers at a screen position
   */
  getLayersAtPosition(x: number, y: number, camera: THREE.Camera): BaseLayer[] {
    const raycaster = new THREE.Raycaster();
    const pointer = new THREE.Vector2(x, y);

    raycaster.setFromCamera(pointer, camera);

    const intersects = this.scene.raycastComposition(raycaster);
    const layerIds = new Set<string>();

    for (const intersection of intersects) {
      let obj: THREE.Object3D | null = intersection.object;
      while (obj) {
        if (obj.userData.layerId) {
          layerIds.add(obj.userData.layerId);
          break;
        }
        obj = obj.parent;
      }
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    return Array.from(layerIds)
      .map((id) => this.layers.get(id))
      .filter((layer): layer is BaseLayer => typeof layer === "object" && layer !== null);
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Dispose all layers and resources
   */
  dispose(): void {
    for (const layer of this.layers.values()) {
      this.scene.removeFromComposition(layer.getObject());
      layer.dispose();
    }
    this.layers.clear();
  }
}
