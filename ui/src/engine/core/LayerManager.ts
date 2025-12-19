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

import * as THREE from 'three';
import type { Layer, LayerType, LayerMask } from '@/types/project';
import type { SceneManager } from './SceneManager';
import type { ResourceManager } from './ResourceManager';
import type { LayerInstance } from '../types';
import type { EvaluatedLayer } from '../MotionEngine';
import { BaseLayer } from '../layers/BaseLayer';
import { ImageLayer } from '../layers/ImageLayer';
import { SolidLayer } from '../layers/SolidLayer';
import { ControlLayer } from '../layers/ControlLayer';
import { TextLayer } from '../layers/TextLayer';
import { SplineLayer } from '../layers/SplineLayer';
import { ParticleLayer } from '../layers/ParticleLayer';
import { VideoLayer, type VideoMetadata } from '../layers/VideoLayer';
import { NestedCompLayer, type NestedCompRenderContext } from '../layers/NestedCompLayer';
import { EffectLayer, type EffectLayerRenderContext, type AdjustmentRenderContext } from '../layers/EffectLayer';
import { CameraLayer, type CameraGetter, type CameraUpdater } from '../layers/CameraLayer';
import { LightLayer } from '../layers/LightLayer';
import { DepthflowLayer } from '../layers/DepthflowLayer';
import { ProceduralMatteLayer } from '../layers/ProceduralMatteLayer';
import { ShapeLayer } from '../layers/ShapeLayer';
import { ModelLayer } from '../layers/ModelLayer';
import { PointCloudLayer } from '../layers/PointCloudLayer';
import type { TargetParameter } from '@/services/audioReactiveMapping';
import type { SplineQueryResult, SplinePathProvider } from '@/services/particleSystem';
import { layerLogger } from '@/utils/logger';

/** Callback to get audio reactive values for a specific layer at a frame */
export type LayerAudioReactiveGetter = (layerId: string, frame: number) => Map<TargetParameter, number>;

export class LayerManager {
  private readonly scene: SceneManager;
  private readonly resources: ResourceManager;
  private readonly layers: Map<string, BaseLayer>;

  // Callbacks
  private onVideoMetadataLoaded?: (layerId: string, metadata: VideoMetadata) => void;
  private nestedCompRenderContext: NestedCompRenderContext | null = null;
  private effectLayerRenderContext: EffectLayerRenderContext | null = null;
  private cameraGetter?: CameraGetter;
  private cameraAtFrameGetter?: import('../layers/CameraLayer').CameraAtFrameGetter;
  private cameraUpdater?: CameraUpdater;

  // Renderer reference for particle systems
  private rendererRef: THREE.WebGLRenderer | null = null;

  // Composition FPS for particle timing
  private compositionFPS: number = 60;

  // Camera reference for particles
  private cameraRef: THREE.PerspectiveCamera | null = null;

  // Audio reactive callback
  private audioReactiveGetter: LayerAudioReactiveGetter | null = null;

  // Matte canvas cache - stores rendered canvases for layers used as matte sources
  private matteCanvases: Map<string, HTMLCanvasElement> = new Map();

  // Ordered layer list for render order (respects track matte dependencies)
  private renderOrder: string[] = [];

  // Callback to get cross-composition matte canvas
  private crossCompMatteGetter: ((compositionId: string, layerId: string, frame: number) => HTMLCanvasElement | null) | null = null;

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
  setVideoMetadataCallback(callback: (layerId: string, metadata: VideoMetadata) => void): void {
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
      if (layer.type === 'nestedComp') {
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
    for (const layer of this.layers.values()) {
      const layerData = (layer as any).layerData;
      if (layer.type === 'solid' && (layerData?.effectLayer || layerData?.adjustmentLayer)) {
        (layer as unknown as EffectLayer).setRenderContext(context);
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
    atFrameGetter?: import('../layers/CameraLayer').CameraAtFrameGetter
  ): void {
    this.cameraGetter = getter;
    this.cameraUpdater = updater;
    this.cameraAtFrameGetter = atFrameGetter;

    // Update existing camera layers
    for (const layer of this.layers.values()) {
      if (layer.type === 'camera') {
        (layer as CameraLayer).setCameraCallbacks(getter, updater, atFrameGetter);
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
      if (layer.type === 'particles') {
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
      if (layer.type === 'particles') {
        (layer as ParticleLayer).setFPS(fps);
      }
      if (layer.type === 'video') {
        (layer as VideoLayer).setFPS(fps);
      }
      if (layer.type === 'nestedComp') {
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
   */
  getCamera(): THREE.PerspectiveCamera | null {
    return this.cameraRef;
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
      layerLogger.warn(`LayerManager: Layer ${layerData.id} already exists, updating instead`);
      this.update(layerData.id, layerData);
      return this.layers.get(layerData.id)!;
    }

    // Create layer instance
    const layer = this.createLayerInstance(layerData);

    // Register layer
    this.layers.set(layerData.id, layer);

    // Set up type-specific callbacks after creation
    this.setupLayerCallbacks(layer, layerData);

    // Set up parenting
    if (layerData.parentId) {
      const parentLayer = this.layers.get(layerData.parentId);
      if (parentLayer) {
        layer.setParent(parentLayer);
      }
    }

    // Add to scene (only if not parented - parented layers are children of their parent's group)
    if (!layer.hasParent()) {
      this.scene.addToComposition(layer.getObject());
    }

    return layer;
  }

  /**
   * Set up type-specific callbacks after layer creation
   */
  private setupLayerCallbacks(layer: BaseLayer, layerData: Layer): void {
    // Video layer: hook up metadata callback for auto-resize
    if (layer.type === 'video' && this.onVideoMetadataLoaded) {
      const videoLayer = layer as VideoLayer;
      videoLayer.setMetadataCallback((metadata) => {
        this.onVideoMetadataLoaded!(layerData.id, metadata);
      });
    }

    // Nested comp layer: provide render context
    if (layer.type === 'nestedComp' && this.nestedCompRenderContext) {
      const nestedCompLayer = layer as NestedCompLayer;
      nestedCompLayer.setRenderContext(this.nestedCompRenderContext);
    }

    // Camera layer: provide camera data access and spline provider
    if (layer.type === 'camera' && this.cameraGetter && this.cameraUpdater) {
      const cameraLayer = layer as CameraLayer;
      cameraLayer.setCameraCallbacks(this.cameraGetter, this.cameraUpdater, this.cameraAtFrameGetter);

      // Set up spline provider for path following
      cameraLayer.setSplineProvider(this.createSplineProvider());
    }

    // Particle layer: provide renderer and FPS
    if (layer.type === 'particles') {
      const particleLayer = layer as ParticleLayer;
      if (this.rendererRef) {
        particleLayer.setRenderer(this.rendererRef);
      }
      particleLayer.setFPS(this.compositionFPS);
    }

    // Video layer: provide FPS
    if (layer.type === 'video') {
      const videoLayer = layer as VideoLayer;
      videoLayer.setFPS(this.compositionFPS);
    }

    // Nested comp layer: provide FPS
    if (layer.type === 'nestedComp') {
      const nestedCompLayer = layer as NestedCompLayer;
      nestedCompLayer.setFPS(this.compositionFPS);
    }

    // Any layer with effectLayer/adjustmentLayer flag: provide render context
    if ((layerData.effectLayer || layerData.adjustmentLayer) && this.effectLayerRenderContext) {
      // The layer might be a solid or any other type with effect layer flag
      // Cast to access setRenderContext if available
      if ('setRenderContext' in layer) {
        (layer as unknown as EffectLayer).setRenderContext(this.effectLayerRenderContext);
      }
    }

    // Light layer: provide layer position getter for POI and spline provider for path
    if (layer.type === 'light') {
      const lightLayer = layer as LightLayer;

      // Provide a way to get other layer positions (for POI targeting)
      lightLayer.setLayerPositionGetter((layerId: string) => {
        const targetLayer = this.layers.get(layerId);
        if (targetLayer) {
          const obj = targetLayer.getObject();
          return new THREE.Vector3(obj.position.x, obj.position.y, obj.position.z);
        }
        return null;
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
      case 'image':
        return new ImageLayer(layerData, this.resources);

      case 'solid':
        return new SolidLayer(layerData);

      case 'control':
      case 'null': // Deprecated, use 'control'
        return new ControlLayer(layerData);

      case 'text':
        return new TextLayer(layerData, this.resources);

      case 'spline':
        return new SplineLayer(layerData);

      case 'particles':
        return new ParticleLayer(layerData);

      case 'video':
        return new VideoLayer(layerData, this.resources);

      case 'nestedComp':
        return new NestedCompLayer(layerData);

      case 'camera':
        return new CameraLayer(layerData);

      case 'light':
        return new LightLayer(layerData);

      case 'depthflow':
        return new DepthflowLayer(layerData, this.resources);

      case 'matte':
        return new ProceduralMatteLayer(layerData);

      case 'shape':
        return new ShapeLayer(layerData);

      case 'model':
        return new ModelLayer(layerData);

      case 'pointcloud':
        return new PointCloudLayer(layerData);

      default:
        layerLogger.warn(`LayerManager: Unknown layer type: ${layerData.type}, creating ControlLayer`);
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
  batchUpdate(updates: Array<{ id: string; properties: Partial<Layer> }>): void {
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
    for (const [id, layer] of this.layers) {
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
  applyEvaluatedState(evaluatedLayers: readonly EvaluatedLayer[], frame?: number): void {
    const currentFrame = frame ?? 0;

    // First, apply state to spline layers so they evaluate their control points
    // This ensures animated splines are ready before text layers query them
    for (const evalLayer of evaluatedLayers) {
      const layer = this.layers.get(evalLayer.id);
      if (layer && layer.type === 'spline') {
        layer.applyEvaluatedState(evalLayer);
      }
    }

    // Update text-on-path connections (with frame for animated splines)
    this.updateTextPathConnections(frame);

    // Process track mattes - collect matte canvases and distribute to target layers
    // This must happen before applying state to layers that use track mattes
    this.processTrackMattes(currentFrame);

    // Apply evaluated state to remaining layers
    for (const evalLayer of evaluatedLayers) {
      const layer = this.layers.get(evalLayer.id);
      if (layer && layer.type !== 'spline') {
        layer.applyEvaluatedState(evalLayer);
      }
    }

    // Re-sort by Z after evaluation (positions may have changed)
    this.scene.sortByZ();
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
  evaluateFrame(frame: number, audioReactiveGetter?: LayerAudioReactiveGetter | null): void {
    // First, update text-on-path connections
    this.updateTextPathConnections(frame);

    // Process track mattes - collect matte canvases and distribute to target layers
    this.processTrackMattes(frame);

    // Use provided getter or fall back to stored one
    const getter = audioReactiveGetter ?? this.audioReactiveGetter;

    for (const layer of this.layers.values()) {
      // Get audio reactive values for this layer if available
      if (getter) {
        const audioValues = getter(layer.id, frame);
        if (audioValues.size > 0) {
          layer.setAudioReactiveValues(audioValues);
        }
      }

      layer.evaluateFrame(frame);
    }

    // Re-sort by Z after evaluation (positions may have changed)
    this.scene.sortByZ();
  }

  /**
   * Set the audio reactive getter callback
   */
  setAudioReactiveCallback(getter: LayerAudioReactiveGetter | null): void {
    this.audioReactiveGetter = getter;
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
    if (layer) {
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
   * Update text layer connections to spline paths
   * Called before frame evaluation to ensure paths are current
   *
   * For animated splines, this must be called with the current frame
   * to get properly evaluated control points.
   *
   * @param frame - Optional frame number for animated spline evaluation
   */
  private updateTextPathConnections(frame?: number): void {
    for (const layer of this.layers.values()) {
      if (layer.type === 'text') {
        const textLayer = layer as TextLayer;
        const textData = textLayer.getTextData();

        if (textData.pathLayerId) {
          const splineLayer = this.layers.get(textData.pathLayerId) as SplineLayer | undefined;

          if (splineLayer && splineLayer.type === 'spline') {
            // Check if spline is animated and we have a frame
            if (splineLayer.isAnimated() && frame !== undefined) {
              // Get evaluated control points for this frame
              const evaluatedPoints = splineLayer.getEvaluatedControlPoints(frame);

              // Convert EvaluatedControlPoint to ControlPoint for TextLayer
              const controlPoints = evaluatedPoints.map(ep => ({
                id: ep.id,
                x: ep.x,
                y: ep.y,
                depth: ep.depth,
                handleIn: ep.handleIn,
                handleOut: ep.handleOut,
                type: ep.type,
              }));

              // Update text layer with animated path
              textLayer.setPathFromControlPoints(controlPoints, splineLayer.isClosed());
            } else {
              // Static spline - use cached curve
              const curve = splineLayer.getCurve();
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
    return (layerId: string, t: number, frame: number): SplineQueryResult | null => {
      return this.querySplinePath(layerId, t, frame);
    };
  }

  /**
   * Query a spline layer for position and tangent at parameter t
   *
   * @param layerId - ID of the spline layer
   * @param t - Parameter along the path (0-1)
   * @param frame - Current frame for animated splines
   * @returns Position, tangent, and length or null if spline not found
   */
  querySplinePath(layerId: string, t: number, frame: number): SplineQueryResult | null {
    const layer = this.layers.get(layerId);

    if (!layer || layer.type !== 'spline') {
      return null;
    }

    const splineLayer = layer as SplineLayer;

    // For animated splines, ensure we have evaluated control points
    // This triggers rebuild if points have changed
    if (splineLayer.isAnimated()) {
      splineLayer.getEvaluatedControlPoints(frame);
    }

    // Query the curve
    const point = splineLayer.getPointAt(t);
    const tangent = splineLayer.getTangentAt(t);
    const length = splineLayer.getLength();

    if (!point || !tangent) {
      return null;
    }

    // Convert Three.js coordinates to normalized coordinates
    // Spline coordinates are in canvas pixels, normalize to 0-1
    // Note: The Y coordinate is negated in SplineLayer, so we negate it back
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
   * Get all spline layer IDs (useful for UI to list available paths)
   */
  getSplineLayerIds(): string[] {
    const ids: string[] = [];
    for (const [id, layer] of this.layers) {
      if (layer.type === 'spline') {
        ids.push(id);
      }
    }
    return ids;
  }

  /**
   * Connect a text layer to a spline path
   */
  connectTextToPath(textLayerId: string, splineLayerId: string | null): void {
    const textLayer = this.layers.get(textLayerId) as TextLayer | undefined;

    if (!textLayer || textLayer.type !== 'text') {
      layerLogger.warn(`LayerManager: Text layer ${textLayerId} not found`);
      return;
    }

    if (!splineLayerId) {
      textLayer.clearPath();
      return;
    }

    const splineLayer = this.layers.get(splineLayerId) as SplineLayer | undefined;

    if (!splineLayer || splineLayer.type !== 'spline') {
      layerLogger.warn(`LayerManager: Spline layer ${splineLayerId} not found`);
      return;
    }

    const curve = splineLayer.getCurve();
    if (curve) {
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
    return this.layers.get(layerId)?.getObject() ?? null;
  }

  /**
   * Get a layer instance
   */
  getLayer(layerId: string): BaseLayer | null {
    return this.layers.get(layerId) ?? null;
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
      layer => layer.type === type
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
        const parent = layer.getParent();
        if (parent) {
          parent.getObject().remove(layer.getObject());
        }
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
      const oldParent = layer.getParent();
      if (oldParent) {
        oldParent.getObject().remove(layer.getObject());
      }
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
  setCrossCompMatteGetter(
    getter: ((compositionId: string, layerId: string, frame: number) => HTMLCanvasElement | null) | null
  ): void {
    this.crossCompMatteGetter = getter;
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

      if (!matteLayerId || matteType === 'none') {
        continue;
      }

      let matteCanvas: HTMLCanvasElement | null = null;

      // Check if this is a cross-composition matte
      if (layer.hasCrossCompMatte() && this.crossCompMatteGetter) {
        const compositionId = layer.getTrackMatteCompositionId()!;
        matteCanvas = this.crossCompMatteGetter(compositionId, matteLayerId, frame);

        if (!matteCanvas) {
          layerLogger.warn(
            `Cross-comp track matte not found: composition=${compositionId}, layer=${matteLayerId}`
          );
        }
      } else {
        // Same composition matte
        const matteLayer = this.layers.get(matteLayerId);

        if (matteLayer) {
          // Check cache first
          if (this.matteCanvases.has(matteLayerId)) {
            matteCanvas = this.matteCanvases.get(matteLayerId)!;
          } else {
            // Render and cache the matte
            matteCanvas = this.getLayerRenderedCanvas(matteLayer, frame);
            if (matteCanvas) {
              this.matteCanvases.set(matteLayerId, matteCanvas);
            }
          }
        } else {
          layerLogger.warn(`Matte source layer ${matteLayerId} not found`);
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
   * @returns Canvas with layer's rendered content, or null if unavailable
   */
  private getLayerRenderedCanvas(layer: BaseLayer, frame: number): HTMLCanvasElement | null {
    // For layers with getSourceCanvas, use that
    // Note: This is a simplified implementation - in production,
    // this would need to render the full layer to an offscreen canvas
    // including transforms, effects, and nested content

    // Try to get the layer's source canvas through a render-to-texture approach
    // For now, we use the internal source canvas method
    // Subclasses like ImageLayer, VideoLayer, TextLayer implement getSourceCanvas()

    // Cast to access protected method via any type assertion
    // In production, BaseLayer would expose a public getRenderedCanvas() method
    const sourceCanvas = (layer as unknown as { getSourceCanvas(): HTMLCanvasElement | null }).getSourceCanvas?.();

    if (sourceCanvas) {
      // Clone the canvas to avoid mutation issues
      const canvas = document.createElement('canvas');
      canvas.width = sourceCanvas.width;
      canvas.height = sourceCanvas.height;
      const ctx = canvas.getContext('2d');
      if (ctx) {
        ctx.drawImage(sourceCanvas, 0, 0);
        return canvas;
      }
    }

    return null;
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
        layerLogger.warn(`Circular track matte dependency detected involving layer ${layerId}`);
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
  getLayersAtPosition(
    x: number,
    y: number,
    camera: THREE.Camera
  ): BaseLayer[] {
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

    return Array.from(layerIds)
      .map(id => this.layers.get(id))
      .filter((layer): layer is BaseLayer => layer !== undefined);
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
