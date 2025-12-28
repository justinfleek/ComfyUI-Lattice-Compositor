/**
 * BaseLayer - Abstract Base Class for All Layers
 *
 * Provides common functionality for all layer types:
 * - Transform management
 * - Animation evaluation
 * - Visibility control
 * - Resource lifecycle
 */

import * as THREE from 'three';
import type { Layer, AnimatableProperty, LayerTransform, LayerMask, MatteType, LayerMotionBlurSettings, AutoOrientMode, LayerStyles } from '@/types/project';
import type { EffectInstance } from '@/types/effects';
import { renderLayerStyles } from '@/services/effects/layerStyleRenderer';
import type { LayerInstance } from '../types';
import type { TargetParameter } from '@/services/audioReactiveMapping';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';
import { processEffectStack, hasEnabledEffects } from '@/services/effectProcessor';
import { applyMasksToLayer, applyTrackMatte } from '@/services/effects/maskRenderer';
import { MotionBlurProcessor, createDefaultMotionBlurSettings, type VelocityData } from '@/services/motionBlur';
import { layerLogger } from '@/utils/logger';
import { setMaterialBlendMode, applyBlendModeToGroup } from './blendModeUtils';

export abstract class BaseLayer implements LayerInstance {
  /** Unique layer identifier */
  public readonly id: string;

  /** Layer type */
  public readonly type: string;

  /** The Three.js group containing this layer's content */
  protected readonly group: THREE.Group;

  /** Three.js object representing this layer (from LayerInstance) */
  public get object(): THREE.Object3D {
    return this.group;
  }

  /** Keyframe evaluator for animated properties */
  protected readonly evaluator: KeyframeEvaluator;

  /** Layer visibility */
  protected visible: boolean;

  /** Layer locked state */
  protected locked: boolean;

  /** In point (start frame) */
  protected inPoint: number;

  /** Out point (end frame) */
  protected outPoint: number;

  /** Layer opacity (0-100) */
  protected opacity: AnimatableProperty<number>;

  /** Layer transform */
  protected transform: LayerTransform;

  /** 3D layer flag */
  protected threeD: boolean;

  /** Auto-orient mode (billboard to camera, along path, etc.) */
  protected autoOrient: AutoOrientMode = 'off';

  /** Blend mode */
  protected blendMode: string;

  /** Parent layer ID (for parenting hierarchy) */
  protected parentId: string | null;

  /** Reference to parent layer (set by LayerManager) */
  protected parentLayer: BaseLayer | null = null;

  /** Driven values override (from property drivers/expressions) */
  protected drivenValues: Map<string, number> = new Map();

  /** Audio reactive values (from audio analysis mapping) */
  protected audioReactiveValues: Map<TargetParameter, number> = new Map();

  /** Effects stack for this layer */
  protected effects: EffectInstance[] = [];

  /** Layer-level effects enable/disable (fx switch in AE) */
  protected effectsEnabled: boolean = true;

  /** Layer styles (drop shadow, stroke, etc.) */
  protected layerStyles: LayerStyles | undefined;

  /** Layer quality mode (draft = faster, best = full quality) */
  protected quality: 'draft' | 'best' = 'best';

  /** Composition FPS for time-based effects (set by LayerManager) */
  protected compositionFps: number = 16;

  /** BUG-090 fix: Current audio modifiers for color adjustments */
  protected currentAudioModifiers: import('../MotionEngine').AudioReactiveModifiers = {};

  /** Source canvas for effect processing (lazy initialized) */
  protected effectSourceCanvas: HTMLCanvasElement | null = null;

  /** Flag to track if effects need processing */
  protected effectsDirty: boolean = false;

  // ============================================================================
  // MASK & MATTE SYSTEM
  // ============================================================================

  /** Masks applied to this layer (vector cutouts) */
  protected masks: LayerMask[] = [];

  /** Matte source type (uses another layer as alpha/luma source) */
  protected matteType: MatteType = 'none';

  /** ID of the layer used as matte source */
  protected matteLayerId: string | null = null;

  /** ID of composition containing matte layer (for cross-comp mattes) */
  protected matteCompositionId: string | null = null;

  /** Canvas of matte source layer (set externally by LayerManager) */
  protected matteCanvas: HTMLCanvasElement | null = null;

  /** Preserve transparency - only paint on existing pixels */
  protected preserveTransparency: boolean = false;

  // ============================================================================
  // MOTION PATH VISUALIZATION
  // ============================================================================

  /** Motion path line visualization */
  protected motionPath: THREE.Line | null = null;

  /** Motion path points (frame positions) */
  protected motionPathPoints: THREE.Vector3[] = [];

  /** Whether motion path is visible */
  protected showMotionPath: boolean = false;

  /** Motion path keyframe markers */
  protected motionPathMarkers: THREE.Group | null = null;

  /** 3D axis gizmo at anchor point */
  protected axisGizmo: THREE.Group | null = null;

  /** Whether 3D axis gizmo is visible */
  protected showAxisGizmo: boolean = false;

  // ============================================================================
  // MOTION BLUR
  // ============================================================================

  /** Motion blur enabled (layer switch) */
  protected motionBlur: boolean = false;

  /** Motion blur settings */
  protected motionBlurSettings: LayerMotionBlurSettings | null = null;

  /** Motion blur processor instance */
  protected motionBlurProcessor: MotionBlurProcessor | null = null;

  /** Previous frame transform values for velocity calculation */
  protected prevTransform: {
    position: { x: number; y: number; z: number };
    rotation: number;
    scale: { x: number; y: number };
  } | null = null;

  /** Last frame that motion blur was evaluated */
  protected motionBlurLastFrame: number = -1;

  /** Reference to layer data for property access */
  protected layerData: Layer;

  constructor(layerData: Layer) {
    this.id = layerData.id;
    this.type = layerData.type;

    // Create container group
    this.group = new THREE.Group();
    this.group.name = `layer_${this.id}`;
    this.group.userData.layerId = this.id;
    this.group.userData.layerType = this.type;

    // Initialize evaluator
    this.evaluator = new KeyframeEvaluator();

    // Copy properties
    this.visible = layerData.visible;
    this.locked = layerData.locked;
    this.inPoint = layerData.startFrame ?? layerData.inPoint ?? 0;
    this.outPoint = layerData.endFrame ?? layerData.outPoint ?? 80;
    this.opacity = layerData.opacity;
    this.transform = layerData.transform;
    this.threeD = layerData.threeD ?? false;
    this.autoOrient = layerData.autoOrient ?? 'off';
    this.blendMode = layerData.blendMode ?? 'normal';
    this.parentId = layerData.parentId ?? null;
    this.effects = layerData.effects ?? [];
    this.effectsEnabled = layerData.effectsEnabled !== false; // Default true
    this.layerStyles = layerData.layerStyles;
    this.quality = layerData.quality ?? 'best';

    // Motion blur properties
    this.motionBlur = layerData.motionBlur ?? false;
    this.motionBlurSettings = layerData.motionBlurSettings ?? null;
    this.layerData = layerData;

    // Mask & matte properties (with backwards compatibility for old property names)
    this.masks = layerData.masks ?? [];
    this.matteType = layerData.matteType ?? layerData.trackMatteType ?? 'none';
    this.matteLayerId = layerData.matteLayerId ?? layerData.trackMatteLayerId ?? null;
    this.matteCompositionId = layerData.matteCompositionId ?? layerData.trackMatteCompositionId ?? null;
    this.preserveTransparency = layerData.preserveTransparency ?? false;
  }

  /**
   * Initialize blend mode after subclass creates mesh
   * Subclasses should call this at the end of their constructor
   */
  protected initializeBlendMode(): void {
    if (this.blendMode !== 'normal') {
      this.applyBlendMode(this.blendMode);
    }
  }

  // ============================================================================
  // OBJECT ACCESS
  // ============================================================================

  /**
   * Get the Three.js object representing this layer
   */
  getObject(): THREE.Group {
    return this.group;
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  /**
   * Evaluate all animated properties at the given frame
   */
  evaluateFrame(frame: number): void {
    // Check if layer is visible at this frame
    const inRange = frame >= this.inPoint && frame <= this.outPoint;
    this.group.visible = this.visible && inRange;

    if (!this.group.visible) {
      return; // Skip evaluation for invisible layers
    }

    // Evaluate opacity (apply driven value if present, then audio reactive)
    let baseOpacity = this.evaluator.evaluate(this.opacity, frame);
    baseOpacity = this.getDrivenOrBase('opacity', baseOpacity);
    // Apply audio reactive modulation to opacity (multiplicative, clamped 0-100)
    const opacityValue = this.applyAudioModulation(baseOpacity, 'layer.opacity', 'multiply', { min: 0, max: 100 });
    this.applyOpacity(opacityValue);

    // Evaluate transform (with audio reactive modulation)
    this.evaluateTransform(frame);

    // Call subclass-specific evaluation
    this.onEvaluateFrame(frame);
  }

  /**
   * Evaluate and apply transform at the given frame
   */
  protected evaluateTransform(frame: number): void {
    // Position (apply driven values if present, then audio reactive)
    const basePosition = this.evaluator.evaluate(this.transform.position, frame);
    let posX = this.getDrivenOrBase('transform.position.x', basePosition.x);
    let posY = this.getDrivenOrBase('transform.position.y', basePosition.y);
    const posZ = this.getDrivenOrBase('transform.position.z', basePosition.z ?? 0);

    // Apply audio reactive modulation to position (additive)
    posX = this.applyAudioModulation(posX, 'layer.x', 'add');
    posY = this.applyAudioModulation(posY, 'layer.y', 'add');

    const position = { x: posX, y: posY, z: posZ };

    // Scale (stored as percentage, convert to multiplier)
    const baseScale = this.evaluator.evaluate(this.transform.scale, frame);
    let scaleX = this.getDrivenOrBase('transform.scale.x', baseScale.x ?? 100);
    let scaleY = this.getDrivenOrBase('transform.scale.y', baseScale.y ?? 100);
    const scaleZ = this.getDrivenOrBase('transform.scale.z', baseScale.z ?? 100);

    // Apply audio reactive modulation to scale (multiplicative, affects both X and Y uniformly)
    const audioScaleMod = this.getAudioReactiveValue('layer.scale');
    if (audioScaleMod !== 0) {
      const scaleFactor = 0.5 + audioScaleMod; // 0 -> 0.5x, 0.5 -> 1x, 1 -> 1.5x
      scaleX *= scaleFactor;
      scaleY *= scaleFactor;
    }

    const scale = { x: scaleX, y: scaleY, z: scaleZ };

    // Origin (formerly anchorPoint)
    const originProp = this.transform.origin || this.transform.anchorPoint;
    const baseOrigin = originProp ? this.evaluator.evaluate(originProp, frame) : { x: 0, y: 0, z: 0 };
    const origin = {
      x: this.getDrivenOrBase('transform.origin.x', baseOrigin.x ?? 0),
      y: this.getDrivenOrBase('transform.origin.y', baseOrigin.y ?? 0),
      z: this.getDrivenOrBase('transform.origin.z', baseOrigin.z ?? 0)
    };
    // Keep anchorPoint alias for backwards compatibility
    const anchorPoint = origin;

    // Rotation (depends on 3D mode)
    let rotation = 0;
    let rotationX = 0;
    let rotationY = 0;

    if (this.threeD) {
      // 3D mode: use separate X, Y, Z rotations
      const baseRotX = this.transform.rotationX
        ? this.evaluator.evaluate(this.transform.rotationX, frame)
        : 0;
      rotationX = this.getDrivenOrBase('transform.rotationX', baseRotX);

      const baseRotY = this.transform.rotationY
        ? this.evaluator.evaluate(this.transform.rotationY, frame)
        : 0;
      rotationY = this.getDrivenOrBase('transform.rotationY', baseRotY);

      const baseRotZ = this.transform.rotationZ
        ? this.evaluator.evaluate(this.transform.rotationZ, frame)
        : 0;
      rotation = this.getDrivenOrBase('transform.rotationZ', baseRotZ);
    } else {
      // 2D mode: use single rotation
      const baseRotation = this.evaluator.evaluate(this.transform.rotation, frame);
      rotation = this.getDrivenOrBase('transform.rotation', baseRotation);
    }

    // Apply audio reactive modulation to rotation (additive, scaled to degrees)
    const audioRotMod = this.getAudioReactiveValue('layer.rotation');
    if (audioRotMod !== 0) {
      rotation += audioRotMod * 360; // Full rotation range
    }

    // Apply transform (using origin, formerly anchorPoint)
    this.applyTransform({
      position: {
        x: position.x,
        y: position.y,
        z: position.z,
      },
      rotation: {
        x: rotationX,
        y: rotationY,
        z: rotation,
      },
      scale: {
        x: scale.x / 100,
        y: scale.y / 100,
        z: scale.z / 100,
      },
      origin: {
        x: origin.x,
        y: origin.y,
        z: origin.z,
      },
    });
  }

  /**
   * Apply transform to the group
   */
  protected applyTransform(transform: {
    position: { x: number; y: number; z: number };
    rotation: { x: number; y: number; z: number };
    scale: { x: number; y: number; z: number };
    origin: { x: number; y: number; z: number };
  }): void {
    const { position, rotation, scale, origin } = transform;

    // Validate all transform values (NaN causes Three.js rendering issues)
    const posX = Number.isFinite(position.x) ? position.x : 0;
    const posY = Number.isFinite(position.y) ? position.y : 0;
    const posZ = Number.isFinite(position.z) ? position.z : 0;
    const originX = Number.isFinite(origin.x) ? origin.x : 0;
    const originY = Number.isFinite(origin.y) ? origin.y : 0;
    const originZ = Number.isFinite(origin.z) ? origin.z : 0;
    const rotX = Number.isFinite(rotation.x) ? rotation.x : 0;
    const rotY = Number.isFinite(rotation.y) ? rotation.y : 0;
    const rotZ = Number.isFinite(rotation.z) ? rotation.z : 0;
    // Scale defaults to 1 (not 0) to prevent invisible layers
    const scaleX = Number.isFinite(scale.x) ? scale.x : 1;
    const scaleY = Number.isFinite(scale.y) ? scale.y : 1;
    const scaleZ = Number.isFinite(scale.z) ? scale.z : 1;

    // Position (with origin offset, formerly anchorPoint)
    // In screen coordinates: Y is down, so negate Y
    this.group.position.set(
      posX - originX,
      -(posY - originY), // Negate for screen coords
      posZ - originZ
    );

    // Rotation (convert degrees to radians)
    // Negate Z for screen coords
    this.group.rotation.set(
      THREE.MathUtils.degToRad(rotX),
      THREE.MathUtils.degToRad(rotY),
      THREE.MathUtils.degToRad(-rotZ)
    );

    // Scale
    this.group.scale.set(scaleX, scaleY, scaleZ);

    // Update matrix
    this.group.updateMatrix();
  }

  /**
   * Apply auto-orient behavior (billboarding, path orientation, etc.)
   *
   * Call this after applyTransform when the layer should face the camera.
   * For 'toCamera' mode, the layer always faces the camera but only X/Y position moves.
   *
   * @param camera - The camera to orient toward (for 'toCamera' mode)
   * @param pathTangent - Optional path tangent vector (for 'alongPath' mode)
   */
  applyAutoOrient(camera?: THREE.Camera, pathTangent?: THREE.Vector3): void {
    if (this.autoOrient === 'off') {
      return;
    }

    if (this.autoOrient === 'toCamera' && camera) {
      // Billboard mode: Layer always faces the camera
      // Keep position, just modify rotation to face camera
      const cameraPosition = new THREE.Vector3();
      camera.getWorldPosition(cameraPosition);

      const layerPosition = new THREE.Vector3();
      this.group.getWorldPosition(layerPosition);

      // Calculate direction from layer to camera
      const direction = new THREE.Vector3()
        .subVectors(cameraPosition, layerPosition)
        .normalize();

      // Create a quaternion that rotates the layer to face the camera
      // We only rotate around Y axis for vertical billboarding (sprite-style)
      const targetQuaternion = new THREE.Quaternion();

      // For 2D-style billboarding, we want the layer to face the camera
      // but keep its "up" direction aligned with world up
      const up = new THREE.Vector3(0, 1, 0);
      const matrix = new THREE.Matrix4();
      matrix.lookAt(layerPosition, cameraPosition, up);
      targetQuaternion.setFromRotationMatrix(matrix);

      // Apply the billboard rotation
      this.group.quaternion.copy(targetQuaternion);
      this.group.updateMatrix();
    }

    if (this.autoOrient === 'alongPath' && pathTangent) {
      // Orient along motion path tangent
      // The tangent vector points in the direction of movement
      const angle = Math.atan2(pathTangent.y, pathTangent.x);

      // Apply rotation (keeping any existing X/Y rotation from 3D layers)
      if (this.threeD) {
        // For 3D layers, only modify Z rotation
        this.group.rotation.z = -angle;
      } else {
        // For 2D layers, set the Z rotation
        this.group.rotation.set(0, 0, -angle);
      }
      this.group.updateMatrix();
    }
  }

  /**
   * Get the current auto-orient mode
   */
  getAutoOrient(): AutoOrientMode {
    return this.autoOrient;
  }

  /**
   * Set the auto-orient mode
   */
  setAutoOrient(mode: AutoOrientMode): void {
    this.autoOrient = mode;
  }

  /**
   * Apply opacity to layer materials
   */
  protected applyOpacity(opacity: number): void {
    // Validate opacity (NaN bypasses Math.max/min clamp)
    const validOpacity = Number.isFinite(opacity) ? opacity : 100;
    const normalizedOpacity = Math.max(0, Math.min(100, validOpacity)) / 100;

    this.group.traverse((child) => {
      if (child instanceof THREE.Mesh && child.material) {
        const material = child.material as THREE.Material & { opacity?: number };
        if ('opacity' in material) {
          material.opacity = normalizedOpacity;
          material.transparent = normalizedOpacity < 1;
          material.needsUpdate = true;
        }
      }
    });
  }

  /**
   * Override in subclasses for type-specific frame evaluation
   * @deprecated Use onApplyEvaluatedState instead
   */
  protected abstract onEvaluateFrame(frame: number): void;

  // ============================================================================
  // EVALUATED STATE APPLICATION (NEW - SINGLE SOURCE OF TRUTH)
  // ============================================================================

  /**
   * Apply pre-evaluated state from MotionEngine
   *
   * This is the NEW canonical way to update layer visual state.
   * All values are already computed - layers only APPLY them.
   * NO interpolation or time sampling happens here.
   *
   * @param state - Pre-evaluated layer state from MotionEngine
   */
  applyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Set visibility
    this.group.visible = state.visible;

    if (!state.visible) {
      return; // Skip applying state to invisible layers
    }

    // Apply opacity (with driven value override if present)
    // Audio modifiers for opacity are already applied in MotionEngine.evaluateLayers
    const opacity = this.getDrivenOrBase('opacity', state.opacity);
    this.applyOpacity(opacity);

    // Get audio modifiers (additive values from audio mappings)
    const audioMod = state.audioModifiers || {};

    // BUG-090 fix: Store audio modifiers for color adjustment processing
    this.currentAudioModifiers = audioMod;

    // Apply transform (with driven value overrides and audio modifiers if present)
    // Audio modifiers are ADDITIVE to the base transform values
    const transform = state.transform;
    // Use origin (new name) with fallback to anchorPoint (deprecated)
    const originVal = transform.origin || transform.anchorPoint || { x: 0, y: 0, z: 0 };

    // Calculate base values with driven overrides
    let posX = this.getDrivenOrBase('transform.position.x', transform.position.x);
    let posY = this.getDrivenOrBase('transform.position.y', transform.position.y);
    let posZ = this.getDrivenOrBase('transform.position.z', transform.position.z ?? 0);
    let scaleX = this.getDrivenOrBase('transform.scale.x', transform.scale.x ?? 100) / 100;
    let scaleY = this.getDrivenOrBase('transform.scale.y', transform.scale.y ?? 100) / 100;
    let scaleZ = this.getDrivenOrBase('transform.scale.z', transform.scale.z ?? 100) / 100;
    let rotZ = this.getDrivenOrBase('transform.rotation', transform.rotation);

    // Apply audio modifiers (additive)
    if (audioMod.x !== undefined) posX += audioMod.x;
    if (audioMod.y !== undefined) posY += audioMod.y;
    if (audioMod.rotation !== undefined) rotZ += audioMod.rotation;

    // Scale modifiers are multiplicative (1 + modifier)
    if (audioMod.scaleUniform !== undefined) {
      const scaleMult = 1 + audioMod.scaleUniform;
      scaleX *= scaleMult;
      scaleY *= scaleMult;
      scaleZ *= scaleMult;
    }
    if (audioMod.scaleX !== undefined) scaleX *= (1 + audioMod.scaleX);
    if (audioMod.scaleY !== undefined) scaleY *= (1 + audioMod.scaleY);

    this.applyTransform({
      position: { x: posX, y: posY, z: posZ },
      rotation: {
        x: this.getDrivenOrBase('transform.rotationX', transform.rotationX ?? 0),
        y: this.getDrivenOrBase('transform.rotationY', transform.rotationY ?? 0),
        z: rotZ,
      },
      scale: { x: scaleX, y: scaleY, z: scaleZ },
      origin: {
        x: this.getDrivenOrBase('transform.origin.x', originVal.x),
        y: this.getDrivenOrBase('transform.origin.y', originVal.y),
        z: this.getDrivenOrBase('transform.origin.z', originVal.z ?? 0),
      },
    });

    // Call subclass-specific state application
    this.onApplyEvaluatedState(state);
  }

  /**
   * Override in subclasses for type-specific state application
   * Default implementation calls legacy onEvaluateFrame for compatibility
   */
  protected onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Default: fall back to legacy evaluation for backwards compatibility
    // Subclasses should override this to use evaluated state directly
    // NOTE: This is a transitional measure - eventually all layers should
    // implement proper onApplyEvaluatedState and not call onEvaluateFrame
  }

  // ============================================================================
  // PROPERTY UPDATES
  // ============================================================================

  /**
   * Update layer properties
   */
  update(properties: Partial<Layer>): void {
    if (properties.visible !== undefined) {
      this.visible = properties.visible;
      this.group.visible = this.visible;
    }

    if (properties.locked !== undefined) {
      this.locked = properties.locked;
    }

    if (properties.inPoint !== undefined) {
      this.inPoint = properties.inPoint;
    }

    if (properties.outPoint !== undefined) {
      this.outPoint = properties.outPoint;
    }

    if (properties.opacity !== undefined) {
      this.opacity = properties.opacity;
    }

    if (properties.transform !== undefined) {
      this.transform = properties.transform;
    }

    if (properties.threeD !== undefined) {
      this.threeD = properties.threeD;
    }

    if (properties.autoOrient !== undefined) {
      this.autoOrient = properties.autoOrient;
    }

    if (properties.blendMode !== undefined) {
      this.blendMode = properties.blendMode;
      this.applyBlendMode(this.blendMode);
    }

    if (properties.effects !== undefined) {
      this.setEffects(properties.effects);
    }

    // Mask and matte property updates (supporting both new and deprecated names)
    if (properties.masks !== undefined) {
      this.masks = properties.masks;
    }

    const newMatteType = properties.matteType ?? properties.trackMatteType;
    if (newMatteType !== undefined) {
      this.matteType = newMatteType;
    }

    const newMatteLayerId = properties.matteLayerId ?? properties.trackMatteLayerId;
    if (newMatteLayerId !== undefined) {
      this.matteLayerId = newMatteLayerId;
      // Clear the cached canvas when matte source changes
      this.matteCanvas = null;
    }

    const newMatteCompId = properties.matteCompositionId ?? properties.trackMatteCompositionId;
    if (newMatteCompId !== undefined) {
      this.matteCompositionId = newMatteCompId;
      // Clear the cached canvas when matte composition changes
      this.matteCanvas = null;
    }

    if (properties.preserveTransparency !== undefined) {
      this.preserveTransparency = properties.preserveTransparency;
    }

    // Call subclass-specific update
    this.onUpdate(properties);
  }

  /**
   * Override in subclasses for type-specific updates
   */
  protected abstract onUpdate(properties: Partial<Layer>): void;

  // ============================================================================
  // VISIBILITY
  // ============================================================================

  /**
   * Set layer visibility
   */
  setVisible(visible: boolean): void {
    this.visible = visible;
    this.group.visible = visible;
  }

  /**
   * Get layer visibility
   */
  isVisible(): boolean {
    return this.visible;
  }

  /**
   * Get the underlying layer data
   * Used for accessing transform, anchor point, and other layer properties
   */
  getLayerData(): Layer {
    return this.layerData;
  }

  // ============================================================================
  // DRIVEN VALUES (Expressions/Links)
  // ============================================================================

  /**
   * Set driven values from property drivers
   * These override the base animated values during transform evaluation
   * @param values Map of property path to driven value
   */
  setDrivenValues(values: Map<string, number>): void {
    this.drivenValues = values;
  }

  /**
   * Clear driven values
   */
  clearDrivenValues(): void {
    this.drivenValues.clear();
  }

  /**
   * Get a driven value if it exists, otherwise return the base value
   */
  protected getDrivenOrBase(propertyPath: string, baseValue: number): number {
    const drivenValue = this.drivenValues.get(propertyPath);
    // Validate driven value (NaN from expressions would corrupt transform pipeline)
    if (drivenValue !== undefined && Number.isFinite(drivenValue)) {
      return drivenValue;
    }
    // Validate base value as final fallback
    return Number.isFinite(baseValue) ? baseValue : 0;
  }

  // ============================================================================
  // AUDIO REACTIVE VALUES
  // ============================================================================

  /**
   * Set audio reactive values from audio analysis
   * These are applied additively/multiplicatively to animated properties
   * @param values Map of target parameter to audio-derived value (0-1 range typically)
   */
  setAudioReactiveValues(values: Map<TargetParameter, number>): void {
    this.audioReactiveValues = values;
  }

  /**
   * Clear audio reactive values
   */
  clearAudioReactiveValues(): void {
    this.audioReactiveValues.clear();
  }

  /**
   * Get audio reactive modulation for a property
   * Returns 0 if no mapping exists (additive identity)
   */
  protected getAudioReactiveValue(target: TargetParameter): number {
    return this.audioReactiveValues.get(target) ?? 0;
  }

  /**
   * Apply audio reactive modulation to a base value
   * Mode determines how the modulation is applied
   */
  protected applyAudioModulation(
    baseValue: number,
    target: TargetParameter,
    mode: 'add' | 'multiply' | 'replace' = 'add',
    range: { min?: number; max?: number } = {}
  ): number {
    // Validate baseValue (NaN propagates through all calculations)
    const validBase = Number.isFinite(baseValue) ? baseValue : 0;

    const audioValue = this.getAudioReactiveValue(target);
    // Validate audioValue (could be NaN from audio analysis)
    const validAudio = Number.isFinite(audioValue) ? audioValue : 0;
    if (validAudio === 0) return validBase;

    let result: number;
    switch (mode) {
      case 'multiply':
        // Audio value of 0.5 = no change, 0 = halved, 1 = doubled
        result = validBase * (0.5 + validAudio);
        break;
      case 'replace':
        // Audio value directly replaces base value
        result = validAudio;
        break;
      case 'add':
      default:
        // Audio value added to base (scaled to reasonable range)
        result = validBase + validAudio * 100; // Scale for typical property ranges
        break;
    }

    // Final NaN check (defensive, shouldn't happen after validation)
    if (!Number.isFinite(result)) result = validBase;

    // Clamp to range if specified (using validated range values)
    const validMin = Number.isFinite(range.min) ? range.min : undefined;
    const validMax = Number.isFinite(range.max) ? range.max : undefined;
    if (validMin !== undefined) result = Math.max(validMin, result);
    if (validMax !== undefined) result = Math.min(validMax, result);

    return result;
  }

  // ============================================================================
  // EFFECTS
  // ============================================================================

  /**
   * Update the effects stack for this layer
   * @param effects - Array of effect instances
   */
  setEffects(effects: EffectInstance[]): void {
    this.effects = effects;
    this.effectsDirty = true;
  }

  /**
   * Get the current effects stack
   */
  getEffects(): EffectInstance[] {
    return this.effects;
  }

  /**
   * Check if this layer has any enabled effects
   * Also respects the layer-level effectsEnabled flag (fx switch)
   */
  hasEnabledEffects(): boolean {
    // Layer-level effects toggle (fx switch) disables ALL effects
    if (!this.effectsEnabled) {
      return false;
    }
    return hasEnabledEffects(this.effects);
  }

  /**
   * Set layer-level effects enabled state (fx switch)
   */
  setEffectsEnabled(enabled: boolean): void {
    this.effectsEnabled = enabled;
  }

  /**
   * Get layer-level effects enabled state
   */
  getEffectsEnabled(): boolean {
    return this.effectsEnabled;
  }

  /**
   * Check if this layer has any enabled layer styles
   * Returns true if the layer has layer styles with at least one style type enabled
   */
  hasEnabledLayerStyles(): boolean {
    if (!this.layerStyles?.enabled) {
      return false;
    }
    // Check if any individual style is enabled
    return !!(
      this.layerStyles.dropShadow?.enabled ||
      this.layerStyles.innerShadow?.enabled ||
      this.layerStyles.outerGlow?.enabled ||
      this.layerStyles.innerGlow?.enabled ||
      this.layerStyles.bevelEmboss?.enabled ||
      this.layerStyles.satin?.enabled ||
      this.layerStyles.colorOverlay?.enabled ||
      this.layerStyles.gradientOverlay?.enabled ||
      this.layerStyles.stroke?.enabled
    );
  }

  /**
   * Get layer styles
   */
  getLayerStyles(): LayerStyles | undefined {
    return this.layerStyles;
  }

  // ============================================================================
  // BUG-090/091 FIX: VISUAL MODIFIERS (COLOR + BLUR)
  // ============================================================================

  /**
   * Check if any visual audio modifiers are active (color or blur)
   */
  protected hasColorModifiers(): boolean {
    const m = this.currentAudioModifiers;
    return m.brightness !== undefined ||
           m.saturation !== undefined ||
           m.contrast !== undefined ||
           m.hue !== undefined ||
           m.blur !== undefined;  // BUG-091: Include blur
  }

  /**
   * Apply visual audio modifiers to a canvas (color adjustments + blur)
   * Uses CSS filter syntax for brightness, saturation, contrast, hue-rotate, blur
   * @param canvas - Source canvas to apply adjustments to
   * @returns New canvas with adjustments applied, or original if no adjustments needed
   */
  protected applyColorAdjustments(canvas: HTMLCanvasElement): HTMLCanvasElement {
    const m = this.currentAudioModifiers;

    // Build CSS filter string
    const filters: string[] = [];

    // BUG-090: Color adjustments
    // Brightness: audio value 0 = normal, -0.5 = 50% darker, +0.5 = 50% brighter
    if (m.brightness !== undefined && m.brightness !== 0) {
      filters.push(`brightness(${1 + m.brightness})`);
    }

    // Saturation: audio value 0 = normal, -0.5 = 50% less, +0.5 = 50% more
    if (m.saturation !== undefined && m.saturation !== 0) {
      filters.push(`saturate(${1 + m.saturation})`);
    }

    // Contrast: audio value 0 = normal, -0.5 = 50% less, +0.5 = 50% more
    if (m.contrast !== undefined && m.contrast !== 0) {
      filters.push(`contrast(${1 + m.contrast})`);
    }

    // Hue: audio value 0 = no shift, 0.5 = 180° shift, 1 = 360° shift
    if (m.hue !== undefined && m.hue !== 0) {
      filters.push(`hue-rotate(${m.hue * 360}deg)`);
    }

    // BUG-091: Blur - audio value 0 = no blur, 1 = 20px blur
    if (m.blur !== undefined && m.blur !== 0) {
      const blurPx = Math.max(0, m.blur * 20);  // Scale 0-1 to 0-20px
      filters.push(`blur(${blurPx}px)`);
    }

    // If no filters, return original
    if (filters.length === 0) {
      return canvas;
    }

    // Create new canvas with filters applied
    // Note: blur filter extends beyond canvas bounds, so we need padding
    const blurPadding = m.blur ? Math.ceil(m.blur * 20 * 2) : 0;
    const resultCanvas = document.createElement('canvas');
    resultCanvas.width = canvas.width + blurPadding * 2;
    resultCanvas.height = canvas.height + blurPadding * 2;
    const ctx = resultCanvas.getContext('2d');

    if (!ctx) {
      return canvas;
    }

    // Apply CSS filter and draw with padding offset
    ctx.filter = filters.join(' ');
    ctx.drawImage(canvas, blurPadding, blurPadding);

    // If blur was applied, we need to crop back to original size
    if (blurPadding > 0) {
      const croppedCanvas = document.createElement('canvas');
      croppedCanvas.width = canvas.width;
      croppedCanvas.height = canvas.height;
      const croppedCtx = croppedCanvas.getContext('2d');
      if (croppedCtx) {
        croppedCtx.drawImage(resultCanvas, -blurPadding, -blurPadding);
        return croppedCanvas;
      }
    }

    return resultCanvas;
  }

  /**
   * Get audio modifier values for effect parameters
   * Used by effect processing to apply audio-reactive glow intensity/radius
   */
  protected getEffectAudioModifiers(): { glowIntensity?: number; glowRadius?: number } {
    return {
      glowIntensity: this.currentAudioModifiers.glowIntensity,
      glowRadius: this.currentAudioModifiers.glowRadius,
    };
  }

  /**
   * Set layer styles
   */
  setLayerStyles(styles: LayerStyles | undefined): void {
    this.layerStyles = styles;
    this.effectsDirty = true;
  }

  /**
   * Set layer quality mode (draft = faster preview, best = full quality)
   */
  setQuality(quality: 'draft' | 'best'): void {
    this.quality = quality;
  }

  /**
   * Get layer quality mode
   */
  getQuality(): 'draft' | 'best' {
    return this.quality;
  }

  /**
   * Check if layer is in draft quality mode
   */
  isDraftQuality(): boolean {
    return this.quality === 'draft';
  }

  /**
   * Process layer styles and effects on a source canvas
   * Layer styles are applied BEFORE effects (matching Photoshop/AE behavior)
   * Subclasses that support effects should override getSourceCanvas()
   * @param frame - Current frame for animated effect parameters
   * @returns Processed canvas or null if no processing needed
   */
  protected processEffects(frame: number): HTMLCanvasElement | null {
    const hasStyles = this.layerStyles?.enabled && this.hasEnabledLayerStyles();
    const hasEffects = this.hasEnabledEffects();
    const hasColorMods = this.hasColorModifiers(); // BUG-090 fix

    if (!hasStyles && !hasEffects && !hasColorMods) {
      return null;
    }

    const sourceCanvas = this.getSourceCanvas();
    if (!sourceCanvas) {
      return null;
    }

    try {
      // Pass quality mode to effect processor
      // Draft mode uses faster, lower-quality effect rendering
      const qualityHint = this.isDraftQuality() ? 'draft' : 'high';

      // Build context for time-based effects (Echo, Posterize Time)
      // These effects need frame, fps, and layerId to access frame buffers
      const effectContext = {
        frame,
        fps: this.compositionFps,
        layerId: this.id
      };

      // STEP 1: Apply layer styles FIRST (before effects)
      // Layer styles include: drop shadow, stroke, glow, bevel/emboss, overlays
      let styledCanvas = sourceCanvas;
      if (hasStyles && this.layerStyles) {
        // Note: renderLayerStyles expects (canvas, styles, globalLight?)
        // Frame-based animation of layer styles should be handled by evaluating
        // animated properties before calling this function
        styledCanvas = renderLayerStyles(sourceCanvas, this.layerStyles);
      }

      // STEP 2: Apply effects on styled content
      // BUG-091/093 fix: Pass audio modifiers to effect processor for glow/glitch/rgbSplit
      let processedCanvas = styledCanvas;
      if (hasEffects) {
        const result = processEffectStack(
          this.effects,
          styledCanvas,
          frame,
          qualityHint,
          effectContext,
          this.compositionFps,
          this.currentAudioModifiers
        );
        processedCanvas = result.canvas;
      }

      // STEP 3: BUG-090 fix - Apply audio-reactive color adjustments
      if (hasColorMods) {
        processedCanvas = this.applyColorAdjustments(processedCanvas);
      }

      // Apply motion blur as final step if enabled
      if (this.motionBlur) {
        const currentTransform = this.getCurrentTransformValues();
        processedCanvas = this.applyMotionBlur(processedCanvas, frame, currentTransform);
      }

      return processedCanvas;
    } catch (error) {
      layerLogger.error(`Error processing effects for layer ${this.id}:`, error);
      return null;
    }
  }

  /**
   * Get current transform values for motion blur calculation
   * Uses evaluated values from the current frame
   */
  protected getCurrentTransformValues(): {
    position: { x: number; y: number; z: number };
    rotation: number;
    scale: { x: number; y: number };
  } {
    // Extract current values from the Three.js group (already evaluated)
    return {
      position: {
        x: this.group.position.x,
        y: -this.group.position.y, // Negate to convert back to screen coords
        z: this.group.position.z,
      },
      rotation: THREE.MathUtils.radToDeg(-this.group.rotation.z), // Convert back
      scale: {
        x: this.group.scale.x * 100,
        y: this.group.scale.y * 100,
      },
    };
  }

  /**
   * Get the source canvas for effect processing
   * Override in subclasses that support effects (ImageLayer, VideoLayer, TextLayer)
   * @returns Canvas with the layer's visual content, or null if not supported
   */
  protected getSourceCanvas(): HTMLCanvasElement | null {
    // Default: no source canvas (effects not supported)
    // Subclasses should override to provide their texture as a canvas
    return null;
  }

  /**
   * Apply processed effects back to the layer
   * Override in subclasses to update their texture from the processed canvas
   * @param processedCanvas - Canvas with effects applied
   */
  protected applyProcessedEffects(_processedCanvas: HTMLCanvasElement): void {
    // Default: no-op
    // Subclasses should override to update their material/texture
  }

  // ============================================================================
  // MOTION BLUR PROCESSING
  // ============================================================================

  /**
   * Check if motion blur should be applied
   */
  protected shouldApplyMotionBlur(): boolean {
    return this.motionBlur && this.getSourceCanvas() !== null;
  }

  /**
   * Initialize motion blur processor with layer dimensions
   */
  protected initializeMotionBlurProcessor(width: number, height: number): void {
    if (!this.motionBlurProcessor) {
      const settings = this.motionBlurSettings
        ? {
            enabled: true,
            type: this.motionBlurSettings.type,
            shutterAngle: this.motionBlurSettings.shutterAngle,
            shutterPhase: this.motionBlurSettings.shutterPhase,
            samplesPerFrame: this.motionBlurSettings.samplesPerFrame,
            direction: this.motionBlurSettings.direction,
            blurLength: this.motionBlurSettings.blurLength,
          }
        : { ...createDefaultMotionBlurSettings(), enabled: true };

      this.motionBlurProcessor = new MotionBlurProcessor(width, height, settings);
    } else if (
      this.motionBlurProcessor.getSettings().shutterAngle !==
      (this.motionBlurSettings?.shutterAngle ?? 180)
    ) {
      // Update settings if changed
      this.motionBlurProcessor.setSettings({
        shutterAngle: this.motionBlurSettings?.shutterAngle ?? 180,
        shutterPhase: this.motionBlurSettings?.shutterPhase ?? -90,
        samplesPerFrame: this.motionBlurSettings?.samplesPerFrame ?? 16,
      });
    }
  }

  /**
   * Calculate velocity from current and previous transforms
   */
  protected calculateTransformVelocity(currentTransform: {
    position: { x: number; y: number; z: number };
    rotation: number;
    scale: { x: number; y: number };
  }): VelocityData {
    if (!this.prevTransform) {
      return { x: 0, y: 0, rotation: 0, scale: 0 };
    }

    return {
      x: currentTransform.position.x - this.prevTransform.position.x,
      y: currentTransform.position.y - this.prevTransform.position.y,
      rotation: currentTransform.rotation - this.prevTransform.rotation,
      scale:
        ((currentTransform.scale.x - this.prevTransform.scale.x) +
         (currentTransform.scale.y - this.prevTransform.scale.y)) / 2,
    };
  }

  /**
   * Apply motion blur to a canvas based on transform velocity
   * @param sourceCanvas - Canvas to apply motion blur to
   * @param frame - Current frame number
   * @param currentTransform - Current transform values
   * @returns Canvas with motion blur applied, or source if no blur needed
   */
  protected applyMotionBlur(
    sourceCanvas: HTMLCanvasElement,
    frame: number,
    currentTransform: {
      position: { x: number; y: number; z: number };
      rotation: number;
      scale: { x: number; y: number };
    }
  ): HTMLCanvasElement {
    if (!this.motionBlur) {
      return sourceCanvas;
    }

    // Initialize processor if needed
    this.initializeMotionBlurProcessor(sourceCanvas.width, sourceCanvas.height);

    if (!this.motionBlurProcessor) {
      return sourceCanvas;
    }

    // Calculate velocity
    const velocity = this.calculateTransformVelocity(currentTransform);

    // Store current transform for next frame
    this.prevTransform = {
      position: { ...currentTransform.position },
      rotation: currentTransform.rotation,
      scale: { ...currentTransform.scale },
    };

    // Skip blur if velocity is negligible
    const velocityMagnitude = Math.sqrt(velocity.x * velocity.x + velocity.y * velocity.y);
    if (velocityMagnitude < 0.5 && Math.abs(velocity.rotation) < 0.5 && Math.abs(velocity.scale) < 0.01) {
      return sourceCanvas;
    }

    // Apply motion blur
    try {
      // Convert HTMLCanvasElement to OffscreenCanvas for the processor
      const offscreen = new OffscreenCanvas(sourceCanvas.width, sourceCanvas.height);
      const ctx = offscreen.getContext('2d');
      if (ctx) {
        ctx.drawImage(sourceCanvas, 0, 0);
        const blurredOffscreen = this.motionBlurProcessor.applyMotionBlur(offscreen, velocity, frame);

        // Convert back to HTMLCanvasElement
        const resultCanvas = document.createElement('canvas');
        resultCanvas.width = sourceCanvas.width;
        resultCanvas.height = sourceCanvas.height;
        const resultCtx = resultCanvas.getContext('2d');
        if (resultCtx) {
          resultCtx.drawImage(blurredOffscreen, 0, 0);
          return resultCanvas;
        }
      }
    } catch (error) {
      layerLogger.error(`Error applying motion blur to layer ${this.id}:`, error);
    }

    return sourceCanvas;
  }

  /**
   * Set motion blur enabled state
   */
  setMotionBlur(enabled: boolean): void {
    this.motionBlur = enabled;
    this.layerData.motionBlur = enabled;
    if (!enabled) {
      this.motionBlurProcessor?.clearBuffer();
      this.prevTransform = null;
    }
  }

  /**
   * Update motion blur settings
   */
  setMotionBlurSettings(settings: Partial<LayerMotionBlurSettings>): void {
    if (!this.motionBlurSettings) {
      this.motionBlurSettings = {
        type: 'standard',
        shutterAngle: 180,
        shutterPhase: -90,
        samplesPerFrame: 16,
        ...settings,
      };
    } else {
      Object.assign(this.motionBlurSettings, settings);
    }

    if (this.motionBlurProcessor) {
      this.motionBlurProcessor.setSettings({
        type: this.motionBlurSettings.type,
        shutterAngle: this.motionBlurSettings.shutterAngle,
        shutterPhase: this.motionBlurSettings.shutterPhase,
        samplesPerFrame: this.motionBlurSettings.samplesPerFrame,
      });
    }
  }

  // ============================================================================
  // MASK PROCESSING
  // ============================================================================

  /**
   * Check if this layer has any enabled masks
   */
  protected hasMasks(): boolean {
    return this.masks.length > 0 && this.masks.some(m => m.enabled);
  }

  /**
   * Check if this layer has a matte source assigned
   */
  protected hasMatte(): boolean {
    return this.matteType !== 'none' && this.matteCanvas !== null;
  }

  /** @deprecated Use hasMatte() instead */
  protected hasTrackMatte(): boolean {
    return this.hasMatte();
  }

  /**
   * Set the matte canvas (called by LayerManager when compositing)
   * @param canvas - The rendered canvas of the matte layer
   */
  setMatteCanvas(canvas: HTMLCanvasElement | null): void {
    this.matteCanvas = canvas;
  }

  /** @deprecated Use setMatteCanvas() instead */
  setTrackMatteCanvas(canvas: HTMLCanvasElement | null): void {
    this.setMatteCanvas(canvas);
  }

  /**
   * Get the matte layer ID
   */
  getMatteLayerId(): string | null {
    return this.matteLayerId;
  }

  /** @deprecated Use getMatteLayerId() instead */
  getTrackMatteLayerId(): string | null {
    return this.getMatteLayerId();
  }

  /**
   * Get the matte composition ID (for cross-comp mattes)
   * Returns null if matte is in the same composition
   */
  getMatteCompositionId(): string | null {
    return this.matteCompositionId;
  }

  /** @deprecated Use getMatteCompositionId() instead */
  getTrackMatteCompositionId(): string | null {
    return this.getMatteCompositionId();
  }

  /**
   * Check if this layer uses a cross-composition matte
   */
  hasCrossCompMatte(): boolean {
    return this.matteCompositionId !== null && this.matteLayerId !== null;
  }

  /**
   * Get the matte type
   */
  getMatteType(): MatteType {
    return this.matteType;
  }

  /** @deprecated Use getMatteType() instead */
  getTrackMatteType(): MatteType {
    return this.getMatteType();
  }

  /**
   * Update masks
   */
  setMasks(masks: LayerMask[]): void {
    this.masks = masks;
  }

  /**
   * Process masks and matte source on a canvas
   * @param canvas - Source canvas to apply masks to
   * @param frame - Current frame for animated masks
   * @returns Processed canvas with masks applied
   */
  protected processMasksAndMattes(canvas: HTMLCanvasElement, frame: number): HTMLCanvasElement {
    let result = canvas;

    // Apply layer masks (vector paths)
    if (this.hasMasks()) {
      result = applyMasksToLayer(result, this.masks, frame, this.compositionFps);
    }

    // Apply matte source (uses another layer's canvas)
    if (this.hasMatte() && this.matteCanvas) {
      result = applyTrackMatte(result, this.matteCanvas, this.matteType);
    }

    return result;
  }

  /**
   * Called after frame evaluation to apply effects AND masks
   * This should be called by subclasses after their content is rendered
   */
  protected evaluateEffects(frame: number): void {
    const hasEffects = this.hasEnabledEffects();
    const hasMasks = this.hasMasks();
    const hasTrackMatte = this.hasTrackMatte();
    const hasColorMods = this.hasColorModifiers(); // BUG-090 fix

    // Early exit if nothing to process
    if (!hasEffects && !hasMasks && !hasTrackMatte && !hasColorMods) {
      return;
    }

    // Get source canvas
    const sourceCanvas = this.getSourceCanvas();
    if (!sourceCanvas) {
      return;
    }

    let processedCanvas = sourceCanvas;

    // Step 1: Apply effects (includes color adjustments via processEffects)
    if (hasEffects || hasColorMods) {
      const effectResult = this.processEffects(frame);
      if (effectResult) {
        processedCanvas = effectResult;
      }
    }

    // Step 2: Apply masks and track mattes
    if (hasMasks || hasTrackMatte) {
      processedCanvas = this.processMasksAndMattes(processedCanvas, frame);
    }

    // Apply final result back to layer
    if (processedCanvas !== sourceCanvas) {
      this.applyProcessedEffects(processedCanvas);
    }
  }

  /**
   * Apply pre-evaluated effects from MotionEngine
   * Uses the evaluated effect parameters rather than re-evaluating
   */
  protected applyEvaluatedEffects(evaluatedEffects: readonly import('../MotionEngine').EvaluatedEffect[]): void {
    if (evaluatedEffects.length === 0 || !this.hasEnabledEffects()) {
      return;
    }

    // Process effects using the pre-evaluated parameters
    // The effects are already evaluated by MotionEngine, so we apply them directly
    const processedCanvas = this.processEffectsWithEvaluated(evaluatedEffects);
    if (processedCanvas) {
      this.applyProcessedEffects(processedCanvas);
    }
  }

  /**
   * Process effects using pre-evaluated parameters
   */
  protected processEffectsWithEvaluated(
    evaluatedEffects: readonly import('../MotionEngine').EvaluatedEffect[]
  ): HTMLCanvasElement | null {
    const sourceCanvas = this.getSourceCanvas();
    if (!sourceCanvas) {
      return null;
    }

    // Process effects in order using evaluated parameters
    let currentCanvas = sourceCanvas;
    for (const evalEffect of evaluatedEffects) {
      if (!evalEffect.enabled) continue;

      // Find matching effect instance
      const effect = this.effects.find(e => e.id === evalEffect.id);
      if (!effect) continue;

      // Apply effect with pre-evaluated parameters
      const result = this.processEffectWithParams(effect, currentCanvas, evalEffect.parameters);
      if (result) {
        currentCanvas = result;
      }
    }

    return currentCanvas !== sourceCanvas ? currentCanvas : null;
  }

  /**
   * Process a single effect with pre-evaluated parameters
   */
  protected processEffectWithParams(
    effect: EffectInstance,
    sourceCanvas: HTMLCanvasElement,
    params: Record<string, unknown>
  ): HTMLCanvasElement | null {
    // This would delegate to effect-specific processors
    // For now, mark canvas for re-processing with new params
    // The actual implementation would use the effect processor
    return null; // Subclasses can override for custom effect handling
  }

  // ============================================================================
  // PARENTING
  // ============================================================================

  /**
   * Set parent layer reference
   */
  setParent(parent: BaseLayer | null): void {
    // Remove from old parent's Three.js hierarchy
    if (this.parentLayer) {
      this.parentLayer.getObject().remove(this.group);
    }

    this.parentLayer = parent;

    // Add to new parent's Three.js hierarchy
    if (parent) {
      parent.getObject().add(this.group);
    }
  }

  /**
   * Get parent layer reference
   */
  getParent(): BaseLayer | null {
    return this.parentLayer;
  }

  /**
   * Get parent layer ID
   */
  getParentId(): string | null {
    return this.parentId;
  }

  /**
   * Check if this layer has a parent
   */
  hasParent(): boolean {
    return this.parentId !== null;
  }

  /**
   * Set composition FPS for time-based effects (Echo, Posterize Time, etc.)
   * Called by LayerManager when composition settings change.
   */
  setCompositionFps(fps: number): void {
    // Validate fps (NaN/0 causes division errors in time-based effects)
    this.compositionFps = (Number.isFinite(fps) && fps > 0) ? fps : 16;
  }

  // ============================================================================
  // BLEND MODES
  // ============================================================================

  /**
   * Apply blend mode to layer materials
   * Delegates to blendModeUtils for actual blend configuration
   */
  protected applyBlendMode(mode: string): void {
    applyBlendModeToGroup(this.group, mode);
  }

  // ============================================================================
  // MOTION PATH VISUALIZATION
  // ============================================================================

  /**
   * Compute motion path from position keyframes
   * Samples position at each frame from inPoint to outPoint
   */
  computeMotionPath(startFrame?: number, endFrame?: number): void {
    // Validate frame bounds (NaN/Infinity would cause infinite loop or no iterations)
    const rawStart = startFrame ?? this.inPoint;
    const rawEnd = endFrame ?? this.outPoint;
    const start = Number.isFinite(rawStart) ? Math.max(0, Math.floor(rawStart)) : 0;
    const end = Number.isFinite(rawEnd) ? Math.floor(rawEnd) : start;

    // Cap motion path length to prevent memory exhaustion (max 10,000 points)
    const MAX_PATH_POINTS = 10000;
    const cappedEnd = Math.min(end, start + MAX_PATH_POINTS);

    this.motionPathPoints = [];

    // Sample position at each frame
    for (let frame = start; frame <= cappedEnd; frame++) {
      const pos = this.evaluator.evaluate(this.transform.position, frame);
      // Convert to Three.js coordinates (Y is flipped)
      // Validate position values to prevent NaN in Three.js
      const validX = Number.isFinite(pos.x) ? pos.x : 0;
      const validY = Number.isFinite(pos.y) ? pos.y : 0;
      const validZ = Number.isFinite(pos.z) ? pos.z : 0;
      this.motionPathPoints.push(new THREE.Vector3(validX, -validY, validZ));
    }

    // Rebuild the path visualization
    this.rebuildMotionPath();
  }

  /**
   * Rebuild the motion path line from computed points
   */
  private rebuildMotionPath(): void {
    // Dispose existing path
    if (this.motionPath) {
      this.group.remove(this.motionPath);
      this.motionPath.geometry.dispose();
      (this.motionPath.material as THREE.Material).dispose();
      this.motionPath = null;
    }

    // Dispose existing markers
    if (this.motionPathMarkers) {
      this.group.remove(this.motionPathMarkers);
      this.motionPathMarkers.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.motionPathMarkers = null;
    }

    if (this.motionPathPoints.length < 2) return;

    // Create smooth curve through points
    const curve = new THREE.CatmullRomCurve3(this.motionPathPoints);
    const curvePoints = curve.getPoints(this.motionPathPoints.length * 10);

    // Create line geometry
    const geometry = new THREE.BufferGeometry().setFromPoints(curvePoints);
    const material = new THREE.LineBasicMaterial({
      color: 0x4a90d9,  // Blue motion path
      linewidth: 2,
      transparent: true,
      opacity: 0.8,
      depthTest: false,
    });

    this.motionPath = new THREE.Line(geometry, material);
    this.motionPath.name = `motion_path_${this.id}`;
    this.motionPath.renderOrder = 998;
    this.motionPath.visible = this.showMotionPath;

    // Don't add to group - add to parent so it doesn't move with layer
    // Instead, position at world origin
    this.motionPath.matrixAutoUpdate = false;
    this.motionPath.matrix.identity();

    this.group.add(this.motionPath);

    // Create keyframe markers
    this.createMotionPathMarkers();
  }

  /**
   * Create markers at keyframe positions on the motion path
   */
  private createMotionPathMarkers(): void {
    this.motionPathMarkers = new THREE.Group();
    this.motionPathMarkers.name = `motion_path_markers_${this.id}`;
    this.motionPathMarkers.renderOrder = 999;

    const positionKeyframes = this.transform.position.keyframes;
    if (!positionKeyframes || positionKeyframes.length === 0) return;

    // Create a small diamond shape for each keyframe
    const markerGeometry = new THREE.OctahedronGeometry(5, 0);
    const markerMaterial = new THREE.MeshBasicMaterial({
      color: 0xffcc00,  // Yellow keyframe markers
      transparent: true,
      opacity: 0.9,
      depthTest: false,
    });

    for (const kf of positionKeyframes) {
      const pos = kf.value;
      const marker = new THREE.Mesh(markerGeometry.clone(), markerMaterial.clone());
      marker.position.set(pos.x, -pos.y, pos.z ?? 0);
      marker.userData.frame = kf.frame;
      this.motionPathMarkers.add(marker);
    }

    this.motionPathMarkers.visible = this.showMotionPath;
    this.group.add(this.motionPathMarkers);
  }

  /**
   * Set motion path visibility
   */
  setMotionPathVisible(visible: boolean): void {
    this.showMotionPath = visible;

    if (visible && this.motionPathPoints.length === 0) {
      // Compute path on first show
      this.computeMotionPath();
    }

    if (this.motionPath) {
      this.motionPath.visible = visible;
    }
    if (this.motionPathMarkers) {
      this.motionPathMarkers.visible = visible;
    }
  }

  /**
   * Check if motion path is visible
   */
  isMotionPathVisible(): boolean {
    return this.showMotionPath;
  }

  /**
   * Check if layer has position animation
   */
  hasPositionAnimation(): boolean {
    return (this.transform.position.keyframes?.length ?? 0) > 0;
  }

  // ============================================================================
  // 3D AXIS GIZMO
  // ============================================================================

  /**
   * Create 3D axis gizmo at anchor point
   */
  createAxisGizmo(size: number = 50): void {
    // Dispose existing gizmo
    if (this.axisGizmo) {
      this.group.remove(this.axisGizmo);
      this.axisGizmo.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.axisGizmo = null;
    }

    this.axisGizmo = new THREE.Group();
    this.axisGizmo.name = `axis_gizmo_${this.id}`;
    this.axisGizmo.renderOrder = 1000;

    // X axis (Red)
    const xGeom = new THREE.BufferGeometry().setFromPoints([
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(size, 0, 0),
    ]);
    const xMat = new THREE.LineBasicMaterial({
      color: 0xff0000,
      linewidth: 2,
      depthTest: false,
    });
    const xLine = new THREE.Line(xGeom, xMat);
    this.axisGizmo.add(xLine);

    // Y axis (Green)
    const yGeom = new THREE.BufferGeometry().setFromPoints([
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(0, size, 0),
    ]);
    const yMat = new THREE.LineBasicMaterial({
      color: 0x00ff00,
      linewidth: 2,
      depthTest: false,
    });
    const yLine = new THREE.Line(yGeom, yMat);
    this.axisGizmo.add(yLine);

    // Z axis (Blue) - only for 3D layers
    if (this.threeD) {
      const zGeom = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(0, 0, 0),
        new THREE.Vector3(0, 0, size),
      ]);
      const zMat = new THREE.LineBasicMaterial({
        color: 0x0088ff,
        linewidth: 2,
        depthTest: false,
      });
      const zLine = new THREE.Line(zGeom, zMat);
      this.axisGizmo.add(zLine);
    }

    // Add axis labels
    this.addAxisLabels(size);

    // Position at origin (formerly anchor point)
    const originProp = this.transform.origin || this.transform.anchorPoint;
    const originVal = originProp?.value || { x: 0, y: 0, z: 0 };
    this.axisGizmo.position.set(-originVal.x, originVal.y, -(originVal.z ?? 0));

    this.axisGizmo.visible = this.showAxisGizmo;
    this.group.add(this.axisGizmo);
  }

  /**
   * Add axis labels (X, Y, Z)
   */
  private addAxisLabels(size: number): void {
    if (!this.axisGizmo) return;

    // Create small spheres at axis ends as labels
    const sphereGeom = new THREE.SphereGeometry(3, 8, 8);

    // X label (red sphere)
    const xSphere = new THREE.Mesh(
      sphereGeom.clone(),
      new THREE.MeshBasicMaterial({ color: 0xff0000, depthTest: false })
    );
    xSphere.position.set(size + 5, 0, 0);
    this.axisGizmo.add(xSphere);

    // Y label (green sphere)
    const ySphere = new THREE.Mesh(
      sphereGeom.clone(),
      new THREE.MeshBasicMaterial({ color: 0x00ff00, depthTest: false })
    );
    ySphere.position.set(0, size + 5, 0);
    this.axisGizmo.add(ySphere);

    // Z label (blue sphere) - only for 3D layers
    if (this.threeD) {
      const zSphere = new THREE.Mesh(
        sphereGeom.clone(),
        new THREE.MeshBasicMaterial({ color: 0x0088ff, depthTest: false })
      );
      zSphere.position.set(0, 0, size + 5);
      this.axisGizmo.add(zSphere);
    }
  }

  /**
   * Set axis gizmo visibility
   */
  setAxisGizmoVisible(visible: boolean): void {
    this.showAxisGizmo = visible;

    if (visible && !this.axisGizmo) {
      this.createAxisGizmo();
    }

    if (this.axisGizmo) {
      this.axisGizmo.visible = visible;
    }
  }

  /**
   * Check if axis gizmo is visible
   */
  isAxisGizmoVisible(): boolean {
    return this.showAxisGizmo;
  }

  /**
   * Update axis gizmo position to match origin
   */
  updateAxisGizmoPosition(): void {
    if (!this.axisGizmo) return;

    const originProp = this.transform.origin || this.transform.anchorPoint;
    const originVal = originProp?.value || { x: 0, y: 0, z: 0 };
    this.axisGizmo.position.set(-originVal.x, originVal.y, -(originVal.z ?? 0));
  }

  // ============================================================================
  // BOUNDS
  // ============================================================================

  /**
   * Get the bounding box of this layer
   */
  getBoundingBox(): THREE.Box3 {
    const box = new THREE.Box3();
    box.setFromObject(this.group);
    return box;
  }

  /**
   * Get the center point of this layer
   */
  getCenter(): THREE.Vector3 {
    const box = this.getBoundingBox();
    const center = new THREE.Vector3();
    box.getCenter(center);
    return center;
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Dispose layer resources
   */
  dispose(): void {
    // Dispose motion path
    if (this.motionPath) {
      this.motionPath.geometry.dispose();
      (this.motionPath.material as THREE.Material).dispose();
      this.motionPath = null;
    }

    // Dispose motion path markers
    if (this.motionPathMarkers) {
      this.motionPathMarkers.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.motionPathMarkers = null;
    }

    // Dispose axis gizmo
    if (this.axisGizmo) {
      this.axisGizmo.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.axisGizmo = null;
    }

    // Dispose all meshes in the group
    this.group.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        child.geometry?.dispose();

        if (Array.isArray(child.material)) {
          child.material.forEach(m => m.dispose());
        } else if (child.material) {
          child.material.dispose();
        }
      }
    });

    // Clear group
    this.group.clear();

    // Call subclass-specific disposal
    this.onDispose();
  }

  /**
   * Override in subclasses for type-specific cleanup
   */
  protected onDispose(): void {
    // Default: no additional cleanup
  }
}
