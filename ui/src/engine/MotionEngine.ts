/**
 * MotionEngine - Single Source of Truth for Time-Based Evaluation
 *
 * ARCHITECTURAL CONTRACT:
 * ========================
 * This module is the SOLE AUTHORITY for answering:
 * "What is the complete evaluated state at frame N?"
 *
 * AXIOMS ENFORCED:
 * 1. Time is immutable input, never accumulated state
 * 2. Frame evaluation must be order-independent
 * 3. evaluate(frame) MUST NOT mutate any external state
 * 4. All returned values are snapshots, not live references
 *
 * PURE DEPENDENCIES ONLY:
 * - interpolation.ts (keyframe evaluation)
 * - audioFeatures.ts (pre-computed audio lookup)
 *
 * DO NOT:
 * - Import stores
 * - Import renderers
 * - Accumulate state between calls
 * - Use Math.random() without seed
 * - Reference requestAnimationFrame
 */

import type {
  WeylProject,
  Composition,
  Layer,
  LayerTransform,
  AnimatableProperty,
  CompositionSettings,
  CameraLayerData,
  EffectInstance,
} from '@/types/project';
import type { AudioAnalysis } from '@/services/audioFeatures';
import { interpolateProperty } from '@/services/interpolation';
import { getFeatureAtFrame } from '@/services/audioFeatures';

// ============================================================================
// EVALUATED STATE INTERFACES
// These are immutable snapshots returned by evaluate()
// ============================================================================

/**
 * Complete evaluated state for a single frame
 * This is the output of MotionEngine.evaluate()
 *
 * DETERMINISM: This interface contains ONLY deterministic values.
 * Same frame + same project = byte-identical FrameState.
 * No timestamps, no random values, no order-dependent state.
 */
export interface FrameState {
  /** The frame number this state represents */
  readonly frame: number;

  /** Composition settings (immutable reference) */
  readonly composition: CompositionSettings;

  /** Evaluated state for all visible layers */
  readonly layers: readonly EvaluatedLayer[];

  /** Evaluated camera state (null if no camera layer active) */
  readonly camera: EvaluatedCamera | null;

  /** Audio feature values at this frame (empty if no audio) */
  readonly audio: EvaluatedAudio;
}

/**
 * Evaluated state for a single layer at a specific frame
 *
 * ARCHITECTURAL RULE:
 * This interface contains ALL evaluated values a layer needs.
 * Layers must ONLY accept these pre-evaluated values.
 * Layers must NEVER call interpolateProperty() or sample time internally.
 */
export interface EvaluatedLayer {
  /** Layer ID (immutable reference) */
  readonly id: string;

  /** Layer type */
  readonly type: string;

  /** Layer name */
  readonly name: string;

  /** Whether this layer is visible at this frame */
  readonly visible: boolean;

  /** Whether layer is within in/out points */
  readonly inRange: boolean;

  /** Evaluated opacity (0-100) */
  readonly opacity: number;

  /** Evaluated transform values */
  readonly transform: EvaluatedTransform;

  /** Evaluated effect parameters */
  readonly effects: readonly EvaluatedEffect[];

  /** Layer-specific evaluated properties (type-safe) */
  readonly properties: Readonly<Record<string, unknown>>;

  /** Parent layer ID for hierarchy */
  readonly parentId: string | null;

  /** Blend mode */
  readonly blendMode: string;

  /** 3D layer flag */
  readonly threeD: boolean;

  /** Reference to original layer data (for static data only - NOT for evaluation) */
  readonly layerRef: Layer;
}

/**
 * Evaluated transform at a specific frame
 */
export interface EvaluatedTransform {
  readonly position: Readonly<{ x: number; y: number; z?: number }>;
  readonly anchorPoint: Readonly<{ x: number; y: number; z?: number }>;
  readonly scale: Readonly<{ x: number; y: number; z?: number }>;
  readonly rotation: number;
  readonly rotationX?: number;
  readonly rotationY?: number;
  readonly rotationZ?: number;
}

/**
 * Evaluated camera state at a specific frame
 */
export interface EvaluatedCamera {
  /** Camera layer ID */
  readonly id: string;

  /** Camera name */
  readonly name: string;

  /** Evaluated position */
  readonly position: Readonly<{ x: number; y: number; z: number }>;

  /** Evaluated target/look-at point */
  readonly target: Readonly<{ x: number; y: number; z: number }>;

  /** Evaluated field of view */
  readonly fov: number;

  /** Evaluated focal length */
  readonly focalLength: number;

  /** Depth of field settings */
  readonly depthOfField: {
    readonly enabled: boolean;
    readonly focusDistance: number;
    readonly aperture: number;
    readonly blurLevel: number;
  };
}

/**
 * Evaluated effect with all parameters resolved
 */
export interface EvaluatedEffect {
  readonly id: string;
  readonly type: string;
  readonly enabled: boolean;
  readonly parameters: Readonly<Record<string, unknown>>;
}

/**
 * Evaluated audio features at a specific frame
 */
export interface EvaluatedAudio {
  /** Whether audio analysis data is available */
  readonly hasAudio: boolean;

  /** Common audio features (0-1 normalized) */
  readonly amplitude: number;
  readonly rms: number;
  readonly bass: number;
  readonly mid: number;
  readonly high: number;
  readonly spectralCentroid: number;

  /** Beat detection */
  readonly isBeat: boolean;
  readonly isOnset: boolean;

  /** BPM if detected */
  readonly bpm: number;
}

/**
 * Evaluated property value with metadata
 */
export interface EvaluatedProperty<T = unknown> {
  readonly name: string;
  readonly value: T;
  readonly animated: boolean;
  readonly atKeyframe: boolean;
}

// ============================================================================
// MOTION ENGINE IMPLEMENTATION
// ============================================================================

/**
 * MotionEngine - Stateless frame evaluator
 *
 * USAGE:
 * ```typescript
 * const engine = new MotionEngine();
 * const state = engine.evaluate(frame, project, audioAnalysis);
 * renderer.render(state);
 * ```
 */
export class MotionEngine {
  /**
   * Internal state: NONE
   * This class is intentionally stateless between evaluate() calls
   */

  /**
   * Evaluate complete frame state
   *
   * PURE FUNCTION: Same inputs always produce same outputs
   * NO SIDE EFFECTS: Does not mutate project, layers, or any external state
   *
   * @param frame - Absolute frame number (0-indexed)
   * @param project - The project data (read-only)
   * @param audioAnalysis - Pre-computed audio analysis (optional)
   * @param activeCameraId - ID of active camera layer (optional)
   * @returns Immutable FrameState snapshot
   */
  evaluate(
    frame: number,
    project: WeylProject,
    audioAnalysis?: AudioAnalysis | null,
    activeCameraId?: string | null
  ): FrameState {
    // DETERMINISM: No timestamps or non-deterministic values in output

    // Get active composition
    const composition = project.compositions[project.mainCompositionId];
    if (!composition) {
      return this.createEmptyFrameState(frame, project.composition);
    }

    // Evaluate all layers
    const evaluatedLayers = this.evaluateLayers(frame, composition.layers);

    // Evaluate camera
    const evaluatedCamera = this.evaluateCamera(
      frame,
      composition.layers,
      activeCameraId ?? null
    );

    // Evaluate audio
    const evaluatedAudio = this.evaluateAudio(frame, audioAnalysis ?? null);

    return Object.freeze({
      frame,
      composition: composition.settings,
      layers: Object.freeze(evaluatedLayers),
      camera: evaluatedCamera,
      audio: evaluatedAudio,
    });
  }

  /**
   * Evaluate a single property at a given frame
   * Utility method for UI components that need individual values
   */
  evaluateProperty<T>(property: AnimatableProperty<T>, frame: number): T {
    return interpolateProperty(property, frame);
  }

  /**
   * Check if a layer is visible at a given frame
   */
  isLayerVisibleAtFrame(layer: Layer, frame: number): boolean {
    return layer.visible && frame >= layer.inPoint && frame <= layer.outPoint;
  }

  // ============================================================================
  // PRIVATE EVALUATION METHODS
  // ============================================================================

  private evaluateLayers(frame: number, layers: Layer[]): EvaluatedLayer[] {
    const evaluated: EvaluatedLayer[] = [];

    for (const layer of layers) {
      const inRange = frame >= layer.inPoint && frame <= layer.outPoint;
      const visible = layer.visible && inRange;

      // Evaluate transform
      const transform = this.evaluateTransform(frame, layer.transform, layer.threeD);

      // Evaluate opacity
      const opacity = interpolateProperty(layer.opacity, frame);

      // Evaluate effects
      const effects = this.evaluateEffects(frame, layer.effects);

      // Evaluate layer-specific properties
      const properties = this.evaluateLayerProperties(frame, layer);

      evaluated.push(Object.freeze({
        id: layer.id,
        type: layer.type,
        name: layer.name,
        visible,
        inRange,
        opacity,
        transform: Object.freeze(transform),
        effects: Object.freeze(effects),
        properties: Object.freeze(properties),
        parentId: layer.parentId,
        blendMode: layer.blendMode,
        threeD: layer.threeD,
        layerRef: layer, // Reference for static data only - NOT for evaluation
      }));
    }

    return evaluated;
  }

  private evaluateTransform(
    frame: number,
    transform: LayerTransform,
    is3D: boolean
  ): EvaluatedTransform {
    const position = interpolateProperty(transform.position, frame);
    const anchorPoint = interpolateProperty(transform.anchorPoint, frame);
    const scale = interpolateProperty(transform.scale, frame);
    const rotation = interpolateProperty(transform.rotation, frame);

    const result: EvaluatedTransform = {
      position: { ...position },
      anchorPoint: { ...anchorPoint },
      scale: { ...scale },
      rotation,
    };

    // Add 3D rotations if layer is 3D
    if (is3D) {
      return {
        ...result,
        rotationX: transform.rotationX
          ? interpolateProperty(transform.rotationX, frame)
          : 0,
        rotationY: transform.rotationY
          ? interpolateProperty(transform.rotationY, frame)
          : 0,
        rotationZ: transform.rotationZ
          ? interpolateProperty(transform.rotationZ, frame)
          : rotation,
      };
    }

    return result;
  }

  private evaluateEffects(
    frame: number,
    effects: EffectInstance[]
  ): EvaluatedEffect[] {
    return effects.map((effect) => {
      const evaluatedParams: Record<string, unknown> = {};

      // Evaluate each parameter
      for (const [key, param] of Object.entries(effect.parameters)) {
        if (this.isAnimatableProperty(param)) {
          evaluatedParams[key] = interpolateProperty(param, frame);
        } else {
          evaluatedParams[key] = param;
        }
      }

      return Object.freeze({
        id: effect.id,
        type: effect.effectKey,  // Use effectKey as the effect type identifier
        enabled: effect.enabled,
        parameters: Object.freeze(evaluatedParams),
      });
    });
  }

  private evaluateLayerProperties(
    frame: number,
    layer: Layer
  ): Record<string, unknown> {
    const evaluated: Record<string, unknown> = {};

    // Evaluate properties array
    for (const prop of layer.properties) {
      evaluated[prop.name] = interpolateProperty(prop, frame);
    }

    // Type-specific evaluation
    switch (layer.type) {
      case 'text':
        if (layer.data && 'fontSize' in layer.data) {
          // Text layers may have additional animatable properties
          // stored in data - handle them here if needed
        }
        break;

      case 'solid':
        // Solid color might be animatable
        break;

      case 'depthflow':
        if (layer.data && 'animatedZoom' in layer.data) {
          const data = layer.data;
          if (data.animatedZoom) {
            evaluated['zoom'] = interpolateProperty(data.animatedZoom, frame);
          }
          if (data.animatedOffsetX) {
            evaluated['offsetX'] = interpolateProperty(data.animatedOffsetX, frame);
          }
          if (data.animatedOffsetY) {
            evaluated['offsetY'] = interpolateProperty(data.animatedOffsetY, frame);
          }
          if (data.animatedRotation) {
            evaluated['rotation'] = interpolateProperty(data.animatedRotation, frame);
          }
        }
        break;

      // NOTE: Particle layers are NOT evaluated here
      // They require special handling via ParticleSimulationController
      // to maintain scrub-determinism
      case 'particles':
        evaluated['_requiresSimulation'] = true;
        break;
    }

    return evaluated;
  }

  private evaluateCamera(
    frame: number,
    layers: Layer[],
    activeCameraId: string | null
  ): EvaluatedCamera | null {
    // Find active camera layer
    let cameraLayer: Layer | undefined;

    if (activeCameraId) {
      cameraLayer = layers.find(
        (l) => l.id === activeCameraId && l.type === 'camera'
      );
    }

    // If no active camera specified, find first visible camera
    if (!cameraLayer) {
      cameraLayer = layers.find(
        (l) =>
          l.type === 'camera' &&
          l.visible &&
          frame >= l.inPoint &&
          frame <= l.outPoint
      );
    }

    if (!cameraLayer || !cameraLayer.data) {
      return null;
    }

    const cameraData = cameraLayer.data as CameraLayerData;

    // Evaluate camera transform
    const transform = this.evaluateTransform(frame, cameraLayer.transform, true);

    // Default camera values
    let position = { x: transform.position.x, y: transform.position.y, z: 0 };
    let target = { x: 0, y: 0, z: 0 };
    let fov = 50;
    let focalLength = 50;

    // Evaluate animated camera properties if they exist
    if (cameraData.animatedPosition) {
      const pos = interpolateProperty(cameraData.animatedPosition, frame);
      position = { x: pos.x, y: pos.y, z: pos.z ?? 0 };
    }

    if (cameraData.animatedTarget) {
      const tgt = interpolateProperty(cameraData.animatedTarget, frame);
      target = { x: tgt.x, y: tgt.y, z: tgt.z ?? 0 };
    }

    if (cameraData.animatedFov) {
      fov = interpolateProperty(cameraData.animatedFov, frame);
    }

    if (cameraData.animatedFocalLength) {
      focalLength = interpolateProperty(cameraData.animatedFocalLength, frame);
    }

    // Evaluate depth of field
    let focusDistance = cameraData.depthOfField?.focusDistance ?? 1000;
    let aperture = cameraData.depthOfField?.aperture ?? 2.8;
    let blurLevel = cameraData.depthOfField?.blurLevel ?? 50;

    if (cameraData.animatedFocusDistance) {
      focusDistance = interpolateProperty(cameraData.animatedFocusDistance, frame);
    }
    if (cameraData.animatedAperture) {
      aperture = interpolateProperty(cameraData.animatedAperture, frame);
    }
    if (cameraData.animatedBlurLevel) {
      blurLevel = interpolateProperty(cameraData.animatedBlurLevel, frame);
    }

    return Object.freeze({
      id: cameraLayer.id,
      name: cameraLayer.name,
      position: Object.freeze(position),
      target: Object.freeze(target),
      fov,
      focalLength,
      depthOfField: Object.freeze({
        enabled: cameraData.depthOfField?.enabled ?? false,
        focusDistance,
        aperture,
        blurLevel,
      }),
    });
  }

  private evaluateAudio(
    frame: number,
    analysis: AudioAnalysis | null
  ): EvaluatedAudio {
    if (!analysis) {
      return Object.freeze({
        hasAudio: false,
        amplitude: 0,
        rms: 0,
        bass: 0,
        mid: 0,
        high: 0,
        spectralCentroid: 0,
        isBeat: false,
        isOnset: false,
        bpm: 0,
      });
    }

    return Object.freeze({
      hasAudio: true,
      amplitude: getFeatureAtFrame(analysis, 'amplitude', frame),
      rms: getFeatureAtFrame(analysis, 'rms', frame),
      bass: getFeatureAtFrame(analysis, 'bass', frame),
      mid: getFeatureAtFrame(analysis, 'mid', frame),
      high: getFeatureAtFrame(analysis, 'high', frame),
      spectralCentroid: getFeatureAtFrame(analysis, 'spectralCentroid', frame),
      isBeat: getFeatureAtFrame(analysis, 'onsets', frame) > 0.5,
      isOnset: getFeatureAtFrame(analysis, 'onsets', frame) > 0,
      bpm: analysis.bpm,
    });
  }

  /**
   * Create empty frame state for missing compositions
   * DETERMINISM: No timestamps or non-deterministic values
   */
  private createEmptyFrameState(
    frame: number,
    settings: CompositionSettings
  ): FrameState {
    return Object.freeze({
      frame,
      composition: settings,
      layers: Object.freeze([]),
      camera: null,
      audio: Object.freeze({
        hasAudio: false,
        amplitude: 0,
        rms: 0,
        bass: 0,
        mid: 0,
        high: 0,
        spectralCentroid: 0,
        isBeat: false,
        isOnset: false,
        bpm: 0,
      }),
    });
  }

  /**
   * Type guard to check if a value is an AnimatableProperty
   */
  private isAnimatableProperty(value: unknown): value is AnimatableProperty<unknown> {
    return (
      typeof value === 'object' &&
      value !== null &&
      'value' in value &&
      'keyframes' in value &&
      Array.isArray((value as AnimatableProperty<unknown>).keyframes)
    );
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

/**
 * Global MotionEngine instance
 * Since the engine is stateless, a single instance can be shared
 */
export const motionEngine = new MotionEngine();

// ============================================================================
// EXPORTS
// ============================================================================

export default MotionEngine;
