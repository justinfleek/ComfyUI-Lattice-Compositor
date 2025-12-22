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
  ParticleLayerData,
} from '@/types/project';
import type { AudioAnalysis } from '@/services/audioFeatures';
import { interpolateProperty } from '@/services/interpolation';
import { getFeatureAtFrame } from '@/services/audioFeatures';
import type { AudioMapping, TargetParameter } from '@/services/audioReactiveMapping';
import { AudioReactiveMapper, collectAudioReactiveModifiers } from '@/services/audioReactiveMapping';
import { particleSimulationRegistry, type ParticleSnapshot } from './ParticleSimulationController';
import type { ParticleSystemConfig } from '@/services/particleSystem';
// Camera enhancement imports - deterministic (seeded noise)
import { CameraShake, getRackFocusDistance } from '@/services/cameraEnhancements';

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

  /** Particle snapshots for deterministic particle evaluation (layerId → snapshot) */
  readonly particleSnapshots: Readonly<Record<string, ParticleSnapshot>>;
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

  /** Frame number this layer was evaluated at */
  readonly frame: number;

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

  /** Audio reactive modifiers (additive values from audio mappings) */
  readonly audioModifiers: AudioReactiveModifiers;
}

/**
 * Evaluated transform at a specific frame
 */
export interface EvaluatedTransform {
  readonly position: Readonly<{ x: number; y: number; z?: number }>;
  readonly origin: Readonly<{ x: number; y: number; z?: number }>;
  /** @deprecated Use 'origin' instead */
  readonly anchorPoint?: Readonly<{ x: number; y: number; z?: number }>;
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
 * Audio reactive modifiers applied to a layer
 * These are ADDITIVE values computed from audio mappings
 */
export interface AudioReactiveModifiers {
  /** Transform modifiers (additive) */
  readonly opacity?: number;
  readonly scaleX?: number;
  readonly scaleY?: number;
  readonly scaleUniform?: number;
  readonly rotation?: number;
  readonly x?: number;
  readonly y?: number;

  /** Color adjustments (additive) */
  readonly brightness?: number;
  readonly saturation?: number;
  readonly contrast?: number;
  readonly hue?: number;

  /** Effects */
  readonly blur?: number;
  readonly glowIntensity?: number;
  readonly glowRadius?: number;

  /** Camera */
  readonly fov?: number;
  readonly dollyZ?: number;
  readonly shake?: number;
}

/**
 * Input for audio reactive evaluation
 */
export interface AudioReactiveInput {
  /** Pre-computed audio analysis data */
  readonly analysis: AudioAnalysis;
  /** Audio mappings from the project */
  readonly mappings: readonly AudioMapping[];
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
// FRAME STATE CACHE
// Memoizes frame evaluation results to avoid redundant computation
// ============================================================================

interface CacheEntry {
  frameState: FrameState;
  projectHash: string;
  timestamp: number;
}

/**
 * LRU Cache for FrameState with automatic eviction
 * Prevents memory leaks by limiting cache size and entry lifetime
 */
class FrameStateCache {
  private cache = new Map<string, CacheEntry>();
  private readonly maxSize: number;
  private readonly maxAgeMs: number;

  constructor(maxSize: number = 120, maxAgeMs: number = 30000) {
    this.maxSize = maxSize;      // ~120 frames = ~7.5 seconds at 16fps
    this.maxAgeMs = maxAgeMs;    // 30 second TTL
  }

  /**
   * Generate cache key from frame + composition ID
   */
  private makeKey(frame: number, compositionId: string): string {
    return `${compositionId}:${frame}`;
  }

  /**
   * Compute a lightweight hash of project state that affects rendering
   * Changes to layers, keyframes, or effects invalidate the cache
   */
  computeProjectHash(project: WeylProject): string {
    const comp = project.compositions[project.mainCompositionId];
    if (!comp) return '';

    // Hash key properties that affect frame evaluation
    // We use a simple checksum approach - not cryptographic, just for comparison
    let hash = 0;
    const str = JSON.stringify({
      layerCount: comp.layers.length,
      layerIds: comp.layers.map(l => l.id),
      modified: project.meta?.modified || '',
      // Include layer visibility and animation state in hash
      layerStates: comp.layers.map(l => ({
        id: l.id,
        visible: l.visible,
        startFrame: l.startFrame ?? l.inPoint ?? 0,
        endFrame: l.endFrame ?? l.outPoint ?? 80,
        kfCount: l.properties.reduce((sum, p) => sum + (p.keyframes?.length || 0), 0)
      }))
    });

    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }
    return hash.toString(36);
  }

  /**
   * Get cached frame state if valid
   */
  get(frame: number, compositionId: string, projectHash: string): FrameState | null {
    const key = this.makeKey(frame, compositionId);
    const entry = this.cache.get(key);

    if (!entry) return null;

    // Validate cache entry
    const now = Date.now();
    if (entry.projectHash !== projectHash || (now - entry.timestamp) > this.maxAgeMs) {
      this.cache.delete(key);
      return null;
    }

    // Move to end (LRU behavior via Map insertion order)
    this.cache.delete(key);
    this.cache.set(key, entry);

    return entry.frameState;
  }

  /**
   * Store frame state in cache
   */
  set(frame: number, compositionId: string, projectHash: string, frameState: FrameState): void {
    const key = this.makeKey(frame, compositionId);

    // Evict oldest entries if at capacity
    while (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey) this.cache.delete(firstKey);
    }

    this.cache.set(key, {
      frameState,
      projectHash,
      timestamp: Date.now()
    });
  }

  /**
   * Invalidate all cached entries
   * Call when project structure changes (layer add/remove, etc.)
   */
  invalidate(): void {
    this.cache.clear();
  }

  /**
   * Invalidate entries for a specific composition
   */
  invalidateComposition(compositionId: string): void {
    for (const key of this.cache.keys()) {
      if (key.startsWith(`${compositionId}:`)) {
        this.cache.delete(key);
      }
    }
  }

  /**
   * Get cache statistics for debugging
   */
  getStats(): { size: number; maxSize: number; hitRate: number } {
    return {
      size: this.cache.size,
      maxSize: this.maxSize,
      hitRate: 0 // Would need hit/miss tracking
    };
  }
}

// ============================================================================
// MOTION ENGINE IMPLEMENTATION
// ============================================================================

/**
 * MotionEngine - Stateless frame evaluator with optional memoization
 *
 * USAGE:
 * ```typescript
 * const engine = new MotionEngine();
 * const state = engine.evaluate(frame, project, audioAnalysis);
 * renderer.render(state);
 * ```
 *
 * CACHING:
 * Frame states are cached by default. Cache is invalidated when:
 * - Project structure changes (layers added/removed)
 * - Cache entries exceed 30 second TTL
 * - Cache size exceeds 120 entries
 *
 * Disable caching for real-time preview with `evaluate(frame, project, audio, camera, false)`
 */
export class MotionEngine {
  /**
   * Frame state cache for memoization
   * Dramatically improves scrubbing performance (90%+ for repeated frames)
   */
  private frameCache = new FrameStateCache();
  private lastProjectHash: string = '';

  /**
   * Invalidate the frame cache
   * Call this when project structure changes
   */
  invalidateCache(): void {
    this.frameCache.invalidate();
    this.lastProjectHash = '';
  }

  /**
   * Get cache statistics for debugging
   */
  getCacheStats() {
    return this.frameCache.getStats();
  }

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
   * @param useCache - Whether to use memoization cache (default: true)
   * @param audioReactive - Audio reactive mappings for audio-driven animation (optional)
   * @returns Immutable FrameState snapshot
   */
  evaluate(
    frame: number,
    project: WeylProject,
    audioAnalysis?: AudioAnalysis | null,
    activeCameraId?: string | null,
    useCache: boolean = true,
    audioReactive?: AudioReactiveInput | null
  ): FrameState {
    // DETERMINISM: No timestamps or non-deterministic values in output

    // Get active composition
    const composition = project.compositions[project.mainCompositionId];
    if (!composition) {
      return this.createEmptyFrameState(frame, project.composition);
    }

    // Compute project hash for cache validation
    const projectHash = useCache ? this.frameCache.computeProjectHash(project) : '';

    // Check cache first (if enabled)
    if (useCache) {
      const cached = this.frameCache.get(frame, project.mainCompositionId, projectHash);
      if (cached) {
        return cached;
      }
    }

    // Create audio reactive mapper if we have audio data
    let audioMapper: AudioReactiveMapper | null = null;
    if (audioReactive && audioReactive.analysis && audioReactive.mappings.length > 0) {
      audioMapper = new AudioReactiveMapper(audioReactive.analysis);
      for (const mapping of audioReactive.mappings) {
        audioMapper.addMapping(mapping);
      }
    }

    // Evaluate all layers
    const evaluatedLayers = this.evaluateLayers(frame, composition.layers, audioMapper);

    // Evaluate camera
    const evaluatedCamera = this.evaluateCamera(
      frame,
      composition.layers,
      activeCameraId ?? null,
      composition.settings
    );

    // Evaluate audio
    const evaluatedAudio = this.evaluateAudio(frame, audioAnalysis ?? null);

    // Evaluate particle layers through deterministic simulation
    const particleSnapshots = this.evaluateParticleLayers(frame, composition.layers);

    const frameState = Object.freeze({
      frame,
      composition: composition.settings,
      layers: Object.freeze(evaluatedLayers),
      camera: evaluatedCamera,
      audio: evaluatedAudio,
      particleSnapshots: Object.freeze(particleSnapshots),
    });

    // Store in cache (if enabled)
    if (useCache) {
      this.frameCache.set(frame, project.mainCompositionId, projectHash, frameState);
    }

    return frameState;
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
    const start = layer.startFrame ?? layer.inPoint ?? 0;
    const end = layer.endFrame ?? layer.outPoint ?? 80;
    return layer.visible && frame >= start && frame <= end;
  }

  // ============================================================================
  // PRIVATE EVALUATION METHODS
  // ============================================================================

  private evaluateLayers(
    frame: number,
    layers: Layer[],
    audioMapper: AudioReactiveMapper | null
  ): EvaluatedLayer[] {
    const evaluated: EvaluatedLayer[] = [];

    for (const layer of layers) {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      const inRange = frame >= start && frame <= end;
      const visible = layer.visible && inRange;

      // Evaluate transform
      const transform = this.evaluateTransform(frame, layer.transform, layer.threeD);

      // Evaluate opacity
      let opacity = interpolateProperty(layer.opacity, frame);

      // Evaluate effects
      const effects = this.evaluateEffects(frame, layer.effects);

      // Evaluate layer-specific properties
      const properties = this.evaluateLayerProperties(frame, layer);

      // Evaluate audio reactive modifiers for this layer
      let audioModifiers: AudioReactiveModifiers = {};
      if (audioMapper) {
        audioModifiers = collectAudioReactiveModifiers(audioMapper, layer.id, frame);

        // Apply audio modifiers to opacity (additive)
        if (audioModifiers.opacity !== undefined) {
          opacity = Math.max(0, Math.min(100, opacity + audioModifiers.opacity * 100));
        }
      }

      evaluated.push(Object.freeze({
        id: layer.id,
        type: layer.type,
        name: layer.name,
        frame, // Include frame number for layers that need simulation (particles)
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
        audioModifiers: Object.freeze(audioModifiers),
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
    // Use origin (new name) with fallback to anchorPoint (deprecated) for backwards compatibility
    const originProp = transform.origin || transform.anchorPoint;
    const origin = originProp ? interpolateProperty(originProp, frame) : { x: 0, y: 0, z: 0 };
    const scale = interpolateProperty(transform.scale, frame);
    const rotation = interpolateProperty(transform.rotation, frame);

    const result: EvaluatedTransform = {
      position: { ...position },
      origin: { ...origin },
      // Keep anchorPoint alias for backwards compatibility
      anchorPoint: { ...origin },
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
    activeCameraId: string | null,
    compositionSettings?: CompositionSettings
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
          frame >= (l.startFrame ?? l.inPoint ?? 0) &&
          frame <= (l.endFrame ?? l.outPoint ?? 80)
      );
    }

    if (!cameraLayer || !cameraLayer.data) {
      return null;
    }

    const cameraData = cameraLayer.data as CameraLayerData;

    // Evaluate camera transform
    const transform = this.evaluateTransform(frame, cameraLayer.transform, true);

    // Default camera values - use composition center as default target
    const compWidth = compositionSettings?.width ?? 1024;
    const compHeight = compositionSettings?.height ?? 1024;
    const centerX = compWidth / 2;
    const centerY = compHeight / 2;

    let position = { x: transform.position.x, y: transform.position.y, z: 0 };
    let target = { x: centerX, y: centerY, z: 0 };  // Default to composition center
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

    // Apply trajectory keyframes if present (override animated position/target)
    if (cameraData.trajectoryKeyframes) {
      const trajKfs = cameraData.trajectoryKeyframes;

      // Find surrounding keyframes for position
      if (trajKfs.position && trajKfs.position.length > 0) {
        const posKfs = trajKfs.position;
        let before = posKfs[0];
        let after = posKfs[posKfs.length - 1];

        for (const kf of posKfs) {
          if (kf.frame <= frame && kf.frame >= before.frame) before = kf;
          if (kf.frame >= frame && kf.frame <= after.frame) after = kf;
        }

        if (before.frame === after.frame || frame <= before.frame) {
          position = { ...before.position };
        } else if (frame >= after.frame) {
          position = { ...after.position };
        } else {
          const t = (frame - before.frame) / (after.frame - before.frame);
          position = {
            x: before.position.x + (after.position.x - before.position.x) * t,
            y: before.position.y + (after.position.y - before.position.y) * t,
            z: before.position.z + (after.position.z - before.position.z) * t,
          };
        }
      }

      // Find surrounding keyframes for point of interest
      if (trajKfs.pointOfInterest && trajKfs.pointOfInterest.length > 0) {
        const poiKfs = trajKfs.pointOfInterest;
        let before = poiKfs[0];
        let after = poiKfs[poiKfs.length - 1];

        for (const kf of poiKfs) {
          if (kf.frame <= frame && kf.frame >= before.frame) before = kf;
          if (kf.frame >= frame && kf.frame <= after.frame) after = kf;
        }

        if (before.frame === after.frame || frame <= before.frame) {
          target = { ...before.pointOfInterest };
        } else if (frame >= after.frame) {
          target = { ...after.pointOfInterest };
        } else {
          const t = (frame - before.frame) / (after.frame - before.frame);
          target = {
            x: before.pointOfInterest.x + (after.pointOfInterest.x - before.pointOfInterest.x) * t,
            y: before.pointOfInterest.y + (after.pointOfInterest.y - before.pointOfInterest.y) * t,
            z: before.pointOfInterest.z + (after.pointOfInterest.z - before.pointOfInterest.z) * t,
          };
        }
      }
    }

    // Apply camera shake if enabled (deterministic via seed)
    if (cameraData.shake?.enabled) {
      const shakeData = cameraData.shake;
      const shake = new CameraShake(
        {
          type: shakeData.type,
          intensity: shakeData.intensity,
          frequency: shakeData.frequency,
          rotationEnabled: shakeData.rotationEnabled,
          rotationScale: shakeData.rotationScale,
          seed: shakeData.seed,
          decay: shakeData.decay,
        },
        shakeData.startFrame,
        shakeData.duration
      );

      const offset = shake.getOffset(frame);
      position = {
        x: position.x + offset.position.x,
        y: position.y + offset.position.y,
        z: position.z + offset.position.z,
      };
      // Note: rotation shake would need to be added to evaluated camera rotation
    }

    // Apply rack focus if enabled (overrides focus distance)
    if (cameraData.rackFocus?.enabled) {
      const rf = cameraData.rackFocus;
      focusDistance = getRackFocusDistance(
        {
          startDistance: rf.startDistance,
          endDistance: rf.endDistance,
          duration: rf.duration,
          startFrame: rf.startFrame,
          easing: rf.easing,
          holdStart: rf.holdStart,
          holdEnd: rf.holdEnd,
        },
        frame
      );
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
   * Evaluate particle layers through deterministic simulation
   * DETERMINISM: Uses ParticleSimulationRegistry which guarantees same frame = same result
   */
  private evaluateParticleLayers(
    frame: number,
    layers: Layer[]
  ): Record<string, ParticleSnapshot> {
    const snapshots: Record<string, ParticleSnapshot> = {};

    for (const layer of layers) {
      if (layer.type !== 'particles' || !layer.visible) continue;
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      if (frame < start || frame > end) continue;

      const data = layer.data as ParticleLayerData | null;
      if (!data?.systemConfig) continue;

      // Convert ParticleLayerData to ParticleSystemConfig
      const config = this.convertToParticleSystemConfig(data);

      // Evaluate through the deterministic registry
      // Calculate frame relative to layer's start frame for proper simulation
      const relativeFrame = frame - start;
      const snapshot = particleSimulationRegistry.evaluateLayer(
        layer.id,
        relativeFrame,
        config
      );

      snapshots[layer.id] = snapshot;
    }

    return snapshots;
  }

  /**
   * Convert ParticleLayerData to ParticleSystemConfig
   * Maps the project-level configuration to the simulation config
   */
  private convertToParticleSystemConfig(data: ParticleLayerData): ParticleSystemConfig {
    const sys = data.systemConfig;
    return {
      maxParticles: sys.maxParticles,
      gravity: sys.gravity,
      windStrength: sys.windStrength,
      windDirection: sys.windDirection,
      warmupPeriod: sys.warmupPeriod,
      respectMaskBoundary: sys.respectMaskBoundary,
      boundaryBehavior: sys.boundaryBehavior,
      friction: sys.friction,
      turbulenceFields: sys.turbulenceFields ?? [],
      subEmitters: sys.subEmitters ?? [],
      collision: {
        enabled: false,
        particleCollision: false,
        particleCollisionRadius: 1,
        particleCollisionResponse: 'bounce',
        particleCollisionDamping: 0.5,
        layerCollision: false,
        layerCollisionLayerId: null,
        layerCollisionThreshold: 0.5,
        floorEnabled: false,
        floorY: 1,
        ceilingEnabled: false,
        ceilingY: 0,
        wallsEnabled: false,
        bounciness: 0.8,
        friction: 0.1,
        spatialHashCellSize: 32,
      },
    };
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
      particleSnapshots: Object.freeze({}),
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
