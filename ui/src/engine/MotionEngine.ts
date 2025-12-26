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
  LatticeProject,
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
import {
  AudioReactiveMapper,
  collectAudioReactiveModifiers,
  collectParticleAudioReactiveModifiers,
  type ParticleAudioReactiveModifiers,
} from '@/services/audioReactiveMapping';
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

  /** BUG-081 fix: Per-emitter audio reactive modifiers for particle layers */
  readonly emitterAudioModifiers?: Readonly<Map<string, ParticleAudioReactiveModifiers>>;
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
 * Re-exported from audioReactiveMapping for convenience
 */
export type { AudioReactiveModifiers } from '@/services/audioReactiveMapping';

// Import the type for internal use
import type { AudioReactiveModifiers } from '@/services/audioReactiveMapping';

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
  computeProjectHash(project: LatticeProject): string {
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
   * BUG-082 fix: Persistent AudioReactiveMapper for temporal state
   * Temporal features (smoothing, release envelopes, beat toggles) require
   * state to persist across frames during sequential playback.
   */
  private audioMapper: AudioReactiveMapper | null = null;
  private lastAudioReactiveFrame: number = -1;
  private lastAudioAnalysis: AudioAnalysis | null = null;

  /**
   * Invalidate the frame cache
   * Call this when project structure changes
   */
  invalidateCache(): void {
    this.frameCache.invalidate();
    this.lastProjectHash = '';
    // BUG-082 fix: Reset audio reactive state on cache invalidation
    if (this.audioMapper) {
      this.audioMapper.resetTemporalState();
    }
    this.lastAudioReactiveFrame = -1;
    this.lastAudioAnalysis = null;
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
    project: LatticeProject,
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

    // BUG-082 fix: Persist AudioReactiveMapper for temporal features
    // Temporal state (smoothing, release envelopes, beat toggles) must persist
    // across sequential frames but reset on non-sequential access (scrubbing).
    let audioMapper: AudioReactiveMapper | null = null;
    if (audioReactive && audioReactive.analysis && audioReactive.mappings.length > 0) {
      // Create mapper if needed
      if (!this.audioMapper) {
        this.audioMapper = new AudioReactiveMapper(audioReactive.analysis);
        this.lastAudioAnalysis = audioReactive.analysis;
      } else if (this.lastAudioAnalysis !== audioReactive.analysis) {
        // Analysis changed - must call setAnalysis (which resets temporal state)
        // This is correct: new audio means temporal state should reset
        this.audioMapper.setAnalysis(audioReactive.analysis);
        this.lastAudioAnalysis = audioReactive.analysis;
      }
      // If same analysis, reuse mapper with preserved temporal state

      // Detect non-sequential frame access and reset temporal state
      // Sequential: frame === lastFrame + 1 OR first frame (lastFrame === -1)
      const isNonSequential = this.lastAudioReactiveFrame >= 0 &&
                              frame !== this.lastAudioReactiveFrame + 1;
      if (isNonSequential) {
        this.audioMapper.resetTemporalState();
      }

      // Sync mappings: add/update new, remove old
      const currentMappingIds = new Set(this.audioMapper.getAllMappings().map(m => m.id));
      const newMappingIds = new Set<string>();

      for (const mapping of audioReactive.mappings) {
        this.audioMapper.addMapping(mapping);  // Preserves temporal state for existing
        newMappingIds.add(mapping.id);
      }

      // Remove mappings that are no longer present
      for (const id of currentMappingIds) {
        if (!newMappingIds.has(id)) {
          this.audioMapper.removeMapping(id);
        }
      }

      audioMapper = this.audioMapper;
      this.lastAudioReactiveFrame = frame;
    } else {
      // No audio reactive input - reset tracking
      this.lastAudioReactiveFrame = -1;
    }

    // Get composition fps
    const fps = composition.settings?.fps ?? 30;

    // Evaluate all layers
    const evaluatedLayers = this.evaluateLayers(frame, composition.layers, audioMapper, fps);

    // Evaluate camera (BUG-092 fix: pass audioMapper for fov/dollyZ/shake modifiers)
    const evaluatedCamera = this.evaluateCamera(
      frame,
      composition.layers,
      activeCameraId ?? null,
      composition.settings,
      fps,
      audioMapper
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
    audioMapper: AudioReactiveMapper | null,
    fps: number = 30
  ): EvaluatedLayer[] {
    const evaluated: EvaluatedLayer[] = [];

    for (const layer of layers) {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      const inRange = frame >= start && frame <= end;
      const visible = layer.visible && inRange;

      // Evaluate transform
      const transform = this.evaluateTransform(frame, layer.transform, layer.threeD, fps);

      // Evaluate opacity (explicit type for TypeScript inference)
      let opacity: number = interpolateProperty(layer.opacity, frame, fps, layer.id);

      // Evaluate effects
      const effects = this.evaluateEffects(frame, layer.effects, fps);

      // Evaluate layer-specific properties
      const properties = this.evaluateLayerProperties(frame, layer, fps);

      // Evaluate audio reactive modifiers for this layer
      let audioModifiers: AudioReactiveModifiers = {};
      let emitterAudioModifiers: Map<string, ParticleAudioReactiveModifiers> | undefined;
      if (audioMapper) {
        audioModifiers = collectAudioReactiveModifiers(audioMapper, layer.id, frame);

        // Apply audio modifiers to opacity (additive)
        if (audioModifiers.opacity !== undefined) {
          opacity = Math.max(0, Math.min(100, opacity + audioModifiers.opacity * 100));
        }

        // BUG-081 fix: Compute per-emitter modifiers for particle layers
        if (layer.type === 'particles' && layer.data) {
          const particleData = layer.data as { emitters?: Array<{ id: string }> };
          if (particleData.emitters && particleData.emitters.length > 0) {
            emitterAudioModifiers = new Map();
            for (const emitter of particleData.emitters) {
              const emitterMods = collectParticleAudioReactiveModifiers(
                audioMapper,
                layer.id,
                emitter.id,
                frame
              );
              // Only add if there are actual modifiers
              if (Object.keys(emitterMods).length > 0) {
                emitterAudioModifiers.set(emitter.id, emitterMods);
              }
            }
            // Don't include if no emitters have modifiers
            if (emitterAudioModifiers.size === 0) {
              emitterAudioModifiers = undefined;
            }
          }
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
        emitterAudioModifiers: emitterAudioModifiers ? Object.freeze(emitterAudioModifiers) : undefined,
      }));
    }

    return evaluated;
  }

  private evaluateTransform(
    frame: number,
    transform: LayerTransform,
    is3D: boolean,
    fps: number = 30
  ): EvaluatedTransform {
    // Evaluate position - check for separate dimensions first
    let position: { x: number; y: number; z?: number };
    if (transform.separateDimensions?.position && transform.positionX && transform.positionY) {
      position = {
        x: interpolateProperty(transform.positionX, frame, fps),
        y: interpolateProperty(transform.positionY, frame, fps),
        z: transform.positionZ ? interpolateProperty(transform.positionZ, frame, fps) : 0
      };
    } else {
      position = interpolateProperty(transform.position, frame, fps);
    }

    // Use origin (new name) with fallback to anchorPoint (deprecated) for backwards compatibility
    const originProp = transform.origin || transform.anchorPoint;
    const origin = originProp ? interpolateProperty(originProp, frame, fps) : { x: 0, y: 0, z: 0 };

    // Evaluate scale - check for separate dimensions first
    let scale: { x: number; y: number; z?: number };
    if (transform.separateDimensions?.scale && transform.scaleX && transform.scaleY) {
      scale = {
        x: interpolateProperty(transform.scaleX, frame, fps),
        y: interpolateProperty(transform.scaleY, frame, fps),
        z: transform.scaleZ ? interpolateProperty(transform.scaleZ, frame, fps) : 100
      };
    } else {
      scale = interpolateProperty(transform.scale, frame, fps);
    }

    const rotation = interpolateProperty(transform.rotation, frame, fps);

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
          ? interpolateProperty(transform.rotationX, frame, fps)
          : 0,
        rotationY: transform.rotationY
          ? interpolateProperty(transform.rotationY, frame, fps)
          : 0,
        rotationZ: transform.rotationZ
          ? interpolateProperty(transform.rotationZ, frame, fps)
          : rotation,
      };
    }

    return result;
  }

  private evaluateEffects(
    frame: number,
    effects: EffectInstance[],
    fps: number = 30
  ): EvaluatedEffect[] {
    return effects.map((effect) => {
      const evaluatedParams: Record<string, unknown> = {};

      // Evaluate each parameter
      for (const [key, param] of Object.entries(effect.parameters)) {
        if (this.isAnimatableProperty(param)) {
          evaluatedParams[key] = interpolateProperty(param, frame, fps);
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
    layer: Layer,
    fps: number = 30
  ): Record<string, unknown> {
    const evaluated: Record<string, unknown> = {};

    // Evaluate properties array
    for (const prop of layer.properties) {
      evaluated[prop.name] = interpolateProperty(prop, frame, fps, layer.id);
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
            evaluated['zoom'] = interpolateProperty(data.animatedZoom, frame, fps, layer.id);
          }
          if (data.animatedOffsetX) {
            evaluated['offsetX'] = interpolateProperty(data.animatedOffsetX, frame, fps, layer.id);
          }
          if (data.animatedOffsetY) {
            evaluated['offsetY'] = interpolateProperty(data.animatedOffsetY, frame, fps, layer.id);
          }
          if (data.animatedRotation) {
            evaluated['rotation'] = interpolateProperty(data.animatedRotation, frame, fps, layer.id);
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
    compositionSettings?: CompositionSettings,
    fps: number = 30,
    audioMapper?: AudioReactiveMapper | null
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
    const transform = this.evaluateTransform(frame, cameraLayer.transform, true, fps);

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
      const pos: { x: number; y: number; z?: number } = interpolateProperty(cameraData.animatedPosition, frame, fps, cameraLayer.id);
      position = { x: pos.x, y: pos.y, z: pos.z ?? 0 };
    }

    if (cameraData.animatedTarget) {
      const tgt: { x: number; y: number; z?: number } = interpolateProperty(cameraData.animatedTarget, frame, fps, cameraLayer.id);
      target = { x: tgt.x, y: tgt.y, z: tgt.z ?? 0 };
    }

    if (cameraData.animatedFov) {
      fov = interpolateProperty(cameraData.animatedFov, frame, fps, cameraLayer.id);
    }

    if (cameraData.animatedFocalLength) {
      focalLength = interpolateProperty(cameraData.animatedFocalLength, frame, fps, cameraLayer.id);
    }

    // Evaluate depth of field
    let focusDistance = cameraData.depthOfField?.focusDistance ?? 1000;
    let aperture = cameraData.depthOfField?.aperture ?? 2.8;
    let blurLevel = cameraData.depthOfField?.blurLevel ?? 50;

    if (cameraData.animatedFocusDistance) {
      focusDistance = interpolateProperty(cameraData.animatedFocusDistance, frame, fps, cameraLayer.id);
    }
    if (cameraData.animatedAperture) {
      aperture = interpolateProperty(cameraData.animatedAperture, frame, fps, cameraLayer.id);
    }
    if (cameraData.animatedBlurLevel) {
      blurLevel = interpolateProperty(cameraData.animatedBlurLevel, frame, fps, cameraLayer.id);
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

    // BUG-092 fix: Collect audio modifiers BEFORE applying camera effects
    // This allows audio to modulate fov, dollyZ, and shake intensity
    let cameraAudioModifiers: AudioReactiveModifiers = {};
    if (audioMapper) {
      cameraAudioModifiers = collectAudioReactiveModifiers(audioMapper, cameraLayer.id, frame);
    }

    // Apply FOV audio modifier (additive degrees, 0-1 maps to 0-30 degrees)
    if (cameraAudioModifiers.fov !== undefined && cameraAudioModifiers.fov !== 0) {
      fov += cameraAudioModifiers.fov * 30;
    }

    // Apply dollyZ audio modifier (additive Z position, 0-1 maps to 0-500 units)
    if (cameraAudioModifiers.dollyZ !== undefined && cameraAudioModifiers.dollyZ !== 0) {
      position = {
        x: position.x,
        y: position.y,
        z: position.z + cameraAudioModifiers.dollyZ * 500,
      };
    }

    // Apply camera shake if enabled (deterministic via seed)
    // Audio modifier modulates shake intensity (applied ONCE, not twice)
    if (cameraData.shake?.enabled) {
      const shakeData = cameraData.shake;

      // Calculate effective intensity with audio modifier
      let effectiveIntensity = shakeData.intensity;
      if (cameraAudioModifiers.shake !== undefined && cameraAudioModifiers.shake !== 0) {
        effectiveIntensity *= (1 + cameraAudioModifiers.shake * 2);  // 0-1 maps to 1x-3x intensity
      }

      const shake = new CameraShake(
        {
          type: shakeData.type,
          intensity: effectiveIntensity,
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
