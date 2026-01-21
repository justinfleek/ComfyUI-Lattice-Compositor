/**
 * Layer Evaluation Cache
 *
 * Differential layer evaluation system that:
 * 1. Tracks layer versions to detect changes
 * 2. Caches evaluated layer results by (layerId, frame, version)
 * 3. Only re-evaluates layers whose properties have changed
 *
 * Performance characteristics:
 * - Cache hit: O(1) lookup
 * - Cache miss: Full evaluation
 * - Version tracking: O(1) per change
 * - Memory: Bounded by maxCacheSize
 */

import type {
  EvaluatedEffect,
  EvaluatedLayer,
  EvaluatedTransform,
} from "@/engine/MotionEngine";
import { interpolateProperty } from "@/services/interpolation";
import { isFiniteNumber } from "@/utils/typeGuards";
import type {
  AnimatableProperty,
  EffectInstance,
  Layer,
  LayerTransform,
  PropertyValue,
} from "@/types/project";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ============================================================================
// VERSION TRACKING
// ============================================================================

/**
 * Version counter per layer - incremented on any property change
 * Key: layerId, Value: version number
 */
const layerVersions = new Map<string, number>();

/**
 * Global version that increments on any change (for bulk invalidation)
 */
let globalVersion = 0;

/**
 * Mark a layer as dirty (property changed)
 * Should be called whenever a layer property is modified
 */
export function markLayerDirty(layerId: string): void {
  // Type proof: Map.get() returns number | undefined → number
  const currentValue = layerVersions.get(layerId);
  const current = isFiniteNumber(currentValue) && Number.isInteger(currentValue) && currentValue >= 0 ? currentValue : 0;
  layerVersions.set(layerId, current + 1);
  globalVersion++;
}

/**
 * Mark all layers as dirty (e.g., project reload)
 */
export function markAllLayersDirty(): void {
  layerVersions.clear();
  globalVersion++;
}

/**
 * Get current version for a layer
 */
export function getLayerVersion(layerId: string): number {
  // Type proof: Map.get() returns number | undefined → number
  const versionValue = layerVersions.get(layerId);
  return isFiniteNumber(versionValue) && Number.isInteger(versionValue) && versionValue >= 0 ? versionValue : 0;
}

/**
 * Get global version (for detecting any change)
 */
export function getGlobalVersion(): number {
  return globalVersion;
}

// ============================================================================
// EVALUATION CACHE
// ============================================================================

interface CacheEntry {
  evaluatedLayer: EvaluatedLayer;
  layerVersion: number;
  accessTime: number;
}

/**
 * Cache for evaluated layer results
 * Key format: `${layerId}:${frame}`
 */
const evaluationCache = new Map<string, CacheEntry>();

/**
 * Maximum number of cached entries
 * At 81 frames × 20 layers = 1620 entries max typical workload
 */
const MAX_CACHE_SIZE = 5000;

/**
 * Build cache key from layerId and frame
 */
function buildCacheKey(layerId: string, frame: number): string {
  return `${layerId}:${frame}`;
}

/**
 * Check if a cached entry is still valid
 */
function isCacheValid(entry: CacheEntry, layerId: string): boolean {
  const currentVersion = getLayerVersion(layerId);
  return entry.layerVersion === currentVersion;
}

/**
 * Get cached evaluation result if valid
 */
export function getCachedEvaluation(
  layerId: string,
  frame: number,
): EvaluatedLayer | null {
  const key = buildCacheKey(layerId, frame);
  const entry = evaluationCache.get(key);

  if (entry && isCacheValid(entry, layerId)) {
    // Update access time for LRU
    entry.accessTime = Date.now();
    return entry.evaluatedLayer;
  }

  throw new Error(`[LayerEvaluationCache] Cache miss for layer "${layerId}" at frame ${frame}`);
}

/**
 * Store evaluation result in cache
 */
export function setCachedEvaluation(
  layerId: string,
  frame: number,
  evaluatedLayer: EvaluatedLayer,
): void {
  // Evict old entries if cache is full
  if (evaluationCache.size >= MAX_CACHE_SIZE) {
    evictOldEntries(MAX_CACHE_SIZE / 4); // Evict 25% of cache
  }

  const key = buildCacheKey(layerId, frame);
  evaluationCache.set(key, {
    evaluatedLayer,
    layerVersion: getLayerVersion(layerId),
    accessTime: Date.now(),
  });
}

/**
 * Evict oldest entries to make room
 */
function evictOldEntries(count: number): void {
  // Sort entries by access time
  const entries = Array.from(evaluationCache.entries()).sort(
    ([, a], [, b]) => a.accessTime - b.accessTime,
  );

  // Remove oldest entries
  for (let i = 0; i < count && i < entries.length; i++) {
    evaluationCache.delete(entries[i][0]);
  }
}

/**
 * Clear cache for a specific layer
 */
export function clearLayerCache(layerId: string): void {
  const keysToDelete: string[] = [];
  for (const key of evaluationCache.keys()) {
    if (key.startsWith(`${layerId}:`)) {
      keysToDelete.push(key);
    }
  }
  keysToDelete.forEach((key) => evaluationCache.delete(key));
}

/**
 * Clear entire cache
 */
export function clearEvaluationCache(): void {
  evaluationCache.clear();
}

/**
 * Get cache statistics
 */
export function getEvaluationCacheStats(): {
  size: number;
  maxSize: number;
  layerVersions: number;
  globalVersion: number;
} {
  return {
    size: evaluationCache.size,
    maxSize: MAX_CACHE_SIZE,
    layerVersions: layerVersions.size,
    globalVersion,
  };
}

// ============================================================================
// LAYER EVALUATION WITH CACHING
// ============================================================================

/**
 * Type guard for animatable properties
 */
function isAnimatableProperty(
  value: RuntimeValue,
): value is AnimatableProperty<PropertyValue> {
  return (
    typeof value === "object" &&
    value !== null &&
    "value" in value &&
    "keyframes" in value
  );
}

/**
 * Evaluate transform properties at a frame
 *
 * IMPORTANT: This function handles separated dimensions (positionX/Y/Z and scaleX/Y/Z).
 * When `transform.separateDimensions.position` is true, individual dimension properties
 * are evaluated instead of the combined position property. Same for scale.
 *
 * This must match the behavior in MotionEngine.ts:evaluateTransform to ensure
 * consistent results between rendering and export.
 *
 * @param fps - Frames per second (required for expression evaluation)
 */
function evaluateTransform(
  frame: number,
  transform: LayerTransform,
  is3D: boolean,
  fps: number,
): EvaluatedTransform {
  // Evaluate position - check for separate dimensions first
  let position: { x: number; y: number; z?: number };
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const separateDimensions = (transform != null && typeof transform === "object" && "separateDimensions" in transform && transform.separateDimensions != null && typeof transform.separateDimensions === "object") ? transform.separateDimensions : undefined;
  const positionSeparated = (separateDimensions != null && typeof separateDimensions === "object" && "position" in separateDimensions && typeof separateDimensions.position === "boolean" && separateDimensions.position) ? true : false;
  if (
    positionSeparated &&
    transform.positionX &&
    transform.positionY
  ) {
    position = {
      x: interpolateProperty(transform.positionX, frame, fps),
      y: interpolateProperty(transform.positionY, frame, fps),
      z: transform.positionZ
        ? interpolateProperty(transform.positionZ, frame, fps)
        : 0,
    };
  } else {
    position = interpolateProperty(transform.position, frame, fps);
  }

  // Use origin (new name) with fallback to anchorPoint for backwards compatibility
  const originProp = transform.origin || transform.anchorPoint;
  const origin = originProp
    ? interpolateProperty(originProp, frame, fps)
    : { x: 0, y: 0, z: 0 };

  // Evaluate scale - check for separate dimensions first
  let scale: { x: number; y: number; z?: number };
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const scaleSeparated = (separateDimensions != null && typeof separateDimensions === "object" && "scale" in separateDimensions && typeof separateDimensions.scale === "boolean" && separateDimensions.scale) ? true : false;
  if (
    scaleSeparated &&
    transform.scaleX &&
    transform.scaleY
  ) {
    scale = {
      x: interpolateProperty(transform.scaleX, frame, fps),
      y: interpolateProperty(transform.scaleY, frame, fps),
      z: transform.scaleZ
        ? interpolateProperty(transform.scaleZ, frame, fps)
        : 100,
    };
  } else {
    scale = interpolateProperty(transform.scale, frame, fps);
  }

  const rotation = interpolateProperty(transform.rotation, frame, fps);

  const result: EvaluatedTransform = {
    position: { ...position },
    origin: { ...origin },
    anchorPoint: { ...origin }, // @deprecated alias
    scale: { ...scale },
    rotation,
  };

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

/**
 * Evaluate effects at a frame
 * @param fps - Frames per second (required for expression evaluation)
 */
/**
 * Type for evaluated effect parameters
 * Values come from AnimatableProperty evaluation, which returns PropertyValue
 */
type EvaluatedEffectParameters = Readonly<Record<string, PropertyValue>>;

function evaluateEffects(
  frame: number,
  effects: EffectInstance[],
  fps: number,
): EvaluatedEffect[] {
  return effects.map((effect) => {
    const evaluatedParams: Record<string, PropertyValue> = {};

    for (const [key, param] of Object.entries(effect.parameters)) {
      const paramValue = param as RuntimeValue;
      if (isAnimatableProperty(paramValue)) {
        evaluatedParams[key] = interpolateProperty(paramValue, frame, fps);
      } else {
        // Non-animatable parameters are already PropertyValue
        // Type guard: validate param is PropertyValue
        if (typeof paramValue === "number" || typeof paramValue === "string" || typeof paramValue === "boolean" ||
            (typeof paramValue === "object" && paramValue !== null && ("x" in paramValue || "r" in paramValue))) {
          evaluatedParams[key] = paramValue as PropertyValue;
        } else {
          // Fallback: convert to number if possible, otherwise 0
          evaluatedParams[key] = (typeof paramValue === "number" && Number.isFinite(paramValue)) ? paramValue : 0;
        }
      }
    }

    return Object.freeze({
      id: effect.id,
      type: effect.effectKey,
      enabled: effect.enabled,
      parameters: Object.freeze(evaluatedParams) as EvaluatedEffectParameters,
    });
  });
}

/**
 * Type for evaluated layer properties
 * Values come from AnimatableProperty evaluation, which returns PropertyValue
 */
type EvaluatedLayerProperties = Readonly<Record<string, PropertyValue>>;

/**
 * Evaluate layer-specific properties at a frame
 * @param fps - Frames per second (required for expression evaluation)
 */
function evaluateLayerProperties(
  frame: number,
  layer: Layer,
  fps: number,
): EvaluatedLayerProperties {
  const evaluated: Record<string, PropertyValue> = {};

  // Guard against missing properties array (e.g., from old/corrupted project data)
  if (layer.properties && Array.isArray(layer.properties)) {
    for (const prop of layer.properties) {
      evaluated[prop.name] = interpolateProperty(prop, frame, fps);
    }
  }

  // Handle type-specific animatable properties in data
  if (layer.data && typeof layer.data === "object") {
    for (const [key, value] of Object.entries(layer.data)) {
      if (isAnimatableProperty(value)) {
        evaluated[key] = interpolateProperty(value, frame, fps);
      }
    }
  }

  return Object.freeze(evaluated) as EvaluatedLayerProperties;
}

/**
 * Evaluate a single layer at a frame (with caching)
 *
 * @param layer - The layer to evaluate
 * @param frame - The frame number
 * @param fps - Frames per second (REQUIRED for correct expression evaluation)
 * @returns The evaluated layer state
 */
export function evaluateLayerCached(
  layer: Layer,
  frame: number,
  fps: number,
): EvaluatedLayer {
  // Check cache first
  const cached = getCachedEvaluation(layer.id, frame);
  if (cached) {
    return cached;
  }

  // Evaluate layer
  // Type proof: startFrame ∈ ℕ ∪ {undefined}, inPoint ∈ ℕ ∪ {undefined} → startFrame ∈ ℕ
  const startFrameValue = layer.startFrame;
  const start = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0
    ? startFrameValue
    : (isFiniteNumber(layer.inPoint) && Number.isInteger(layer.inPoint) && layer.inPoint >= 0 ? layer.inPoint : 0);
  // Type proof: endFrame ∈ ℕ ∪ {undefined}, outPoint ∈ ℕ ∪ {undefined} → endFrame ∈ ℕ
  const endFrameValue = layer.endFrame;
  const end = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0
    ? endFrameValue
    : (isFiniteNumber(layer.outPoint) && Number.isInteger(layer.outPoint) && layer.outPoint >= 0 ? layer.outPoint : 80);
  const inRange = frame >= start && frame <= end;
  const visible = layer.visible && inRange;

  const transform = evaluateTransform(
    frame,
    layer.transform,
    layer.threeD,
    fps,
  );
  const opacity = interpolateProperty(layer.opacity, frame, fps);
  const effects = evaluateEffects(frame, layer.effects, fps);
  const properties = evaluateLayerProperties(frame, layer, fps);

  const evaluated: EvaluatedLayer = Object.freeze({
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
    layerRef: layer,
    frame, // Include frame for particle system deterministic simulation
    audioModifiers: {}, // Empty audio modifiers for non-audio-reactive layers
  });

  // Store in cache
  setCachedEvaluation(layer.id, frame, evaluated);

  return evaluated;
}

/**
 * Evaluate multiple layers with differential caching
 *
 * @param layers - Layers to evaluate
 * @param frame - Frame number
 * @param fps - Frames per second (REQUIRED for correct expression evaluation)
 * @returns Array of evaluated layers
 */
export function evaluateLayersCached(
  layers: Layer[],
  frame: number,
  fps: number,
): EvaluatedLayer[] {
  return layers.map((layer) => evaluateLayerCached(layer, frame, fps));
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  // Version tracking
  markLayerDirty,
  markAllLayersDirty,
  getLayerVersion,
  getGlobalVersion,
  // Cache management
  getCachedEvaluation,
  setCachedEvaluation,
  clearLayerCache,
  clearEvaluationCache,
  getEvaluationCacheStats,
  // Evaluation with caching
  evaluateLayerCached,
  evaluateLayersCached,
};
