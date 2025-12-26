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

import type { EvaluatedLayer, EvaluatedTransform, EvaluatedEffect } from '@/engine/MotionEngine';
import type { Layer, AnimatableProperty, EffectInstance, LayerTransform } from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';

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
  const current = layerVersions.get(layerId) ?? 0;
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
  return layerVersions.get(layerId) ?? 0;
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
export function getCachedEvaluation(layerId: string, frame: number): EvaluatedLayer | null {
  const key = buildCacheKey(layerId, frame);
  const entry = evaluationCache.get(key);

  if (entry && isCacheValid(entry, layerId)) {
    // Update access time for LRU
    entry.accessTime = Date.now();
    return entry.evaluatedLayer;
  }

  return null;
}

/**
 * Store evaluation result in cache
 */
export function setCachedEvaluation(
  layerId: string,
  frame: number,
  evaluatedLayer: EvaluatedLayer
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
  const entries = Array.from(evaluationCache.entries())
    .sort(([, a], [, b]) => a.accessTime - b.accessTime);

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
  keysToDelete.forEach(key => evaluationCache.delete(key));
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
function isAnimatableProperty(value: unknown): value is AnimatableProperty<unknown> {
  return (
    typeof value === 'object' &&
    value !== null &&
    'value' in value &&
    'keyframes' in value
  );
}

/**
 * Evaluate transform properties at a frame
 * @param fps - Frames per second (required for expression evaluation)
 */
function evaluateTransform(
  frame: number,
  transform: LayerTransform,
  is3D: boolean,
  fps: number
): EvaluatedTransform {
  const position = interpolateProperty(transform.position, frame, fps);
  // Use origin (new name) with fallback to anchorPoint for backwards compatibility
  const originProp = transform.origin || transform.anchorPoint;
  const origin = originProp ? interpolateProperty(originProp, frame, fps) : { x: 0, y: 0, z: 0 };
  const scale = interpolateProperty(transform.scale, frame, fps);
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
function evaluateEffects(
  frame: number,
  effects: EffectInstance[],
  fps: number
): EvaluatedEffect[] {
  return effects.map((effect) => {
    const evaluatedParams: Record<string, unknown> = {};

    for (const [key, param] of Object.entries(effect.parameters)) {
      if (isAnimatableProperty(param)) {
        evaluatedParams[key] = interpolateProperty(param, frame, fps);
      } else {
        evaluatedParams[key] = param;
      }
    }

    return Object.freeze({
      id: effect.id,
      type: effect.effectKey,
      enabled: effect.enabled,
      parameters: Object.freeze(evaluatedParams),
    });
  });
}

/**
 * Evaluate layer-specific properties at a frame
 * @param fps - Frames per second (required for expression evaluation)
 */
function evaluateLayerProperties(
  frame: number,
  layer: Layer,
  fps: number
): Record<string, unknown> {
  const evaluated: Record<string, unknown> = {};

  // Guard against missing properties array (e.g., from old/corrupted project data)
  if (layer.properties && Array.isArray(layer.properties)) {
    for (const prop of layer.properties) {
      evaluated[prop.name] = interpolateProperty(prop, frame, fps);
    }
  }

  // Handle type-specific animatable properties in data
  if (layer.data) {
    for (const [key, value] of Object.entries(layer.data)) {
      if (isAnimatableProperty(value)) {
        evaluated[key] = interpolateProperty(value, frame, fps);
      }
    }
  }

  return evaluated;
}

/**
 * Evaluate a single layer at a frame (with caching)
 *
 * @param layer - The layer to evaluate
 * @param frame - The frame number
 * @param fps - Frames per second (REQUIRED for correct expression evaluation)
 * @returns The evaluated layer state
 */
export function evaluateLayerCached(layer: Layer, frame: number, fps: number): EvaluatedLayer {
  // Check cache first
  const cached = getCachedEvaluation(layer.id, frame);
  if (cached) {
    return cached;
  }

  // Evaluate layer
  const start = layer.startFrame ?? layer.inPoint ?? 0;
  const end = layer.endFrame ?? layer.outPoint ?? 80;
  const inRange = frame >= start && frame <= end;
  const visible = layer.visible && inRange;

  const transform = evaluateTransform(frame, layer.transform, layer.threeD, fps);
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
export function evaluateLayersCached(layers: Layer[], frame: number, fps: number): EvaluatedLayer[] {
  return layers.map(layer => evaluateLayerCached(layer, frame, fps));
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
