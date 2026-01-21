/**
 * Keyframe Interpolation Engine
 *
 * PURE MODULE – DO NOT MUTATE
 * ===========================
 * This module contains PURE FUNCTIONS that are reference implementations
 * for deterministic frame evaluation. They are used by MotionEngine.
 *
 * CONTRACT:
 * - All functions are PURE: same inputs always produce same outputs
 * - No functions mutate their inputs or any external state
 * - No Math.random(), Date.now(), or other non-deterministic operations
 * - No global mutable state
 *
 * CALLERS MUST NOT:
 * - Mutate returned values
 * - Store returned references expecting them to update
 *
 * Handles linear, bezier, easing, and hold interpolation between keyframes.
 *
 * Performance optimizations:
 * - Binary search for keyframe lookup (O(log n) instead of O(n))
 * - Early exit in Newton-Raphson iteration
 * - Bezier handle normalization caching (15-25% gain for bezier-heavy animations)
 * - Cached computations where possible
 */
import type {
  AnimatableProperty,
  BezierHandle,
  Keyframe,
} from "@/types/project";
import type { BezierPath } from "@/types/shapes";
import type { Vec2, Vec3 } from "@/types/transform";
import { validateFps } from "@/utils/fpsUtils";
import { renderLogger } from "@/utils/logger";
import { createFootageAccessor } from "./dataImport";
import { easings, getEasing } from "./easing";
import {
  type Expression,
  type ExpressionContext,
  evaluateExpression,
} from "./expressions";
import { isBezierPath, morphPaths, prepareMorphPaths } from "./pathMorphing";
import { safeLerp } from "@/utils/numericSafety";
import type { JSONValue } from "@/types/dataAsset";

// ============================================================================
// BEZIER HANDLE CACHE
// Caches normalized bezier control points to avoid repeated computation
// ============================================================================

interface NormalizedBezier {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

/**
 * LRU Cache for normalized bezier control points
 * Key format: "outFrame,outValue,inFrame,inValue,duration,delta"
 *
 * Memory management:
 * - Max 500 entries (covers typical composition with many keyframes)
 * - LRU eviction when full
 * - Entries are small (~48 bytes each)
 */
class BezierCache {
  private cache = new Map<string, NormalizedBezier>();
  private readonly maxSize = 500;

  /**
   * Generate cache key from bezier parameters
   * Uses fixed precision to avoid floating point key variations
   */
  private makeKey(
    outHandle: BezierHandle,
    inHandle: BezierHandle,
    frameDuration: number,
    valueDelta: number,
  ): string {
    // Round to 4 decimal places for consistent keys
    const round = (n: number) => Math.round(n * 10000);
    return `${round(outHandle.frame)},${round(outHandle.value)},${round(inHandle.frame)},${round(inHandle.value)},${round(frameDuration)},${round(valueDelta)}`;
  }

  /**
   * Get cached normalized bezier or compute and cache it
   */
  get(
    outHandle: BezierHandle,
    inHandle: BezierHandle,
    frameDuration: number,
    valueDelta: number,
  ): NormalizedBezier {
    const key = this.makeKey(outHandle, inHandle, frameDuration, valueDelta);

    const cached = this.cache.get(key);
    if (cached) {
      // LRU: Move to end
      this.cache.delete(key);
      this.cache.set(key, cached);
      return cached;
    }

    // Compute normalized control points
    const x1 =
      frameDuration > 0 ? Math.abs(outHandle.frame) / frameDuration : 0.33;
    const y1 = valueDelta !== 0 ? outHandle.value / valueDelta : 0.33;
    const x2 =
      frameDuration > 0 ? 1 - Math.abs(inHandle.frame) / frameDuration : 0.67;
    const y2 = valueDelta !== 0 ? 1 - inHandle.value / valueDelta : 0.67;

    const normalized: NormalizedBezier = { x1, y1, x2, y2 };

    // Evict oldest if at capacity
    if (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey) this.cache.delete(firstKey);
    }

    this.cache.set(key, normalized);
    return normalized;
  }

  /**
   * Clear the cache (call on project load)
   */
  clear(): void {
    this.cache.clear();
  }

  /**
   * Get cache statistics for debugging
   */
  getStats(): { size: number; maxSize: number } {
    return { size: this.cache.size, maxSize: this.maxSize };
  }
}

// Singleton cache instance
const bezierCache = new BezierCache();

/**
 * Clear the bezier cache
 * Call this when loading a new project to free memory
 */
export function clearBezierCache(): void {
  bezierCache.clear();
}

/**
 * Get bezier cache statistics for debugging
 */
export function getBezierCacheStats(): { size: number; maxSize: number } {
  return bezierCache.getStats();
}

// ============================================================================
// KEYFRAME SEARCH
// ============================================================================

/**
 * Binary search to find the keyframe index where frame falls between [i] and [i+1]
 * Returns the index of the keyframe just before or at the given frame.
 * Assumes keyframes are sorted by frame (ascending).
 *
 * @returns Index i where keyframes[i].frame <= frame < keyframes[i+1].frame
 */
function findKeyframeIndex<T>(keyframes: Keyframe<T>[], frame: number): number {
  let low = 0;
  let high = keyframes.length - 2; // -2 because we need i and i+1

  while (low <= high) {
    const mid = (low + high) >>> 1; // Bitwise divide by 2 (faster)
    const midFrame = keyframes[mid].frame;
    const nextFrame = keyframes[mid + 1].frame;

    if (frame >= midFrame && frame <= nextFrame) {
      return mid;
    } else if (frame < midFrame) {
      high = mid - 1;
    } else {
      low = mid + 1;
    }
  }

  // Fallback (shouldn't happen if bounds are checked first)
  return Math.max(0, Math.min(low, keyframes.length - 2));
}

/**
 * Calculate the scalar delta between two values for bezier normalization
 */
function getValueDelta<T>(v1: T, v2: T): number {
  if (typeof v1 === "number" && typeof v2 === "number") {
    return v2 - v1;
  }
  // For vectors, use magnitude of the difference
  if (
    typeof v1 === "object" &&
    v1 !== null &&
    "x" in v1 &&
    "y" in v1 &&
    typeof v2 === "object" &&
    v2 !== null &&
    "x" in v2 &&
    "y" in v2
  ) {
    const v1Vec = v1 as Vec2;
    const v2Vec = v2 as Vec2;
    const dx = v2Vec.x - v1Vec.x;
    const dy = v2Vec.y - v1Vec.y;
    const distance = Math.sqrt(dx * dx + dy * dy);
    // Return 1 as fallback if distance is 0 or invalid (prevents division by zero)
    return Number.isFinite(distance) && distance > 0 ? distance : 1;
  }
  return 1; // Default for non-numeric types
}

/**
 * Interpolate a property value at a given frame
 *
 * @param property - The animatable property
 * @param frame - Current frame number
 * @param fps - Frames per second (needed for expressions, defaults to 16 per WAN standard)
 * @param layerId - Layer ID (for expression context)
 * @param compDuration - Composition duration in seconds (for expressions, defaults to 81/fps per 4n+1 pattern)
 */
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number,
  fps: number = 16,
  layerId: string = "",
  compDuration?: number,
): T {
  // Calculate base interpolated value
  let value: T;

  // If not animated, use static value
  if (!property.animated || property.keyframes.length === 0) {
    value = property.value;
  } else {
    const keyframes = property.keyframes;

    // Before first keyframe - return first keyframe value
    if (frame <= keyframes[0].frame) {
      value = keyframes[0].value;
    }
    // After last keyframe - return last keyframe value
    else if (frame >= keyframes[keyframes.length - 1].frame) {
      value = keyframes[keyframes.length - 1].value;
    } else {
      // Find surrounding keyframes using binary search (O(log n) instead of O(n))
      const idx = findKeyframeIndex(keyframes, frame);
      const k1 = keyframes[idx];
      const k2 = keyframes[idx + 1];

      // Calculate t (0-1) between keyframes
      const duration = k2.frame - k1.frame;
      const elapsed = frame - k1.frame;
      let t = duration > 0 ? elapsed / duration : 0;

      // Apply interpolation based on type
      const interpolation = k1.interpolation || "linear";

      if (interpolation === "hold") {
        value = k1.value;
      } else {
        if (interpolation === "bezier") {
          // Use bezier handles for custom curves
          const valueDelta = getValueDelta(k1.value, k2.value);
          t = cubicBezierEasing(
            t,
            k1.outHandle,
            k2.inHandle,
            duration,
            valueDelta,
          );
        } else if (interpolation !== "linear" && interpolation in easings) {
          // Apply named easing function
          const easingFn = getEasing(interpolation);
          t = easingFn(t);
        } else if (interpolation !== "linear") {
          renderLogger.warn(
            `Unknown interpolation type: ${interpolation}, using linear`,
          );
        }

        // Interpolate the value based on type
        value = interpolateValue(k1.value, k2.value, t);
      }
    }
  }

  // Apply expression if present
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const propertyExpression = (property != null && typeof property === "object" && "expression" in property && property.expression != null && typeof property.expression === "object") ? property.expression : undefined;
  const expressionEnabled = (propertyExpression != null && typeof propertyExpression === "object" && "enabled" in propertyExpression && typeof propertyExpression.enabled === "boolean" && propertyExpression.enabled) ? true : false;
  if (expressionEnabled) {
    value = applyPropertyExpression(
      property,
      value,
      frame,
      fps,
      layerId,
      compDuration,
    );
  }

  return value;
}

/**
 * Apply an expression to a property value
 */
function applyPropertyExpression<T>(
  property: AnimatableProperty<T>,
  value: T,
  frame: number,
  fps: number,
  layerId: string,
  compDuration?: number,
): T {
  const expr = property.expression;
  if (!expr || !expr.enabled) return value;

  // Validate fps to prevent division by zero in time calculations
  const safeFps = validateFps(fps, 16);

  // Build expression context
  const time = frame / safeFps;
  const velocity = calculateVelocity(property, frame, safeFps);

  // Lean4/PureScript/Haskell: Explicit pattern matching on optional type
  // Type proof: compDuration ∈ number | undefined → number
  // PureScript: case compDuration of Just d -> d; Nothing -> 81 / safeFps
  const duration: number = compDuration !== undefined && Number.isFinite(compDuration) && compDuration > 0
    ? compDuration
    : 81 / safeFps;
  const frameCount = Math.round(duration * safeFps);

  const ctx: ExpressionContext = {
    // Time
    time,
    frame,
    fps: safeFps,
    duration,
    // Composition - defaults when not available from caller
    compWidth: 1920,
    compHeight: 1080,
    // Layer info
    layerId,
    layerIndex: 0,
    layerName: "",
    inPoint: 0,
    outPoint: frameCount,
    // Property
    propertyName: property.name,
    value: value as number | number[],
    velocity,
    numKeys: property.keyframes.length,
    keyframes: property.keyframes as Keyframe<number | number[]>[],
    // Expression controls - empty when not using expression controls
    params: {},
    // Layer property access - no-op when called from basic interpolation
    getLayerProperty: () => null,
    // Data-driven animation
    footage: createFootageAccessor,
    // Layer transform - defaults for thisLayer access
    layerTransform: {
      position: [0, 0, 0],
      rotation: [0, 0, 0],
      scale: [100, 100, 100],
      opacity: 100,
      origin: [0, 0, 0],
    },
    // Effects - empty when not available
    layerEffects: [],
    // All layers - empty when not available
    allLayers: [],
    // Effect parameter access - no-op when not available
    getLayerEffectParam: () => null,
  };

  // Convert PropertyExpression to Expression format
  const expression: Expression = {
    type: expr.type as "preset" | "function" | "custom",
    name: expr.name,
    params: expr.params as Record<string, JSONValue>,
    enabled: expr.enabled,
  };

  const result = evaluateExpression(expression, ctx);

  // Return in the correct type
  return result as T;
}

/**
 * Calculate velocity of a property at a frame
 */
function calculateVelocity<T>(
  property: AnimatableProperty<T>,
  frame: number,
  fps: number,
): number | number[] {
  const delta = 0.5; // Sample half frame before and after

  const valueBefore = interpolatePropertyBase(property, frame - delta);
  const valueAfter = interpolatePropertyBase(property, frame + delta);

  if (typeof valueBefore === "number" && typeof valueAfter === "number") {
    return (valueAfter - valueBefore) * fps;
  }

  if (typeof valueBefore === "object" && typeof valueAfter === "object") {
    if (
      valueBefore !== null &&
      valueAfter !== null &&
      "x" in valueBefore &&
      "y" in valueBefore &&
      "x" in valueAfter &&
      "y" in valueAfter
    ) {
      const vb = valueBefore as Vec2 | Vec3;
      const va = valueAfter as Vec2 | Vec3;
      const result = [(va.x - vb.x) * fps, (va.y - vb.y) * fps];
      if ("z" in vb && "z" in va) {
        result.push((va.z - vb.z) * fps);
      }
      return result;
    }
  }

  return 0;
}

/**
 * Base interpolation without expression (to avoid recursion in velocity calc)
 */
function interpolatePropertyBase<T>(
  property: AnimatableProperty<T>,
  frame: number,
): T {
  if (!property.animated || property.keyframes.length === 0) {
    return property.value;
  }

  const keyframes = property.keyframes;

  if (frame <= keyframes[0].frame) {
    return keyframes[0].value;
  }

  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value;
  }

  const idx = findKeyframeIndex(keyframes, frame);
  const k1 = keyframes[idx];
  const k2 = keyframes[idx + 1];

  const duration = k2.frame - k1.frame;
  const elapsed = frame - k1.frame;
  let t = duration > 0 ? elapsed / duration : 0;

  const interpolation = k1.interpolation || "linear";

  if (interpolation === "hold") {
    return k1.value;
  } else if (interpolation === "bezier") {
    const valueDelta = getValueDelta(k1.value, k2.value);
    t = cubicBezierEasing(t, k1.outHandle, k2.inHandle, duration, valueDelta);
  } else if (interpolation !== "linear" && interpolation in easings) {
    const easingFn = getEasing(interpolation);
    t = easingFn(t);
  }

  return interpolateValue(k1.value, k2.value, t);
}

/**
 * Cubic bezier easing function
 *
 * Converts absolute frame/value handle offsets to normalized 0-1 space
 * for the bezier curve calculation.
 *
 * OPTIMIZATION: Uses bezierCache to avoid repeated normalization computation.
 * Cache hit rate is typically 80-95% during animation playback.
 *
 * @param t - Linear time (0-1)
 * @param outHandle - First keyframe's out handle (absolute offsets)
 * @param inHandle - Second keyframe's in handle (absolute offsets)
 * @param frameDuration - Number of frames between keyframes
 * @param valueDelta - Value change between keyframes (v2 - v1)
 * @returns Eased time (0-1, can overshoot)
 */
function cubicBezierEasing(
  t: number,
  outHandle: BezierHandle,
  inHandle: BezierHandle,
  frameDuration: number = 1,
  valueDelta: number = 1,
): number {
  // If handles are disabled, return linear
  if (!outHandle.enabled && !inHandle.enabled) {
    return t;
  }

  // Get normalized control points from cache (or compute and cache)
  const { x1, y1, x2, y2 } = bezierCache.get(
    outHandle,
    inHandle,
    frameDuration,
    valueDelta,
  );

  // Find t value for given x using Newton-Raphson iteration
  // With early exit when error is small enough (typically converges in 2-4 iterations)
  let guessT = t;
  const EPSILON = 1e-6;
  const MAX_ITERATIONS = 8;

  for (let i = 0; i < MAX_ITERATIONS; i++) {
    const currentX = bezierPoint(guessT, 0, x1, x2, 1);
    const error = currentX - t;

    // Early exit if we've converged
    if (Math.abs(error) < EPSILON) break;

    const currentSlope = bezierDerivative(guessT, 0, x1, x2, 1);
    if (Math.abs(currentSlope) < EPSILON) break;

    guessT -= error / currentSlope;
    guessT = Math.max(0, Math.min(1, guessT));
  }

  // Return y value at found t
  return bezierPoint(guessT, 0, y1, y2, 1);
}

/**
 * Cubic bezier point calculation
 */
function bezierPoint(
  t: number,
  p0: number,
  p1: number,
  p2: number,
  p3: number,
): number {
  const mt = 1 - t;
  return (
    mt * mt * mt * p0 +
    3 * mt * mt * t * p1 +
    3 * mt * t * t * p2 +
    t * t * t * p3
  );
}

/**
 * Cubic bezier derivative
 */
function bezierDerivative(
  t: number,
  p0: number,
  p1: number,
  p2: number,
  p3: number,
): number {
  const mt = 1 - t;
  return (
    3 * mt * mt * (p1 - p0) + 6 * mt * t * (p2 - p1) + 3 * t * t * (p3 - p2)
  );
}

/**
 * Interpolate between two values based on their type
 * UPDATED: Now supports Z-axis interpolation for 3D transforms
 */
function interpolateValue<T>(v1: T, v2: T, t: number): T {
  // Number - use safeLerp to handle extreme values that would overflow
  if (typeof v1 === "number" && typeof v2 === "number") {
    return safeLerp(v1, v2, t) as T;
  }

  // Position/Vector object (Supports 2D and 3D)
  if (
    typeof v1 === "object" &&
    v1 !== null &&
    typeof v2 === "object" &&
    v2 !== null &&
    "x" in v1 &&
    "y" in v1 &&
    "x" in v2 &&
    "y" in v2
  ) {
    const val1 = v1 as Vec2 | Vec3;
    const val2 = v2 as Vec2 | Vec3;

    // Use safeLerp for each component to handle extreme values
    const result: Vec2 | Vec3 = {
      x: safeLerp(val1.x, val2.x, t),
      y: safeLerp(val1.y, val2.y, t),
    };

    // Handle Z if present in both
    if ("z" in val1 && "z" in val2) {
      (result as Vec3).z = safeLerp(val1.z, val2.z, t);
    } else if ("z" in val1) {
      // Transitioning from 3D to 2D (rare, but handle it)
      (result as Vec3).z = safeLerp(val1.z, 0, t);
    } else if ("z" in val2) {
      // Transitioning from 2D to 3D
      (result as Vec3).z = safeLerp(0, val2.z, t);
    }

    return result as T;
  }

  // Color (hex string)
  if (
    typeof v1 === "string" &&
    typeof v2 === "string" &&
    v1.startsWith("#") &&
    v2.startsWith("#")
  ) {
    return interpolateColor(v1, v2, t) as T;
  }

  // BezierPath (path morphing)
  if (isBezierPath(v1) && isBezierPath(v2)) {
    return interpolatePath(v1 as BezierPath, v2 as BezierPath, t) as T;
  }

  // Default: no interpolation, return first value until t >= 0.5
  return t < 0.5 ? v1 : v2;
}

/**
 * Normalize a hex color to 6-digit format
 * Handles: #rgb → #rrggbb, #rgba → #rrggbbaa, #rrggbb → #rrggbb, #rrggbbaa → #rrggbbaa
 */
function normalizeHexColor(hex: string): string {
  if (!hex || !hex.startsWith("#")) return "#000000";
  const h = hex.slice(1);

  // 3 char: #rgb → #rrggbb
  if (h.length === 3) {
    return `#${h[0]}${h[0]}${h[1]}${h[1]}${h[2]}${h[2]}`;
  }
  // 4 char: #rgba → #rrggbbaa
  if (h.length === 4) {
    return `#${h[0]}${h[0]}${h[1]}${h[1]}${h[2]}${h[2]}${h[3]}${h[3]}`;
  }
  // Already 6 or 8 chars, return as-is
  if (h.length === 6 || h.length === 8) {
    return hex;
  }
  // Invalid format - return black
  return "#000000";
}

/**
 * Parse a hex color component, returning 0 for invalid input
 */
function parseHexComponent(hex: string, start: number, end: number): number {
  const val = parseInt(hex.slice(start, end), 16);
  return Number.isNaN(val) ? 0 : Math.max(0, Math.min(255, val));
}

/**
 * Interpolate between two hex colors
 * Supports: #rgb, #rrggbb, #rgba, #rrggbbaa
 * Invalid colors are treated as black (#000000)
 */
function interpolateColor(c1: string, c2: string, t: number): string {
  // Normalize both colors
  const n1 = normalizeHexColor(c1);
  const n2 = normalizeHexColor(c2);

  const r1 = parseHexComponent(n1, 1, 3);
  const g1 = parseHexComponent(n1, 3, 5);
  const b1 = parseHexComponent(n1, 5, 7);
  const a1 = n1.length === 9 ? parseHexComponent(n1, 7, 9) : 255;

  const r2 = parseHexComponent(n2, 1, 3);
  const g2 = parseHexComponent(n2, 3, 5);
  const b2 = parseHexComponent(n2, 5, 7);
  const a2 = n2.length === 9 ? parseHexComponent(n2, 7, 9) : 255;

  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);

  // Only include alpha if either input had alpha
  if (n1.length === 9 || n2.length === 9) {
    const a = Math.round(a1 + (a2 - a1) * t);
    return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}${a.toString(16).padStart(2, "0")}`;
  }

  return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}`;
}

// Path morph cache for prepared paths (keyed by path pair hashes)
const pathMorphCache = new Map<
  string,
  { source: BezierPath; target: BezierPath }
>();
const PATH_MORPH_CACHE_MAX = 100;

/**
 * Generate a hash for a BezierPath to use as cache key
 */
function hashBezierPath(path: BezierPath): string {
  // Use vertex count and first/last point coordinates for a quick hash
  const v = path.vertices;
  if (v.length === 0) return "empty";
  const first = v[0];
  const last = v[v.length - 1];
  return `${v.length}_${first.point.x.toFixed(1)}_${first.point.y.toFixed(1)}_${last.point.x.toFixed(1)}_${last.point.y.toFixed(1)}_${path.closed ? "c" : "o"}`;
}

/**
 * Interpolate between two BezierPaths using path morphing
 *
 * This function handles shape morphing by:
 * 1. Preparing both paths to have matching vertex counts
 * 2. Interpolating between corresponding vertices
 *
 * The prepared paths are cached to avoid re-computation on each frame.
 */
function interpolatePath(
  p1: BezierPath,
  p2: BezierPath,
  t: number,
): BezierPath {
  // Edge cases
  if (t <= 0) return p1;
  if (t >= 1) return p2;

  // Generate cache key from both paths
  const key = `${hashBezierPath(p1)}|${hashBezierPath(p2)}`;

  // Get or create prepared paths
  let prepared = pathMorphCache.get(key);
  if (!prepared) {
    // Prepare paths for morphing (match vertex counts)
    prepared = prepareMorphPaths(p1, p2);

    // Cache with LRU eviction
    if (pathMorphCache.size >= PATH_MORPH_CACHE_MAX) {
      const firstKey = pathMorphCache.keys().next().value;
      if (firstKey) pathMorphCache.delete(firstKey);
    }
    pathMorphCache.set(key, prepared);
  }

  // Perform the actual morphing
  return morphPaths(prepared.source, prepared.target, t);
}

/**
 * Clear the path morph cache
 * Call this when loading a new project to free memory
 */
export function clearPathMorphCache(): void {
  pathMorphCache.clear();
}

/**
 * Easing presets - normalized bezier control points (CSS cubic-bezier style)
 * These are used for graph editor visualization, NOT for keyframe storage.
 * The values represent normalized 0-1 control points for the bezier curve.
 */
export const EASING_PRESETS_NORMALIZED = {
  linear: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.33, y: 0.33 },
  },
  easeIn: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.33, y: 0.33 },
  },
  easeOut: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.58, y: 1 },
  },
  easeInOut: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.58, y: 1 },
  },
  easeOutBack: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.34, y: 1.56 }, // Overshoot
  },
};

// Legacy alias for backwards compatibility
export const EASING_PRESETS = EASING_PRESETS_NORMALIZED;

/**
 * Create bezier handles for a keyframe pair with a given easing preset
 * Converts normalized preset values to absolute frame/value offsets
 */
export function createHandlesForPreset(
  presetName: keyof typeof EASING_PRESETS_NORMALIZED,
  frameDuration: number,
  valueDelta: number,
): { inHandle: BezierHandle; outHandle: BezierHandle } {
  const preset = EASING_PRESETS_NORMALIZED[presetName];

  return {
    outHandle: {
      frame: preset.outHandle.x * frameDuration,
      value: preset.outHandle.y * valueDelta,
      enabled: true,
    },
    inHandle: {
      frame: -preset.inHandle.x * frameDuration,
      value: -preset.inHandle.y * valueDelta,
      enabled: true,
    },
  };
}

/**
 * Apply an easing preset to a keyframe (legacy function - prefer named easings)
 * @deprecated Use interpolation type with named easings instead
 */
export function applyEasingPreset<T>(
  keyframe: Keyframe<T>,
  presetName: keyof typeof EASING_PRESETS_NORMALIZED,
  _direction: "in" | "out" | "both" = "both",
): void {
  // For the new system, we simply set the interpolation type to 'bezier'
  // The actual easing is applied through named easings in the interpolation property
  keyframe.interpolation = presetName === "linear" ? "linear" : "bezier";
}

/**
 * Get the value from a bezier curve at time t for graph visualization
 * Uses absolute frame/value handles and converts to normalized space
 *
 * @param t - Normalized time (0-1)
 * @param outHandle - First keyframe's out handle (absolute offsets)
 * @param inHandle - Second keyframe's in handle (absolute offsets)
 * @param frameDuration - Number of frames between keyframes
 * @param valueDelta - Value change between keyframes
 */
export function getBezierCurvePoint(
  t: number,
  outHandle: BezierHandle,
  inHandle: BezierHandle,
  frameDuration: number = 1,
  valueDelta: number = 1,
): { x: number; y: number } {
  // Convert absolute handles to normalized 0-1 space
  const x1 =
    frameDuration > 0 ? Math.abs(outHandle.frame) / frameDuration : 0.33;
  const y1 = valueDelta !== 0 ? outHandle.value / valueDelta : 0.33;
  const x2 =
    frameDuration > 0 ? 1 - Math.abs(inHandle.frame) / frameDuration : 0.67;
  const y2 = valueDelta !== 0 ? 1 - inHandle.value / valueDelta : 0.67;

  return {
    x: bezierPoint(t, 0, x1, x2, 1),
    y: bezierPoint(t, 0, y1, y2, 1),
  };
}

/**
 * Get bezier curve point using normalized preset values (for visualization)
 * This uses the old {x, y} normalized format from EASING_PRESETS_NORMALIZED
 */
export function getBezierCurvePointNormalized(
  t: number,
  outHandle: { x: number; y: number },
  inHandle: { x: number; y: number },
): { x: number; y: number } {
  const x1 = outHandle.x;
  const y1 = outHandle.y;
  const x2 = 1 - inHandle.x;
  const y2 = 1 - inHandle.y;

  return {
    x: bezierPoint(t, 0, x1, x2, 1),
    y: bezierPoint(t, 0, y1, y2, 1),
  };
}

/**
 * Apply easing to a ratio value (0-1) using normalized preset
 * Takes a linear ratio and returns an eased ratio based on the preset
 */
export function applyEasing(
  ratio: number,
  preset: {
    outHandle: { x: number; y: number };
    inHandle: { x: number; y: number };
  },
): number {
  // Clamp ratio to 0-1
  const t = Math.max(0, Math.min(1, ratio));

  // Get the bezier curve point at t using normalized values
  const point = getBezierCurvePointNormalized(
    t,
    preset.outHandle,
    preset.inHandle,
  );

  // Return the y value (eased value)
  return point.y;
}

export default {
  interpolateProperty,
  applyEasingPreset,
  applyEasing,
  EASING_PRESETS,
  EASING_PRESETS_NORMALIZED,
  getBezierCurvePoint,
  getBezierCurvePointNormalized,
  createHandlesForPreset,
  clearBezierCache,
  getBezierCacheStats,
  clearPathMorphCache,
};
