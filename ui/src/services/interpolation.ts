/**
 * Keyframe Interpolation Engine
 *
 * Handles linear, bezier, easing, and hold interpolation between keyframes.
 */
import type { Keyframe, AnimatableProperty, BezierHandle } from '@/types/project';
import { getEasing, easings, type EasingName } from './easing';

/**
 * Calculate the scalar delta between two values for bezier normalization
 */
function getValueDelta<T>(v1: T, v2: T): number {
  if (typeof v1 === 'number' && typeof v2 === 'number') {
    return v2 - v1;
  }
  // For vectors, use magnitude of the difference
  if (typeof v1 === 'object' && v1 !== null && 'x' in v1 && 'y' in v1 &&
      typeof v2 === 'object' && v2 !== null && 'x' in v2 && 'y' in v2) {
    const dx = (v2 as any).x - (v1 as any).x;
    const dy = (v2 as any).y - (v1 as any).y;
    return Math.sqrt(dx * dx + dy * dy) || 1;
  }
  return 1; // Default for non-numeric types
}

/**
 * Interpolate a property value at a given frame
 */
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number
): T {
  // If not animated, return static value
  if (!property.animated || property.keyframes.length === 0) {
    return property.value;
  }

  const keyframes = property.keyframes;

  // Before first keyframe - return first keyframe value
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value;
  }

  // After last keyframe - return last keyframe value
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value;
  }

  // Find surrounding keyframes
  let k1: Keyframe<T> = keyframes[0];
  let k2: Keyframe<T> = keyframes[1];

  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame <= keyframes[i + 1].frame) {
      k1 = keyframes[i];
      k2 = keyframes[i + 1];
      break;
    }
  }

  // Calculate t (0-1) between keyframes
  const duration = k2.frame - k1.frame;
  const elapsed = frame - k1.frame;
  let t = duration > 0 ? elapsed / duration : 0;

  // Apply interpolation based on type
  const interpolation = k1.interpolation || 'linear';

  if (interpolation === 'hold') {
    return k1.value;
  } else if (interpolation === 'bezier') {
    // Use bezier handles for custom curves
    // Calculate value delta for proper normalization
    const valueDelta = getValueDelta(k1.value, k2.value);
    t = cubicBezierEasing(t, k1.outHandle, k2.inHandle, duration, valueDelta);
  } else if (interpolation === 'linear') {
    // t stays linear
  } else if (interpolation in easings) {
    // Apply named easing function
    const easingFn = getEasing(interpolation);
    t = easingFn(t);
  } else {
    // Unknown interpolation type, default to linear
    console.warn(`Unknown interpolation type: ${interpolation}, using linear`);
  }

  // Interpolate the value based on type
  return interpolateValue(k1.value, k2.value, t);
}

/**
 * Cubic bezier easing function
 *
 * Converts absolute frame/value handle offsets to normalized 0-1 space
 * for the bezier curve calculation.
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
  valueDelta: number = 1
): number {
  // If handles are disabled, return linear
  if (!outHandle.enabled && !inHandle.enabled) {
    return t;
  }

  // Convert absolute frame/value offsets to normalized 0-1 space
  // outHandle: positive frame offset from k1, normalized by duration
  // inHandle: negative frame offset from k2, so we compute from the end
  const x1 = frameDuration > 0 ? Math.abs(outHandle.frame) / frameDuration : 0.33;
  const y1 = valueDelta !== 0 ? outHandle.value / valueDelta : 0.33;

  // inHandle is relative to k2, so we need to compute its position from k1's perspective
  // inHandle.frame is typically negative (pointing backward from k2)
  const x2 = frameDuration > 0 ? 1 - Math.abs(inHandle.frame) / frameDuration : 0.67;
  const y2 = valueDelta !== 0 ? 1 - inHandle.value / valueDelta : 0.67;

  // Find t value for given x using Newton-Raphson iteration
  let guessT = t;

  for (let i = 0; i < 8; i++) {
    const currentX = bezierPoint(guessT, 0, x1, x2, 1);
    const currentSlope = bezierDerivative(guessT, 0, x1, x2, 1);

    if (Math.abs(currentSlope) < 1e-6) break;

    const error = currentX - t;
    guessT -= error / currentSlope;

    guessT = Math.max(0, Math.min(1, guessT));
  }

  // Return y value at found t
  return bezierPoint(guessT, 0, y1, y2, 1);
}

/**
 * Cubic bezier point calculation
 */
function bezierPoint(t: number, p0: number, p1: number, p2: number, p3: number): number {
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
function bezierDerivative(t: number, p0: number, p1: number, p2: number, p3: number): number {
  const mt = 1 - t;
  return (
    3 * mt * mt * (p1 - p0) +
    6 * mt * t * (p2 - p1) +
    3 * t * t * (p3 - p2)
  );
}

/**
 * Interpolate between two values based on their type
 * UPDATED: Now supports Z-axis interpolation for 3D transforms
 */
function interpolateValue<T>(v1: T, v2: T, t: number): T {
  // Number
  if (typeof v1 === 'number' && typeof v2 === 'number') {
    return (v1 + (v2 - v1) * t) as T;
  }

  // Position/Vector object (Supports 2D and 3D)
  if (
    typeof v1 === 'object' && v1 !== null &&
    typeof v2 === 'object' && v2 !== null &&
    'x' in v1 && 'y' in v1 &&
    'x' in v2 && 'y' in v2
  ) {
    const val1 = v1 as any;
    const val2 = v2 as any;

    const result: any = {
      x: val1.x + (val2.x - val1.x) * t,
      y: val1.y + (val2.y - val1.y) * t
    };

    // Handle Z if present in both
    if ('z' in val1 && 'z' in val2) {
      result.z = val1.z + (val2.z - val1.z) * t;
    } else if ('z' in val1) {
      // Transitioning from 3D to 2D (rare, but handle it)
      result.z = val1.z * (1 - t);
    } else if ('z' in val2) {
      // Transitioning from 2D to 3D
      result.z = val2.z * t;
    }

    return result as T;
  }

  // Color (hex string)
  if (typeof v1 === 'string' && typeof v2 === 'string' &&
      v1.startsWith('#') && v2.startsWith('#')) {
    return interpolateColor(v1, v2, t) as T;
  }

  // Default: no interpolation, return first value until t >= 0.5
  return t < 0.5 ? v1 : v2;
}

/**
 * Interpolate between two hex colors
 */
function interpolateColor(c1: string, c2: string, t: number): string {
  const r1 = parseInt(c1.slice(1, 3), 16);
  const g1 = parseInt(c1.slice(3, 5), 16);
  const b1 = parseInt(c1.slice(5, 7), 16);

  const r2 = parseInt(c2.slice(1, 3), 16);
  const g2 = parseInt(c2.slice(3, 5), 16);
  const b2 = parseInt(c2.slice(5, 7), 16);

  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);

  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}

/**
 * Easing presets - normalized bezier control points (CSS cubic-bezier style)
 * These are used for graph editor visualization, NOT for keyframe storage.
 * The values represent normalized 0-1 control points for the bezier curve.
 */
export const EASING_PRESETS_NORMALIZED = {
  linear: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeIn: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeOut: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeInOut: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeOutBack: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.34, y: 1.56 }  // Overshoot
  }
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
  valueDelta: number
): { inHandle: BezierHandle; outHandle: BezierHandle } {
  const preset = EASING_PRESETS_NORMALIZED[presetName];

  return {
    outHandle: {
      frame: preset.outHandle.x * frameDuration,
      value: preset.outHandle.y * valueDelta,
      enabled: true
    },
    inHandle: {
      frame: -preset.inHandle.x * frameDuration,
      value: -preset.inHandle.y * valueDelta,
      enabled: true
    }
  };
}

/**
 * Apply an easing preset to a keyframe (legacy function - prefer named easings)
 * @deprecated Use interpolation type with named easings instead
 */
export function applyEasingPreset(
  keyframe: Keyframe<any>,
  presetName: keyof typeof EASING_PRESETS_NORMALIZED,
  _direction: 'in' | 'out' | 'both' = 'both'
): void {
  // For the new system, we simply set the interpolation type to 'bezier'
  // The actual easing is applied through named easings in the interpolation property
  keyframe.interpolation = presetName === 'linear' ? 'linear' : 'bezier';
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
  valueDelta: number = 1
): { x: number; y: number } {
  // Convert absolute handles to normalized 0-1 space
  const x1 = frameDuration > 0 ? Math.abs(outHandle.frame) / frameDuration : 0.33;
  const y1 = valueDelta !== 0 ? outHandle.value / valueDelta : 0.33;
  const x2 = frameDuration > 0 ? 1 - Math.abs(inHandle.frame) / frameDuration : 0.67;
  const y2 = valueDelta !== 0 ? 1 - inHandle.value / valueDelta : 0.67;

  return {
    x: bezierPoint(t, 0, x1, x2, 1),
    y: bezierPoint(t, 0, y1, y2, 1)
  };
}

/**
 * Get bezier curve point using normalized preset values (for visualization)
 * This uses the old {x, y} normalized format from EASING_PRESETS_NORMALIZED
 */
export function getBezierCurvePointNormalized(
  t: number,
  outHandle: { x: number; y: number },
  inHandle: { x: number; y: number }
): { x: number; y: number } {
  const x1 = outHandle.x;
  const y1 = outHandle.y;
  const x2 = 1 - inHandle.x;
  const y2 = 1 - inHandle.y;

  return {
    x: bezierPoint(t, 0, x1, x2, 1),
    y: bezierPoint(t, 0, y1, y2, 1)
  };
}

/**
 * Apply easing to a ratio value (0-1) using normalized preset
 * Takes a linear ratio and returns an eased ratio based on the preset
 */
export function applyEasing(
  ratio: number,
  preset: { outHandle: { x: number; y: number }; inHandle: { x: number; y: number } }
): number {
  // Clamp ratio to 0-1
  const t = Math.max(0, Math.min(1, ratio));

  // Get the bezier curve point at t using normalized values
  const point = getBezierCurvePointNormalized(t, preset.outHandle, preset.inHandle);

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
  createHandlesForPreset
};
