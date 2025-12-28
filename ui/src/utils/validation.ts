/**
 * Validation Utilities
 *
 * Centralized input validation to eliminate NaN/Infinity/null bugs.
 * Created during forensic audit to fix SYSTEMIC-001 through SYSTEMIC-006.
 *
 * Usage:
 *   import { safeNumber, safeFps, safeDivide, safeIndex } from '@/utils/validation';
 */

// ============================================================================
// SYSTEM DEFAULTS (Wan model requirements)
// ============================================================================

/**
 * Default FPS for static/generated content (Wan model standard)
 * Used by: image, shape, particles, camera, lights, spline, path layers
 */
export const WAN_DEFAULT_FPS = 16;

/**
 * Default frame count for Wan model (4n+1 requirement)
 * Used by: static/generated layers
 */
export const WAN_DEFAULT_FRAMES = 81;

/**
 * Content-based layers (video, audio, animated imports) should use
 * their native FPS from the content metadata, NOT these defaults.
 */

// ============================================================================
// SYSTEMIC-003, SYSTEMIC-005: Safe number validation
// ============================================================================

export interface SafeNumberOptions {
  min?: number;
  max?: number;
  allowZero?: boolean;
  allowNegative?: boolean;
}

/**
 * Validates a number is finite and optionally within range.
 * Returns defaultValue if invalid.
 *
 * Fixes: SYSTEMIC-005 (Math.max/min don't catch NaN)
 *
 * @example
 * safeNumber(userInput, 1.0, { min: 0, max: 1 })  // clamp opacity
 * safeNumber(scale, 1.0, { allowZero: false })    // prevent scale=0
 */
export function safeNumber(
  value: unknown,
  defaultValue: number,
  options: SafeNumberOptions = {}
): number {
  // Check if it's a finite number
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    return defaultValue;
  }

  // Check zero
  if (!options.allowZero && value === 0) {
    return defaultValue;
  }

  // Check negative
  if (!options.allowNegative && value < 0) {
    return options.min !== undefined ? options.min : defaultValue;
  }

  // Apply min/max bounds
  let result = value;
  if (options.min !== undefined && result < options.min) {
    result = options.min;
  }
  if (options.max !== undefined && result > options.max) {
    result = options.max;
  }

  return result;
}

// ============================================================================
// SYSTEMIC-003: Safe FPS validation
// ============================================================================

/**
 * Validates FPS - must be positive finite number.
 *
 * IMPORTANT: defaultFps is REQUIRED. Caller must specify the correct default:
 * - For static/generated layers: use WAN_DEFAULT_FPS (16)
 * - For content-based layers: use content.fps or content metadata
 *
 * Fixes: SYSTEMIC-003 (Division by fps=0)
 *
 * @example
 * // Static layer (particles, shape, etc.)
 * const fps = safeFps(composition.fps, WAN_DEFAULT_FPS);
 *
 * // Content-based layer (video, audio)
 * const fps = safeFps(composition.fps, videoMetadata.fps);
 */
export function safeFps(fps: unknown, defaultFps: number): number {
  // Validate defaultFps itself (developer error if invalid)
  if (typeof defaultFps !== 'number' || !Number.isFinite(defaultFps) || defaultFps <= 0) {
    console.error('[safeFps] Invalid defaultFps provided:', defaultFps, '- using WAN_DEFAULT_FPS');
    defaultFps = 16; // Fallback to Wan default as last resort
  }

  if (typeof fps !== 'number' || !Number.isFinite(fps) || fps <= 0) {
    return defaultFps;
  }
  // Clamp to reasonable range (1-240 fps)
  return Math.max(1, Math.min(fps, 240));
}

// ============================================================================
// SYSTEMIC-003: Safe division
// ============================================================================

/**
 * Safe division - returns defaultValue if divisor is 0, NaN, or Infinity.
 *
 * Fixes: SYSTEMIC-003 (Division by zero)
 *
 * @example
 * const frameTime = safeDivide(1, fps, 1/30);
 * const normalized = safeDivide(value, max, 0);
 */
export function safeDivide(
  numerator: number,
  divisor: number,
  defaultValue: number = 0
): number {
  if (!Number.isFinite(divisor) || divisor === 0) {
    return defaultValue;
  }
  if (!Number.isFinite(numerator)) {
    return defaultValue;
  }
  const result = numerator / divisor;
  return Number.isFinite(result) ? result : defaultValue;
}

// ============================================================================
// SYSTEMIC-002: Safe array index validation
// ============================================================================

/**
 * Validates array index is a valid integer within bounds.
 * Returns null if invalid (caller must handle).
 *
 * Fixes: SYSTEMIC-002 (NaN bypasses comparison guards)
 *
 * @example
 * const idx = safeIndex(userIndex, array.length);
 * if (idx === null) return;  // Invalid index
 * const item = array[idx];   // Safe access
 */
export function safeIndex(
  index: unknown,
  arrayLength: number
): number | null {
  if (!Number.isInteger(index)) {
    return null;
  }
  const idx = index as number;
  if (idx < 0 || idx >= arrayLength) {
    return null;
  }
  return idx;
}

/**
 * Safe array access - returns defaultValue if index is invalid.
 *
 * @example
 * const item = safeArrayAccess(items, userIndex, defaultItem);
 */
export function safeArrayAccess<T>(
  array: T[],
  index: unknown,
  defaultValue: T
): T {
  const idx = safeIndex(index, array.length);
  if (idx === null) {
    return defaultValue;
  }
  return array[idx] ?? defaultValue;
}

// ============================================================================
// SYSTEMIC-001: Safe frame number validation
// ============================================================================

/**
 * Validates a frame number is a finite integer >= 0.
 *
 * Fixes: SYSTEMIC-001 (NaN frame equality fails)
 *
 * @example
 * const frame = safeFrame(keyframe.frame, 0);
 */
export function safeFrame(frame: unknown, defaultFrame: number = 0): number {
  if (typeof frame !== 'number' || !Number.isFinite(frame)) {
    return defaultFrame;
  }
  return Math.max(0, Math.round(frame));
}

/**
 * Compares two frame numbers, handling NaN correctly.
 *
 * Fixes: SYSTEMIC-001 (NaN === NaN is false)
 *
 * @example
 * if (framesEqual(k.frame, targetFrame)) { ... }
 */
export function framesEqual(a: number, b: number): boolean {
  if (Number.isNaN(a) && Number.isNaN(b)) {
    return true;  // Both NaN = equal (for finding NaN keyframes)
  }
  return a === b;
}

// ============================================================================
// Safe object/null validation
// ============================================================================

/**
 * Validates object is not null/undefined before property access.
 * Returns true if safe to access, false otherwise.
 *
 * @example
 * if (!isValidObject(material)) return;
 * material.opacity = 0.5;  // Safe
 */
export function isValidObject(obj: unknown): obj is object {
  return obj !== null && obj !== undefined && typeof obj === 'object';
}

/**
 * Safe property access with default value.
 *
 * @example
 * const opacity = safeGet(material, 'opacity', 1.0);
 */
export function safeGet<T>(
  obj: unknown,
  key: string,
  defaultValue: T
): T {
  if (!isValidObject(obj)) {
    return defaultValue;
  }
  const value = (obj as Record<string, unknown>)[key];
  return (value !== undefined && value !== null) ? value as T : defaultValue;
}

// ============================================================================
// SYSTEMIC-006: Safe particle/loop count
// ============================================================================

/**
 * Validates a count for loops - must be finite positive integer with max cap.
 * Prevents infinite loops from Infinity or huge values.
 *
 * Fixes: SYSTEMIC-006 (Unbounded maxParticles causes infinite loops)
 *
 * @example
 * const count = safeLoopCount(maxParticles, 10000, 1000000);
 * for (let i = 0; i < count; i++) { ... }  // Guaranteed to terminate
 */
export function safeLoopCount(
  count: unknown,
  defaultCount: number,
  maxAllowed: number = 1000000
): number {
  if (typeof count !== 'number' || !Number.isFinite(count) || count < 0) {
    return defaultCount;
  }
  return Math.min(Math.floor(count), maxAllowed);
}

// ============================================================================
// Validation error logging (optional, for debugging)
// ============================================================================

let validationWarningsEnabled = false;

export function enableValidationWarnings(enabled: boolean): void {
  validationWarningsEnabled = enabled;
}

export function logValidationWarning(
  functionName: string,
  paramName: string,
  value: unknown,
  defaultUsed: unknown
): void {
  if (validationWarningsEnabled) {
    console.warn(
      `[Validation] ${functionName}: Invalid ${paramName}=${value}, using default=${defaultUsed}`
    );
  }
}
