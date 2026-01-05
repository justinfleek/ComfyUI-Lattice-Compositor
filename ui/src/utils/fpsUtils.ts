/**
 * FPS Utilities
 *
 * Validation and helper functions for frame rate handling.
 * Ensures fps values are valid to prevent division by zero errors.
 */

/** Default fps for Lattice Compositor (WAN model standard) */
export const DEFAULT_FPS = 16;

/** Minimum allowed fps value */
export const MIN_FPS = 1;

/** Maximum allowed fps value */
export const MAX_FPS = 120;

/**
 * Validates that fps is a positive number within acceptable range.
 * Returns the validated fps or the default if invalid.
 *
 * @param fps - The fps value to validate
 * @param fallback - Fallback value if fps is invalid (default: 16)
 * @returns Valid fps value
 *
 * @example
 * ```ts
 * const fps = validateFps(store.fps);  // Returns store.fps if valid, else 16
 * const fps = validateFps(0);          // Returns 16 (0 is invalid)
 * const fps = validateFps(-5);         // Returns 16 (negative is invalid)
 * const fps = validateFps(null);       // Returns 16 (null is invalid)
 * ```
 */
export function validateFps(
  fps: number | null | undefined,
  fallback: number = DEFAULT_FPS,
): number {
  if (fps === null || fps === undefined || !Number.isFinite(fps) || fps <= 0) {
    return fallback;
  }
  return Math.max(MIN_FPS, Math.min(MAX_FPS, fps));
}

/**
 * Safely divides by fps, returning fallback if fps is invalid.
 * Prevents division by zero errors.
 *
 * @param numerator - The value to divide
 * @param fps - The fps value (must be > 0)
 * @param fallback - Value to return if fps is invalid (default: 0)
 * @returns numerator / fps, or fallback if fps is invalid
 *
 * @example
 * ```ts
 * const time = safeDivideByFps(frame, fps);        // frame / fps or 0
 * const duration = safeDivideByFps(frames, fps, 1); // frames / fps or 1
 * ```
 */
export function safeDivideByFps(
  numerator: number,
  fps: number | null | undefined,
  _fallback: number = 0,
): number {
  const validFps = validateFps(fps);
  return numerator / validFps;
}

/**
 * Converts frame number to time in seconds.
 * Validates fps to prevent division by zero.
 *
 * @param frame - Frame number
 * @param fps - Frames per second (must be > 0)
 * @returns Time in seconds
 *
 * @example
 * ```ts
 * const time = frameToTime(16, 16);  // 1.0 second
 * const time = frameToTime(30, 30);  // 1.0 second
 * ```
 */
export function frameToTime(frame: number, fps: number): number {
  return frame / validateFps(fps);
}

/**
 * Converts time in seconds to frame number.
 * Validates fps to ensure valid multiplication.
 *
 * @param time - Time in seconds
 * @param fps - Frames per second (must be > 0)
 * @returns Frame number (not rounded)
 *
 * @example
 * ```ts
 * const frame = timeToFrame(1.0, 16);  // 16
 * const frame = timeToFrame(1.0, 30);  // 30
 * ```
 */
export function timeToFrame(time: number, fps: number): number {
  return time * validateFps(fps);
}

/**
 * Calculates duration in seconds from frame count.
 *
 * @param frameCount - Number of frames
 * @param fps - Frames per second (must be > 0)
 * @returns Duration in seconds
 */
export function calculateDuration(frameCount: number, fps: number): number {
  return frameCount / validateFps(fps);
}

/**
 * Calculates frame count from duration.
 *
 * @param duration - Duration in seconds
 * @param fps - Frames per second (must be > 0)
 * @returns Frame count (ceiling)
 */
export function calculateFrameCount(duration: number, fps: number): number {
  return Math.ceil(duration * validateFps(fps));
}

/**
 * Asserts that fps is valid, throwing if not.
 * Use this at function entry points where invalid fps should be a hard error.
 *
 * @param fps - The fps value to validate
 * @param context - Optional context for error message
 * @throws Error if fps is invalid
 *
 * @example
 * ```ts
 * function processVideo(fps: number) {
 *   assertValidFps(fps, 'processVideo');  // Throws if fps <= 0
 *   // ... rest of function
 * }
 * ```
 */
export function assertValidFps(
  fps: number | null | undefined,
  context?: string,
): asserts fps is number {
  if (fps === null || fps === undefined || !Number.isFinite(fps) || fps <= 0) {
    const ctx = context ? ` in ${context}` : "";
    throw new Error(
      `Invalid fps value${ctx}: ${fps}. FPS must be a positive number.`,
    );
  }
}
