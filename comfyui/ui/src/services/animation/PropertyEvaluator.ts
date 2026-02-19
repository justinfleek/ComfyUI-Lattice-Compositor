/**
 * PropertyEvaluator - Evaluates animated properties at specific frames
 *
 * This class provides a simple interface for evaluating AnimatableProperty
 * values at any given frame, handling interpolation between keyframes.
 *
 * Used by particle systems for time remapping (speed maps), where the
 * particle simulation frame needs to be computed from an animated curve.
 *
 * CONTRACT:
 * - evaluate() returns the interpolated value at the given frame
 * - For non-animated properties, returns the static value
 * - NaN/Infinity inputs are handled gracefully
 *
 * @example
 * ```ts
 * const evaluator = new PropertyEvaluator(30); // 30 fps
 * const time = evaluator.evaluate(speedMap, currentFrame);
 * ```
 */
import type { AnimatableProperty } from "@/types/animation";
import { interpolateProperty } from "@/services/interpolation";

export class PropertyEvaluator {
  /** Frames per second for interpolation calculations */
  private readonly fps: number;

  /**
   * Create a new PropertyEvaluator
   * @param fps - The composition's frames per second
   */
  constructor(fps: number) {
    // Validate fps to prevent division by zero or invalid calculations
    if (!Number.isFinite(fps) || fps <= 0) {
      console.warn(
        `PropertyEvaluator: Invalid fps ${fps}, defaulting to 30`
      );
      this.fps = 30;
    } else {
      this.fps = fps;
    }
  }

  /**
   * Evaluate an animated property at a specific frame
   *
   * @param property - The animated property to evaluate
   * @param frame - The frame number to evaluate at
   * @returns The interpolated value at the given frame
   */
  evaluate<T>(property: AnimatableProperty<T>, frame: number): T {
    // Handle invalid frame input
    if (!Number.isFinite(frame)) {
      console.warn(
        `PropertyEvaluator.evaluate: Invalid frame ${frame}, using 0`
      );
      frame = 0;
    }

    // Use the existing interpolation engine which handles:
    // - Non-animated properties (returns static value)
    // - Linear, bezier, easing, and hold interpolation
    // - Expression evaluation
    // - Before/after keyframe clamping
    return interpolateProperty(
      property,
      frame,
      this.fps,
      "", // layerId - not needed for simple property evaluation
      undefined // compDuration - not needed for simple evaluation
    );
  }

  /**
   * Get the configured FPS
   */
  getFps(): number {
    return this.fps;
  }
}
