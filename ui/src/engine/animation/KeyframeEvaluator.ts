/**
 * KeyframeEvaluator - Keyframe Animation Evaluation
 *
 * Evaluates animated properties at specific frames:
 * - Finds surrounding keyframes
 * - Applies interpolation/easing
 * - Handles different value types (number, position, color)
 */

import type {
  AnimatableProperty,
  InterpolationType,
  Keyframe,
} from "@/types/project";
import { easingFunctions } from "./EasingFunctions";

export class KeyframeEvaluator {
  // Cache for recent evaluations (cleared per frame batch)
  private cache: Map<string, { frame: number; value: any }> = new Map();

  /**
   * Evaluate an animatable property at a given frame
   */
  evaluate<T>(property: AnimatableProperty<T>, frame: number): T {
    // Check cache
    const cacheKey = property.id;
    const cached = this.cache.get(cacheKey);
    if (cached && cached.frame === frame) {
      return cached.value;
    }

    let value: T;

    // If not animated or no keyframes, return default value
    if (
      !property.animated ||
      !property.keyframes ||
      property.keyframes.length === 0
    ) {
      value = property.value;
    } else {
      value = this.evaluateKeyframes(property.keyframes, frame, property.value);
    }

    // Cache result
    this.cache.set(cacheKey, { frame, value });

    return value;
  }

  /**
   * Evaluate keyframes at a given frame
   */
  private evaluateKeyframes<T>(
    keyframes: Keyframe<T>[],
    frame: number,
    defaultValue: T,
  ): T {
    // Sort keyframes by frame (should already be sorted, but ensure)
    const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);

    // Before first keyframe
    if (frame <= sorted[0].frame) {
      return sorted[0].value;
    }

    // After last keyframe
    if (frame >= sorted[sorted.length - 1].frame) {
      return sorted[sorted.length - 1].value;
    }

    // Find surrounding keyframes
    let prevKeyframe = sorted[0];
    let nextKeyframe = sorted[sorted.length - 1];

    for (let i = 0; i < sorted.length - 1; i++) {
      if (sorted[i].frame <= frame && sorted[i + 1].frame > frame) {
        prevKeyframe = sorted[i];
        nextKeyframe = sorted[i + 1];
        break;
      }
    }

    // Calculate interpolation factor
    const frameDiff = nextKeyframe.frame - prevKeyframe.frame;
    const rawT = frameDiff > 0 ? (frame - prevKeyframe.frame) / frameDiff : 0;

    // Apply easing
    const easedT = this.applyEasing(
      rawT,
      prevKeyframe.interpolation,
      prevKeyframe,
      nextKeyframe,
    );

    // Interpolate value
    return this.interpolateValue(
      prevKeyframe.value,
      nextKeyframe.value,
      easedT,
      defaultValue,
    );
  }

  /**
   * Apply easing function to raw t value
   */
  private applyEasing<T>(
    t: number,
    interpolation: InterpolationType,
    prevKeyframe: Keyframe<T>,
    nextKeyframe: Keyframe<T>,
  ): number {
    switch (interpolation) {
      case "hold":
        return 0; // No interpolation, use previous value

      case "linear":
        return t;

      case "bezier":
        // Use bezier handles if available
        return this.evaluateBezier(t, prevKeyframe, nextKeyframe);

      default: {
        // Check if it's an easing function name
        const easingFn = easingFunctions[interpolation];
        if (easingFn) {
          return easingFn(t);
        }
        return t; // Default to linear
      }
    }
  }

  /**
   * Evaluate bezier curve using keyframe handles
   */
  private evaluateBezier<T>(
    t: number,
    prevKeyframe: Keyframe<T>,
    nextKeyframe: Keyframe<T>,
  ): number {
    // Get handle values (normalized 0-1)
    const outHandle = prevKeyframe.outHandle;
    const inHandle = nextKeyframe.inHandle;

    if (!outHandle?.enabled && !inHandle?.enabled) {
      return t; // No handles, use linear
    }

    // Convert handle frames to normalized values
    const frameDiff = nextKeyframe.frame - prevKeyframe.frame;

    // Control points for cubic bezier
    const p0 = { x: 0, y: 0 };
    const p1 = {
      x: outHandle?.enabled
        ? Math.min(1, Math.max(0, outHandle.frame / frameDiff))
        : 0.33,
      y: outHandle?.enabled ? outHandle.value : 0,
    };
    const p2 = {
      x: inHandle?.enabled
        ? Math.min(1, Math.max(0, 1 + inHandle.frame / frameDiff))
        : 0.67,
      y: inHandle?.enabled ? 1 + inHandle.value : 1,
    };
    const p3 = { x: 1, y: 1 };

    // Find Y for given X using Newton-Raphson
    return this.solveCubicBezier(
      t,
      p0.x,
      p1.x,
      p2.x,
      p3.x,
      p0.y,
      p1.y,
      p2.y,
      p3.y,
    );
  }

  /**
   * Solve cubic bezier curve for Y given X
   */
  private solveCubicBezier(
    x: number,
    x0: number,
    x1: number,
    x2: number,
    x3: number,
    y0: number,
    y1: number,
    y2: number,
    y3: number,
  ): number {
    // Find t for given x using Newton-Raphson
    let t = x;
    const epsilon = 0.0001;

    for (let i = 0; i < 10; i++) {
      const currentX = this.cubicBezier(t, x0, x1, x2, x3);
      const diff = currentX - x;

      if (Math.abs(diff) < epsilon) {
        break;
      }

      const derivative = this.cubicBezierDerivative(t, x0, x1, x2, x3);
      if (Math.abs(derivative) < epsilon) {
        break;
      }

      t -= diff / derivative;
      t = Math.max(0, Math.min(1, t));
    }

    // Calculate Y at t
    return this.cubicBezier(t, y0, y1, y2, y3);
  }

  /**
   * Evaluate cubic bezier at t
   */
  private cubicBezier(
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
   * Evaluate cubic bezier derivative at t
   */
  private cubicBezierDerivative(
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
   * Interpolate between two values
   */
  private interpolateValue<T>(from: T, to: T, t: number, _defaultValue: T): T {
    // Number
    if (typeof from === "number" && typeof to === "number") {
      return (from + (to - from) * t) as unknown as T;
    }

    // Position/Vector object
    if (this.isPositionLike(from) && this.isPositionLike(to)) {
      return this.interpolatePosition(from, to, t) as unknown as T;
    }

    // Color string
    if (typeof from === "string" && typeof to === "string") {
      if (from.startsWith("#") && to.startsWith("#")) {
        return this.interpolateColor(from, to, t) as unknown as T;
      }
    }

    // Array
    if (Array.isArray(from) && Array.isArray(to)) {
      return this.interpolateArray(from, to, t) as unknown as T;
    }

    // Default: return from value (no interpolation)
    return t < 0.5 ? from : to;
  }

  /**
   * Check if value is position-like (has x, y properties)
   */
  private isPositionLike(
    value: any,
  ): value is { x: number; y: number; z?: number } {
    return (
      value !== null &&
      typeof value === "object" &&
      "x" in value &&
      "y" in value
    );
  }

  /**
   * Interpolate position/vector values
   */
  private interpolatePosition(
    from: { x: number; y: number; z?: number },
    to: { x: number; y: number; z?: number },
    t: number,
  ): { x: number; y: number; z?: number } {
    const result: { x: number; y: number; z?: number } = {
      x: from.x + (to.x - from.x) * t,
      y: from.y + (to.y - from.y) * t,
    };

    if ("z" in from || "z" in to) {
      result.z = (from.z ?? 0) + ((to.z ?? 0) - (from.z ?? 0)) * t;
    }

    return result;
  }

  /**
   * Interpolate hex color strings
   */
  private interpolateColor(from: string, to: string, t: number): string {
    const fromRGB = this.hexToRGB(from);
    const toRGB = this.hexToRGB(to);

    const r = Math.round(fromRGB.r + (toRGB.r - fromRGB.r) * t);
    const g = Math.round(fromRGB.g + (toRGB.g - fromRGB.g) * t);
    const b = Math.round(fromRGB.b + (toRGB.b - fromRGB.b) * t);

    return this.rgbToHex(r, g, b);
  }

  /**
   * Interpolate arrays
   */
  private interpolateArray(from: number[], to: number[], t: number): number[] {
    const length = Math.max(from.length, to.length);
    const result: number[] = [];

    for (let i = 0; i < length; i++) {
      const fromVal = from[i] ?? 0;
      const toVal = to[i] ?? 0;
      result.push(fromVal + (toVal - fromVal) * t);
    }

    return result;
  }

  /**
   * Convert hex color to RGB
   */
  private hexToRGB(hex: string): { r: number; g: number; b: number } {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result
      ? {
          r: parseInt(result[1], 16),
          g: parseInt(result[2], 16),
          b: parseInt(result[3], 16),
        }
      : { r: 0, g: 0, b: 0 };
  }

  /**
   * Convert RGB to hex color
   */
  private rgbToHex(r: number, g: number, b: number): string {
    return (
      "#" +
      [r, g, b]
        .map((x) => Math.max(0, Math.min(255, x)).toString(16).padStart(2, "0"))
        .join("")
    );
  }

  /**
   * Clear the evaluation cache
   */
  clearCache(): void {
    this.cache.clear();
  }
}
