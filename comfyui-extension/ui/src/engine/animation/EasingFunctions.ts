/**
 * EasingFunctions - Standard Easing Function Library
 *
 * Comprehensive collection of easing functions matching:
 * - CSS timing functions
 * - Common animation libraries
 */

export type EasingFunction = (t: number) => number;

/**
 * Standard easing functions
 */
export const easingFunctions: Record<string, EasingFunction> = {
  // ============================================================================
  // LINEAR
  // ============================================================================

  linear: (t) => t,

  // ============================================================================
  // SINE
  // ============================================================================

  easeInSine: (t) => 1 - Math.cos((t * Math.PI) / 2),

  easeOutSine: (t) => Math.sin((t * Math.PI) / 2),

  easeInOutSine: (t) => -(Math.cos(Math.PI * t) - 1) / 2,

  // ============================================================================
  // QUADRATIC
  // ============================================================================

  easeInQuad: (t) => t * t,

  easeOutQuad: (t) => 1 - (1 - t) * (1 - t),

  easeInOutQuad: (t) => (t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2),

  // ============================================================================
  // CUBIC
  // ============================================================================

  easeInCubic: (t) => t * t * t,

  easeOutCubic: (t) => 1 - (1 - t) ** 3,

  easeInOutCubic: (t) => (t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2),

  // ============================================================================
  // QUARTIC
  // ============================================================================

  easeInQuart: (t) => t * t * t * t,

  easeOutQuart: (t) => 1 - (1 - t) ** 4,

  easeInOutQuart: (t) =>
    t < 0.5 ? 8 * t * t * t * t : 1 - (-2 * t + 2) ** 4 / 2,

  // ============================================================================
  // QUINTIC
  // ============================================================================

  easeInQuint: (t) => t * t * t * t * t,

  easeOutQuint: (t) => 1 - (1 - t) ** 5,

  easeInOutQuint: (t) =>
    t < 0.5 ? 16 * t * t * t * t * t : 1 - (-2 * t + 2) ** 5 / 2,

  // ============================================================================
  // EXPONENTIAL
  // ============================================================================

  easeInExpo: (t) => (t === 0 ? 0 : 2 ** (10 * t - 10)),

  easeOutExpo: (t) => (t === 1 ? 1 : 1 - 2 ** (-10 * t)),

  easeInOutExpo: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return t < 0.5 ? 2 ** (20 * t - 10) / 2 : (2 - 2 ** (-20 * t + 10)) / 2;
  },

  // ============================================================================
  // CIRCULAR
  // ============================================================================

  easeInCirc: (t) => 1 - Math.sqrt(1 - t ** 2),

  easeOutCirc: (t) => Math.sqrt(1 - (t - 1) ** 2),

  easeInOutCirc: (t) =>
    t < 0.5
      ? (1 - Math.sqrt(1 - (2 * t) ** 2)) / 2
      : (Math.sqrt(1 - (-2 * t + 2) ** 2) + 1) / 2,

  // ============================================================================
  // BACK (OVERSHOOT)
  // ============================================================================

  easeInBack: (t) => {
    const c1 = 1.70158;
    const c3 = c1 + 1;
    return c3 * t * t * t - c1 * t * t;
  },

  easeOutBack: (t) => {
    const c1 = 1.70158;
    const c3 = c1 + 1;
    return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2;
  },

  easeInOutBack: (t) => {
    const c1 = 1.70158;
    const c2 = c1 * 1.525;
    return t < 0.5
      ? ((2 * t) ** 2 * ((c2 + 1) * 2 * t - c2)) / 2
      : ((2 * t - 2) ** 2 * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2;
  },

  // ============================================================================
  // ELASTIC
  // ============================================================================

  easeInElastic: (t) => {
    const c4 = (2 * Math.PI) / 3;
    return t === 0
      ? 0
      : t === 1
        ? 1
        : -(2 ** (10 * t - 10)) * Math.sin((t * 10 - 10.75) * c4);
  },

  easeOutElastic: (t) => {
    const c4 = (2 * Math.PI) / 3;
    return t === 0
      ? 0
      : t === 1
        ? 1
        : 2 ** (-10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
  },

  easeInOutElastic: (t) => {
    const c5 = (2 * Math.PI) / 4.5;
    return t === 0
      ? 0
      : t === 1
        ? 1
        : t < 0.5
          ? -(2 ** (20 * t - 10) * Math.sin((20 * t - 11.125) * c5)) / 2
          : (2 ** (-20 * t + 10) * Math.sin((20 * t - 11.125) * c5)) / 2 + 1;
  },

  // ============================================================================
  // BOUNCE
  // ============================================================================

  easeInBounce: (t) => 1 - easingFunctions.easeOutBounce(1 - t),

  easeOutBounce: (t) => {
    const n1 = 7.5625;
    const d1 = 2.75;

    if (t < 1 / d1) {
      return n1 * t * t;
    } else if (t < 2 / d1) {
      return n1 * (t -= 1.5 / d1) * t + 0.75;
    } else if (t < 2.5 / d1) {
      return n1 * (t -= 2.25 / d1) * t + 0.9375;
    } else {
      return n1 * (t -= 2.625 / d1) * t + 0.984375;
    }
  },

  easeInOutBounce: (t) =>
    t < 0.5
      ? (1 - easingFunctions.easeOutBounce(1 - 2 * t)) / 2
      : (1 + easingFunctions.easeOutBounce(2 * t - 1)) / 2,
};

/**
 * Get easing function by name
 * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
 */
export function getEasing(name: string): EasingFunction {
  const easing = easingFunctions[name];
  return (easing !== null && easing !== undefined && typeof easing === "function") ? easing : easingFunctions.linear;
}

/**
 * Get all available easing function names
 */
export function getEasingNames(): string[] {
  return Object.keys(easingFunctions);
}

/**
 * Check if an easing function exists
 */
export function hasEasing(name: string): boolean {
  return name in easingFunctions;
}
