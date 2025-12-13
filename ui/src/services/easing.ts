/**
 * Easing Functions for Weyl Compositor
 *
 * Ported from mojs easing library (https://github.com/mojs/mojs)
 * All functions take a normalized time value t (0-1) and return an eased value (0-1)
 */

export type EasingFunction = (t: number) => number;

// Constants for specific easing calculations
const PI = Math.PI;
const c1 = 1.70158;
const c2 = c1 * 1.525;
const c3 = c1 + 1;
const c4 = (2 * PI) / 3;
const c5 = (2 * PI) / 4.5;

/**
 * All available easing functions
 */
export const easings = {
  // Linear - no easing
  linear: (t: number): number => t,

  // Sine easing
  easeInSine: (t: number): number => 1 - Math.cos((t * PI) / 2),
  easeOutSine: (t: number): number => Math.sin((t * PI) / 2),
  easeInOutSine: (t: number): number => -(Math.cos(PI * t) - 1) / 2,

  // Quad (power of 2)
  easeInQuad: (t: number): number => t * t,
  easeOutQuad: (t: number): number => 1 - (1 - t) * (1 - t),
  easeInOutQuad: (t: number): number =>
    t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2,

  // Cubic (power of 3)
  easeInCubic: (t: number): number => t * t * t,
  easeOutCubic: (t: number): number => 1 - Math.pow(1 - t, 3),
  easeInOutCubic: (t: number): number =>
    t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2,

  // Quart (power of 4)
  easeInQuart: (t: number): number => t * t * t * t,
  easeOutQuart: (t: number): number => 1 - Math.pow(1 - t, 4),
  easeInOutQuart: (t: number): number =>
    t < 0.5 ? 8 * t * t * t * t : 1 - Math.pow(-2 * t + 2, 4) / 2,

  // Quint (power of 5)
  easeInQuint: (t: number): number => t * t * t * t * t,
  easeOutQuint: (t: number): number => 1 - Math.pow(1 - t, 5),
  easeInOutQuint: (t: number): number =>
    t < 0.5 ? 16 * t * t * t * t * t : 1 - Math.pow(-2 * t + 2, 5) / 2,

  // Expo (exponential)
  easeInExpo: (t: number): number =>
    t === 0 ? 0 : Math.pow(2, 10 * t - 10),
  easeOutExpo: (t: number): number =>
    t === 1 ? 1 : 1 - Math.pow(2, -10 * t),
  easeInOutExpo: (t: number): number => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    if (t < 0.5) return Math.pow(2, 20 * t - 10) / 2;
    return (2 - Math.pow(2, -20 * t + 10)) / 2;
  },

  // Circ (circular)
  easeInCirc: (t: number): number => 1 - Math.sqrt(1 - Math.pow(t, 2)),
  easeOutCirc: (t: number): number => Math.sqrt(1 - Math.pow(t - 1, 2)),
  easeInOutCirc: (t: number): number =>
    t < 0.5
      ? (1 - Math.sqrt(1 - Math.pow(2 * t, 2))) / 2
      : (Math.sqrt(1 - Math.pow(-2 * t + 2, 2)) + 1) / 2,

  // Back (overshoot)
  easeInBack: (t: number): number => c3 * t * t * t - c1 * t * t,
  easeOutBack: (t: number): number =>
    1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2),
  easeInOutBack: (t: number): number =>
    t < 0.5
      ? (Math.pow(2 * t, 2) * ((c2 + 1) * 2 * t - c2)) / 2
      : (Math.pow(2 * t - 2, 2) * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2,

  // Elastic
  easeInElastic: (t: number): number => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return -Math.pow(2, 10 * t - 10) * Math.sin((t * 10 - 10.75) * c4);
  },
  easeOutElastic: (t: number): number => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
  },
  easeInOutElastic: (t: number): number => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    if (t < 0.5) {
      return -(Math.pow(2, 20 * t - 10) * Math.sin((20 * t - 11.125) * c5)) / 2;
    }
    return (Math.pow(2, -20 * t + 10) * Math.sin((20 * t - 11.125) * c5)) / 2 + 1;
  },

  // Bounce
  easeOutBounce: (t: number): number => {
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
  easeInBounce: (t: number): number => 1 - easings.easeOutBounce(1 - t),
  easeInOutBounce: (t: number): number =>
    t < 0.5
      ? (1 - easings.easeOutBounce(1 - 2 * t)) / 2
      : (1 + easings.easeOutBounce(2 * t - 1)) / 2,
} as const;

/**
 * Type representing all valid easing names
 */
export type EasingName = keyof typeof easings;

/**
 * List of all easing names for UI dropdowns
 */
export const easingNames: EasingName[] = Object.keys(easings) as EasingName[];

/**
 * Grouped easing names for organized UI display
 */
export const easingGroups = {
  'Linear': ['linear'] as EasingName[],
  'Sine': ['easeInSine', 'easeOutSine', 'easeInOutSine'] as EasingName[],
  'Quad': ['easeInQuad', 'easeOutQuad', 'easeInOutQuad'] as EasingName[],
  'Cubic': ['easeInCubic', 'easeOutCubic', 'easeInOutCubic'] as EasingName[],
  'Quart': ['easeInQuart', 'easeOutQuart', 'easeInOutQuart'] as EasingName[],
  'Quint': ['easeInQuint', 'easeOutQuint', 'easeInOutQuint'] as EasingName[],
  'Expo': ['easeInExpo', 'easeOutExpo', 'easeInOutExpo'] as EasingName[],
  'Circ': ['easeInCirc', 'easeOutCirc', 'easeInOutCirc'] as EasingName[],
  'Back': ['easeInBack', 'easeOutBack', 'easeInOutBack'] as EasingName[],
  'Elastic': ['easeInElastic', 'easeOutElastic', 'easeInOutElastic'] as EasingName[],
  'Bounce': ['easeInBounce', 'easeOutBounce', 'easeInOutBounce'] as EasingName[],
} as const;

/**
 * Get an easing function by name
 * Returns linear if the name is not found
 */
export function getEasing(name: string): EasingFunction {
  if (name in easings) {
    return easings[name as EasingName];
  }
  // Fallback to linear for unknown easings
  return easings.linear;
}

/**
 * Apply easing to a value
 * @param t - Normalized time (0-1)
 * @param easingName - Name of the easing function
 * @returns Eased value (0-1)
 */
export function applyEasing(t: number, easingName: string = 'linear'): number {
  const easingFn = getEasing(easingName);
  return easingFn(Math.max(0, Math.min(1, t)));
}

/**
 * Interpolate a value with easing
 * @param start - Start value
 * @param end - End value
 * @param t - Normalized time (0-1)
 * @param easingName - Name of the easing function
 * @returns Interpolated value
 */
export function interpolateWithEasing(
  start: number,
  end: number,
  t: number,
  easingName: string = 'linear'
): number {
  const easedT = applyEasing(t, easingName);
  return start + (end - start) * easedT;
}
