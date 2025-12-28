/**
 * Easing Functions Module
 *
 * Complete set of easing functions for animation interpolation.
 * Includes Penner easing functions, CSS cubic-bezier, and named presets.
 *
 * All functions validate input and return safe values for NaN/Infinity.
 */

// ============================================================================
// EASING FUNCTIONS - Complete Set
// ============================================================================

/**
 * Standard easing types (matches CSS/Penner)
 */
export type EasingFunction = (t: number) => number;

/**
 * Normalize easing input: clamp to [0,1] range, return 0 for invalid
 */
function normalizeT(t: number): number {
  if (!Number.isFinite(t)) return 0;
  return Math.max(0, Math.min(1, t));
}

// Sine easing
export const easeInSine: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.cos((t * Math.PI) / 2);
};
export const easeOutSine: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return Math.sin((t * Math.PI) / 2);
};
export const easeInOutSine: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return -(Math.cos(Math.PI * t) - 1) / 2;
};

// Quad easing
export const easeInQuad: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t * t;
};
export const easeOutQuad: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - (1 - t) * (1 - t);
};
export const easeInOutQuad: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
};

// Cubic easing
export const easeInCubic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t;
};
export const easeOutCubic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.pow(1 - t, 3);
};
export const easeInOutCubic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
};

// Quart easing
export const easeInQuart: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t * t;
};
export const easeOutQuart: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.pow(1 - t, 4);
};
export const easeInOutQuart: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 8 * t * t * t * t : 1 - Math.pow(-2 * t + 2, 4) / 2;
};

// Quint easing
export const easeInQuint: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t * t * t;
};
export const easeOutQuint: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.pow(1 - t, 5);
};
export const easeInOutQuint: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 16 * t * t * t * t * t : 1 - Math.pow(-2 * t + 2, 5) / 2;
};

// Expo easing
export const easeInExpo: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : Math.pow(2, 10 * t - 10);
};
export const easeOutExpo: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 1 ? 1 : 1 - Math.pow(2, -10 * t);
};
export const easeInOutExpo: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 :
    t < 0.5 ? Math.pow(2, 20 * t - 10) / 2 : (2 - Math.pow(2, -20 * t + 10)) / 2;
};

// Circ easing
export const easeInCirc: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.sqrt(1 - t * t);
};
export const easeOutCirc: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return Math.sqrt(1 - (t - 1) * (t - 1));
};
export const easeInOutCirc: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5
    ? (1 - Math.sqrt(1 - Math.pow(2 * t, 2))) / 2
    : (Math.sqrt(1 - Math.pow(-2 * t + 2, 2)) + 1) / 2;
};

// Back easing (with overshoot)
const c1 = 1.70158;
const c2 = c1 * 1.525;
const c3 = c1 + 1;

export const easeInBack: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return c3 * t * t * t - c1 * t * t;
};
export const easeOutBack: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
};
export const easeInOutBack: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5
    ? (Math.pow(2 * t, 2) * ((c2 + 1) * 2 * t - c2)) / 2
    : (Math.pow(2 * t - 2, 2) * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2;
};

// Elastic easing
const c4 = (2 * Math.PI) / 3;
const c5 = (2 * Math.PI) / 4.5;

export const easeInElastic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 :
    -Math.pow(2, 10 * t - 10) * Math.sin((t * 10 - 10.75) * c4);
};
export const easeOutElastic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 :
    Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
};
export const easeInOutElastic: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 :
    t < 0.5
      ? -(Math.pow(2, 20 * t - 10) * Math.sin((20 * t - 11.125) * c5)) / 2
      : (Math.pow(2, -20 * t + 10) * Math.sin((20 * t - 11.125) * c5)) / 2 + 1;
};

// Bounce easing (internal helper without normalization - called by normalized wrappers)
function bounceOut(t: number): number {
  const n1 = 7.5625;
  const d1 = 2.75;

  if (t < 1 / d1) {
    return n1 * t * t;
  } else if (t < 2 / d1) {
    const adjusted = t - 1.5 / d1;
    return n1 * adjusted * adjusted + 0.75;
  } else if (t < 2.5 / d1) {
    const adjusted = t - 2.25 / d1;
    return n1 * adjusted * adjusted + 0.9375;
  } else {
    const adjusted = t - 2.625 / d1;
    return n1 * adjusted * adjusted + 0.984375;
  }
}

export const easeOutBounce: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return bounceOut(t);
};
export const easeInBounce: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - bounceOut(1 - t);
};
export const easeInOutBounce: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5
    ? (1 - bounceOut(1 - 2 * t)) / 2
    : (1 + bounceOut(2 * t - 1)) / 2;
};

// Linear (no easing)
export const linear: EasingFunction = (rawT) => {
  const t = normalizeT(rawT);
  return t;
};

// Step functions
export const stepStart: EasingFunction = (rawT) => {
  if (!Number.isFinite(rawT)) return 0;
  return rawT <= 0 ? 0 : 1;
};
export const stepEnd: EasingFunction = (rawT) => {
  if (!Number.isFinite(rawT)) return 0;
  return rawT >= 1 ? 1 : 0;
};

// ============================================================================
// CUBIC BEZIER
// ============================================================================

/**
 * Cubic bezier easing (CSS-style)
 * Control points are clamped to valid ranges to prevent NaN propagation.
 */
export function cubicBezier(x1: number, y1: number, x2: number, y2: number): EasingFunction {
  // Validate and clamp control points (CSS spec: x values must be in [0,1])
  const safeX1 = Number.isFinite(x1) ? Math.max(0, Math.min(1, x1)) : 0;
  const safeY1 = Number.isFinite(y1) ? y1 : 0;
  const safeX2 = Number.isFinite(x2) ? Math.max(0, Math.min(1, x2)) : 1;
  const safeY2 = Number.isFinite(y2) ? y2 : 1;

  const epsilon = 1e-6;

  return (rawX: number): number => {
    const x = normalizeT(rawX);
    if (x <= 0) return 0;
    if (x >= 1) return 1;

    // Newton-Raphson iteration for finding t given x
    let t = x;
    for (let i = 0; i < 8; i++) {
      const currentX = bezierPoint(t, safeX1, safeX2);
      const diff = currentX - x;
      if (Math.abs(diff) < epsilon) break;

      const derivative = bezierDerivative(t, safeX1, safeX2);
      if (Math.abs(derivative) < epsilon) break;

      t -= diff / derivative;
      t = Math.max(0, Math.min(1, t));
    }

    return bezierPoint(t, safeY1, safeY2);
  };
}

function bezierPoint(t: number, p1: number, p2: number): number {
  // B(t) = 3(1-t)²t*p1 + 3(1-t)t²*p2 + t³
  const mt = 1 - t;
  return 3 * mt * mt * t * p1 + 3 * mt * t * t * p2 + t * t * t;
}

function bezierDerivative(t: number, p1: number, p2: number): number {
  // B'(t) = 3(1-t)²*p1 + 6(1-t)t*(p2-p1) + 3t²*(1-p2)
  const mt = 1 - t;
  return 3 * mt * mt * p1 + 6 * mt * t * (p2 - p1) + 3 * t * t * (1 - p2);
}

// ============================================================================
// EASING MAP
// ============================================================================

export const EASING_FUNCTIONS: Record<string, EasingFunction> = {
  // Linear
  linear,

  // Sine
  easeInSine, easeOutSine, easeInOutSine,

  // Quad
  easeInQuad, easeOutQuad, easeInOutQuad,

  // Cubic
  easeInCubic, easeOutCubic, easeInOutCubic,

  // Quart
  easeInQuart, easeOutQuart, easeInOutQuart,

  // Quint
  easeInQuint, easeOutQuint, easeInOutQuint,

  // Expo
  easeInExpo, easeOutExpo, easeInOutExpo,

  // Circ
  easeInCirc, easeOutCirc, easeInOutCirc,

  // Back
  easeInBack, easeOutBack, easeInOutBack,

  // Elastic
  easeInElastic, easeOutElastic, easeInOutElastic,

  // Bounce
  easeInBounce, easeOutBounce, easeInOutBounce,

  // Step
  stepStart, stepEnd,
};

/**
 * Get easing function by name
 */
export function getEasingFunction(name: string): EasingFunction {
  return EASING_FUNCTIONS[name] || linear;
}

// ============================================================================
// EASING PRESETS (Named curves for motion design)
// ============================================================================

export const EASING_PRESETS: Record<string, { fn: EasingFunction; description: string }> = {
  // Standard ease presets (industry standard curves)
  'easyEase': {
    fn: cubicBezier(0.42, 0, 0.58, 1),
    description: 'Standard easy ease - smooth start and end',
  },
  'easyEaseIn': {
    fn: cubicBezier(0.42, 0, 1, 1),
    description: 'Easy ease in - gradual acceleration',
  },
  'easyEaseOut': {
    fn: cubicBezier(0, 0, 0.58, 1),
    description: 'Easy ease out - gradual deceleration',
  },

  // Flow-style presets (smooth motion design)
  'smooth': {
    fn: cubicBezier(0.4, 0, 0.2, 1),
    description: 'Material Design smooth curve',
  },
  'smoothIn': {
    fn: cubicBezier(0.4, 0, 1, 1),
    description: 'Material Design ease in',
  },
  'smoothOut': {
    fn: cubicBezier(0, 0, 0.2, 1),
    description: 'Material Design ease out',
  },

  // Snappy motion
  'snappy': {
    fn: cubicBezier(0.5, 0, 0.1, 1),
    description: 'Quick and snappy - fast start, smooth end',
  },
  'snappyIn': {
    fn: cubicBezier(0.7, 0, 1, 1),
    description: 'Snappy ease in',
  },
  'snappyOut': {
    fn: cubicBezier(0, 0, 0.1, 1),
    description: 'Snappy ease out',
  },

  // Anticipation
  'anticipate': {
    fn: cubicBezier(0.36, 0, 0.66, -0.56),
    description: 'Slight pullback before motion',
  },
  'overshoot': {
    fn: cubicBezier(0.34, 1.56, 0.64, 1),
    description: 'Goes past target then settles',
  },
  'anticipateOvershoot': {
    fn: (rawT) => {
      const t = normalizeT(rawT);
      const s = 1.70158 * 1.525;
      if (t < 0.5) {
        return (Math.pow(2 * t, 2) * ((s + 1) * 2 * t - s)) / 2;
      }
      return (Math.pow(2 * t - 2, 2) * ((s + 1) * (t * 2 - 2) + s) + 2) / 2;
    },
    description: 'Pull back then overshoot',
  },

  // Dramatic
  'dramatic': {
    fn: cubicBezier(0.6, 0.04, 0.98, 0.335),
    description: 'Dramatic acceleration',
  },
  'dramaticIn': {
    fn: cubicBezier(0.55, 0.085, 0.68, 0.53),
    description: 'Dramatic ease in',
  },
  'dramaticOut': {
    fn: cubicBezier(0.25, 0.46, 0.45, 0.94),
    description: 'Dramatic ease out',
  },

  // Physical/Spring-like
  'spring': {
    fn: (rawT) => {
      const t = normalizeT(rawT);
      const freq = 4.5;
      const decay = 4;
      return 1 - Math.exp(-decay * t) * Math.cos(freq * Math.PI * t);
    },
    description: 'Spring physics - oscillating settle',
  },
  'springLight': {
    fn: (rawT) => {
      const t = normalizeT(rawT);
      const freq = 3;
      const decay = 3;
      return 1 - Math.exp(-decay * t) * Math.cos(freq * Math.PI * t);
    },
    description: 'Light spring - gentle oscillation',
  },
  'springHeavy': {
    fn: (rawT) => {
      const t = normalizeT(rawT);
      const freq = 6;
      const decay = 5;
      return 1 - Math.exp(-decay * t) * Math.cos(freq * Math.PI * t);
    },
    description: 'Heavy spring - quick damped oscillation',
  },

  // UI-specific
  'uiEnter': {
    fn: cubicBezier(0, 0, 0.2, 1),
    description: 'UI element entering view',
  },
  'uiExit': {
    fn: cubicBezier(0.4, 0, 1, 1),
    description: 'UI element leaving view',
  },
  'uiStandard': {
    fn: cubicBezier(0.4, 0, 0.2, 1),
    description: 'Standard UI transition',
  },

  // Lottie-style
  'lottieSmooth': {
    fn: cubicBezier(0.33, 0, 0.67, 1),
    description: 'Lottie smooth interpolation',
  },
  'lottieSnap': {
    fn: cubicBezier(0.5, 0, 0, 1),
    description: 'Lottie snap animation',
  },
};
