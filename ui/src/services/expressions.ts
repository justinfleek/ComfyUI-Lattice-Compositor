/**
 * Expression System - Comprehensive Animation Expressions
 *
 * Full expression engine supporting:
 * - All standard easing functions (Penner easing, CSS cubic-bezier)
 * - Motion expressions (inertia, bounce, elastic, overshoot)
 * - Loop expressions (repeatBefore, repeatAfter, pingpong, cycle)
 * - Jitter and noise functions
 * - Time and math functions
 * - Property references and linking
 * - Data-driven animation (JSON)
 */

import type { AnimatableProperty, Keyframe, InterpolationType } from '@/types/project';

// ============================================================================
// EXPRESSION CONTEXT
// ============================================================================

export interface ExpressionContext {
  // Time
  time: number;           // Current time in seconds
  frame: number;          // Current frame number
  fps: number;            // Frames per second
  duration: number;       // Composition duration

  // Layer info
  layerId: string;
  layerIndex: number;
  layerName: string;
  inPoint: number;        // Layer start time
  outPoint: number;       // Layer end time

  // Property info
  propertyName: string;
  value: number | number[];  // Current interpolated value
  velocity: number | number[];  // Current velocity

  // Keyframe info
  numKeys: number;
  keyframes: Keyframe<any>[];

  // External data (JSON-driven)
  data?: Record<string, any>;

  // Other layer properties (for linking)
  getLayerProperty?: (layerId: string, propertyPath: string) => number | number[] | null;
}

// ============================================================================
// EASING FUNCTIONS - Complete Set
// ============================================================================

/**
 * Standard easing types (matches CSS/Penner)
 */
export type EasingFunction = (t: number) => number;

// Sine easing
export const easeInSine: EasingFunction = (t) => 1 - Math.cos((t * Math.PI) / 2);
export const easeOutSine: EasingFunction = (t) => Math.sin((t * Math.PI) / 2);
export const easeInOutSine: EasingFunction = (t) => -(Math.cos(Math.PI * t) - 1) / 2;

// Quad easing
export const easeInQuad: EasingFunction = (t) => t * t;
export const easeOutQuad: EasingFunction = (t) => 1 - (1 - t) * (1 - t);
export const easeInOutQuad: EasingFunction = (t) =>
  t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;

// Cubic easing
export const easeInCubic: EasingFunction = (t) => t * t * t;
export const easeOutCubic: EasingFunction = (t) => 1 - Math.pow(1 - t, 3);
export const easeInOutCubic: EasingFunction = (t) =>
  t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;

// Quart easing
export const easeInQuart: EasingFunction = (t) => t * t * t * t;
export const easeOutQuart: EasingFunction = (t) => 1 - Math.pow(1 - t, 4);
export const easeInOutQuart: EasingFunction = (t) =>
  t < 0.5 ? 8 * t * t * t * t : 1 - Math.pow(-2 * t + 2, 4) / 2;

// Quint easing
export const easeInQuint: EasingFunction = (t) => t * t * t * t * t;
export const easeOutQuint: EasingFunction = (t) => 1 - Math.pow(1 - t, 5);
export const easeInOutQuint: EasingFunction = (t) =>
  t < 0.5 ? 16 * t * t * t * t * t : 1 - Math.pow(-2 * t + 2, 5) / 2;

// Expo easing
export const easeInExpo: EasingFunction = (t) =>
  t === 0 ? 0 : Math.pow(2, 10 * t - 10);
export const easeOutExpo: EasingFunction = (t) =>
  t === 1 ? 1 : 1 - Math.pow(2, -10 * t);
export const easeInOutExpo: EasingFunction = (t) =>
  t === 0 ? 0 : t === 1 ? 1 :
  t < 0.5 ? Math.pow(2, 20 * t - 10) / 2 : (2 - Math.pow(2, -20 * t + 10)) / 2;

// Circ easing
export const easeInCirc: EasingFunction = (t) => 1 - Math.sqrt(1 - Math.pow(t, 2));
export const easeOutCirc: EasingFunction = (t) => Math.sqrt(1 - Math.pow(t - 1, 2));
export const easeInOutCirc: EasingFunction = (t) =>
  t < 0.5
    ? (1 - Math.sqrt(1 - Math.pow(2 * t, 2))) / 2
    : (Math.sqrt(1 - Math.pow(-2 * t + 2, 2)) + 1) / 2;

// Back easing (with overshoot)
const c1 = 1.70158;
const c2 = c1 * 1.525;
const c3 = c1 + 1;

export const easeInBack: EasingFunction = (t) => c3 * t * t * t - c1 * t * t;
export const easeOutBack: EasingFunction = (t) =>
  1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
export const easeInOutBack: EasingFunction = (t) =>
  t < 0.5
    ? (Math.pow(2 * t, 2) * ((c2 + 1) * 2 * t - c2)) / 2
    : (Math.pow(2 * t - 2, 2) * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2;

// Elastic easing
const c4 = (2 * Math.PI) / 3;
const c5 = (2 * Math.PI) / 4.5;

export const easeInElastic: EasingFunction = (t) =>
  t === 0 ? 0 : t === 1 ? 1 :
  -Math.pow(2, 10 * t - 10) * Math.sin((t * 10 - 10.75) * c4);
export const easeOutElastic: EasingFunction = (t) =>
  t === 0 ? 0 : t === 1 ? 1 :
  Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
export const easeInOutElastic: EasingFunction = (t) =>
  t === 0 ? 0 : t === 1 ? 1 :
  t < 0.5
    ? -(Math.pow(2, 20 * t - 10) * Math.sin((20 * t - 11.125) * c5)) / 2
    : (Math.pow(2, -20 * t + 10) * Math.sin((20 * t - 11.125) * c5)) / 2 + 1;

// Bounce easing
export const easeOutBounce: EasingFunction = (t) => {
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
};
export const easeInBounce: EasingFunction = (t) => 1 - easeOutBounce(1 - t);
export const easeInOutBounce: EasingFunction = (t) =>
  t < 0.5
    ? (1 - easeOutBounce(1 - 2 * t)) / 2
    : (1 + easeOutBounce(2 * t - 1)) / 2;

// Linear (no easing)
export const linear: EasingFunction = (t) => t;

// Step functions
export const stepStart: EasingFunction = (t) => t === 0 ? 0 : 1;
export const stepEnd: EasingFunction = (t) => t === 1 ? 1 : 0;

/**
 * Cubic bezier easing (CSS-style)
 */
export function cubicBezier(x1: number, y1: number, x2: number, y2: number): EasingFunction {
  // Newton-Raphson iteration for finding t given x
  const epsilon = 1e-6;

  return (x: number): number => {
    if (x <= 0) return 0;
    if (x >= 1) return 1;

    // Binary search for t
    let t = x;
    for (let i = 0; i < 8; i++) {
      const currentX = bezierPoint(t, x1, x2);
      const diff = currentX - x;
      if (Math.abs(diff) < epsilon) break;

      const derivative = bezierDerivative(t, x1, x2);
      if (Math.abs(derivative) < epsilon) break;

      t -= diff / derivative;
      t = Math.max(0, Math.min(1, t));
    }

    return bezierPoint(t, y1, y2);
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
    fn: (t) => {
      // Combine anticipation and overshoot
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
    fn: (t) => {
      const freq = 4.5;
      const decay = 4;
      return 1 - Math.exp(-decay * t) * Math.cos(freq * Math.PI * t);
    },
    description: 'Spring physics - oscillating settle',
  },
  'springLight': {
    fn: (t) => {
      const freq = 3;
      const decay = 3;
      return 1 - Math.exp(-decay * t) * Math.cos(freq * Math.PI * t);
    },
    description: 'Light spring - gentle oscillation',
  },
  'springHeavy': {
    fn: (t) => {
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

// ============================================================================
// MOTION EXPRESSIONS
// ============================================================================

/**
 * Inertia/Overshoot expression
 * Creates momentum-based animation after keyframes
 */
export function inertia(
  ctx: ExpressionContext,
  amplitude: number = 0.1,
  frequency: number = 2.0,
  decay: number = 2.0
): number | number[] {
  const { time, keyframes, value, velocity } = ctx;

  if (keyframes.length === 0) return value;

  // Find nearest keyframe before current time
  const fps = ctx.fps || 30;
  const currentFrame = time * fps;

  let nearestKey: Keyframe<any> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      nearestKey = keyframes[i];
      break;
    }
  }

  if (!nearestKey) return value;

  const keyTime = nearestKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  // Calculate velocity at keyframe
  const vel = typeof velocity === 'number' ? velocity : velocity[0];
  const val = typeof value === 'number' ? value : value[0];

  const oscillation = vel * amplitude * Math.sin(frequency * t * 2 * Math.PI) / Math.exp(decay * t);

  if (typeof value === 'number') {
    return val + oscillation;
  }
  // For arrays, apply to all components
  return (value as number[]).map((v, i) => {
    const componentVel = (velocity as number[])[i] || 0;
    return v + componentVel * amplitude * Math.sin(frequency * t * 2 * Math.PI) / Math.exp(decay * t);
  });
}

/**
 * Bounce expression
 * Creates bouncing settle after keyframes
 */
export function bounce(
  ctx: ExpressionContext,
  elasticity: number = 0.7,
  gravity: number = 4000
): number | number[] {
  const { time, keyframes, value } = ctx;

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 30;
  const currentFrame = time * fps;

  // Find last keyframe
  let lastKey: Keyframe<any> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }

  if (!lastKey) return value;

  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  // Bounce physics
  let bounceTime = t;
  let bounceHeight = 1;
  let totalBounces = 0;
  const maxBounces = 10;

  // Calculate which bounce we're in
  while (bounceTime > 0 && totalBounces < maxBounces) {
    const bounceDuration = Math.sqrt(2 * bounceHeight / gravity);
    if (bounceTime < bounceDuration * 2) {
      break;
    }
    bounceTime -= bounceDuration * 2;
    bounceHeight *= elasticity * elasticity;
    totalBounces++;
  }

  // Position within current bounce
  const bounceDuration = Math.sqrt(2 * bounceHeight / gravity);
  const bounceT = bounceTime / (bounceDuration * 2);
  const bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT);

  if (typeof value === 'number') {
    return value - bounceOffset * (1 - elasticity);
  }

  return (value as number[]).map((v) => v - bounceOffset * (1 - elasticity));
}

/**
 * Elastic expression
 * Creates elastic spring-like motion
 */
export function elastic(
  ctx: ExpressionContext,
  amplitude: number = 1,
  period: number = 0.3
): number | number[] {
  const { time, keyframes, value } = ctx;

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 30;
  const currentFrame = time * fps;

  let lastKey: Keyframe<any> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }

  if (!lastKey) return value;

  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  const s = period / 4;
  const decay = Math.pow(2, -10 * t);
  const oscillation = decay * Math.sin((t - s) * (2 * Math.PI) / period);

  if (typeof value === 'number') {
    return value + amplitude * oscillation;
  }

  return (value as number[]).map((v) => v + amplitude * oscillation);
}

// ============================================================================
// LOOP EXPRESSIONS
// ============================================================================

export type LoopType = 'cycle' | 'pingpong' | 'offset' | 'continue';

/**
 * Repeat After expression
 * Repeats animation after last keyframe
 */
export function repeatAfter(
  ctx: ExpressionContext,
  type: LoopType = 'cycle',
  numKeyframes: number = 0
): number | number[] {
  const { time, keyframes, fps } = ctx;

  if (keyframes.length < 2) return ctx.value;

  const startIdx = numKeyframes > 0 ? Math.max(0, keyframes.length - numKeyframes) : 0;
  const startKey = keyframes[startIdx];
  const endKey = keyframes[keyframes.length - 1];

  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;

  if (duration <= 0 || time <= endTime) return ctx.value;

  const elapsed = time - endTime;

  switch (type) {
    case 'cycle': {
      // Repeat from start
      const cycleTime = startTime + (elapsed % duration);
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'pingpong': {
      // Alternate forward/backward
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = (elapsed % duration) / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? 1 - cycleProgress : cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'offset': {
      // Add cumulative offset each cycle
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = startTime + (elapsed % duration);
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(endKey.value, startKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case 'continue': {
      // Continue at last velocity
      const velocity = ctx.velocity;
      if (typeof velocity === 'number') {
        return (ctx.value as number) + velocity * elapsed;
      }
      return (ctx.value as number[]).map((v, i) => v + (velocity as number[])[i] * elapsed);
    }
  }
}

/**
 * Repeat Before expression
 * Repeats animation before first keyframe
 */
export function repeatBefore(
  ctx: ExpressionContext,
  type: LoopType = 'cycle',
  numKeyframes: number = 0
): number | number[] {
  const { time, keyframes, fps } = ctx;

  if (keyframes.length < 2) return ctx.value;

  const endIdx = numKeyframes > 0 ? Math.min(keyframes.length - 1, numKeyframes - 1) : keyframes.length - 1;
  const startKey = keyframes[0];
  const endKey = keyframes[endIdx];

  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;

  if (duration <= 0 || time >= startTime) return ctx.value;

  const elapsed = startTime - time;

  switch (type) {
    case 'cycle': {
      const cycleTime = endTime - (elapsed % duration);
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'pingpong': {
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = (elapsed % duration) / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? cycleProgress : 1 - cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'offset': {
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = endTime - (elapsed % duration);
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(startKey.value, endKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case 'continue': {
      const velocity = ctx.velocity;
      if (typeof velocity === 'number') {
        return (ctx.value as number) - velocity * elapsed;
      }
      return (ctx.value as number[]).map((v, i) => v - (velocity as number[])[i] * elapsed);
    }
  }
}

// ============================================================================
// JITTER EXPRESSION
// ============================================================================

/**
 * Jitter expression
 * Adds random noise to value
 */
export function jitter(
  ctx: ExpressionContext,
  frequency: number = 5,
  amplitude: number = 50,
  octaves: number = 1,
  amplitudeMultiplier: number = 0.5,
  time?: number
): number | number[] {
  const t = time ?? ctx.time;
  const { value } = ctx;

  // Simple noise implementation
  const noise = (seed: number, t: number): number => {
    // Combine multiple sine waves for pseudo-noise
    let result = 0;
    let amp = 1;
    let freq = 1;

    for (let i = 0; i < octaves; i++) {
      result += amp * Math.sin(t * frequency * freq * Math.PI * 2 + seed * 1000);
      result += amp * 0.5 * Math.sin(t * frequency * freq * Math.PI * 2 * 1.5 + seed * 500);
      amp *= amplitudeMultiplier;
      freq *= 2;
    }

    return result / (1 + (octaves - 1) * amplitudeMultiplier);
  };

  if (typeof value === 'number') {
    return value + noise(0, t) * amplitude;
  }

  // For arrays, use different seeds for each component
  return (value as number[]).map((v, i) => v + noise(i, t) * amplitude);
}

/**
 * Smooth jitter with temporal correlation
 */
export function temporalJitter(
  ctx: ExpressionContext,
  frequency: number = 5,
  amplitude: number = 50,
  octaves: number = 1,
  time?: number
): number | number[] {
  const t = time ?? ctx.time;

  // Use interpolated noise for smoother results
  const smoothNoise = (seed: number, t: number): number => {
    const period = 1 / frequency;
    const index = Math.floor(t / period);
    const frac = (t / period) - index;

    // Generate deterministic random values
    const rand = (n: number) => {
      const x = Math.sin(n * 12.9898 + seed * 78.233) * 43758.5453;
      return x - Math.floor(x);
    };

    // Cubic interpolation between random values
    const v0 = rand(index - 1) * 2 - 1;
    const v1 = rand(index) * 2 - 1;
    const v2 = rand(index + 1) * 2 - 1;
    const v3 = rand(index + 2) * 2 - 1;

    // Catmull-Rom interpolation
    const t2 = frac * frac;
    const t3 = t2 * frac;

    return 0.5 * (
      (2 * v1) +
      (-v0 + v2) * frac +
      (2 * v0 - 5 * v1 + 4 * v2 - v3) * t2 +
      (-v0 + 3 * v1 - 3 * v2 + v3) * t3
    );
  };

  const { value } = ctx;

  if (typeof value === 'number') {
    let result = 0;
    let amp = amplitude;
    let freq = frequency;
    for (let i = 0; i < octaves; i++) {
      result += smoothNoise(i * 100, t * freq / frequency) * amp;
      amp *= 0.5;
      freq *= 2;
    }
    return value + result;
  }

  return (value as number[]).map((v, idx) => {
    let result = 0;
    let amp = amplitude;
    let freq = frequency;
    for (let i = 0; i < octaves; i++) {
      result += smoothNoise(idx * 100 + i * 1000, t * freq / frequency) * amp;
      amp *= 0.5;
      freq *= 2;
    }
    return v + result;
  });
}

// ============================================================================
// TIME EXPRESSIONS
// ============================================================================

/**
 * Time-based expressions
 */
export const timeExpressions = {
  /**
   * Linear time ramp
   */
  timeRamp(startTime: number, endTime: number, startValue: number, endValue: number, time: number): number {
    if (time <= startTime) return startValue;
    if (time >= endTime) return endValue;
    const t = (time - startTime) / (endTime - startTime);
    return startValue + (endValue - startValue) * t;
  },

  /**
   * Periodic function (loops every period seconds)
   */
  periodic(time: number, period: number): number {
    return (time % period) / period;
  },

  /**
   * Sawtooth wave
   */
  sawtooth(time: number, frequency: number, amplitude: number = 1): number {
    const t = time * frequency;
    return amplitude * 2 * (t - Math.floor(t + 0.5));
  },

  /**
   * Triangle wave
   */
  triangle(time: number, frequency: number, amplitude: number = 1): number {
    const t = time * frequency;
    return amplitude * (2 * Math.abs(2 * (t - Math.floor(t + 0.5))) - 1);
  },

  /**
   * Square wave
   */
  square(time: number, frequency: number, amplitude: number = 1): number {
    const t = time * frequency;
    return amplitude * (t - Math.floor(t) < 0.5 ? 1 : -1);
  },

  /**
   * Sine wave
   */
  sine(time: number, frequency: number, amplitude: number = 1, phase: number = 0): number {
    return amplitude * Math.sin(2 * Math.PI * frequency * time + phase);
  },

  /**
   * Pulse (duty cycle controlled square)
   */
  pulse(time: number, frequency: number, dutyCycle: number = 0.5, amplitude: number = 1): number {
    const t = (time * frequency) % 1;
    return amplitude * (t < dutyCycle ? 1 : 0);
  },
};

// ============================================================================
// MATH EXPRESSIONS
// ============================================================================

export const mathExpressions = {
  /**
   * Linear interpolation
   */
  lerp(a: number, b: number, t: number): number {
    return a + (b - a) * t;
  },

  /**
   * Clamp value between min and max
   */
  clamp(value: number, min: number, max: number): number {
    return Math.min(max, Math.max(min, value));
  },

  /**
   * Map value from one range to another
   */
  map(value: number, inMin: number, inMax: number, outMin: number, outMax: number): number {
    return outMin + (outMax - outMin) * ((value - inMin) / (inMax - inMin));
  },

  /**
   * Normalized value (0-1) based on range
   */
  normalize(value: number, min: number, max: number): number {
    return (value - min) / (max - min);
  },

  /**
   * Smooth step (Hermite interpolation)
   */
  smoothstep(edge0: number, edge1: number, x: number): number {
    const t = mathExpressions.clamp((x - edge0) / (edge1 - edge0), 0, 1);
    return t * t * (3 - 2 * t);
  },

  /**
   * Smoother step (Ken Perlin's improved version)
   */
  smootherstep(edge0: number, edge1: number, x: number): number {
    const t = mathExpressions.clamp((x - edge0) / (edge1 - edge0), 0, 1);
    return t * t * t * (t * (t * 6 - 15) + 10);
  },

  /**
   * Modulo with support for negative numbers
   */
  mod(a: number, b: number): number {
    return ((a % b) + b) % b;
  },

  /**
   * Distance between two 2D points
   */
  distance(x1: number, y1: number, x2: number, y2: number): number {
    const dx = x2 - x1;
    const dy = y2 - y1;
    return Math.sqrt(dx * dx + dy * dy);
  },

  /**
   * Angle between two 2D points (in radians)
   */
  angleBetween(x1: number, y1: number, x2: number, y2: number): number {
    return Math.atan2(y2 - y1, x2 - x1);
  },

  /**
   * Convert degrees to radians
   */
  degreesToRadians(degrees: number): number {
    return degrees * Math.PI / 180;
  },

  /**
   * Convert radians to degrees
   */
  radiansToDegrees(radians: number): number {
    return radians * 180 / Math.PI;
  },

  /**
   * Random number with seed (deterministic)
   */
  seedRandom(seed: number, min: number = 0, max: number = 1): number {
    const x = Math.sin(seed * 12.9898) * 43758.5453;
    const rand = x - Math.floor(x);
    return min + rand * (max - min);
  },

  /**
   * Gaussian random (normal distribution)
   */
  gaussRandom(mean: number = 0, stdDev: number = 1): number {
    // Box-Muller transform
    const u1 = Math.random();
    const u2 = Math.random();
    const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
    return mean + z0 * stdDev;
  },
};

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

function interpolateAtTime(keyframes: Keyframe<any>[], time: number, fps: number): number | number[] {
  const frame = time * fps;

  // Find surrounding keyframes
  let before: Keyframe<any> | null = null;
  let after: Keyframe<any> | null = null;

  for (const kf of keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (!after) {
      after = kf;
      break;
    }
  }

  if (!before) return keyframes[0].value;
  if (!after) return before.value;

  const t = (frame - before.frame) / (after.frame - before.frame);
  const easedT = applyEasing(t, before.interpolation);

  return lerpValues(before.value, after.value, easedT);
}

function applyEasing(t: number, interpolation: InterpolationType): number {
  const fn = EASING_FUNCTIONS[interpolation];
  return fn ? fn(t) : t;
}

function lerpValues(a: any, b: any, t: number): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a + (b - a) * t;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + (b[i] - v) * t);
  }
  return a;
}

function subtractValues(a: any, b: any): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a - b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v - b[i]);
  }
  return 0;
}

function addValues(a: any, b: any): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a + b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + b[i]);
  }
  return a;
}

function scaleValue(v: any, s: number): number | number[] {
  if (typeof v === 'number') {
    return v * s;
  }
  if (Array.isArray(v)) {
    return v.map((x) => x * s);
  }
  return 0;
}

// ============================================================================
// EXPRESSION EVALUATOR
// ============================================================================

export interface Expression {
  type: 'preset' | 'function' | 'custom';
  name: string;
  params: Record<string, any>;
  enabled: boolean;
}

/**
 * Evaluate an expression on a property
 */
export function evaluateExpression(
  expression: Expression,
  ctx: ExpressionContext
): number | number[] {
  if (!expression.enabled) return ctx.value;

  switch (expression.type) {
    case 'preset':
      return evaluatePreset(expression.name, ctx, expression.params);
    case 'function':
      return evaluateFunction(expression.name, ctx, expression.params);
    default:
      return ctx.value;
  }
}

function evaluatePreset(name: string, ctx: ExpressionContext, params: Record<string, any>): number | number[] {
  switch (name) {
    case 'inertia':
      return inertia(ctx, params.amplitude, params.frequency, params.decay);
    case 'bounce':
      return bounce(ctx, params.elasticity, params.gravity);
    case 'elastic':
      return elastic(ctx, params.amplitude, params.period);
    case 'jitter':
      return jitter(ctx, params.frequency, params.amplitude, params.octaves);
    case 'repeatAfter':
      return repeatAfter(ctx, params.type, params.numKeyframes);
    case 'repeatBefore':
      return repeatBefore(ctx, params.type, params.numKeyframes);
    default:
      return ctx.value;
  }
}

function evaluateFunction(name: string, ctx: ExpressionContext, params: Record<string, any>): number | number[] {
  // Time functions
  if (name in timeExpressions) {
    const fn = (timeExpressions as any)[name];
    return fn(ctx.time, ...Object.values(params));
  }

  // Math functions
  if (name in mathExpressions) {
    const fn = (mathExpressions as any)[name];
    const val = typeof ctx.value === 'number' ? ctx.value : ctx.value[0];
    return fn(val, ...Object.values(params));
  }

  return ctx.value;
}

// ============================================================================
// EXPRESSION PRESETS
// ============================================================================

export const EXPRESSION_PRESETS: Record<string, Expression> = {
  // Motion presets
  inertiaLight: {
    type: 'preset',
    name: 'inertia',
    params: { amplitude: 0.05, frequency: 3, decay: 3 },
    enabled: true,
  },
  inertiaHeavy: {
    type: 'preset',
    name: 'inertia',
    params: { amplitude: 0.15, frequency: 1.5, decay: 1.5 },
    enabled: true,
  },
  bounceGentle: {
    type: 'preset',
    name: 'bounce',
    params: { elasticity: 0.6, gravity: 3000 },
    enabled: true,
  },
  bounceFirm: {
    type: 'preset',
    name: 'bounce',
    params: { elasticity: 0.8, gravity: 5000 },
    enabled: true,
  },
  elasticSnappy: {
    type: 'preset',
    name: 'elastic',
    params: { amplitude: 1, period: 0.2 },
    enabled: true,
  },
  elasticLoose: {
    type: 'preset',
    name: 'elastic',
    params: { amplitude: 1.5, period: 0.5 },
    enabled: true,
  },

  // Jitter presets
  jitterSubtle: {
    type: 'preset',
    name: 'jitter',
    params: { frequency: 2, amplitude: 10, octaves: 1 },
    enabled: true,
  },
  jitterModerate: {
    type: 'preset',
    name: 'jitter',
    params: { frequency: 4, amplitude: 30, octaves: 2 },
    enabled: true,
  },
  jitterIntense: {
    type: 'preset',
    name: 'jitter',
    params: { frequency: 8, amplitude: 50, octaves: 3 },
    enabled: true,
  },

  // Repeat presets
  repeatCycle: {
    type: 'preset',
    name: 'repeatAfter',
    params: { type: 'cycle', numKeyframes: 0 },
    enabled: true,
  },
  repeatPingpong: {
    type: 'preset',
    name: 'repeatAfter',
    params: { type: 'pingpong', numKeyframes: 0 },
    enabled: true,
  },
  repeatOffset: {
    type: 'preset',
    name: 'repeatAfter',
    params: { type: 'offset', numKeyframes: 0 },
    enabled: true,
  },
};

/**
 * Get an expression preset by name
 */
export function getExpressionPreset(name: string): Expression | null {
  return EXPRESSION_PRESETS[name] || null;
}

/**
 * List all expression presets
 */
export function listExpressionPresets(): string[] {
  return Object.keys(EXPRESSION_PRESETS);
}

/**
 * List all easing presets
 */
export function listEasingPresets(): string[] {
  return Object.keys(EASING_PRESETS);
}

// ============================================================================
// NAMESPACE EXPORTS (for index.ts and test compatibility)
// ============================================================================

/**
 * Easing namespace - all easing functions in one object
 */
export const easing = {
  linear,
  easeInQuad,
  easeOutQuad,
  easeInOutQuad,
  easeInCubic,
  easeOutCubic,
  easeInOutCubic,
  easeInQuart,
  easeOutQuart,
  easeInOutQuart,
  easeInQuint,
  easeOutQuint,
  easeInOutQuint,
  easeInSine,
  easeOutSine,
  easeInOutSine,
  easeInExpo,
  easeOutExpo,
  easeInOutExpo,
  easeInCirc,
  easeOutCirc,
  easeInOutCirc,
  easeInBack,
  easeOutBack,
  easeInOutBack,
  easeInElastic,
  easeOutElastic,
  easeInOutElastic,
  easeInBounce,
  easeOutBounce,
  easeInOutBounce,
  stepStart,
  stepEnd,
  cubicBezier,
};

/**
 * Motion namespace - motion expression functions
 */
export const motion = {
  inertia,
  bounce,
  elastic,
  jitter,
  temporalJitter,
};

/**
 * Loop namespace - loop expression functions
 */
export const loop = {
  repeatAfter,
  repeatBefore,
};

/**
 * Time namespace - time-based functions
 */
export const time = {
  timeRamp: timeExpressions.timeRamp,
  periodic: timeExpressions.periodic,
  sawtooth: timeExpressions.sawtooth,
  triangle: timeExpressions.triangle,
  square: timeExpressions.square,
  sine: timeExpressions.sine,
  pulse: timeExpressions.pulse,
};

/**
 * Math namespace - math utility functions
 */
export const math = {
  lerp: mathExpressions.lerp,
  clamp: mathExpressions.clamp,
  map: mathExpressions.map,
  normalize: mathExpressions.normalize,
  smoothstep: mathExpressions.smoothstep,
  smootherstep: mathExpressions.smootherstep,
  mod: mathExpressions.mod,
  distance: mathExpressions.distance,
  angleBetween: mathExpressions.angleBetween,
  degreesToRadians: mathExpressions.degreesToRadians,
  radiansToDegrees: mathExpressions.radiansToDegrees,
  seedRandom: mathExpressions.seedRandom,
  gaussRandom: mathExpressions.gaussRandom,
};

// ============================================================================
// AUDIO EXPRESSION FUNCTIONS
// ============================================================================

/**
 * valueAtTime - Get the value of a property at a specific time
 *
 * This is a core expression function used for audio reactivity.
 * Example: thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider").valueAtTime(time - 0.1)
 *
 * @param ctx - Expression context
 * @param targetTime - The time in seconds to sample
 * @returns The interpolated value at that time
 */
export function valueAtTime(
  ctx: ExpressionContext,
  targetTime: number
): number | number[] {
  const { keyframes, fps, value } = ctx;

  // If no keyframes, return current value
  if (!keyframes || keyframes.length === 0) {
    return value;
  }

  // Convert time to frame
  const targetFrame = targetTime * fps;

  // Find surrounding keyframes
  const sortedKfs = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Before first keyframe
  if (targetFrame <= sortedKfs[0].frame) {
    return sortedKfs[0].value;
  }

  // After last keyframe
  if (targetFrame >= sortedKfs[sortedKfs.length - 1].frame) {
    return sortedKfs[sortedKfs.length - 1].value;
  }

  // Find surrounding keyframes
  let prevKf = sortedKfs[0];
  let nextKf = sortedKfs[1];

  for (let i = 0; i < sortedKfs.length - 1; i++) {
    if (targetFrame >= sortedKfs[i].frame && targetFrame < sortedKfs[i + 1].frame) {
      prevKf = sortedKfs[i];
      nextKf = sortedKfs[i + 1];
      break;
    }
  }

  // Linear interpolation between keyframes
  const t = (targetFrame - prevKf.frame) / (nextKf.frame - prevKf.frame);

  if (typeof prevKf.value === 'number' && typeof nextKf.value === 'number') {
    return prevKf.value + t * (nextKf.value - prevKf.value);
  }

  // Array interpolation
  if (Array.isArray(prevKf.value) && Array.isArray(nextKf.value)) {
    return prevKf.value.map((v, i) =>
      v + t * ((nextKf.value as number[])[i] - v)
    );
  }

  return value;
}

/**
 * posterizeTime - Reduce the frame rate of the expression evaluation
 *
 * This is useful for creating a more rhythmic, less smooth animation response.
 * Instead of updating every frame, it only updates at the specified rate.
 *
 * Example:
 *   posterizeTime(12);
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   amp * 5 + 50
 *
 * @param ctx - Expression context
 * @param framesPerSecond - The reduced frame rate to sample at
 * @returns The time quantized to the specified frame rate
 */
export function posterizeTime(
  ctx: ExpressionContext,
  framesPerSecond: number
): number {
  const { time, fps } = ctx;

  // Calculate the interval between samples
  const interval = 1 / framesPerSecond;

  // Quantize time to the nearest interval
  const quantizedTime = Math.floor(time / interval) * interval;

  return quantizedTime;
}

/**
 * Get the posterized frame number
 */
export function posterizedFrame(
  ctx: ExpressionContext,
  framesPerSecond: number
): number {
  const quantizedTime = posterizeTime(ctx, framesPerSecond);
  return Math.floor(quantizedTime * ctx.fps);
}

/**
 * linearInterp - Linear interpolation with range mapping
 *
 * Maps a value from one range to another using linear interpolation.
 * Unlike simple lerp, this takes input range and output range.
 *
 * Example:
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   linear(amp, 0, 25, 50, 150)  // Maps amplitude 0-25 to scale 50-150
 *
 * @param t - Input value
 * @param tMin - Input range minimum
 * @param tMax - Input range maximum
 * @param vMin - Output range minimum
 * @param vMax - Output range maximum
 * @returns The mapped value, clamped to output range
 */
export function linearInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  // Normalize t to 0-1 range within input range
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));

  // Map to output range
  return vMin + normalized * (vMax - vMin);
}

/**
 * easeInterp - Eased interpolation with range mapping
 *
 * Like linear() but with smooth ease-in-out interpolation.
 * Creates more organic, natural-looking transitions.
 *
 * Example:
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   ease(amp, 0, 25, 50, 150)  // Maps with smooth easing
 *
 * @param t - Input value
 * @param tMin - Input range minimum
 * @param tMax - Input range maximum
 * @param vMin - Output range minimum
 * @param vMax - Output range maximum
 * @returns The eased mapped value, clamped to output range
 */
export function easeInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  // Normalize t to 0-1 range within input range
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));

  // Apply smooth ease (cubic ease-in-out)
  const eased = normalized < 0.5
    ? 4 * normalized * normalized * normalized
    : 1 - Math.pow(-2 * normalized + 2, 3) / 2;

  // Map to output range
  return vMin + eased * (vMax - vMin);
}

/**
 * easeIn - Ease-in interpolation with range mapping
 */
export function easeInInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));
  const eased = normalized * normalized * normalized;
  return vMin + eased * (vMax - vMin);
}

/**
 * easeOut - Ease-out interpolation with range mapping
 */
export function easeOutInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));
  const eased = 1 - Math.pow(1 - normalized, 3);
  return vMin + eased * (vMax - vMin);
}

/**
 * Audio amplitude reference helper
 *
 * Creates an expression-friendly reference to the Audio Amplitude layer's slider.
 * This simplifies the common pattern of referencing audio data in expressions.
 *
 * @param layerName - Name of the Audio Amplitude layer (default: "Audio Amplitude")
 * @param channel - "both" | "left" | "right" (default: "both")
 * @param frame - Frame number to sample
 * @param keyframes - The slider's keyframes array
 * @param fps - Frames per second
 * @returns The amplitude value at the specified frame
 */
export function audioAmplitude(
  keyframes: Keyframe<number>[],
  frame: number,
  fps: number,
  timeOffset: number = 0
): number {
  if (!keyframes || keyframes.length === 0) return 0;

  // Apply time offset
  const targetFrame = frame - (timeOffset * fps);

  // Find the keyframe at this frame
  const exactKf = keyframes.find(k => k.frame === Math.floor(targetFrame));
  if (exactKf) return exactKf.value;

  // Interpolate between keyframes
  const sortedKfs = [...keyframes].sort((a, b) => a.frame - b.frame);

  if (targetFrame <= sortedKfs[0].frame) return sortedKfs[0].value;
  if (targetFrame >= sortedKfs[sortedKfs.length - 1].frame) {
    return sortedKfs[sortedKfs.length - 1].value;
  }

  // Find surrounding keyframes
  for (let i = 0; i < sortedKfs.length - 1; i++) {
    if (targetFrame >= sortedKfs[i].frame && targetFrame < sortedKfs[i + 1].frame) {
      const t = (targetFrame - sortedKfs[i].frame) / (sortedKfs[i + 1].frame - sortedKfs[i].frame);
      return sortedKfs[i].value + t * (sortedKfs[i + 1].value - sortedKfs[i].value);
    }
  }

  return 0;
}

/**
 * Audio expression namespace - convenient access to all audio functions
 */
export const audio = {
  valueAtTime,
  posterizeTime,
  posterizedFrame,
  linear: linearInterp,
  ease: easeInterp,
  easeIn: easeInInterp,
  easeOut: easeOutInterp,
  amplitude: audioAmplitude,
};

