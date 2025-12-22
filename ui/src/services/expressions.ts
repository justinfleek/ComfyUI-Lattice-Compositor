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
 * - Data-driven animation (JSON/CSV)
 * - footage() function for data access
 */

import type { AnimatableProperty, Keyframe, InterpolationType } from '@/types/project';
import { measureTextLayerRect } from './textMeasurement';
import type { FootageDataAccessor } from '@/types/dataAsset';

// ============================================================================
// EXPRESSION CONTEXT
// ============================================================================

export interface ExpressionContext {
  // Time
  time: number;           // Current time in seconds
  frame: number;          // Current frame number
  fps: number;            // Frames per second
  duration: number;       // Composition duration

  // Composition info
  compWidth?: number;     // Composition width in pixels
  compHeight?: number;    // Composition height in pixels

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

  // Expression control parameters (for effect("Slider")("Slider") access)
  params?: Record<string, any>;

  // Other layer properties (for linking)
  getLayerProperty?: (layerId: string, propertyPath: string) => number | number[] | null;

  // Data-driven animation (footage access)
  footage?: (name: string) => FootageDataAccessor | null;

  // === NEW: Enhanced layer/effect access for thisLayer/thisComp ===

  // Current layer's transform values (for thisLayer.transform)
  layerTransform?: {
    position: number[];
    rotation: number[];
    scale: number[];
    opacity: number;
    origin: number[];  // anchor point
  };

  // Current layer's effects (for thisLayer.effect())
  layerEffects?: Array<{
    name: string;
    effectKey: string;
    enabled: boolean;
    parameters: Record<string, number | number[] | string | boolean>;
  }>;

  // All layers in composition (for thisComp.layer(name))
  allLayers?: Array<{
    id: string;
    name: string;
    index: number;
  }>;

  // Get effect parameter value from any layer
  getLayerEffectParam?: (layerId: string, effectName: string, paramName: string) => number | number[] | string | boolean | null;
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
   * Gaussian random (normal distribution) - DETERMINISTIC
   * Uses seeded random for reproducible results
   */
  gaussRandom(mean: number = 0, stdDev: number = 1, seed: number = 12345): number {
    // Box-Muller transform with seeded random
    // Use different seeds for u1 and u2 to avoid correlation
    const seededRand = (s: number) => {
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    };
    const u1 = Math.max(0.0001, seededRand(seed)); // Avoid log(0)
    const u2 = seededRand(seed + 1);
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
  code?: string;  // For custom expressions - JavaScript code string
}

/**
 * Evaluate an expression on a property
 */
export function evaluateExpression(
  expression: Expression,
  ctx: ExpressionContext
): number | number[] | string {
  if (!expression.enabled) return ctx.value;

  switch (expression.type) {
    case 'preset':
      return evaluatePreset(expression.name, ctx, expression.params);
    case 'function':
      return evaluateFunction(expression.name, ctx, expression.params);
    case 'custom':
      return evaluateCustomExpression(expression.code || '', ctx);
    default:
      return ctx.value;
  }
}

/**
 * Evaluate a custom JavaScript expression string
 *
 * This provides a sandboxed environment with access to:
 * - time, frame, fps, duration
 * - value, velocity
 * - footage() for data access
 * - Math functions
 * - ease() for count-up animations
 * - String methods (toLocaleString, toFixed, etc.)
 */
export function evaluateCustomExpression(
  code: string,
  ctx: ExpressionContext
): number | number[] | string {
  if (!code || code.trim() === '') {
    return ctx.value;
  }

  try {
    // Helper: Get keyframe at index (1-based like AE)
    const key = (n: number) => {
      const kfs = ctx.keyframes || [];
      if (n < 1 || n > kfs.length) return { time: 0, value: ctx.value };
      const kf = kfs[n - 1];
      return { time: kf.frame / ctx.fps, value: kf.value };
    };

    // Helper: Find nearest keyframe to current time
    const nearestKey = (t: number) => {
      const kfs = ctx.keyframes || [];
      if (kfs.length === 0) return { index: 0, time: 0 };
      let nearest = 0;
      let minDist = Infinity;
      const targetFrame = t * ctx.fps;
      for (let i = 0; i < kfs.length; i++) {
        const dist = Math.abs(kfs[i].frame - targetFrame);
        if (dist < minDist) {
          minDist = dist;
          nearest = i;
        }
      }
      return { index: nearest + 1, time: kfs[nearest].frame / ctx.fps };
    };

    // Helper: wiggle (alias for jitter, AE-compatible API)
    const wiggle = (freq: number, amp: number, octaves: number = 1, amp_mult: number = 0.5, t?: number): number | number[] => {
      const targetTime = t ?? ctx.time;
      // Simple multi-octave noise
      const noise = (seed: number, time: number): number => {
        let result = 0;
        let amplitude = 1;
        let frequency = freq;
        for (let i = 0; i < octaves; i++) {
          result += amplitude * Math.sin(time * frequency * Math.PI * 2 + seed * 1000);
          result += amplitude * 0.5 * Math.sin(time * frequency * Math.PI * 2 * 1.618 + seed * 500);
          amplitude *= amp_mult;
          frequency *= 2;
        }
        return result / (1 + (octaves - 1) * amp_mult);
      };

      if (typeof ctx.value === 'number') {
        return ctx.value + noise(0, targetTime) * amp;
      }
      return (ctx.value as number[]).map((v, i) => v + noise(i, targetTime) * amp);
    };

    // Helper: loopOut (alias for repeatAfter)
    const loopOut = (type: string = 'cycle', numKf: number = 0): number | number[] => {
      return repeatAfter(ctx, type as LoopType, numKf);
    };

    // Helper: loopIn (alias for repeatBefore)
    const loopIn = (type: string = 'cycle', numKf: number = 0): number | number[] => {
      return repeatBefore(ctx, type as LoopType, numKf);
    };

    // Helper: length (vector distance)
    const length = (a: number | number[], b?: number | number[]): number => {
      if (b === undefined) {
        // length(vector) - magnitude
        if (typeof a === 'number') return Math.abs(a);
        return Math.sqrt(a.reduce((sum, v) => sum + v * v, 0));
      }
      // length(a, b) - distance between points
      if (typeof a === 'number' && typeof b === 'number') {
        return Math.abs(a - b);
      }
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      let sum = 0;
      for (let i = 0; i < Math.max(arrA.length, arrB.length); i++) {
        const diff = (arrA[i] || 0) - (arrB[i] || 0);
        sum += diff * diff;
      }
      return Math.sqrt(sum);
    };

    // Helper: seedRandom (set random seed for deterministic random)
    const seedRandom = (seed: number, timeless: boolean = false): void => {
      // In our implementation, random() already uses frame-based seeding
      // This is a no-op but maintains API compatibility
    };

    // Helper: valueAtTime for expressions
    const valueAtTimeExpr = (t: number): number | number[] => {
      return valueAtTime(ctx, t);
    };

    // Helper: velocityAtTime
    const velocityAtTimeExpr = (t: number): number | number[] => {
      // Approximate velocity using finite difference
      const dt = 1 / ctx.fps;
      const v1 = valueAtTime(ctx, t - dt);
      const v2 = valueAtTime(ctx, t + dt);
      if (typeof v1 === 'number' && typeof v2 === 'number') {
        return (v2 - v1) / (2 * dt);
      }
      if (Array.isArray(v1) && Array.isArray(v2)) {
        return v1.map((_, i) => ((v2 as number[])[i] - (v1 as number[])[i]) / (2 * dt));
      }
      return 0;
    };

    // Build the expression context variables
    const contextVars = {
      // Time
      time: ctx.time,
      frame: ctx.frame,
      fps: ctx.fps,
      duration: ctx.duration,

      // Layer
      index: ctx.layerIndex,  // Layer index (1-based)
      layerName: ctx.layerName,
      inPoint: ctx.inPoint,
      outPoint: ctx.outPoint,

      // Property
      value: ctx.value,
      velocity: ctx.velocity,
      numKeys: ctx.numKeys,

      // Keyframe access
      key,
      nearestKey,

      // Math (safe subset)
      Math: Math,
      parseInt: parseInt,
      parseFloat: parseFloat,
      isNaN: isNaN,
      isFinite: isFinite,

      // footage() function
      footage: ctx.footage || (() => null),

      // Ease functions (AE-compatible)
      ease: expressionEase,
      easeIn: expressionEaseIn,
      easeOut: expressionEaseOut,

      // linear interpolation
      linear: (t: number, tMin: number, tMax: number, vMin: number, vMax: number): number => {
        if (t <= tMin) return vMin;
        if (t >= tMax) return vMax;
        return vMin + (vMax - vMin) * ((t - tMin) / (tMax - tMin));
      },

      // Clamp
      clamp: (val: number, min: number, max: number): number => {
        return Math.max(min, Math.min(max, val));
      },

      // Random (seeded based on frame for determinism)
      random: (seed?: number): number => {
        const s = seed !== undefined ? seed : ctx.frame;
        const x = Math.sin(s * 12.9898) * 43758.5453;
        return x - Math.floor(x);
      },

      // Motion functions (AE-compatible aliases)
      wiggle,
      loopOut,
      loopIn,

      // Utility functions
      length,
      seedRandom,
      valueAtTime: valueAtTimeExpr,
      velocityAtTime: velocityAtTimeExpr,

      // Angle conversion
      radiansToDegrees: (rad: number): number => rad * 180 / Math.PI,
      degreesToRadians: (deg: number): number => deg * Math.PI / 180,

      // Time conversion
      timeToFrames: (t: number = ctx.time): number => Math.round(t * ctx.fps),
      framesToTime: (f: number): number => f / ctx.fps,

      // Vector math functions (AE-compatible)
      add: (a: number | number[], b: number | number[]): number | number[] => {
        if (typeof a === 'number' && typeof b === 'number') return a + b;
        const arrA = Array.isArray(a) ? a : [a];
        const arrB = Array.isArray(b) ? b : [b];
        return vectorAdd(arrA, arrB);
      },
      sub: (a: number | number[], b: number | number[]): number | number[] => {
        if (typeof a === 'number' && typeof b === 'number') return a - b;
        const arrA = Array.isArray(a) ? a : [a];
        const arrB = Array.isArray(b) ? b : [b];
        return vectorSub(arrA, arrB);
      },
      mul: (a: number | number[], b: number | number[]): number | number[] => {
        if (typeof a === 'number' && typeof b === 'number') return a * b;
        return vectorMul(a, b);
      },
      div: (a: number | number[], b: number | number[]): number | number[] => {
        if (typeof a === 'number' && typeof b === 'number') return a / (b || 1);
        return vectorDiv(a, b);
      },
      normalize: (vec: number[]): number[] => vectorNormalize(vec),
      dot: (a: number[], b: number[]): number => vectorDot(a, b),
      cross: (a: number[], b: number[]): number[] => vectorCross(a, b),

      // Coordinate conversion (requires layer transform data)
      toComp: (point: number[]): number[] => {
        // Simplified - in real use, would get transform from layer
        return point;
      },
      fromComp: (point: number[]): number[] => {
        // Simplified - in real use, would get transform from layer
        return point;
      },
      toWorld: (point: number[]): number[] => {
        // Simplified - alias for toComp in 3D
        return point;
      },
      fromWorld: (point: number[]): number[] => {
        // Simplified - alias for fromComp in 3D
        return point;
      },

      // 3D orientation
      lookAt: (fromPoint: number[], atPoint: number[]): number[] => lookAt(fromPoint, atPoint),

      // Noise
      noise: (val: number | number[]): number => noise(val),

      // Degree-based trig (optional aliases)
      sinDeg: (deg: number): number => Math.sin(deg * Math.PI / 180),
      cosDeg: (deg: number): number => Math.cos(deg * Math.PI / 180),
      tanDeg: (deg: number): number => Math.tan(deg * Math.PI / 180),

      // thisComp / thisLayer simulation
      thisComp: {
        duration: ctx.duration,
        frameDuration: 1 / ctx.fps,
        width: ctx.compWidth ?? 1920,
        height: ctx.compHeight ?? 1080,
        numLayers: ctx.allLayers?.length ?? 0,
        layer: (nameOrIndex: string | number) => {
          // Resolve layer ID from name or index
          const getLayerProperty = ctx.getLayerProperty;
          const getLayerEffectParam = ctx.getLayerEffectParam;
          let layerId: string;

          if (typeof nameOrIndex === 'number') {
            // Find layer by index (1-based like AE)
            const layerInfo = ctx.allLayers?.find(l => l.index === nameOrIndex);
            layerId = layerInfo?.id ?? `layer_${nameOrIndex}`;
          } else {
            // Find layer by name first, then fall back to using name as ID
            const layerInfo = ctx.allLayers?.find(l => l.name === nameOrIndex);
            layerId = layerInfo?.id ?? nameOrIndex;
          }

          // Get layer transform for coordinate conversion
          const getTransform = (): LayerTransform => ({
            position: (getLayerProperty?.(layerId, 'transform.position') as number[]) ?? [0, 0, 0],
            scale: (getLayerProperty?.(layerId, 'transform.scale') as number[]) ?? [100, 100, 100],
            rotation: (getLayerProperty?.(layerId, 'transform.rotation') as number[]) ?? [0, 0, 0],
            anchor: (getLayerProperty?.(layerId, 'transform.anchorPoint') as number[]) ?? [0, 0, 0],
          });

          // Create effect accessor with callable syntax: effect("name")("param") or effect("name").param("param")
          const createEffectAccessor = (effectName: string) => {
            const accessor = (paramName: string) => {
              return getLayerEffectParam?.(layerId, effectName, paramName) ?? 0;
            };
            // Also expose as .param() method
            accessor.param = accessor;
            // Add common expression control names as properties
            accessor.value = getLayerEffectParam?.(layerId, effectName, 'value') ?? 0;
            accessor.slider = getLayerEffectParam?.(layerId, effectName, 'slider') ?? 0;
            accessor.angle = getLayerEffectParam?.(layerId, effectName, 'angle') ?? 0;
            accessor.checkbox = getLayerEffectParam?.(layerId, effectName, 'checkbox') ?? false;
            accessor.color = getLayerEffectParam?.(layerId, effectName, 'color') ?? [1, 1, 1, 1];
            accessor.point = getLayerEffectParam?.(layerId, effectName, 'point') ?? [0, 0];
            return accessor;
          };

          return {
            name: ctx.allLayers?.find(l => l.id === layerId)?.name ?? '',
            index: ctx.allLayers?.find(l => l.id === layerId)?.index ?? 0,
            position: getLayerProperty?.(layerId, 'transform.position') ?? [0, 0],
            scale: getLayerProperty?.(layerId, 'transform.scale') ?? [100, 100],
            rotation: getLayerProperty?.(layerId, 'transform.rotation') ?? 0,
            opacity: getLayerProperty?.(layerId, 'transform.opacity') ?? 100,
            anchorPoint: getLayerProperty?.(layerId, 'transform.anchorPoint') ?? [0, 0],
            origin: getLayerProperty?.(layerId, 'transform.origin') ?? [0, 0],
            // Transform sub-object for thisComp.layer("x").transform.position syntax
            transform: {
              position: getLayerProperty?.(layerId, 'transform.position') ?? [0, 0, 0],
              rotation: getLayerProperty?.(layerId, 'transform.rotation') ?? [0, 0, 0],
              scale: getLayerProperty?.(layerId, 'transform.scale') ?? [100, 100, 100],
              opacity: getLayerProperty?.(layerId, 'transform.opacity') ?? 100,
              anchorPoint: getLayerProperty?.(layerId, 'transform.anchorPoint') ?? [0, 0, 0],
              origin: getLayerProperty?.(layerId, 'transform.origin') ?? [0, 0, 0],
            },
            // Coordinate conversion with actual transform
            toComp: (point: number[]) => toComp(point, getTransform()),
            fromComp: (point: number[]) => fromComp(point, getTransform()),
            toWorld: (point: number[]) => toWorld(point, getTransform()),
            fromWorld: (point: number[]) => fromWorld(point, getTransform()),
            // Effect access: effect("Effect Name")("Parameter") or effect("Effect Name").param("Parameter")
            effect: createEffectAccessor
          };
        }
      },
      thisLayer: {
        name: ctx.layerName,
        index: ctx.layerIndex,
        inPoint: ctx.inPoint,
        outPoint: ctx.outPoint,
        // Transform properties (direct access)
        position: ctx.layerTransform?.position ?? [0, 0, 0],
        rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
        scale: ctx.layerTransform?.scale ?? [100, 100, 100],
        opacity: ctx.layerTransform?.opacity ?? 100,
        anchorPoint: ctx.layerTransform?.origin ?? [0, 0, 0],
        origin: ctx.layerTransform?.origin ?? [0, 0, 0],
        // Transform sub-object for thisLayer.transform.position syntax
        transform: {
          position: ctx.layerTransform?.position ?? [0, 0, 0],
          rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
          scale: ctx.layerTransform?.scale ?? [100, 100, 100],
          opacity: ctx.layerTransform?.opacity ?? 100,
          anchorPoint: ctx.layerTransform?.origin ?? [0, 0, 0],
          origin: ctx.layerTransform?.origin ?? [0, 0, 0],
        },
        // Effect access on current layer
        effect: (effectName: string) => {
          const eff = ctx.layerEffects?.find(e => e.name === effectName || e.effectKey === effectName);
          const accessor = (paramName: string) => {
            if (!eff) return 0;
            return eff.parameters[paramName] ?? 0;
          };
          accessor.param = accessor;
          // Common expression control properties
          accessor.value = eff?.parameters['value'] ?? 0;
          accessor.slider = eff?.parameters['slider'] ?? 0;
          accessor.angle = eff?.parameters['angle'] ?? 0;
          accessor.checkbox = eff?.parameters['checkbox'] ?? false;
          accessor.color = eff?.parameters['color'] ?? [1, 1, 1, 1];
          accessor.point = eff?.parameters['point'] ?? [0, 0];
          return accessor;
        },
        // Layer methods
        sourceRectAtTime: (t: number = ctx.time, includeExtents: boolean = false) => {
          // Return default rect - actual implementation needs layer data
          return { top: 0, left: 0, width: 100, height: 100 };
        },
        // Coordinate conversion using actual layer transform
        toComp: (point: number[]) => {
          const transform: LayerTransform = {
            position: ctx.layerTransform?.position ?? [0, 0, 0],
            scale: ctx.layerTransform?.scale ?? [100, 100, 100],
            rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
            anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
          };
          return toComp(point, transform);
        },
        fromComp: (point: number[]) => {
          const transform: LayerTransform = {
            position: ctx.layerTransform?.position ?? [0, 0, 0],
            scale: ctx.layerTransform?.scale ?? [100, 100, 100],
            rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
            anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
          };
          return fromComp(point, transform);
        },
        toWorld: (point: number[]) => {
          const transform: LayerTransform = {
            position: ctx.layerTransform?.position ?? [0, 0, 0],
            scale: ctx.layerTransform?.scale ?? [100, 100, 100],
            rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
            anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
          };
          return toWorld(point, transform);
        },
        fromWorld: (point: number[]) => {
          const transform: LayerTransform = {
            position: ctx.layerTransform?.position ?? [0, 0, 0],
            scale: ctx.layerTransform?.scale ?? [100, 100, 100],
            rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
            anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
          };
          return fromWorld(point, transform);
        },
      },
      thisProperty: {
        value: ctx.value,
        velocity: ctx.velocity,
        numKeys: ctx.numKeys,
        key,
        nearestKey: () => nearestKey(ctx.time),
        valueAtTime: valueAtTimeExpr,
        velocityAtTime: velocityAtTimeExpr
      }
    };

    // Create a safe function that returns the expression result
    const paramNames = Object.keys(contextVars);
    const paramValues = Object.values(contextVars);

    // Wrap in try-catch and return
    const wrappedCode = `
      "use strict";
      try {
        return (function() {
          ${code}
        })();
      } catch(e) {
        return "Error: " + e.message;
      }
    `;

    const fn = new Function(...paramNames, wrappedCode);
    const result = fn(...paramValues);

    return result;
  } catch (error) {
    console.error('[Expressions] Custom expression error:', error);
    return ctx.value;
  }
}

/**
 * Ease function for expressions (count-up animations)
 * Compatible with After Effects ease()
 */
export function expressionEase(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[]
): number | number[] {
  // Normalize t to 0-1 range
  let normalized = (t - tMin) / (tMax - tMin);
  normalized = Math.max(0, Math.min(1, normalized));

  // Apply ease (cubic ease in-out)
  const eased = normalized < 0.5
    ? 4 * normalized * normalized * normalized
    : 1 - Math.pow(-2 * normalized + 2, 3) / 2;

  // Interpolate value
  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
}

/**
 * easeIn function for expressions
 */
export function expressionEaseIn(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[]
): number | number[] {
  let normalized = (t - tMin) / (tMax - tMin);
  normalized = Math.max(0, Math.min(1, normalized));

  // Cubic ease in
  const eased = normalized * normalized * normalized;

  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
}

/**
 * easeOut function for expressions
 */
export function expressionEaseOut(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[]
): number | number[] {
  let normalized = (t - tMin) / (tMax - tMin);
  normalized = Math.max(0, Math.min(1, normalized));

  // Cubic ease out
  const eased = 1 - Math.pow(1 - normalized, 3);

  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
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

// ============================================================
// LAYER DIMENSION EXPRESSIONS
// ============================================================

/**
 * Source rectangle interface matching After Effects
 */
export interface SourceRect {
  top: number;     // Y position of top edge
  left: number;    // X position of left edge
  width: number;   // Width of content
  height: number;  // Height of content
}

/**
 * Get the bounding rectangle of a layer's content at a specific time
 *
 * This is crucial for responsive templates where background elements
 * need to resize based on text content.
 *
 * In After Effects: sourceRectAtTime(t, includeExtents)
 *
 * @param layerData - The layer's type-specific data (e.g., TextLayerData)
 * @param layerType - Type of the layer
 * @param time - Time in seconds (default: 0)
 * @param includeExtents - Include stroke width and effects (default: false)
 * @returns SourceRect with top, left, width, height
 */
export function sourceRectAtTime(
  layerData: any,
  layerType: string,
  time: number = 0,
  includeExtents: boolean = false
): SourceRect {
  // Default rect for unknown layer types
  const defaultRect: SourceRect = {
    top: 0,
    left: 0,
    width: 100,
    height: 100
  };

  if (!layerData) return defaultRect;

  switch (layerType) {
    case 'text':
      return getTextSourceRect(layerData, includeExtents);

    case 'shape':
      return getShapeSourceRect(layerData, includeExtents);

    case 'solid':
      return getSolidSourceRect(layerData);

    case 'image':
    case 'video':
      return getMediaSourceRect(layerData);

    default:
      return defaultRect;
  }
}

/**
 * Calculate source rect for text layers
 * Uses accurate Canvas API text measurement
 */
function getTextSourceRect(data: any, includeExtents: boolean): SourceRect {
  // Use accurate text measurement service
  const rect = measureTextLayerRect(data, includeExtents);

  // measureTextLayerRect already handles alignment and stroke extents
  return {
    top: rect.top,
    left: rect.left,
    width: rect.width,
    height: rect.height
  };
}

/**
 * Calculate source rect for shape layers
 */
function getShapeSourceRect(data: any, includeExtents: boolean): SourceRect {
  // For shape layers, we need to calculate the bounding box of all paths
  let minX = Infinity, minY = Infinity;
  let maxX = -Infinity, maxY = -Infinity;

  const paths = data.paths || [];

  if (paths.length === 0) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  paths.forEach((path: any) => {
    const points = path.points || [];
    points.forEach((point: any) => {
      const x = point.x ?? point[0] ?? 0;
      const y = point.y ?? point[1] ?? 0;
      minX = Math.min(minX, x);
      minY = Math.min(minY, y);
      maxX = Math.max(maxX, x);
      maxY = Math.max(maxY, y);
    });
  });

  if (!isFinite(minX)) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  let width = maxX - minX;
  let height = maxY - minY;

  // Include stroke extents
  if (includeExtents && data.stroke?.width) {
    const strokeExtent = data.stroke.width / 2;
    minX -= strokeExtent;
    minY -= strokeExtent;
    width += strokeExtent * 2;
    height += strokeExtent * 2;
  }

  return {
    top: minY,
    left: minX,
    width,
    height
  };
}

/**
 * Calculate source rect for solid layers
 */
function getSolidSourceRect(data: any): SourceRect {
  const width = data.width || 100;
  const height = data.height || 100;

  return {
    top: -height / 2,
    left: -width / 2,
    width,
    height
  };
}

/**
 * Calculate source rect for image/video layers
 */
function getMediaSourceRect(data: any): SourceRect {
  const width = data.width || data.naturalWidth || 1920;
  const height = data.height || data.naturalHeight || 1080;

  return {
    top: -height / 2,
    left: -width / 2,
    width,
    height
  };
}

/**
 * Get text layer content as an expression-accessible object
 * Mimics After Effects' text.sourceText
 */
export function textSource(layerData: any): TextSourceInfo {
  return {
    text: layerData?.text || '',
    fontSize: layerData?.fontSize || 72,
    fontFamily: layerData?.fontFamily || 'Arial',
    fontStyle: layerData?.fontStyle || 'normal',
    fillColor: layerData?.fill || { r: 1, g: 1, b: 1, a: 1 },
    strokeColor: layerData?.stroke || { r: 0, g: 0, b: 0, a: 1 },
    strokeWidth: layerData?.strokeWidth || 0,
    tracking: layerData?.letterSpacing || 0,
    leading: layerData?.lineHeight || 1.2
  };
}

export interface TextSourceInfo {
  text: string;
  fontSize: number;
  fontFamily: string;
  fontStyle: string;
  fillColor: any;
  strokeColor: any;
  strokeWidth: number;
  tracking: number;
  leading: number;
}

/**
 * Layer dimension expressions namespace
 */
export const layer = {
  sourceRectAtTime,
  textSource
};

// ============================================================
// EFFECT CONTROL ACCESS
// ============================================================

/**
 * Get the value of an expression control effect
 *
 * Usage in expressions:
 *   effect("Slider Control")("Slider")
 *   effect("Checkbox Control")("Checkbox") * 100  // for opacity
 *   effect("Color Control")("Color")
 *
 * @param effects - Array of effects on the layer
 * @param effectName - Name of the effect to find
 * @param parameterName - Name of the parameter to get
 * @param frame - Current frame for animated parameters
 * @returns The parameter value, or null if not found
 */
export function effectValue(
  effects: any[] | undefined,
  effectName: string,
  parameterName: string,
  frame: number = 0
): any {
  if (!effects || effects.length === 0) return null;

  // Find the effect by name
  const effect = effects.find((e: any) => e.name === effectName);
  if (!effect) return null;

  // Find the parameter
  // Parameter keys are lowercase with underscores
  const paramKey = parameterName.toLowerCase().replace(/\s+/g, '_');
  const param = effect.parameters?.[paramKey];

  if (!param) return null;

  // Return the value (animation would be handled by the interpolation service)
  return param.value;
}

/**
 * Effect access namespace for expressions
 */
export const effect = {
  value: effectValue
};

// ============================================================
// VECTOR MATH FUNCTIONS (Tutorial 16 - Section 13)
// ============================================================

/**
 * Vector addition
 * add(vec1, vec2) or add(a, b, c, ...)
 */
export function vectorAdd(a: number[], b: number[]): number[] {
  const maxLen = Math.max(a.length, b.length);
  const result: number[] = [];
  for (let i = 0; i < maxLen; i++) {
    result.push((a[i] || 0) + (b[i] || 0));
  }
  return result;
}

/**
 * Vector subtraction
 * sub(vec1, vec2)
 */
export function vectorSub(a: number[], b: number[]): number[] {
  const maxLen = Math.max(a.length, b.length);
  const result: number[] = [];
  for (let i = 0; i < maxLen; i++) {
    result.push((a[i] || 0) - (b[i] || 0));
  }
  return result;
}

/**
 * Vector multiplication (component-wise or scalar)
 * mul(vec, scalar) or mul(vec1, vec2)
 */
export function vectorMul(a: number[] | number, b: number[] | number): number[] {
  if (typeof a === 'number' && Array.isArray(b)) {
    return b.map(v => v * a);
  }
  if (Array.isArray(a) && typeof b === 'number') {
    return a.map(v => v * b);
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    const maxLen = Math.max(a.length, b.length);
    const result: number[] = [];
    for (let i = 0; i < maxLen; i++) {
      result.push((a[i] || 0) * (b[i] || 0));
    }
    return result;
  }
  return [0];
}

/**
 * Vector division (component-wise or scalar)
 * div(vec, scalar) or div(vec1, vec2)
 */
export function vectorDiv(a: number[] | number, b: number[] | number): number[] {
  if (typeof a === 'number' && Array.isArray(b)) {
    return b.map(v => a / (v || 1));
  }
  if (Array.isArray(a) && typeof b === 'number') {
    return a.map(v => v / (b || 1));
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    const maxLen = Math.max(a.length, b.length);
    const result: number[] = [];
    for (let i = 0; i < maxLen; i++) {
      result.push((a[i] || 0) / ((b[i] || 1)));
    }
    return result;
  }
  return [0];
}

/**
 * Normalize vector to unit length
 * normalize(vec) returns vector with length 1
 */
export function vectorNormalize(vec: number[]): number[] {
  const len = Math.sqrt(vec.reduce((sum, v) => sum + v * v, 0));
  if (len === 0) return vec.map(() => 0);
  return vec.map(v => v / len);
}

/**
 * Dot product of two vectors
 * dot(vec1, vec2) returns scalar
 */
export function vectorDot(a: number[], b: number[]): number {
  let sum = 0;
  const maxLen = Math.min(a.length, b.length);
  for (let i = 0; i < maxLen; i++) {
    sum += (a[i] || 0) * (b[i] || 0);
  }
  return sum;
}

/**
 * Cross product of two 3D vectors
 * cross(vec1, vec2) returns perpendicular vector
 */
export function vectorCross(a: number[], b: number[]): number[] {
  // Ensure 3D vectors
  const ax = a[0] || 0, ay = a[1] || 0, az = a[2] || 0;
  const bx = b[0] || 0, by = b[1] || 0, bz = b[2] || 0;

  return [
    ay * bz - az * by,
    az * bx - ax * bz,
    ax * by - ay * bx
  ];
}

/**
 * Calculate vector length/magnitude
 * length(vec) or length(vec1, vec2) for distance
 */
export function vectorLength(a: number[], b?: number[]): number {
  if (b === undefined) {
    // Magnitude of single vector
    return Math.sqrt(a.reduce((sum, v) => sum + v * v, 0));
  }
  // Distance between two points
  let sum = 0;
  const maxLen = Math.max(a.length, b.length);
  for (let i = 0; i < maxLen; i++) {
    const diff = (a[i] || 0) - (b[i] || 0);
    sum += diff * diff;
  }
  return Math.sqrt(sum);
}

/**
 * Clamp vector components
 * clamp(vec, min, max)
 */
export function vectorClamp(vec: number[], min: number | number[], max: number | number[]): number[] {
  return vec.map((v, i) => {
    const minVal = Array.isArray(min) ? (min[i] || 0) : min;
    const maxVal = Array.isArray(max) ? (max[i] || 0) : max;
    return Math.max(minVal, Math.min(maxVal, v));
  });
}

// ============================================================
// 3D ORIENTATION FUNCTIONS (Tutorial 16 - Section 14)
// ============================================================

/**
 * lookAt - Calculate rotation to face a target point
 *
 * Returns [xRotation, yRotation, zRotation] in degrees
 *
 * @param fromPoint - Source position [x, y, z]
 * @param toPoint - Target position [x, y, z]
 * @returns Rotation angles [rx, ry, rz] in degrees
 */
export function lookAt(fromPoint: number[], toPoint: number[]): number[] {
  const dx = (toPoint[0] || 0) - (fromPoint[0] || 0);
  const dy = (toPoint[1] || 0) - (fromPoint[1] || 0);
  const dz = (toPoint[2] || 0) - (fromPoint[2] || 0);

  // Calculate yaw (Y rotation) and pitch (X rotation)
  const yaw = Math.atan2(dx, dz) * 180 / Math.PI;
  const dist = Math.sqrt(dx * dx + dz * dz);
  const pitch = -Math.atan2(dy, dist) * 180 / Math.PI;

  return [pitch, yaw, 0];
}

/**
 * orientToPath - Auto-orient layer along motion path
 *
 * Given position keyframes, calculates rotation to face movement direction
 */
export function orientToPath(
  ctx: ExpressionContext,
  tangentVector?: number[]
): number[] {
  // If tangent provided, use it directly
  if (tangentVector) {
    const [dx, dy, dz] = tangentVector;
    const yaw = Math.atan2(dx || 0, dz || 1) * 180 / Math.PI;
    const dist = Math.sqrt((dx || 0) ** 2 + (dz || 1) ** 2);
    const pitch = -Math.atan2(dy || 0, dist) * 180 / Math.PI;
    return [pitch, yaw, 0];
  }

  // Calculate tangent from velocity
  const vel = ctx.velocity;
  if (Array.isArray(vel) && vel.length >= 2) {
    const dx = vel[0] || 0;
    const dy = vel[1] || 0;
    const dz = vel[2] || 0;
    const yaw = Math.atan2(dx, dz || 1) * 180 / Math.PI;
    const dist = Math.sqrt(dx ** 2 + (dz || 1) ** 2);
    const pitch = -Math.atan2(dy, dist) * 180 / Math.PI;
    return [pitch, yaw, 0];
  }

  return [0, 0, 0];
}

// ============================================================
// COORDINATE CONVERSION (Tutorial 16 - Section 15)
// ============================================================

/**
 * Transform matrix interface for coordinate conversion
 */
export interface LayerTransform {
  position: number[];
  scale: number[];
  rotation: number[];
  anchor: number[];
  parent?: LayerTransform | null;
}

/**
 * toComp - Convert point from layer space to composition space
 *
 * @param point - Point in layer coordinates [x, y] or [x, y, z]
 * @param layerTransform - The layer's transform properties
 * @returns Point in composition coordinates
 */
export function toComp(point: number[], layerTransform: LayerTransform): number[] {
  const [px, py, pz = 0] = point;
  const { position, scale, rotation, anchor } = layerTransform;

  // Apply anchor offset
  let x = px - (anchor[0] || 0);
  let y = py - (anchor[1] || 0);
  let z = pz - (anchor[2] || 0);

  // Apply scale
  x *= (scale[0] || 100) / 100;
  y *= (scale[1] || 100) / 100;
  z *= (scale[2] || 100) / 100;

  // Apply rotation (Z, then Y, then X - matching AE order)
  const rz = (rotation[2] || rotation[0] || 0) * Math.PI / 180;
  const ry = (rotation[1] || 0) * Math.PI / 180;
  const rx = (rotation[0] || 0) * Math.PI / 180;

  // Rotate around Z
  let x1 = x * Math.cos(rz) - y * Math.sin(rz);
  let y1 = x * Math.sin(rz) + y * Math.cos(rz);
  let z1 = z;

  // Rotate around Y (3D only)
  let x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  let y2 = y1;
  let z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around X (3D only)
  let x3 = x2;
  let y3 = y2 * Math.cos(rx) - z2 * Math.sin(rx);
  let z3 = y2 * Math.sin(rx) + z2 * Math.cos(rx);

  // Apply position offset
  x3 += position[0] || 0;
  y3 += position[1] || 0;
  z3 += position[2] || 0;

  // Recursively apply parent transforms
  if (layerTransform.parent) {
    return toComp([x3, y3, z3], layerTransform.parent);
  }

  return point.length === 2 ? [x3, y3] : [x3, y3, z3];
}

/**
 * fromComp - Convert point from composition space to layer space
 *
 * @param point - Point in composition coordinates [x, y] or [x, y, z]
 * @param layerTransform - The layer's transform properties
 * @returns Point in layer coordinates
 */
export function fromComp(point: number[], layerTransform: LayerTransform): number[] {
  let [px, py, pz = 0] = point;

  // First, if there's a parent, convert from comp to parent space
  if (layerTransform.parent) {
    [px, py, pz] = fromComp([px, py, pz], layerTransform.parent);
  }

  const { position, scale, rotation, anchor } = layerTransform;

  // Subtract position
  let x = px - (position[0] || 0);
  let y = py - (position[1] || 0);
  let z = pz - (position[2] || 0);

  // Inverse rotation (X, then Y, then Z - reverse order)
  const rz = -(rotation[2] || rotation[0] || 0) * Math.PI / 180;
  const ry = -(rotation[1] || 0) * Math.PI / 180;
  const rx = -(rotation[0] || 0) * Math.PI / 180;

  // Rotate around X (inverse)
  let x1 = x;
  let y1 = y * Math.cos(rx) - z * Math.sin(rx);
  let z1 = y * Math.sin(rx) + z * Math.cos(rx);

  // Rotate around Y (inverse)
  let x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  let y2 = y1;
  let z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around Z (inverse)
  let x3 = x2 * Math.cos(rz) - y2 * Math.sin(rz);
  let y3 = x2 * Math.sin(rz) + y2 * Math.cos(rz);
  let z3 = z2;

  // Inverse scale
  const sx = (scale[0] || 100) / 100;
  const sy = (scale[1] || 100) / 100;
  const sz = (scale[2] || 100) / 100;
  x3 /= sx || 1;
  y3 /= sy || 1;
  z3 /= sz || 1;

  // Add anchor
  x3 += anchor[0] || 0;
  y3 += anchor[1] || 0;
  z3 += anchor[2] || 0;

  return point.length === 2 ? [x3, y3] : [x3, y3, z3];
}

/**
 * toWorld - Convert point from layer space to world (3D) space
 * Alias for toComp in 3D context
 */
export function toWorld(point: number[], layerTransform: LayerTransform): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return toComp(point3D, layerTransform);
}

/**
 * fromWorld - Convert point from world space to layer space
 * Alias for fromComp in 3D context
 */
export function fromWorld(point: number[], layerTransform: LayerTransform): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return fromComp(point3D, layerTransform);
}

// ============================================================
// TEXT ANIMATOR VARIABLES (Tutorial 16 - Section 16)
// ============================================================

/**
 * Text animator context for per-character expressions
 */
export interface TextAnimatorContext extends ExpressionContext {
  // Per-character index (0-based)
  textIndex: number;
  // Total character count
  textTotal: number;
  // Character being animated
  char: string;
  // Selector value (0-1 range based on selector)
  selectorValue: number;
  // Word index (if text is split by words)
  wordIndex?: number;
  // Line index (for multi-line text)
  lineIndex?: number;
  // Character position in word
  charInWord?: number;
  // Character position in line
  charInLine?: number;
}

/**
 * Create a text animator context for per-character animation
 *
 * @param baseCtx - Base expression context
 * @param text - Full text string
 * @param charIndex - Current character index
 * @param selectorValue - Selector value (0-1)
 * @returns Extended context with text animator variables
 */
export function createTextAnimatorContext(
  baseCtx: ExpressionContext,
  text: string,
  charIndex: number,
  selectorValue: number = 1
): TextAnimatorContext {
  const char = text[charIndex] || '';

  // Calculate word and line positions
  let wordIndex = 0;
  let lineIndex = 0;
  let charInWord = 0;
  let charInLine = 0;
  let currentWordStart = 0;
  let currentLineStart = 0;

  for (let i = 0; i <= charIndex && i < text.length; i++) {
    if (text[i] === ' ' || text[i] === '\t') {
      if (i < charIndex) {
        wordIndex++;
        currentWordStart = i + 1;
      }
    }
    if (text[i] === '\n') {
      if (i < charIndex) {
        lineIndex++;
        currentLineStart = i + 1;
        wordIndex++;
        currentWordStart = i + 1;
      }
    }
  }

  charInWord = charIndex - currentWordStart;
  charInLine = charIndex - currentLineStart;

  return {
    ...baseCtx,
    textIndex: charIndex,
    textTotal: text.length,
    char,
    selectorValue,
    wordIndex,
    lineIndex,
    charInWord,
    charInLine
  };
}

/**
 * Evaluate expression with text animator context
 *
 * This allows expressions like:
 *   position[0] + Math.sin(textIndex * 0.5) * 50
 *   opacity * selectorValue
 *   scale + [textIndex * 5, textIndex * 5]
 */
export function evaluateTextAnimatorExpression(
  code: string,
  ctx: TextAnimatorContext
): number | number[] | string {
  // Add text animator variables to context
  const extendedCode = `
    const textIndex = ${ctx.textIndex};
    const textTotal = ${ctx.textTotal};
    const selectorValue = ${ctx.selectorValue};
    const char = "${ctx.char.replace(/"/g, '\\"')}";
    const wordIndex = ${ctx.wordIndex || 0};
    const lineIndex = ${ctx.lineIndex || 0};
    const charInWord = ${ctx.charInWord || 0};
    const charInLine = ${ctx.charInLine || 0};
    ${code}
  `;

  return evaluateCustomExpression(extendedCode, ctx);
}

// ============================================================
// ADDITIONAL MATH HELPERS
// ============================================================

/**
 * Noise function (Perlin-like) for expressions
 * noise(val) or noise(valArray)
 */
export function noise(val: number | number[]): number {
  if (typeof val === 'number') {
    // 1D noise
    const x = Math.sin(val * 12.9898) * 43758.5453;
    return (x - Math.floor(x)) * 2 - 1;
  }
  // Multi-dimensional noise
  const [x = 0, y = 0, z = 0] = val;
  const n = Math.sin(x * 12.9898 + y * 78.233 + z * 37.719) * 43758.5453;
  return (n - Math.floor(n)) * 2 - 1;
}

/**
 * Degree-based trigonometry helpers
 */
export const degreeTrig = {
  sin: (deg: number): number => Math.sin(deg * Math.PI / 180),
  cos: (deg: number): number => Math.cos(deg * Math.PI / 180),
  tan: (deg: number): number => Math.tan(deg * Math.PI / 180),
  asin: (val: number): number => Math.asin(val) * 180 / Math.PI,
  acos: (val: number): number => Math.acos(val) * 180 / Math.PI,
  atan: (val: number): number => Math.atan(val) * 180 / Math.PI,
  atan2: (y: number, x: number): number => Math.atan2(y, x) * 180 / Math.PI,
};

// ============================================================
// VECTOR NAMESPACE EXPORT
// ============================================================

/**
 * Vector math namespace for expressions
 */
export const vector = {
  add: vectorAdd,
  sub: vectorSub,
  mul: vectorMul,
  div: vectorDiv,
  normalize: vectorNormalize,
  dot: vectorDot,
  cross: vectorCross,
  length: vectorLength,
  clamp: vectorClamp,
};

/**
 * Coordinate conversion namespace
 */
export const coords = {
  toComp,
  fromComp,
  toWorld,
  fromWorld,
  lookAt,
  orientToPath,
};

/**
 * Text animator namespace
 */
export const textAnimator = {
  createContext: createTextAnimatorContext,
  evaluate: evaluateTextAnimatorExpression,
};

// ============================================================
// EXPRESSION VALIDATION
// ============================================================

export interface ExpressionValidationResult {
  valid: boolean;
  error?: string;
  errorLine?: number;
  errorColumn?: number;
}

/**
 * Validate an expression without executing it
 * Returns validation result with error details if invalid
 */
export function validateExpression(code: string): ExpressionValidationResult {
  if (!code || code.trim() === '') {
    return { valid: true };
  }

  try {
    // Create mock context variables for validation
    const mockContextVars = {
      time: 0,
      frame: 0,
      fps: 30,
      duration: 5,
      value: 0,
      velocity: 0,
      index: 0,
      numKeys: 0,
      // Common functions
      wiggle: () => 0,
      loopOut: () => 0,
      loopIn: () => 0,
      repeatAfter: () => 0,
      repeatBefore: () => 0,
      ease: () => 0,
      easeIn: () => 0,
      easeOut: () => 0,
      linear: () => 0,
      random: () => 0,
      clamp: () => 0,
      Math: Math,
      // Objects
      thisComp: {
        duration: 5,
        frameDuration: 1/30,
        width: 1920,
        height: 1080,
        numLayers: 0,
        layer: () => ({
          position: [0, 0],
          scale: [100, 100],
          rotation: 0,
          opacity: 100,
          transform: {},
          effect: () => () => 0,
        }),
      },
      thisLayer: {
        name: '',
        index: 0,
        inPoint: 0,
        outPoint: 5,
        position: [0, 0, 0],
        rotation: [0, 0, 0],
        scale: [100, 100, 100],
        opacity: 100,
        transform: {},
        effect: () => () => 0,
        toComp: () => [0, 0, 0],
        fromComp: () => [0, 0, 0],
      },
      thisProperty: {
        value: 0,
        velocity: 0,
        numKeys: 0,
        key: () => ({ time: 0, value: 0 }),
        nearestKey: () => ({ time: 0, value: 0 }),
        valueAtTime: () => 0,
        velocityAtTime: () => 0,
      },
      footage: () => ({ sourceData: {}, dataValue: () => 0 }),
    };

    const paramNames = Object.keys(mockContextVars);
    const wrappedCode = `
      "use strict";
      return (function() {
        ${code}
      })();
    `;

    // Try to create the function - this validates syntax
    new Function(...paramNames, wrappedCode);

    return { valid: true };
  } catch (error) {
    const err = error as Error;
    let errorMessage = err.message;

    // Try to extract line/column info from error
    let errorLine: number | undefined;
    let errorColumn: number | undefined;

    // Common error message patterns
    const lineMatch = errorMessage.match(/line (\d+)/i);
    const colMatch = errorMessage.match(/column (\d+)/i);

    if (lineMatch) {
      errorLine = parseInt(lineMatch[1], 10) - 4; // Adjust for wrapper lines
    }
    if (colMatch) {
      errorColumn = parseInt(colMatch[1], 10);
    }

    // Clean up error message
    errorMessage = errorMessage
      .replace(/^SyntaxError:\s*/i, '')
      .replace(/\(anonymous\)/g, 'expression');

    return {
      valid: false,
      error: errorMessage,
      errorLine: errorLine && errorLine > 0 ? errorLine : undefined,
      errorColumn,
    };
  }
}

/**
 * Get list of available expression functions for autocomplete/documentation
 */
export function getExpressionFunctions(): Array<{ name: string; description: string; syntax: string }> {
  return [
    { name: 'wiggle', description: 'Random oscillation', syntax: 'wiggle(frequency, amplitude)' },
    { name: 'loopOut', description: 'Loop after last keyframe', syntax: 'loopOut("cycle" | "pingpong" | "offset" | "continue")' },
    { name: 'loopIn', description: 'Loop before first keyframe', syntax: 'loopIn("cycle" | "pingpong" | "offset" | "continue")' },
    { name: 'repeatAfter', description: 'Repeat keyframes after last', syntax: 'repeatAfter("cycle" | "pingpong" | "offset")' },
    { name: 'repeatBefore', description: 'Repeat keyframes before first', syntax: 'repeatBefore("cycle" | "pingpong" | "offset")' },
    { name: 'ease', description: 'Smooth interpolation', syntax: 'ease(t, tMin, tMax, vMin, vMax)' },
    { name: 'easeIn', description: 'Ease in interpolation', syntax: 'easeIn(t, tMin, tMax, vMin, vMax)' },
    { name: 'easeOut', description: 'Ease out interpolation', syntax: 'easeOut(t, tMin, tMax, vMin, vMax)' },
    { name: 'linear', description: 'Linear interpolation', syntax: 'linear(t, tMin, tMax, vMin, vMax)' },
    { name: 'random', description: 'Seeded random number', syntax: 'random() or random(min, max)' },
    { name: 'noise', description: 'Perlin-like noise', syntax: 'noise(value) or noise([x, y, z])' },
    { name: 'clamp', description: 'Clamp value to range', syntax: 'clamp(value, min, max)' },
    { name: 'inertia', description: 'Inertia/overshoot', syntax: 'inertia(amplitude, frequency, decay)' },
    { name: 'bounce', description: 'Bounce at end', syntax: 'bounce(elasticity, gravity)' },
    { name: 'elastic', description: 'Elastic spring', syntax: 'elastic(amplitude, frequency, decay)' },
    { name: 'valueAtTime', description: 'Property value at time', syntax: 'valueAtTime(time)' },
    { name: 'velocityAtTime', description: 'Velocity at time', syntax: 'velocityAtTime(time)' },
    { name: 'key', description: 'Get keyframe by index', syntax: 'key(index)' },
    { name: 'nearestKey', description: 'Get nearest keyframe', syntax: 'nearestKey(time)' },
    { name: 'footage', description: 'Access data file', syntax: 'footage("filename.csv").dataValue([row, col])' },
  ];
}

