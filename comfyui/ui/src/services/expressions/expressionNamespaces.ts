/**
 * Expression Namespaces
 *
 * Convenience namespace objects that group related expression functions.
 * These provide organized access to expression capabilities.
 */

import {
  cubicBezier,
  easeInBack,
  easeInBounce,
  easeInCirc,
  easeInCubic,
  easeInElastic,
  easeInExpo,
  easeInOutBack,
  easeInOutBounce,
  easeInOutCirc,
  easeInOutCubic,
  easeInOutElastic,
  easeInOutExpo,
  easeInOutQuad,
  easeInOutQuart,
  easeInOutQuint,
  easeInOutSine,
  easeInQuad,
  easeInQuart,
  easeInQuint,
  easeInSine,
  easeOutBack,
  easeOutBounce,
  easeOutCirc,
  easeOutCubic,
  easeOutElastic,
  easeOutExpo,
  easeOutQuad,
  easeOutQuart,
  easeOutQuint,
  easeOutSine,
  linear,
  stepEnd,
  stepStart,
} from "./easing";
import { mathExpressions, timeExpressions } from "./expressionEvaluator";
import { jitter, temporalJitter } from "./jitterExpressions";
import { repeatAfter, repeatBefore } from "./loopExpressions";
import { bounce, elastic, inertia } from "./motionExpressions";

// ============================================================
// NAMESPACE EXPORTS
// ============================================================

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
