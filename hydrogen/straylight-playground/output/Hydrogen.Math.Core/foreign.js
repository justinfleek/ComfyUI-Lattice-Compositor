// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // math
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Core math functions via JavaScript Math object
// These are the foundational operations that Color, Dimension, and other
// pillars depend on.

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // constants
// ═══════════════════════════════════════════════════════════════════════════════

export const pi = Math.PI;
export const e = Math.E;
export const tau = Math.PI * 2;
export const sqrt2 = Math.SQRT2;
export const sqrt1_2 = Math.SQRT1_2;
export const ln2 = Math.LN2;
export const ln10 = Math.LN10;
export const log2e = Math.LOG2E;
export const log10e = Math.LOG10E;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // power & roots
// ═══════════════════════════════════════════════════════════════════════════════

export const pow = (base) => (exponent) => Math.pow(base, exponent);
export const sqrt = (x) => Math.sqrt(x);
export const cbrt = (x) => Math.cbrt(x);
export const hypot = (x) => (y) => Math.hypot(x, y);
export const hypot3 = (x) => (y) => (z) => Math.hypot(x, y, z);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // trigonometry
// ═══════════════════════════════════════════════════════════════════════════════

export const sin = (x) => Math.sin(x);
export const cos = (x) => Math.cos(x);
export const tan = (x) => Math.tan(x);
export const asin = (x) => Math.asin(x);
export const acos = (x) => Math.acos(x);
export const atan = (x) => Math.atan(x);
export const atan2 = (y) => (x) => Math.atan2(y, x);
export const sinh = (x) => Math.sinh(x);
export const cosh = (x) => Math.cosh(x);
export const tanh = (x) => Math.tanh(x);
export const asinh = (x) => Math.asinh(x);
export const acosh = (x) => Math.acosh(x);
export const atanh = (x) => Math.atanh(x);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // exponential
// ═══════════════════════════════════════════════════════════════════════════════

export const exp = (x) => Math.exp(x);
export const expm1 = (x) => Math.expm1(x);
export const log = (x) => Math.log(x);
export const log10 = (x) => Math.log10(x);
export const log2 = (x) => Math.log2(x);
export const log1p = (x) => Math.log1p(x);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // rounding
// ═══════════════════════════════════════════════════════════════════════════════

export const floor = (x) => Math.floor(x);
export const ceil = (x) => Math.ceil(x);
export const round = (x) => Math.round(x);
export const trunc = (x) => Math.trunc(x);
export const fround = (x) => Math.fround(x);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // misc
// ═══════════════════════════════════════════════════════════════════════════════

export const abs = (x) => Math.abs(x);
export const sign = (x) => Math.sign(x);
export const min = (a) => (b) => Math.min(a, b);
export const max = (a) => (b) => Math.max(a, b);
export const minArray = (arr) => Math.min(...arr);
export const maxArray = (arr) => Math.max(...arr);
export const clamp = (minVal) => (maxVal) => (x) => Math.min(maxVal, Math.max(minVal, x));

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // random
// ═══════════════════════════════════════════════════════════════════════════════

// Note: random is effectful, handled separately
export const randomImpl = () => Math.random();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // special values
// ═══════════════════════════════════════════════════════════════════════════════

export const isNaN = (x) => Number.isNaN(x);
export const isFinite = (x) => Number.isFinite(x);
export const isInteger = (x) => Number.isInteger(x);
export const infinity = Infinity;
export const negativeInfinity = -Infinity;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // interpolation & easing
// ═══════════════════════════════════════════════════════════════════════════════

// Linear interpolation
export const lerp = (a) => (b) => (t) => a + (b - a) * t;

// Inverse lerp (find t given value)
export const inverseLerp = (a) => (b) => (v) => (v - a) / (b - a);

// Remap from one range to another
export const remap = (inMin) => (inMax) => (outMin) => (outMax) => (v) => {
  const t = (v - inMin) / (inMax - inMin);
  return outMin + (outMax - outMin) * t;
};

// Smoothstep (cubic hermite interpolation)
export const smoothstep = (edge0) => (edge1) => (x) => {
  const t = Math.max(0, Math.min(1, (x - edge0) / (edge1 - edge0)));
  return t * t * (3 - 2 * t);
};

// Smootherstep (Ken Perlin's improved version)
export const smootherstep = (edge0) => (edge1) => (x) => {
  const t = Math.max(0, Math.min(1, (x - edge0) / (edge1 - edge0)));
  return t * t * t * (t * (t * 6 - 15) + 10);
};
