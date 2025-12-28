/**
 * Vector Math Expressions
 *
 * Vector operations for expression evaluation.
 * Includes add, sub, mul, div, normalize, dot, cross, length, clamp.
 */

// ============================================================
// VECTOR MATH FUNCTIONS
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
  // BUG-018: Use ?? with Infinity defaults for missing array elements
  // || 0 was wrong - caused values to be clamped to 0 instead of passing through
  return vec.map((v, i) => {
    const minVal = Array.isArray(min) ? (min[i] ?? -Infinity) : min;
    const maxVal = Array.isArray(max) ? (max[i] ?? Infinity) : max;
    return Math.max(minVal, Math.min(maxVal, v));
  });
}

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
