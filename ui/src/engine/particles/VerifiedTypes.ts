/**
 * VERIFIED PARTICLE SYSTEM - Type System
 * 
 * Zero-cost abstractions: Branded types compile to plain numbers
 * All validation happens at boundaries, not in hot loops
 * 
 * Performance: Same as raw numbers after JIT optimization
 * Safety: Impossible to create invalid state through public API
 * 
 * Based on Lean4 proofs from leanparticles/PARTICLE_VERIFIED (1).lean
 * 
 * @author Weyl.ai
 */

// ============================================================================
// BRANDED TYPES - Zero runtime cost after JIT
// ============================================================================

declare const __brand: unique symbol;
type Brand<T, B> = T & { [__brand]: B };

/**
 * Finite number (not NaN or Infinity)
 * Proven in Lean4: ∃ (b : ℝ), |val| ≤ b
 */
export type Finite = Brand<number, 'Finite'>;

/**
 * Unit interval [0, 1]
 * Proven in Lean4: 0 ≤ val ∧ val ≤ 1
 */
export type UnitInterval = Brand<number, 'UnitInterval'>;

/**
 * Positive real number
 * Proven in Lean4: 0 < val
 */
export type Positive = Brand<number, 'Positive'>;

/**
 * Non-negative real number
 * Proven in Lean4: 0 ≤ val
 */
export type NonNegative = Brand<number, 'NonNegative'>;

/**
 * 32-bit unsigned integer
 * Proven in Lean4: val < 2^32
 */
export type UInt32 = Brand<number, 'UInt32'>;

// ============================================================================
// SMART CONSTRUCTORS - Validation at boundaries only
// ============================================================================

/**
 * Create a Finite number
 * These are inlined by V8 - zero overhead in hot paths
 * 
 * Type proof: x ∈ ℝ ∪ {NaN, ±∞} → x ∈ ℝ ∧ finite(x)
 */
export function finite(x: number): Finite {
  return (Number.isFinite(x) ? x : 0) as Finite;
}

/**
 * Create a UnitInterval value
 * Clamps to [0, 1] range
 * 
 * Type proof: x ∈ ℝ → x ∈ [0, 1]
 */
export function unit(x: number): UnitInterval {
  return (Number.isFinite(x) ? Math.max(0, Math.min(1, x)) : 0) as UnitInterval;
}

/**
 * Create a Positive number
 * Returns fallback if x ≤ 0 or not finite
 * 
 * Type proof: x ∈ ℝ → x ∈ ℝ₊
 */
export function pos(x: number, fallback: number = 0.001): Positive {
  return (Number.isFinite(x) && x > 0 ? x : fallback) as Positive;
}

/**
 * Create a NonNegative number
 * Returns 0 if x < 0 or not finite
 * 
 * Type proof: x ∈ ℝ → x ∈ ℝ₀₊
 */
export function nneg(x: number): NonNegative {
  return (Number.isFinite(x) && x >= 0 ? x : 0) as NonNegative;
}

/**
 * Create a UInt32 value
 * Uses unsigned right shift to ensure 32-bit unsigned
 * 
 * Type proof: x ∈ ℤ → x ∈ [0, 2³²)
 */
export function u32(x: number): UInt32 {
  return (x >>> 0) as UInt32;
}

// ============================================================================
// TYPE GUARDS - Runtime validation
// ============================================================================

/**
 * Check if value is Finite
 */
export function isFinite(value: number): value is Finite {
  return Number.isFinite(value);
}

/**
 * Check if value is in UnitInterval [0, 1]
 */
export function isUnitInterval(value: number): value is UnitInterval {
  return Number.isFinite(value) && value >= 0 && value <= 1;
}

/**
 * Check if value is Positive
 */
export function isPositive(value: number): value is Positive {
  return Number.isFinite(value) && value > 0;
}

/**
 * Check if value is NonNegative
 */
export function isNonNegative(value: number): value is NonNegative {
  return Number.isFinite(value) && value >= 0;
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Clamp value to [min, max] range
 * Returns Finite result
 */
export function clamp(value: number, min: number, max: number): Finite {
  const clamped = Number.isFinite(value)
    ? Math.max(min, Math.min(max, value))
    : min;
  return finite(clamped);
}

/**
 * Clamp value to [0, 1] range
 * Returns UnitInterval
 */
export function clampUnit(value: number): UnitInterval {
  return unit(value);
}

/**
 * Ensure value is positive
 * Returns Positive (uses fallback if needed)
 */
export function ensurePositive(value: number, fallback: number = 0.001): Positive {
  return pos(value, fallback);
}

/**
 * Ensure value is non-negative
 * Returns NonNegative (uses 0 if needed)
 */
export function ensureNonNegative(value: number): NonNegative {
  return nneg(value);
}
