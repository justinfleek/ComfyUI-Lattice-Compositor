/**
 * Expressions Module - Barrel Export
 *
 * This module organizes expression-related functionality into logical submodules:
 * - types: Type definitions for expression context and related interfaces
 * - easing: All easing functions and presets
 * - motionExpressions: Inertia, bounce, elastic animations
 * - loopExpressions: repeatAfter, repeatBefore
 * - jitterExpressions: jitter, temporalJitter
 * - expressionHelpers: Utility functions for expression evaluation
 * - vectorMath: Vector operations (add, sub, mul, normalize, etc.)
 * - coordinateConversion: toComp, fromComp, toWorld, fromWorld, lookAt
 * - audioExpressions: valueAtTime, posterizeTime, audio reactivity
 * - textAnimator: Per-character text animation
 *
 * Import from '@/services/expressions' for all expression functions.
 */

// Type definitions
export * from './types';

// Easing functions and presets
export * from './easing';

// Motion expressions (inertia, bounce, elastic)
export * from './motionExpressions';

// Loop expressions (repeatAfter, repeatBefore)
export * from './loopExpressions';

// Jitter expressions (jitter, temporalJitter)
export * from './jitterExpressions';

// Expression helpers (interpolateAtTime, value operations)
export * from './expressionHelpers';

// Vector math (add, sub, mul, div, normalize, dot, cross, length, clamp, noise)
export * from './vectorMath';

// Coordinate conversion (toComp, fromComp, toWorld, fromWorld, lookAt, orientToPath)
export * from './coordinateConversion';

// Audio expressions (valueAtTime, posterizeTime, amplitude)
export * from './audioExpressions';

// Text animator (per-character animation)
export * from './textAnimator';
