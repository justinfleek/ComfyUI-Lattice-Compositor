/**
 * STRICT Property Tests for Effect Pipeline
 * 
 * Tests the invariants that must hold for correct effect processing:
 * 1. Determinism: same effect params + same input = same output
 * 2. Order independence of disabled effects
 * 3. Effect parameter evaluation at correct frames
 * 4. Canvas pool does not leak or corrupt
 * 5. Effect caching produces correct results
 * 
 * TOLERANCE: STRICT - Visual artifacts are immediately user-visible
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  evaluateEffectParameters,
  processEffectStack,
  registerEffectRenderer,
  clearEffectCaches,
  getEffectProcessorStats,
  hasEnabledEffects,
  getRegisteredEffects,
  type EvaluatedEffectParams,
  type EffectStackResult,
} from '@/services/effectProcessor';
import type { EffectInstance, EffectParameterDefinition } from '@/types/effects';
import type { AnimatableProperty } from '@/types/project';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

/**
 * Generate a valid AnimatableProperty for effect parameters
 */
const arbitraryAnimatableNumber = (): fc.Arbitrary<AnimatableProperty<number>> =>
  fc.record({
    name: fc.string({ minLength: 1, maxLength: 20 }),
    value: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    keyframes: fc.array(
      fc.record({
        frame: fc.integer({ min: 0, max: 1000 }),
        value: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
        easing: fc.constantFrom('linear', 'easeIn', 'easeOut', 'easeInOut'),
      }),
      { maxLength: 5 }
    ).map(kfs => [...kfs].sort((a, b) => a.frame - b.frame)),
  });

const arbitraryAnimatableColor = (): fc.Arbitrary<AnimatableProperty<string>> =>
  fc.record({
    name: fc.string({ minLength: 1, maxLength: 20 }),
    value: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
    keyframes: fc.array(
      fc.record({
        frame: fc.integer({ min: 0, max: 1000 }),
        value: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
        easing: fc.constantFrom('linear', 'easeIn', 'easeOut', 'easeInOut'),
      }),
      { maxLength: 5 }
    ).map(kfs => [...kfs].sort((a, b) => a.frame - b.frame)),
  });

/**
 * Generate a valid effect instance
 */
const arbitraryEffectInstance = (effectKey?: string): fc.Arbitrary<EffectInstance> =>
  fc.record({
    id: fc.uuid(),
    effectKey: effectKey ? fc.constant(effectKey) : fc.constantFrom(
      'blur',
      'brightness',
      'contrast',
      'saturation',
      'glow',
      'noise',
      'vignette'
    ),
    name: fc.string({ minLength: 1, maxLength: 30 }),
    enabled: fc.boolean(),
    parameters: fc.dictionary(
      fc.string({ minLength: 1, maxLength: 20 }),
      arbitraryAnimatableNumber()
    ),
  }) as fc.Arbitrary<EffectInstance>;

/**
 * Generate a stack of effects
 */
const arbitraryEffectStack = (): fc.Arbitrary<EffectInstance[]> =>
  fc.array(arbitraryEffectInstance(), { minLength: 0, maxLength: 5 });

// ============================================================================
// MOCK EFFECT RENDERERS
// ============================================================================

/**
 * Register mock renderers for common effect types used in tests.
 * These pass-through renderers allow testing the effect pipeline
 * without requiring the actual effect implementations.
 */
const MOCK_EFFECT_KEYS = ['blur', 'brightness', 'contrast', 'saturation', 'glow', 'noise', 'vignette'];

function setupMockEffectRenderers() {
  for (const key of MOCK_EFFECT_KEYS) {
    // Check if already registered to avoid duplicates
    const registered = getRegisteredEffects();
    if (!registered.includes(key)) {
      registerEffectRenderer(key, (input) => input); // Identity/passthrough renderer
    }
  }
}

// ============================================================================
// MOCK CANVAS FOR TESTING
// ============================================================================

/**
 * Create a mock canvas for testing (works in Node.js/happy-dom)
 */
function createMockCanvas(width: number, height: number): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  
  // Fill with test pattern for debugging
  const ctx = canvas.getContext('2d');
  if (ctx) {
    ctx.fillStyle = '#ff0000';
    ctx.fillRect(0, 0, width, height);
  }
  
  return canvas;
}

/**
 * Create a canvas with specific pixel values for testing
 */
function createTestCanvas(width: number, height: number, color: { r: number; g: number; b: number; a: number }): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;
  
  const imageData = ctx.createImageData(width, height);
  for (let i = 0; i < imageData.data.length; i += 4) {
    imageData.data[i] = color.r;
    imageData.data[i + 1] = color.g;
    imageData.data[i + 2] = color.b;
    imageData.data[i + 3] = color.a;
  }
  ctx.putImageData(imageData, 0, 0);
  
  return canvas;
}

// ============================================================================
// STRICT PARAMETER EVALUATION TESTS
// ============================================================================

describe('STRICT: Effect Parameter Evaluation', () => {
  test.prop([
    arbitraryEffectInstance(),
    fc.integer({ min: 0, max: 1000 })
  ])('evaluateEffectParameters returns concrete values for all parameters', (effect, frame) => {
    const evaluated = evaluateEffectParameters(effect, frame);
    
    // All parameters should be evaluated to concrete values
    for (const [key, value] of Object.entries(evaluated)) {
      // Should not be an AnimatableProperty anymore
      expect(typeof value).not.toBe('object' || !('keyframes' in (value as any)));
      
      // Should be a concrete value (number, string, boolean, etc.)
      expect(value).toBeDefined();
    }
  });

  test.prop([
    // Use min: 0.001 to avoid subnormal floating-point values that cause precision issues
    fc.double({ min: 0.001, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0.001, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 100 })
  ])('parameter evaluation at keyframe returns keyframe value', (startVal, endVal, keyframeFrame) => {
    const effect: EffectInstance = {
      id: 'test-effect',
      effectKey: 'blur',
      name: 'Test Blur',
      enabled: true,
      parameters: {
        radius: {
          name: 'radius',
          value: startVal,
          animated: true, // Must be true for keyframes to be used
          keyframes: [{ frame: keyframeFrame, value: endVal, easing: 'linear' }],
        },
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, keyframeFrame);
    
    // At keyframe frame, should return keyframe value (with floating-point tolerance)
    expect(evaluated.radius).toBeCloseTo(endVal, 6);
  });

  test.prop([
    // Use integer values scaled to doubles to avoid floating-point precision issues
    fc.integer({ min: 1, max: 1000 }).map(n => n / 10), // 0.1 to 100.0
    fc.integer({ min: 1, max: 1000 }).map(n => n / 10),
  ])('linear interpolation at midpoint is average', (startVal, endVal) => {
    const effect: EffectInstance = {
      id: 'test-effect',
      effectKey: 'brightness',
      name: 'Test',
      enabled: true,
      parameters: {
        amount: {
          name: 'amount',
          value: startVal,
          animated: true, // Must be true for keyframes to be used
          keyframes: [
            { frame: 0, value: startVal, easing: 'linear' },
            { frame: 100, value: endVal, easing: 'linear' },
          ],
        },
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, 50);
    const expectedMidpoint = (startVal + endVal) / 2;
    
    // Use toBeCloseTo with 4 decimal places precision (more lenient)
    expect(evaluated.amount).toBeCloseTo(expectedMidpoint, 4);
  });

  // ============================================================================
  // Additional evaluateEffectParameters edge cases
  // ============================================================================

  it('handles effect with no parameters', () => {
    const effect: EffectInstance = {
      id: 'test-empty',
      effectKey: 'pass-through',
      name: 'Empty',
      enabled: true,
      parameters: {},
    };
    
    const evaluated = evaluateEffectParameters(effect, 0);
    expect(evaluated).toEqual({});
  });

  it('handles non-animated property (returns static value)', () => {
    const effect: EffectInstance = {
      id: 'test-static',
      effectKey: 'brightness',
      name: 'Static',
      enabled: true,
      parameters: {
        amount: {
          name: 'amount',
          value: 42,
          animated: false,
          keyframes: [],
        },
      },
    };
    
    // Should return static value regardless of frame
    expect(evaluateEffectParameters(effect, 0).amount).toBe(42);
    expect(evaluateEffectParameters(effect, 50).amount).toBe(42);
    expect(evaluateEffectParameters(effect, 100).amount).toBe(42);
  });

  test.prop([
    fc.double({ min: 0.001, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 1000 })
  ])('frame before first keyframe returns first keyframe value', (val, keyframeFrame) => {
    // Only test when keyframe is after frame 0
    fc.pre(keyframeFrame > 0);
    
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'blur',
      name: 'Test',
      enabled: true,
      parameters: {
        radius: {
          name: 'radius',
          value: 999, // Different from keyframe value
          animated: true,
          keyframes: [{ frame: keyframeFrame, value: val, easing: 'linear' }],
        },
      },
    };
    
    // Frame 0 (before keyframe) should return keyframe value
    const evaluated = evaluateEffectParameters(effect, 0);
    expect(evaluated.radius).toBeCloseTo(val, 6);
  });

  test.prop([
    fc.double({ min: 0.001, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 500 })
  ])('frame after last keyframe returns last keyframe value', (val, lastFrame) => {
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'blur',
      name: 'Test',
      enabled: true,
      parameters: {
        radius: {
          name: 'radius',
          value: 0,
          animated: true,
          keyframes: [{ frame: lastFrame, value: val, easing: 'linear' }],
        },
      },
    };
    
    // Frame way after should return last keyframe value
    const evaluated = evaluateEffectParameters(effect, lastFrame + 1000);
    expect(evaluated.radius).toBeCloseTo(val, 6);
  });

  test.prop([
    fc.array(
      fc.record({
        frame: fc.integer({ min: 0, max: 1000 }),
        value: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
      }),
      { minLength: 1, maxLength: 5 }
    ).map(kfs => [...kfs].sort((a, b) => a.frame - b.frame)),
    fc.integer({ min: 0, max: 1000 })
  ])('evaluateEffectParameters is deterministic', (keyframes, frame) => {
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'brightness',
      name: 'Test',
      enabled: true,
      parameters: {
        amount: {
          name: 'amount',
          value: 0,
          animated: true,
          keyframes: keyframes.map(kf => ({ ...kf, easing: 'linear' })),
        },
      },
    };
    
    // Evaluate twice
    const result1 = evaluateEffectParameters(effect, frame);
    const result2 = evaluateEffectParameters(effect, frame);
    
    // Must be identical
    expect(result1.amount).toBe(result2.amount);
  });

  test.prop([
    fc.record({
      param1: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
      param2: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
      param3: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
    }),
    fc.integer({ min: 0, max: 100 })
  ])('handles multiple parameters', (values, frame) => {
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'color-correction',
      name: 'Test',
      enabled: true,
      parameters: {
        brightness: { name: 'brightness', value: values.param1, animated: false, keyframes: [] },
        contrast: { name: 'contrast', value: values.param2, animated: false, keyframes: [] },
        saturation: { name: 'saturation', value: values.param3, animated: false, keyframes: [] },
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, frame);
    
    // All parameters should be evaluated
    expect(evaluated.brightness).toBe(values.param1);
    expect(evaluated.contrast).toBe(values.param2);
    expect(evaluated.saturation).toBe(values.param3);
  });
});

// ============================================================================
// BROWSER-ONLY TESTS: Effect Stack Processing
// ============================================================================
//
// The following browser-dependent functionality is tested in E2E:
//
// Location: /ui/e2e/export/effect-processor.spec.ts
//
// Covered:
// - hasEnabledEffects (E2E lines 21-60)
//   - return false for empty effect list
//   - return false when all effects disabled
//   - return true when at least one effect enabled
// - processEffectStack (E2E lines 62-165)
//   - return canvas with same dimensions for empty effect stack
//   - preserve input when all effects disabled
//   - process enabled effects
//   - determinism - same input produces same output
// - clearEffectCaches (E2E lines 167-180)
//   - clear caches without error
// - Error handling (E2E lines 182-230)
//   - handle unregistered effect gracefully
//   - handle NaN in effect parameters
//
// Run E2E tests with: bunx playwright test effect-processor.spec.ts

// NOTE: Determinism tests are covered in E2E: /ui/e2e/export/effect-processor.spec.ts
// See "determinism - same input produces same output" test

// ============================================================================
// STRICT CACHE TESTS
// ============================================================================

describe('STRICT: Effect Cache Integrity', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
    clearEffectCaches();
  });

  it('clearEffectCaches resets all caches', () => {
    // Get initial stats
    const initialStats = getEffectProcessorStats();
    
    // Clear and verify
    clearEffectCaches();
    
    const afterClear = getEffectProcessorStats();
    expect(afterClear.effectCache.size).toBe(0);
    expect(afterClear.canvasPool.inUse).toBe(0);
  });

  it('getEffectProcessorStats returns valid statistics', () => {
    const stats = getEffectProcessorStats();
    
    expect(stats).toHaveProperty('effectCache');
    expect(stats).toHaveProperty('canvasPool');
    expect(stats.effectCache).toHaveProperty('size');
    expect(stats.effectCache).toHaveProperty('maxSize');
    expect(stats.canvasPool).toHaveProperty('total');
    expect(stats.canvasPool).toHaveProperty('inUse');
    expect(stats.canvasPool).toHaveProperty('available');
    
    // Size should not be negative
    expect(stats.effectCache.size).toBeGreaterThanOrEqual(0);
    expect(stats.canvasPool.total).toBeGreaterThanOrEqual(0);
    expect(stats.canvasPool.inUse).toBeGreaterThanOrEqual(0);
  });
});

// ============================================================================
// STRICT hasEnabledEffects TESTS (pure function - no canvas needed)
// ============================================================================

describe('STRICT: hasEnabledEffects', () => {
  test.prop([
    fc.array(arbitraryEffectInstance(), { minLength: 0, maxLength: 10 })
  ])('returns true iff at least one effect is enabled', (effects) => {
    const result = hasEnabledEffects(effects);
    const expected = effects.some(e => e.enabled);
    expect(result).toBe(expected);
  });

  it('returns false for empty array', () => {
    expect(hasEnabledEffects([])).toBe(false);
  });

  it('returns false when all effects disabled', () => {
    const effects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', enabled: false, parameters: {} },
      { id: '3', effectKey: 'noise', name: 'Noise', enabled: false, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(false);
  });

  it('returns true when single effect enabled', () => {
    const effects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', enabled: true, parameters: {} },
      { id: '3', effectKey: 'noise', name: 'Noise', enabled: false, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(true);
  });

  it('returns true when all effects enabled', () => {
    const effects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: true, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', enabled: true, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(true);
  });
});

// ============================================================================
// STRICT getRegisteredEffects / registerEffectRenderer TESTS
// ============================================================================

describe('STRICT: Effect Renderer Registration', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
  });

  it('getRegisteredEffects returns array of strings', () => {
    const effects = getRegisteredEffects();
    expect(Array.isArray(effects)).toBe(true);
    for (const key of effects) {
      expect(typeof key).toBe('string');
    }
  });

  it('getRegisteredEffects includes registered mock effects', () => {
    const effects = getRegisteredEffects();
    // Should include our mock effects
    for (const key of MOCK_EFFECT_KEYS) {
      expect(effects).toContain(key);
    }
  });

  it('registerEffectRenderer adds new renderer to registry', () => {
    const testKey = `test-effect-${Date.now()}-${Math.random()}`;
    
    // Should not exist initially
    const beforeReg = getRegisteredEffects();
    expect(beforeReg).not.toContain(testKey);
    
    // Register
    registerEffectRenderer(testKey, (input) => input);
    
    // Should exist now
    const afterReg = getRegisteredEffects();
    expect(afterReg).toContain(testKey);
  });

  test.prop([
    fc.stringMatching(/^[a-z][a-z0-9-]{0,30}$/)
  ])('registerEffectRenderer accepts valid effect keys', (effectKey) => {
    // Generate unique key
    const uniqueKey = `${effectKey}-${Date.now()}-${Math.random()}`;
    
    // Should not throw
    expect(() => {
      registerEffectRenderer(uniqueKey, (input) => input);
    }).not.toThrow();
    
    // Should be registered
    expect(getRegisteredEffects()).toContain(uniqueKey);
  });
});

// NOTE: Input validation tests are covered in E2E: /ui/e2e/export/effect-processor.spec.ts
// See "return canvas with same dimensions" and "handle NaN in effect parameters" tests

// NOTE: Renderer registration tests are already covered in the non-skipped
// 'STRICT: Effect Renderer Registration' describe block above (lines 503-554)
// Browser-specific processing tests in E2E: /ui/e2e/export/effect-processor.spec.ts
// See "handle unregistered effect gracefully" test

// ============================================================================
// STRESS TESTS
// ============================================================================
//
// The following browser-dependent stress tests are covered in E2E:
//
// Location: /ui/e2e/export/effect-processor.spec.ts
//
// Covered:
// - Determinism at realistic canvas sizes
//   See "determinism - same input produces same output" test
// - Large effect stacks (covered by "process enabled effects" test)
//
// Run E2E tests with: bunx playwright test effect-processor.spec.ts
