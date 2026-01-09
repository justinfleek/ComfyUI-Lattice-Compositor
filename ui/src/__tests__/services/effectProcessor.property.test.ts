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
// STRICT EFFECT STACK PROCESSING TESTS
// NOTE: These tests require browser canvas API - skipped in Node.js
// TODO: Move to Playwright browser tests
// ============================================================================

describe.skip('STRICT: Effect Stack Processing (BROWSER ONLY)', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
    clearEffectCaches();
  });

  test.prop([
    fc.integer({ min: 10, max: 100 }),
    fc.integer({ min: 10, max: 100 })
  ])('empty effect stack returns input unchanged', (width, height) => {
    const inputCanvas = createTestCanvas(width, height, { r: 128, g: 64, b: 32, a: 255 });
    const effects: EffectInstance[] = [];
    
    const result = processEffectStack(effects, inputCanvas, 0);
    
    // Result should have same dimensions
    expect(result.canvas.width).toBe(width);
    expect(result.canvas.height).toBe(height);
    
    // Result should have same pixels (approximately - some color space conversion may occur)
    const inputCtx = inputCanvas.getContext('2d')!;
    const inputData = inputCtx.getImageData(0, 0, width, height);
    const resultData = result.ctx.getImageData(0, 0, width, height);
    
    // At least first pixel should match
    expect(resultData.data[0]).toBe(inputData.data[0]); // R
    expect(resultData.data[1]).toBe(inputData.data[1]); // G
    expect(resultData.data[2]).toBe(inputData.data[2]); // B
    expect(resultData.data[3]).toBe(inputData.data[3]); // A
  });

  test.prop([arbitraryEffectStack()])('disabled effects do not modify output', (effects) => {
    const inputCanvas = createTestCanvas(50, 50, { r: 100, g: 100, b: 100, a: 255 });
    
    // Disable all effects
    const disabledEffects = effects.map(e => ({ ...e, enabled: false }));
    
    const result = processEffectStack(disabledEffects, inputCanvas, 0);
    
    // Output should match input
    const inputCtx = inputCanvas.getContext('2d')!;
    const inputData = inputCtx.getImageData(0, 0, 50, 50);
    const resultData = result.ctx.getImageData(0, 0, 50, 50);
    
    // Compare first few pixels
    for (let i = 0; i < 20; i += 4) {
      expect(resultData.data[i]).toBe(inputData.data[i]);
      expect(resultData.data[i + 1]).toBe(inputData.data[i + 1]);
      expect(resultData.data[i + 2]).toBe(inputData.data[i + 2]);
      expect(resultData.data[i + 3]).toBe(inputData.data[i + 3]);
    }
  });

  it('hasEnabledEffects correctly identifies enabled effects', () => {
    const disabledEffects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', enabled: false, parameters: {} },
    ];
    
    const mixedEffects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', enabled: true, parameters: {} },
    ];
    
    const allEnabled: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', enabled: true, parameters: {} },
    ];
    
    expect(hasEnabledEffects(disabledEffects)).toBe(false);
    expect(hasEnabledEffects(mixedEffects)).toBe(true);
    expect(hasEnabledEffects(allEnabled)).toBe(true);
    expect(hasEnabledEffects([])).toBe(false);
  });
});

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe.skip('STRICT: Effect Processing Determinism (BROWSER ONLY)', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
    clearEffectCaches();
  });

  test.prop([
    fc.integer({ min: 0, max: 100 })
  ], { numRuns: 30 })('same input + same params = same output', (frame) => {
    const effects: EffectInstance[] = [
      {
        id: 'test-blur',
        effectKey: 'blur',
        name: 'Test Blur',
        enabled: true,
        parameters: {
          radius: { name: 'radius', value: 5, keyframes: [] },
        },
      },
    ];
    
    const canvas1 = createTestCanvas(50, 50, { r: 128, g: 64, b: 32, a: 255 });
    const canvas2 = createTestCanvas(50, 50, { r: 128, g: 64, b: 32, a: 255 });
    
    // Process twice with identical inputs
    clearEffectCaches(); // Ensure no caching affects results
    const result1 = processEffectStack(effects, canvas1, frame);
    
    clearEffectCaches();
    const result2 = processEffectStack(effects, canvas2, frame);
    
    // Get pixel data from both results
    const data1 = result1.ctx.getImageData(0, 0, 50, 50);
    const data2 = result2.ctx.getImageData(0, 0, 50, 50);
    
    // Should be byte-identical
    for (let i = 0; i < data1.data.length; i++) {
      expect(data1.data[i]).toBe(data2.data[i]);
    }
  });
});

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

// ============================================================================
// STRICT INPUT VALIDATION TESTS
// ============================================================================

describe.skip('STRICT: Effect Input Validation (BROWSER ONLY)', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
    clearEffectCaches();
  });

  test.prop([
    fc.integer({ min: 1, max: 200 }),
    fc.integer({ min: 1, max: 200 })
  ])('effect preserves canvas dimensions', (width, height) => {
    const effects: EffectInstance[] = [
      {
        id: 'test',
        effectKey: 'brightness',
        name: 'Brightness',
        enabled: true,
        parameters: {
          amount: { name: 'amount', value: 1.5, keyframes: [] },
        },
      },
    ];
    
    const inputCanvas = createTestCanvas(width, height, { r: 128, g: 128, b: 128, a: 255 });
    const result = processEffectStack(effects, inputCanvas, 0);
    
    // Dimensions should be preserved
    expect(result.canvas.width).toBe(width);
    expect(result.canvas.height).toBe(height);
  });

  // NOTE: Alpha channel preservation test skipped.
  // Happy-dom's canvas implementation does not properly preserve alpha values
  // during putImageData/drawImage operations. This is a test environment limitation,
  // not a bug in the actual effect processor code.
  // NOTE: Alpha channel preservation tests are in browser/effectProcessor.browser.test.ts
});

// ============================================================================
// STRICT RENDERER REGISTRATION TESTS
// ============================================================================

describe.skip('STRICT: Effect Renderer Registration (BROWSER ONLY)', () => {
  it('getRegisteredEffects returns registered effect keys', () => {
    const effects = getRegisteredEffects();
    
    // Should return an array
    expect(Array.isArray(effects)).toBe(true);
    
    // All entries should be strings
    for (const key of effects) {
      expect(typeof key).toBe('string');
    }
  });

  it('registerEffectRenderer adds new renderer', () => {
    const testKey = `test-effect-${Date.now()}`;
    let renderCalled = false;
    
    // Register a test renderer
    registerEffectRenderer(testKey, (input, params) => {
      renderCalled = true;
      return input;
    });
    
    // Verify it's registered
    const effects = getRegisteredEffects();
    expect(effects).toContain(testKey);
    
    // Create effect using this renderer
    const effect: EffectInstance = {
      id: 'test',
      effectKey: testKey,
      name: 'Test',
      enabled: true,
      parameters: {},
    };
    
    const inputCanvas = createTestCanvas(10, 10, { r: 128, g: 128, b: 128, a: 255 });
    processEffectStack([effect], inputCanvas, 0);
    
    // Renderer should have been called
    expect(renderCalled).toBe(true);
  });

  it('unregistered effect throws error (BUG-069 fix: loud failure)', () => {
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'definitely-not-registered-effect-xyz',
      name: 'Unknown',
      enabled: true,
      parameters: {},
    };
    
    const inputCanvas = createTestCanvas(10, 10, { r: 128, g: 128, b: 128, a: 255 });
    
    // BUG-069 FIX: Should now throw instead of silently continuing
    expect(() => {
      processEffectStack([effect], inputCanvas, 0);
    }).toThrow(/EFFECT RENDERER NOT FOUND/);
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe.skip('STRESS: Effect Pipeline Under Load (BROWSER ONLY)', () => {
  beforeEach(() => {
    setupMockEffectRenderers();
    clearEffectCaches();
  });

  // Determinism test: Same frame should produce identical output
  // This is NOT a property test because determinism is binary - it works or it doesn't
  // Canvas size is fixed at a realistic 256x256 to catch real-world issues
  test('effect processing is deterministic at realistic canvas size', { timeout: 15000 }, () => {
    const canvasSize = 256; // Realistic size, not tiny
    const testFrames = [0, 25, 50, 75, 100]; // Key frames across animation
    
    const effects: EffectInstance[] = [
      {
        id: 'animated-blur',
        effectKey: 'blur',
        name: 'Animated Blur',
        enabled: true,
        parameters: {
          radius: {
            name: 'radius',
            value: 5,
            animated: true,
            keyframes: [
              { frame: 0, value: 0, easing: 'linear' },
              { frame: 100, value: 10, easing: 'linear' },
            ],
          },
        },
      },
    ];
    
    const inputCanvas = createTestCanvas(canvasSize, canvasSize, { r: 128, g: 64, b: 32, a: 255 });
    const results = new Map<number, Uint8ClampedArray>();
    
    // First pass: evaluate all frames
    for (const frame of testFrames) {
      clearEffectCaches();
      const result = processEffectStack(effects, inputCanvas, frame);
      const data = result.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
      results.set(frame, new Uint8ClampedArray(data));
    }
    
    // Second pass: re-evaluate and verify determinism
    for (const frame of testFrames) {
      clearEffectCaches();
      const result = processEffectStack(effects, inputCanvas, frame);
      const newData = result.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
      const originalData = results.get(frame)!;
      
      // Every pixel must match - determinism is absolute
      for (let i = 0; i < newData.length; i++) {
        expect(newData[i]).toBe(originalData[i]);
      }
    }
  });

  // Property test: Random frame selection still produces consistent results
  // Smaller canvas (64x64) to allow more iterations without timeout
  // The 256x256 test above validates realistic sizes; this validates random frame selection
  test.prop([
    fc.integer({ min: 0, max: 100 }) // Single random frame
  ], { numRuns: 20 })('any random frame evaluates deterministically', (frame) => {
    const canvasSize = 64; // Smaller for property testing speed
    
    const effects: EffectInstance[] = [
      {
        id: 'brightness-effect',
        effectKey: 'brightness',
        name: 'Brightness',
        enabled: true,
        parameters: {
          amount: {
            name: 'amount',
            value: 1.0,
            animated: true,
            keyframes: [
              { frame: 0, value: 0.5, easing: 'linear' },
              { frame: 100, value: 1.5, easing: 'linear' },
            ],
          },
        },
      },
    ];
    
    const inputCanvas = createTestCanvas(canvasSize, canvasSize, { r: 100, g: 100, b: 100, a: 255 });
    
    // Evaluate twice
    clearEffectCaches();
    const result1 = processEffectStack(effects, inputCanvas, frame);
    const data1 = result1.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
    
    clearEffectCaches();
    const result2 = processEffectStack(effects, inputCanvas, frame);
    const data2 = result2.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
    
    // Must match
    expect(data1.length).toBe(data2.length);
    for (let i = 0; i < data1.length; i++) {
      expect(data1[i]).toBe(data2[i]);
    }
  });

  test.prop([
    fc.integer({ min: 1, max: 10 })
  ])('large effect stack processes without error', (effectCount) => {
    const effects: EffectInstance[] = [];
    for (let i = 0; i < effectCount; i++) {
      effects.push({
        id: `effect-${i}`,
        effectKey: 'brightness',
        name: `Effect ${i}`,
        enabled: true,
        parameters: {
          amount: { name: 'amount', value: 1.0, keyframes: [] },
        },
      });
    }
    
    const inputCanvas = createTestCanvas(50, 50, { r: 128, g: 128, b: 128, a: 255 });
    
    // Should not throw
    expect(() => {
      processEffectStack(effects, inputCanvas, 0);
    }).not.toThrow();
  });
});
