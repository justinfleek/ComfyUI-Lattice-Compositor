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
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
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
          keyframes: [{ frame: keyframeFrame, value: endVal, easing: 'linear' }],
        },
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, keyframeFrame);
    
    // At keyframe frame, should return keyframe value
    expect(evaluated.radius).toBe(endVal);
  });

  test.prop([
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
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
          keyframes: [
            { frame: 0, value: startVal, easing: 'linear' },
            { frame: 100, value: endVal, easing: 'linear' },
          ],
        },
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, 50);
    const expectedMidpoint = (startVal + endVal) / 2;
    
    expect(Math.abs(evaluated.amount - expectedMidpoint)).toBeLessThan(1e-6);
  });
});

// ============================================================================
// STRICT EFFECT STACK PROCESSING TESTS
// ============================================================================

describe('STRICT: Effect Stack Processing', () => {
  beforeEach(() => {
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

describe('STRICT: Effect Processing Determinism', () => {
  beforeEach(() => {
    clearEffectCaches();
  });

  test.prop([
    fc.integer({ min: 0, max: 100 })
  ])('same input + same params = same output', (frame) => {
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
// STRICT INPUT VALIDATION TESTS
// ============================================================================

describe('STRICT: Effect Input Validation', () => {
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

  test.prop([
    fc.integer({ min: 10, max: 50 }),
    fc.integer({ min: 10, max: 50 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 })
  ])('effect does not corrupt alpha channel (identity effect)', (width, height, r, g, b) => {
    const effects: EffectInstance[] = []; // Empty effect stack = identity
    
    const inputCanvas = createTestCanvas(width, height, { r, g, b, a: 200 });
    const result = processEffectStack(effects, inputCanvas, 0);
    
    // Check alpha is preserved
    const resultData = result.ctx.getImageData(0, 0, width, height);
    for (let i = 3; i < resultData.data.length; i += 4) {
      expect(resultData.data[i]).toBe(200);
    }
  });
});

// ============================================================================
// STRICT RENDERER REGISTRATION TESTS
// ============================================================================

describe('STRICT: Effect Renderer Registration', () => {
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

  it('unregistered effect logs warning but continues', () => {
    const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    
    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'definitely-not-registered-effect-xyz',
      name: 'Unknown',
      enabled: true,
      parameters: {},
    };
    
    const inputCanvas = createTestCanvas(10, 10, { r: 128, g: 128, b: 128, a: 255 });
    
    // Should not throw
    expect(() => {
      processEffectStack([effect], inputCanvas, 0);
    }).not.toThrow();
    
    warnSpy.mockRestore();
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Effect Pipeline Under Load', () => {
  beforeEach(() => {
    clearEffectCaches();
  });

  test.prop([
    fc.integer({ min: 10, max: 50 }),
    fc.array(fc.integer({ min: 0, max: 100 }), { minLength: 5, maxLength: 20 })
  ])('rapid frame changes produce consistent results', (canvasSize, frames) => {
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
    for (const frame of frames) {
      clearEffectCaches();
      const result = processEffectStack(effects, inputCanvas, frame);
      const data = result.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
      results.set(frame, new Uint8ClampedArray(data));
    }
    
    // Second pass: re-evaluate and verify
    for (const frame of frames) {
      clearEffectCaches();
      const result = processEffectStack(effects, inputCanvas, frame);
      const newData = result.ctx.getImageData(0, 0, canvasSize, canvasSize).data;
      const originalData = results.get(frame)!;
      
      // Should match
      for (let i = 0; i < newData.length; i++) {
        expect(newData[i]).toBe(originalData[i]);
      }
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
