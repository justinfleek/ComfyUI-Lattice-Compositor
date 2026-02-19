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
import type { EffectInstance, EffectCategory } from '@/types/effects';
import type { AnimatableProperty, Keyframe, BezierHandle, ControlMode, InterpolationType } from '@/types/animation';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                   // helper // functions // for // type // safe // fixtures
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create a properly-typed BezierHandle
 */
function createHandle(frame: number, value: number, enabled: boolean = false): BezierHandle {
  return { frame, value, enabled };
}

/**
 * Create a properly-typed Keyframe
 */
function createKeyframe<T>(
  frame: number,
  value: T,
  interpolation: InterpolationType = 'linear'
): Keyframe<T> {
  return {
    id: `kf-${frame}-${Math.random().toString(36).slice(2, 8)}`,
    frame,
    value,
    interpolation,
    inHandle: createHandle(-5, 0, interpolation === 'bezier'),
    outHandle: createHandle(5, 0, interpolation === 'bezier'),
    controlMode: 'smooth' as ControlMode,
  };
}

/**
 * Create a properly-typed AnimatableProperty
 */
function createAnimatableProperty<T>(
  name: string,
  value: T,
  type: AnimatableProperty<T>['type'] = 'number',
  keyframes: Keyframe<T>[] = [],
  animated: boolean = keyframes.length > 0
): AnimatableProperty<T> {
  return {
    id: `prop-${name}-${Math.random().toString(36).slice(2, 8)}`,
    name,
    type,
    value,
    animated,
    keyframes,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                               // test // data // generators
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Generate a valid AnimatableProperty for effect parameters
 */
const arbitraryAnimatableNumber = (): fc.Arbitrary<AnimatableProperty<number>> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    type: fc.constant('number' as const),
    value: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    animated: fc.boolean(),
    keyframes: fc.array(
      fc.record({
        id: fc.uuid(),
        frame: fc.integer({ min: 0, max: 1000 }),
        value: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
        interpolation: fc.constantFrom('linear', 'bezier', 'hold') as fc.Arbitrary<InterpolationType>,
        inHandle: fc.record({
          frame: fc.integer({ min: -10, max: 0 }),
          value: fc.double({ min: -1, max: 1, noNaN: true, noDefaultInfinity: true }),
          enabled: fc.boolean(),
        }),
        outHandle: fc.record({
          frame: fc.integer({ min: 0, max: 10 }),
          value: fc.double({ min: -1, max: 1, noNaN: true, noDefaultInfinity: true }),
          enabled: fc.boolean(),
        }),
        controlMode: fc.constantFrom('smooth', 'corner', 'autoSmooth', 'free') as fc.Arbitrary<ControlMode>,
      }),
      { maxLength: 5 }
    ).map(kfs => [...kfs].sort((a, b) => a.frame - b.frame)),
  }) as fc.Arbitrary<AnimatableProperty<number>>;

const arbitraryAnimatableColor = (): fc.Arbitrary<AnimatableProperty<string>> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    type: fc.constant('color' as const),
    value: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
    animated: fc.boolean(),
    keyframes: fc.array(
      fc.record({
        id: fc.uuid(),
        frame: fc.integer({ min: 0, max: 1000 }),
        value: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
        interpolation: fc.constantFrom('linear', 'bezier', 'hold') as fc.Arbitrary<InterpolationType>,
        inHandle: fc.record({
          frame: fc.integer({ min: -10, max: 0 }),
          value: fc.double({ min: -1, max: 1, noNaN: true, noDefaultInfinity: true }),
          enabled: fc.boolean(),
        }),
        outHandle: fc.record({
          frame: fc.integer({ min: 0, max: 10 }),
          value: fc.double({ min: -1, max: 1, noNaN: true, noDefaultInfinity: true }),
          enabled: fc.boolean(),
        }),
        controlMode: fc.constantFrom('smooth', 'corner', 'autoSmooth', 'free') as fc.Arbitrary<ControlMode>,
      }),
      { maxLength: 5 }
    ).map(kfs => [...kfs].sort((a, b) => a.frame - b.frame)),
  }) as fc.Arbitrary<AnimatableProperty<string>>;

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
    category: fc.constantFrom(
      'blur-sharpen',
      'color-correction',
      'distort',
      'generate',
      'stylize'
    ) as fc.Arbitrary<EffectCategory>,
    enabled: fc.boolean(),
    expanded: fc.boolean(),
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

// ═══════════════════════════════════════════════════════════════════════════
//                                              // mock // effect // renderers
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
//                                         // mock // canvas // for // testing
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
//                               // strict // parameter // evaluation // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Effect Parameter Evaluation', () => {
  test.prop([
    arbitraryEffectInstance(),
    fc.integer({ min: 0, max: 1000 })
  ])('evaluateEffectParameters returns concrete values for all parameters', (effect, frame) => {
    const evaluated = evaluateEffectParameters(effect, frame);
    
    // All parameters should be evaluated to concrete values
    for (const [key, value] of Object.entries(evaluated)) {
      // Should not be an AnimatableProperty anymore (shouldn't have keyframes)
      if (typeof value === 'object' && value !== null) {
        expect(value).not.toHaveProperty('keyframes');
      }

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
      category: 'blur-sharpen',
      enabled: true,
      expanded: false,
      parameters: {
        radius: createAnimatableProperty('radius', startVal, 'number', [
          createKeyframe(keyframeFrame, endVal, 'linear'),
        ], true),
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
      category: 'color-correction',
      enabled: true,
      expanded: false,
      parameters: {
        amount: createAnimatableProperty('amount', startVal, 'number', [
          createKeyframe(0, startVal, 'linear'),
          createKeyframe(100, endVal, 'linear'),
        ], true),
      },
    };
    
    const evaluated = evaluateEffectParameters(effect, 50);
    const expectedMidpoint = (startVal + endVal) / 2;
    
    // Use toBeCloseTo with 4 decimal places precision (more lenient)
    expect(evaluated.amount).toBeCloseTo(expectedMidpoint, 4);
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // Additional evaluateEffectParameters edge cases
  // ═══════════════════════════════════════════════════════════════════════════

  it('handles effect with no parameters', () => {
    const effect: EffectInstance = {
      id: 'test-empty',
      effectKey: 'pass-through',
      name: 'Empty',
      category: 'utility',
      enabled: true,
      expanded: false,
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
      category: 'color-correction',
      enabled: true,
      expanded: false,
      parameters: {
        amount: createAnimatableProperty('amount', 42, 'number', [], false),
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
      category: 'blur-sharpen',
      enabled: true,
      expanded: false,
      parameters: {
        radius: createAnimatableProperty('radius', 999, 'number', [
          createKeyframe(keyframeFrame, val, 'linear'),
        ], true),
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
      category: 'blur-sharpen',
      enabled: true,
      expanded: false,
      parameters: {
        radius: createAnimatableProperty('radius', 0, 'number', [
          createKeyframe(lastFrame, val, 'linear'),
        ], true),
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
  ])('evaluateEffectParameters is deterministic', (keyframeData, frame) => {
    // Convert the generated keyframe data to proper Keyframe<number> objects
    const keyframes = keyframeData.map(kf => createKeyframe(kf.frame, kf.value, 'linear'));

    const effect: EffectInstance = {
      id: 'test',
      effectKey: 'brightness',
      name: 'Test',
      category: 'color-correction',
      enabled: true,
      expanded: false,
      parameters: {
        amount: createAnimatableProperty('amount', 0, 'number', keyframes, true),
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
      category: 'color-correction',
      enabled: true,
      expanded: false,
      parameters: {
        brightness: createAnimatableProperty('brightness', values.param1, 'number', [], false),
        contrast: createAnimatableProperty('contrast', values.param2, 'number', [], false),
        saturation: createAnimatableProperty('saturation', values.param3, 'number', [], false),
      },
    };

    const evaluated = evaluateEffectParameters(effect, frame);

    // All parameters should be evaluated
    expect(evaluated.brightness).toBe(values.param1);
    expect(evaluated.contrast).toBe(values.param2);
    expect(evaluated.saturation).toBe(values.param3);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// BROWSER-ONLY TESTS: Effect Stack Processing
// ═══════════════════════════════════════════════════════════════════════════
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                 // strict // cache // tests
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
// STRICT hasEnabledEffects TESTS (pure function - no canvas needed)
// ═══════════════════════════════════════════════════════════════════════════

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
      { id: '1', effectKey: 'blur', name: 'Blur', category: 'blur-sharpen', enabled: false, expanded: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', category: 'stylize', enabled: false, expanded: false, parameters: {} },
      { id: '3', effectKey: 'noise', name: 'Noise', category: 'noise-grain', enabled: false, expanded: false, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(false);
  });

  it('returns true when single effect enabled', () => {
    const effects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', category: 'blur-sharpen', enabled: false, expanded: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', category: 'stylize', enabled: true, expanded: false, parameters: {} },
      { id: '3', effectKey: 'noise', name: 'Noise', category: 'noise-grain', enabled: false, expanded: false, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(true);
  });

  it('returns true when all effects enabled', () => {
    const effects: EffectInstance[] = [
      { id: '1', effectKey: 'blur', name: 'Blur', category: 'blur-sharpen', enabled: true, expanded: false, parameters: {} },
      { id: '2', effectKey: 'glow', name: 'Glow', category: 'stylize', enabled: true, expanded: false, parameters: {} },
    ];
    expect(hasEnabledEffects(effects)).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// STRICT getRegisteredEffects / registerEffectRenderer TESTS
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // stress // tests
// ═══════════════════════════════════════════════════════════════════════════
//
// The following browser-dependent stress tests are covered in E2E:
//
// Location: /ui/e2e/export/effect-processor.spec.ts
//
// Covered:
//                                     — Determinism at realistic canvas sizes
//   See "determinism - same input produces same output" test
// - Large effect stacks (covered by "process enabled effects" test)
//
// Run E2E tests with: bunx playwright test effect-processor.spec.ts
