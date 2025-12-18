/**
 * Effect Processor Tests
 *
 * Tests effect parameter evaluation, canvas pooling,
 * and effect result caching.
 *
 * Note: Canvas-related tests are skipped in JSDOM since it doesn't
 * support canvas 2D context. These tests should pass in a browser environment.
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  evaluateEffectParameters,
  hasEnabledEffects,
  getRegisteredEffects,
  clearEffectCaches,
  getEffectProcessorStats,
  cleanupEffectResources,
  createMatchingCanvas,
  releaseCanvas,
  processEffectStack,
  registerEffectRenderer,
  imageDataToCanvas,
  canvasToImageData,
  type EvaluatedEffectParams
} from '@/services/effectProcessor';
import type { EffectInstance } from '@/types/effects';
import type { AnimatableProperty } from '@/types/project';

// ============================================================================
// ENVIRONMENT CHECK
// ============================================================================

// Check if canvas 2D context is supported (not in JSDOM)
function isCanvasSupported(): boolean {
  try {
    const canvas = document.createElement('canvas');
    return canvas.getContext('2d') !== null;
  } catch {
    return false;
  }
}

const CANVAS_SUPPORTED = isCanvasSupported();

// ============================================================================
// TEST HELPERS
// ============================================================================

function createMockCanvas(width = 100, height = 100): HTMLCanvasElement | null {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d');
  if (!ctx) return null;
  // Fill with a test pattern
  ctx.fillStyle = '#ff0000';
  ctx.fillRect(0, 0, width, height);
  return canvas;
}

function createAnimatableProperty<T>(value: T): AnimatableProperty<T> {
  return {
    id: `prop_${Math.random().toString(36).substr(2, 9)}`,
    name: 'Test Property',
    type: 'number',
    value,
    keyframes: [],
    animated: false
  };
}

function createMockEffect(
  id: string,
  effectKey: string,
  enabled = true,
  parameters: Record<string, AnimatableProperty<any>> = {}
): EffectInstance {
  return {
    id,
    effectKey,
    name: `Test ${effectKey}`,
    category: 'blur-sharpen',
    enabled,
    parameters,
    expanded: true
  };
}

// ============================================================================
// EFFECT PARAMETER EVALUATION
// ============================================================================

describe('Effect Parameter Evaluation', () => {
  it('should evaluate static parameters', () => {
    const effect = createMockEffect('effect1', 'test-effect', true, {
      intensity: createAnimatableProperty(0.5),
      radius: createAnimatableProperty(10)
    });

    const params = evaluateEffectParameters(effect, 0);

    expect(params.intensity).toBe(0.5);
    expect(params.radius).toBe(10);
  });

  it('should handle empty parameters', () => {
    const effect = createMockEffect('effect1', 'test-effect', true, {});
    const params = evaluateEffectParameters(effect, 0);

    expect(Object.keys(params)).toHaveLength(0);
  });

  it('should evaluate at different frames', () => {
    const effect = createMockEffect('effect1', 'test-effect', true, {
      value: {
        id: 'animated_prop',
        name: 'Animated',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
          { id: 'kf2', frame: 10, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' }
        ]
      }
    });

    const params0 = evaluateEffectParameters(effect, 0);
    const params5 = evaluateEffectParameters(effect, 5);
    const params10 = evaluateEffectParameters(effect, 10);

    expect(params0.value).toBe(0);
    expect(params5.value).toBeCloseTo(50, 1);
    expect(params10.value).toBe(100);
  });
});

// ============================================================================
// CANVAS POOL
// ============================================================================

describe('Canvas Pool', () => {
  beforeEach(() => {
    clearEffectCaches();
  });

  afterEach(() => {
    clearEffectCaches();
  });

  it.skipIf(!CANVAS_SUPPORTED)('should acquire canvas with correct dimensions', () => {
    const source = createMockCanvas(200, 150)!;
    const result = createMatchingCanvas(source);

    expect(result.canvas.width).toBe(200);
    expect(result.canvas.height).toBe(150);
    expect(result.ctx).toBeDefined();
  });

  it.skipIf(!CANVAS_SUPPORTED)('should reuse released canvas of same size', () => {
    const source = createMockCanvas(100, 100)!;

    // Acquire and release
    const first = createMatchingCanvas(source);
    const firstCanvas = first.canvas;
    releaseCanvas(firstCanvas);

    // Acquire again - should get same canvas
    const second = createMatchingCanvas(source);

    // Pool reuse means same canvas instance
    expect(second.canvas).toBe(firstCanvas);
  });

  it.skipIf(!CANVAS_SUPPORTED)('should track pool statistics', () => {
    const source = createMockCanvas(100, 100)!;

    const stats1 = getEffectProcessorStats();
    expect(stats1.canvasPool.total).toBe(0);

    const acquired = createMatchingCanvas(source);
    const stats2 = getEffectProcessorStats();
    expect(stats2.canvasPool.total).toBe(1);
    expect(stats2.canvasPool.inUse).toBe(1);

    releaseCanvas(acquired.canvas);
    const stats3 = getEffectProcessorStats();
    expect(stats3.canvasPool.available).toBe(1);
  });

  it.skipIf(!CANVAS_SUPPORTED)('should clear pool on clearEffectCaches', () => {
    const source = createMockCanvas(100, 100)!;
    createMatchingCanvas(source);
    createMatchingCanvas(source);

    const statsBefore = getEffectProcessorStats();
    expect(statsBefore.canvasPool.total).toBeGreaterThan(0);

    clearEffectCaches();

    const statsAfter = getEffectProcessorStats();
    expect(statsAfter.canvasPool.total).toBe(0);
  });
});

// ============================================================================
// EFFECT STACK PROCESSING
// ============================================================================

describe('Effect Stack Processing', () => {
  beforeEach(() => {
    clearEffectCaches();
  });

  it.skipIf(!CANVAS_SUPPORTED)('should return input when no effects', () => {
    const input = createMockCanvas()!;

    const result = processEffectStack([], input, 0);

    expect(result.canvas.width).toBe(input.width);
    expect(result.canvas.height).toBe(input.height);
  });

  it.skipIf(!CANVAS_SUPPORTED)('should skip disabled effects', () => {
    const input = createMockCanvas()!;
    let rendererCalled = false;

    registerEffectRenderer('disabled-test', () => {
      rendererCalled = true;
      return createMatchingCanvas(input);
    });

    const effect = createMockEffect('e1', 'disabled-test', false);
    processEffectStack([effect], input, 0);

    expect(rendererCalled).toBe(false);
  });

  it.skipIf(!CANVAS_SUPPORTED)('should process enabled effects in order', () => {
    const input = createMockCanvas()!;
    const callOrder: string[] = [];

    registerEffectRenderer('effect-a', (inp) => {
      callOrder.push('a');
      return inp;
    });

    registerEffectRenderer('effect-b', (inp) => {
      callOrder.push('b');
      return inp;
    });

    const effects = [
      createMockEffect('e1', 'effect-a', true),
      createMockEffect('e2', 'effect-b', true)
    ];

    processEffectStack(effects, input, 0);

    expect(callOrder).toEqual(['a', 'b']);
  });

  it.skipIf(!CANVAS_SUPPORTED)('should pass evaluated parameters to renderer', () => {
    const input = createMockCanvas()!;
    let receivedParams: EvaluatedEffectParams | null = null;

    registerEffectRenderer('param-test', (inp, params) => {
      receivedParams = params;
      return inp;
    });

    const effect = createMockEffect('e1', 'param-test', true, {
      amount: createAnimatableProperty(42),
      name: createAnimatableProperty('test')
    });

    processEffectStack([effect], input, 0);

    expect(receivedParams).not.toBeNull();
    expect(receivedParams!.amount).toBe(42);
    expect(receivedParams!.name).toBe('test');
  });

  it.skipIf(!CANVAS_SUPPORTED)('should handle renderer errors gracefully', () => {
    const input = createMockCanvas()!;

    registerEffectRenderer('error-test', () => {
      throw new Error('Test error');
    });

    const effect = createMockEffect('e1', 'error-test', true);

    // Should not throw
    expect(() => processEffectStack([effect], input, 0)).not.toThrow();
  });
});

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

describe('Utility Functions', () => {
  it('hasEnabledEffects should detect enabled effects', () => {
    const effects = [
      createMockEffect('e1', 'test', false),
      createMockEffect('e2', 'test', true),
      createMockEffect('e3', 'test', false)
    ];

    expect(hasEnabledEffects(effects)).toBe(true);
  });

  it('hasEnabledEffects should return false when all disabled', () => {
    const effects = [
      createMockEffect('e1', 'test', false),
      createMockEffect('e2', 'test', false)
    ];

    expect(hasEnabledEffects(effects)).toBe(false);
  });

  it('hasEnabledEffects should return false for empty array', () => {
    expect(hasEnabledEffects([])).toBe(false);
  });

  it.skipIf(!CANVAS_SUPPORTED)('imageDataToCanvas should create canvas from ImageData', () => {
    const imageData = new ImageData(50, 50);
    // Fill with test data
    for (let i = 0; i < imageData.data.length; i += 4) {
      imageData.data[i] = 255;     // R
      imageData.data[i + 1] = 0;   // G
      imageData.data[i + 2] = 0;   // B
      imageData.data[i + 3] = 255; // A
    }

    const canvas = imageDataToCanvas(imageData);

    expect(canvas.width).toBe(50);
    expect(canvas.height).toBe(50);
  });

  it.skipIf(!CANVAS_SUPPORTED)('canvasToImageData should extract ImageData', () => {
    const canvas = createMockCanvas(30, 30)!;
    const imageData = canvasToImageData(canvas);

    expect(imageData.width).toBe(30);
    expect(imageData.height).toBe(30);
    expect(imageData.data.length).toBe(30 * 30 * 4);
  });

  it.skipIf(!CANVAS_SUPPORTED)('getRegisteredEffects should return registered keys', () => {
    registerEffectRenderer('unique-effect-1', (inp) => inp);
    registerEffectRenderer('unique-effect-2', (inp) => inp);

    const effects = getRegisteredEffects();

    expect(effects).toContain('unique-effect-1');
    expect(effects).toContain('unique-effect-2');
  });
});

// ============================================================================
// EFFECT CACHE
// ============================================================================

describe('Effect Cache', () => {
  beforeEach(() => {
    clearEffectCaches();
  });

  it('should track cache statistics', () => {
    const stats = getEffectProcessorStats();

    expect(stats.effectCache).toBeDefined();
    expect(stats.effectCache.size).toBe(0);
    expect(stats.effectCache.maxSize).toBeGreaterThan(0);
  });

  it('should clear cache on clearEffectCaches', () => {
    // The cache is internal, but we can verify it clears via stats
    clearEffectCaches();
    const stats = getEffectProcessorStats();

    expect(stats.effectCache.size).toBe(0);
    expect(stats.canvasPool.total).toBe(0);
  });
});

// ============================================================================
// CLEANUP
// ============================================================================

describe('Resource Cleanup', () => {
  it('cleanupEffectResources should not throw', () => {
    expect(() => cleanupEffectResources()).not.toThrow();
  });

  it.skipIf(!CANVAS_SUPPORTED)('clearEffectCaches should reset all caches', () => {
    // Create some resources
    const source = createMockCanvas()!;
    createMatchingCanvas(source);
    createMatchingCanvas(source);

    // Clear
    clearEffectCaches();

    const stats = getEffectProcessorStats();
    expect(stats.canvasPool.total).toBe(0);
    expect(stats.effectCache.size).toBe(0);
  });
});
