/**
 * Layer Evaluation Cache Tests
 *
 * Tests version tracking, caching, and differential evaluation.
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  markLayerDirty,
  markAllLayersDirty,
  getLayerVersion,
  getGlobalVersion,
  getCachedEvaluation,
  setCachedEvaluation,
  clearLayerCache,
  clearEvaluationCache,
  getEvaluationCacheStats,
  evaluateLayerCached,
  evaluateLayersCached,
} from '@/services/layerEvaluationCache';
import type { Layer } from '@/types/project';
import { createDefaultTransform, createAnimatableProperty } from '@/types/project';

// ============================================================================
// TEST HELPERS
// ============================================================================

function createMockLayer(id: string, overrides: Partial<Layer> = {}): Layer {
  return {
    id,
    name: `Layer ${id}`,
    type: 'solid',
    visible: true,
    locked: false,
    isolate: false,
    startFrame: 0,
    endFrame: 80,
    inPoint: 0,
    outPoint: 80,
    transform: createDefaultTransform(),
    opacity: createAnimatableProperty('opacity', 100),
    blendMode: 'normal',
    parentId: null,
    threeD: false,
    motionBlur: false,
    effects: [],
    properties: [],
    data: null,
    ...overrides,
  };
}

// ============================================================================
// VERSION TRACKING
// ============================================================================

describe('Layer Version Tracking', () => {
  beforeEach(() => {
    markAllLayersDirty(); // Reset state
    clearEvaluationCache();
  });

  it('should start with version 0 for new layers', () => {
    expect(getLayerVersion('new-layer')).toBe(0);
  });

  it('should increment version on markLayerDirty', () => {
    expect(getLayerVersion('test-layer')).toBe(0);

    markLayerDirty('test-layer');
    expect(getLayerVersion('test-layer')).toBe(1);

    markLayerDirty('test-layer');
    expect(getLayerVersion('test-layer')).toBe(2);
  });

  it('should track versions independently per layer', () => {
    markLayerDirty('layer-a');
    markLayerDirty('layer-a');
    markLayerDirty('layer-b');

    expect(getLayerVersion('layer-a')).toBe(2);
    expect(getLayerVersion('layer-b')).toBe(1);
  });

  it('should increment global version on any layer change', () => {
    const initialGlobal = getGlobalVersion();

    markLayerDirty('layer-a');
    expect(getGlobalVersion()).toBe(initialGlobal + 1);

    markLayerDirty('layer-b');
    expect(getGlobalVersion()).toBe(initialGlobal + 2);
  });

  it('should reset versions on markAllLayersDirty', () => {
    markLayerDirty('layer-a');
    markLayerDirty('layer-b');

    expect(getLayerVersion('layer-a')).toBe(1);
    expect(getLayerVersion('layer-b')).toBe(1);

    markAllLayersDirty();

    // After reset, versions start fresh (0)
    expect(getLayerVersion('layer-a')).toBe(0);
    expect(getLayerVersion('layer-b')).toBe(0);
  });
});

// ============================================================================
// EVALUATION CACHE
// ============================================================================

describe('Evaluation Cache', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('should return null for uncached layers', () => {
    const cached = getCachedEvaluation('unknown-layer', 0);
    expect(cached).toBeNull();
  });

  it('should cache and retrieve evaluations', () => {
    const layer = createMockLayer('test-layer');
    const evaluated = evaluateLayerCached(layer, 10);

    // Should be cached now
    const cached = getCachedEvaluation('test-layer', 10);
    expect(cached).not.toBeNull();
    expect(cached?.id).toBe('test-layer');
    expect(cached).toBe(evaluated); // Same reference
  });

  it('should return different cached values for different frames', () => {
    const layer = createMockLayer('test-layer');

    evaluateLayerCached(layer, 0);
    evaluateLayerCached(layer, 10);
    evaluateLayerCached(layer, 20);

    expect(getCachedEvaluation('test-layer', 0)).not.toBeNull();
    expect(getCachedEvaluation('test-layer', 10)).not.toBeNull();
    expect(getCachedEvaluation('test-layer', 20)).not.toBeNull();
    expect(getCachedEvaluation('test-layer', 30)).toBeNull();
  });

  it('should invalidate cache on version change', () => {
    const layer = createMockLayer('test-layer');

    // Cache at frame 10
    evaluateLayerCached(layer, 10);
    expect(getCachedEvaluation('test-layer', 10)).not.toBeNull();

    // Mark dirty - should invalidate
    markLayerDirty('test-layer');
    expect(getCachedEvaluation('test-layer', 10)).toBeNull();
  });

  it('should clear cache for specific layer', () => {
    const layerA = createMockLayer('layer-a');
    const layerB = createMockLayer('layer-b');

    evaluateLayerCached(layerA, 0);
    evaluateLayerCached(layerA, 10);
    evaluateLayerCached(layerB, 0);

    clearLayerCache('layer-a');

    expect(getCachedEvaluation('layer-a', 0)).toBeNull();
    expect(getCachedEvaluation('layer-a', 10)).toBeNull();
    expect(getCachedEvaluation('layer-b', 0)).not.toBeNull();
  });

  it('should clear entire cache', () => {
    const layerA = createMockLayer('layer-a');
    const layerB = createMockLayer('layer-b');

    evaluateLayerCached(layerA, 0);
    evaluateLayerCached(layerB, 0);

    clearEvaluationCache();

    expect(getCachedEvaluation('layer-a', 0)).toBeNull();
    expect(getCachedEvaluation('layer-b', 0)).toBeNull();
  });

  it('should report accurate cache stats', () => {
    const layer = createMockLayer('test-layer');

    const statsBefore = getEvaluationCacheStats();
    expect(statsBefore.size).toBe(0);

    evaluateLayerCached(layer, 0);
    evaluateLayerCached(layer, 10);

    const statsAfter = getEvaluationCacheStats();
    expect(statsAfter.size).toBe(2);
    expect(statsAfter.maxSize).toBeGreaterThan(0);
  });
});

// ============================================================================
// LAYER EVALUATION
// ============================================================================

describe('Layer Evaluation', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('should evaluate transform properties', () => {
    const layer = createMockLayer('test-layer', {
      transform: {
        ...createDefaultTransform(),
        position: {
          id: 'pos',
          name: 'Position',
          type: 'position',
          value: { x: 100, y: 200 },
          keyframes: [],
          animated: false,
        },
      },
    });

    const evaluated = evaluateLayerCached(layer, 0);

    expect(evaluated.transform.position.x).toBe(100);
    expect(evaluated.transform.position.y).toBe(200);
  });

  it('should evaluate opacity', () => {
    const layer = createMockLayer('test-layer', {
      opacity: {
        id: 'opacity',
        name: 'Opacity',
        type: 'number',
        value: 75,
        keyframes: [],
        animated: false,
      },
    });

    const evaluated = evaluateLayerCached(layer, 0);
    expect(evaluated.opacity).toBe(75);
  });

  it('should evaluate visibility based on in/out points', () => {
    const layer = createMockLayer('test-layer', {
      visible: true,
      startFrame: 10,
      endFrame: 50,
      inPoint: 10,
      outPoint: 50,
    });

    const beforeIn = evaluateLayerCached(layer, 5);
    expect(beforeIn.visible).toBe(false);
    expect(beforeIn.inRange).toBe(false);

    clearEvaluationCache();
    const atIn = evaluateLayerCached(layer, 10);
    expect(atIn.visible).toBe(true);
    expect(atIn.inRange).toBe(true);

    clearEvaluationCache();
    const afterOut = evaluateLayerCached(layer, 55);
    expect(afterOut.visible).toBe(false);
    expect(afterOut.inRange).toBe(false);
  });

  it('should evaluate animated properties', () => {
    const layer = createMockLayer('test-layer', {
      opacity: {
        id: 'opacity',
        name: 'Opacity',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          {
            id: 'kf1',
            frame: 0,
            value: 0,
            interpolation: 'linear',
            inHandle: { frame: 0, value: 0, enabled: false },
            outHandle: { frame: 0, value: 0, enabled: false },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 10,
            value: 100,
            interpolation: 'linear',
            inHandle: { frame: 0, value: 0, enabled: false },
            outHandle: { frame: 0, value: 0, enabled: false },
            controlMode: 'smooth',
          },
        ],
      },
    });

    const at0 = evaluateLayerCached(layer, 0);
    expect(at0.opacity).toBe(0);

    clearEvaluationCache();
    const at5 = evaluateLayerCached(layer, 5);
    expect(at5.opacity).toBeCloseTo(50, 1);

    clearEvaluationCache();
    const at10 = evaluateLayerCached(layer, 10);
    expect(at10.opacity).toBe(100);
  });

  it('should evaluate 3D transforms', () => {
    const layer = createMockLayer('test-layer', {
      threeD: true,
      transform: {
        ...createDefaultTransform(),
        rotationX: createAnimatableProperty('rotationX', 45, 'number'),
        rotationY: createAnimatableProperty('rotationY', 90, 'number'),
        rotationZ: createAnimatableProperty('rotationZ', 180, 'number'),
      },
    });

    const evaluated = evaluateLayerCached(layer, 0);

    expect(evaluated.threeD).toBe(true);
    expect(evaluated.transform.rotationX).toBe(45);
    expect(evaluated.transform.rotationY).toBe(90);
    expect(evaluated.transform.rotationZ).toBe(180);
  });

  it('should freeze evaluated objects', () => {
    const layer = createMockLayer('test-layer');
    const evaluated = evaluateLayerCached(layer, 0);

    expect(Object.isFrozen(evaluated)).toBe(true);
    expect(Object.isFrozen(evaluated.transform)).toBe(true);
    expect(Object.isFrozen(evaluated.effects)).toBe(true);
    expect(Object.isFrozen(evaluated.properties)).toBe(true);
  });
});

// ============================================================================
// BATCH EVALUATION
// ============================================================================

describe('Batch Layer Evaluation', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('should evaluate multiple layers', () => {
    const layers = [
      createMockLayer('layer-1'),
      createMockLayer('layer-2'),
      createMockLayer('layer-3'),
    ];

    const evaluated = evaluateLayersCached(layers, 10);

    expect(evaluated).toHaveLength(3);
    expect(evaluated[0].id).toBe('layer-1');
    expect(evaluated[1].id).toBe('layer-2');
    expect(evaluated[2].id).toBe('layer-3');
  });

  it('should cache all evaluated layers', () => {
    const layers = [
      createMockLayer('layer-1'),
      createMockLayer('layer-2'),
    ];

    evaluateLayersCached(layers, 10);

    expect(getCachedEvaluation('layer-1', 10)).not.toBeNull();
    expect(getCachedEvaluation('layer-2', 10)).not.toBeNull();
  });

  it('should reuse cached evaluations in batch', () => {
    const layer = createMockLayer('layer-1');

    // Pre-cache one layer
    const preCached = evaluateLayerCached(layer, 10);

    // Batch evaluate - should reuse cached
    const layers = [layer, createMockLayer('layer-2')];
    const evaluated = evaluateLayersCached(layers, 10);

    expect(evaluated[0]).toBe(preCached); // Same reference
  });

  it('should handle empty layer array', () => {
    const evaluated = evaluateLayersCached([], 10);
    expect(evaluated).toHaveLength(0);
  });
});

// ============================================================================
// CACHE PERFORMANCE
// ============================================================================

describe('Cache Performance', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('should benefit from cache hits', () => {
    const layer = createMockLayer('test-layer');

    // First evaluation (cache miss)
    const start1 = performance.now();
    for (let i = 0; i < 100; i++) {
      clearEvaluationCache();
      evaluateLayerCached(layer, 0);
    }
    const timeWithoutCache = performance.now() - start1;

    // Second evaluation (cache hits)
    evaluateLayerCached(layer, 0);
    const start2 = performance.now();
    for (let i = 0; i < 100; i++) {
      getCachedEvaluation('test-layer', 0);
    }
    const timeWithCache = performance.now() - start2;

    // Cache hits should be faster (or at least not slower)
    // This test is mainly to verify the pattern works
    expect(timeWithCache).toBeLessThanOrEqual(timeWithoutCache + 10);
  });

  it('should handle many cached entries', () => {
    const layers = Array.from({ length: 100 }, (_, i) =>
      createMockLayer(`layer-${i}`)
    );

    // Cache 100 layers × 50 frames = 5000 entries
    for (const layer of layers) {
      for (let frame = 0; frame < 50; frame++) {
        evaluateLayerCached(layer, frame);
      }
    }

    const stats = getEvaluationCacheStats();
    expect(stats.size).toBeLessThanOrEqual(stats.maxSize);

    // Should still be able to retrieve recent entries
    expect(getCachedEvaluation('layer-99', 49)).not.toBeNull();
  });
});
