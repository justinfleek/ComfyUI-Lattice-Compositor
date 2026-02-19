/**
 * STRICT Property Tests for LayerEvaluationCache
 * 
 * Direct tests for the cache API functions.
 * Integration with MotionEngine is tested in strict-layerevaluation.property.test.ts
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
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
import type { EvaluatedLayer } from '@/engine/MotionEngine';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                  // helpers
// ═══════════════════════════════════════════════════════════════════════════

function createMinimalLayer(id: string): Layer {
  const origin = {
    id: 'origin',
    name: 'origin',
    type: 'vector3' as const,
    value: { x: 0, y: 0, z: 0 },
    animated: false,
    keyframes: [],
  };
  return {
    id,
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    locked: false,
    isolate: false,
    motionBlur: false,
    blendMode: 'normal',
    threeD: false,
    parentId: null,
    opacity: {
      id: 'opacity',
      name: 'opacity',
      type: 'number',
      value: 100,
      animated: false,
      keyframes: []
    },
    transform: {
      position: {
        id: 'position',
        name: 'position',
        type: 'vector3',
        value: { x: 0, y: 0, z: 0 },
        animated: false,
        keyframes: []
      },
      scale: {
        id: 'scale',
        name: 'scale',
        type: 'vector3',
        value: { x: 100, y: 100, z: 100 },
        animated: false,
        keyframes: []
      },
      rotation: {
        id: 'rotation',
        name: 'rotation',
        type: 'number',
        value: 0,
        animated: false,
        keyframes: []
      },
      origin,
      anchorPoint: origin,
    },
    effects: [],
    properties: [],
    masks: [],
    startFrame: 0,
    endFrame: 100,
    data: { color: '#000000', width: 100, height: 100 },
  } as Layer;
}

function createMockEvaluatedLayer(id: string): EvaluatedLayer {
  return Object.freeze({
    id,
    type: 'solid',
    name: 'Test Layer',
    visible: true,
    inRange: true,
    opacity: 100,
    transform: Object.freeze({
      position: { x: 0, y: 0, z: 0 },
      origin: { x: 0, y: 0, z: 0 },
      anchorPoint: { x: 0, y: 0, z: 0 },
      scale: { x: 100, y: 100, z: 100 },
      rotation: 0,
    }),
    effects: Object.freeze([]),
    properties: Object.freeze({}),
    parentId: null,
    blendMode: 'normal',
    threeD: false,
    layerRef: createMinimalLayer(id),
    frame: 0,
    audioModifiers: {},
  }) as EvaluatedLayer;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                             // version // tracking // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Version Tracking', () => {
  beforeEach(() => {
    markAllLayersDirty(); // Reset state
    clearEvaluationCache();
  });

  test.prop([
    fc.uuid()
  ])('getLayerVersion returns 0 for unknown layers', (layerId) => {
    markAllLayersDirty(); // Clear versions
    const version = getLayerVersion(layerId);
    expect(version).toBe(0);
  });

  test.prop([
    fc.uuid(),
    fc.integer({ min: 1, max: 100 })
  ])('markLayerDirty increments version', (layerId, times) => {
    markAllLayersDirty();
    const initialVersion = getLayerVersion(layerId);
    
    for (let i = 0; i < times; i++) {
      markLayerDirty(layerId);
    }
    
    const finalVersion = getLayerVersion(layerId);
    expect(finalVersion).toBe(initialVersion + times);
  });

  it('markLayerDirty increments global version', () => {
    markAllLayersDirty();
    const initialGlobal = getGlobalVersion();
    
    markLayerDirty('layer-1');
    markLayerDirty('layer-2');
    
    const finalGlobal = getGlobalVersion();
    expect(finalGlobal).toBe(initialGlobal + 2);
  });

  it('markAllLayersDirty resets layer versions', () => {
    markLayerDirty('layer-a');
    markLayerDirty('layer-b');
    
    markAllLayersDirty();
    
    expect(getLayerVersion('layer-a')).toBe(0);
    expect(getLayerVersion('layer-b')).toBe(0);
  });

  it('markAllLayersDirty increments global version', () => {
    const before = getGlobalVersion();
    markAllLayersDirty();
    const after = getGlobalVersion();
    expect(after).toBe(before + 1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // cache // api // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Cache API', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('getCachedEvaluation returns null for uncached entries', () => {
    const result = getCachedEvaluation('nonexistent', 0);
    expect(result).toBeNull();
  });

  it('setCachedEvaluation + getCachedEvaluation roundtrip', () => {
    const layerId = 'test-layer';
    const frame = 42;
    const evaluated = createMockEvaluatedLayer(layerId);
    
    setCachedEvaluation(layerId, frame, evaluated);
    const cached = getCachedEvaluation(layerId, frame);
    
    expect(cached).not.toBeNull();
    expect(cached?.id).toBe(layerId);
    expect(cached?.opacity).toBe(100);
  });

  it('cache invalidation on markLayerDirty', () => {
    const layerId = 'test-layer';
    const evaluated = createMockEvaluatedLayer(layerId);
    
    setCachedEvaluation(layerId, 0, evaluated);
    expect(getCachedEvaluation(layerId, 0)).not.toBeNull();
    
    markLayerDirty(layerId);
    expect(getCachedEvaluation(layerId, 0)).toBeNull();
  });

  it('clearLayerCache removes only that layer', () => {
    const evaluated1 = createMockEvaluatedLayer('layer-1');
    const evaluated2 = createMockEvaluatedLayer('layer-2');
    
    setCachedEvaluation('layer-1', 0, evaluated1);
    setCachedEvaluation('layer-2', 0, evaluated2);
    
    clearLayerCache('layer-1');
    
    expect(getCachedEvaluation('layer-1', 0)).toBeNull();
    expect(getCachedEvaluation('layer-2', 0)).not.toBeNull();
  });

  it('clearEvaluationCache removes all entries', () => {
    const evaluated1 = createMockEvaluatedLayer('layer-1');
    const evaluated2 = createMockEvaluatedLayer('layer-2');
    
    setCachedEvaluation('layer-1', 0, evaluated1);
    setCachedEvaluation('layer-2', 0, evaluated2);
    
    clearEvaluationCache();
    
    const stats = getEvaluationCacheStats();
    expect(stats.size).toBe(0);
  });

  test.prop([
    fc.array(fc.tuple(fc.uuid(), fc.integer({ min: 0, max: 100 })), { minLength: 1, maxLength: 20 })
  ])('cache stats track size correctly', (entries) => {
    clearEvaluationCache();
    
    for (const [layerId, frame] of entries) {
      const evaluated = createMockEvaluatedLayer(layerId);
      setCachedEvaluation(layerId, frame, evaluated);
    }
    
    const stats = getEvaluationCacheStats();
    // Unique entries (same layer+frame gets overwritten)
    const uniqueKeys = new Set(entries.map(([id, f]) => `${id}:${f}`));
    expect(stats.size).toBe(uniqueKeys.size);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                             // layer // evaluation // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: evaluateLayerCached', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('evaluates layer at frame 0', () => {
    const layer = createMinimalLayer('test-layer');
    const result = evaluateLayerCached(layer, 0, 30);
    
    expect(result.id).toBe('test-layer');
    expect(result.opacity).toBe(100);
    expect(result.visible).toBe(true);
  });

  test.prop([
    fc.integer({ min: 0, max: 100 })
  ])('evaluates layer and caches result', (frame) => {
    const layer = createMinimalLayer('cache-test');
    
    // First evaluation
    const result1 = evaluateLayerCached(layer, frame, 30);
    
    // Should be cached
    const cached = getCachedEvaluation('cache-test', frame);
    expect(cached).not.toBeNull();
    expect(cached?.id).toBe(result1.id);
  });

  it('respects layer visibility', () => {
    const layer = createMinimalLayer('hidden-layer');
    layer.visible = false;
    
    const result = evaluateLayerCached(layer, 50, 30);
    
    expect(result.visible).toBe(false);
  });

  it('respects layer in/out points', () => {
    const layer = createMinimalLayer('range-layer');
    layer.startFrame = 10;
    layer.endFrame = 50;
    
    const beforeRange = evaluateLayerCached(layer, 5, 30);
    expect(beforeRange.inRange).toBe(false);
    
    const inRange = evaluateLayerCached(layer, 30, 30);
    expect(inRange.inRange).toBe(true);
    
    const afterRange = evaluateLayerCached(layer, 60, 30);
    expect(afterRange.inRange).toBe(false);
  });

  test.prop([
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 1, max: 60 })
  ])('DETERMINISM: same inputs = same output', (frame, fps) => {
    const layer = createMinimalLayer('determinism-test');
    
    clearEvaluationCache();
    const result1 = evaluateLayerCached(layer, frame, fps);
    
    clearEvaluationCache();
    const result2 = evaluateLayerCached(layer, frame, fps);
    
    expect(result1.id).toBe(result2.id);
    expect(result1.opacity).toBe(result2.opacity);
    expect(result1.transform.position.x).toBe(result2.transform.position.x);
    expect(result1.transform.position.y).toBe(result2.transform.position.y);
    expect(result1.transform.scale.x).toBe(result2.transform.scale.x);
    expect(result1.transform.rotation).toBe(result2.transform.rotation);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                             // batch // evaluation // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: evaluateLayersCached', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('evaluates multiple layers', () => {
    const layers = [
      createMinimalLayer('layer-1'),
      createMinimalLayer('layer-2'),
      createMinimalLayer('layer-3'),
    ];
    
    const results = evaluateLayersCached(layers, 0, 30);
    
    expect(results.length).toBe(3);
    expect(results[0].id).toBe('layer-1');
    expect(results[1].id).toBe('layer-2');
    expect(results[2].id).toBe('layer-3');
  });

  it('returns empty array for empty input', () => {
    const results = evaluateLayersCached([], 0, 30);
    expect(results).toEqual([]);
  });

  test.prop([
    fc.integer({ min: 1, max: 10 }),
    fc.integer({ min: 0, max: 100 })
  ])('maintains layer order', (count, frame) => {
    const layers = Array.from({ length: count }, (_, i) => 
      createMinimalLayer(`layer-${i}`)
    );
    
    const results = evaluateLayersCached(layers, frame, 30);
    
    for (let i = 0; i < count; i++) {
      expect(results[i].id).toBe(`layer-${i}`);
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                  // cache // stats // tests
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Cache Statistics', () => {
  beforeEach(() => {
    markAllLayersDirty();
    clearEvaluationCache();
  });

  it('getEvaluationCacheStats returns valid structure', () => {
    const stats = getEvaluationCacheStats();
    
    expect(typeof stats.size).toBe('number');
    expect(typeof stats.maxSize).toBe('number');
    expect(typeof stats.layerVersions).toBe('number');
    expect(typeof stats.globalVersion).toBe('number');
    expect(stats.maxSize).toBeGreaterThan(0);
  });

  it('stats.size starts at 0', () => {
    clearEvaluationCache();
    const stats = getEvaluationCacheStats();
    expect(stats.size).toBe(0);
  });

  it('stats.layerVersions tracks marked layers', () => {
    markAllLayersDirty();
    expect(getEvaluationCacheStats().layerVersions).toBe(0);
    
    markLayerDirty('layer-1');
    expect(getEvaluationCacheStats().layerVersions).toBe(1);
    
    markLayerDirty('layer-2');
    expect(getEvaluationCacheStats().layerVersions).toBe(2);
    
    // Same layer doesn't add to count
    markLayerDirty('layer-1');
    expect(getEvaluationCacheStats().layerVersions).toBe(2);
  });
});
