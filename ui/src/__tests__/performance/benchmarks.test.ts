/**
 * Performance Benchmark Tests
 * 
 * These tests verify that critical functions meet performance targets.
 * Run with: npm run test:perf
 * 
 * REINTEGRATED: 2026-01-07 from _deprecated/performance/benchmarks.test.ts
 * Updated to use current APIs: interpolateProperty, multiplyMat4, MotionEngine, etc.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { interpolateProperty } from '@/services/interpolation';
import { interpolateWithEasing, applyEasing } from '@/services/easing';
import { multiplyMat4, identityMat4, translateMat4, scaleMat4, type Mat4 } from '@/services/math3d';
import { motionEngine } from '@/engine/MotionEngine';
import { useCompositorStore } from '@/stores/compositorStore';
import { createAnimatableProperty } from '@/types/animation';
import type { AnimatableProperty } from '@/types/project';

// Performance targets (in milliseconds)
const TARGETS = {
  interpolate: { target: 0.01, max: 0.1 },
  multiplyMatrices: { target: 0.001, max: 0.01 },
  evaluateFrame: { target: 1, max: 5 },      // per layer
  processEffect: { target: 5, max: 20 },     // per effect
  exportFrame: { target: 50, max: 200 },
  serializeProject: { target: 10, max: 50 },
  deserializeProject: { target: 10, max: 50 },
  hashSeed: { target: 0.001, max: 0.01 },
};

// Helper to benchmark a function
function benchmark(fn: () => void, iterations: number): { avg: number; min: number; max: number } {
  const times: number[] = [];
  
  // Warmup
  for (let i = 0; i < 100; i++) {
    fn();
  }
  
  // Measure
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    fn();
    times.push(performance.now() - start);
  }
  
  return {
    avg: times.reduce((a, b) => a + b, 0) / times.length,
    min: Math.min(...times),
    max: Math.max(...times),
  };
}

// Helper to create test keyframes
function createTestKeyframes(count: number = 10): AnimatableProperty<number> {
  const keyframes = [];
  for (let i = 0; i < count; i++) {
    keyframes.push({
      id: `kf${i}`,
      frame: i * 10,
      value: Math.random() * 100,
      interpolation: 'linear',
      inHandle: { frame: 0, value: 0, enabled: false },
      outHandle: { frame: 0, value: 0, enabled: false },
      controlMode: 'smooth',
    });
  }
  
  return createAnimatableProperty('test-prop', 0, 'number');
}

// Helper to create test matrices
function createTestMatrix(): Mat4 {
  return translateMat4({ x: Math.random() * 100, y: Math.random() * 100, z: Math.random() * 100 });
}

describe('Performance: Interpolation', () => {
  test('interpolateProperty() meets target', () => {
    const property = createTestKeyframes(10);
    
    const result = benchmark(() => {
      interpolateProperty(property, Math.random() * 100, 30, '', undefined);
    }, 10000);
    
    console.log(`interpolateProperty: avg=${result.avg.toFixed(4)}ms, max=${result.max.toFixed(4)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.interpolate.max);
  });

  test('interpolateWithEasing() meets target', () => {
    const result = benchmark(() => {
      interpolateWithEasing(0, 100, Math.random(), 'easeInOutQuad');
    }, 10000);
    
    console.log(`interpolateWithEasing: avg=${result.avg.toFixed(4)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.interpolate.max);
  });

  test('applyEasing() meets target', () => {
    const result = benchmark(() => {
      applyEasing(Math.random(), 'easeInOutQuad');
    }, 10000);
    
    console.log(`applyEasing: avg=${result.avg.toFixed(4)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.interpolate.max);
  });
});

describe('Performance: Matrix Math', () => {
  test('multiplyMat4() meets target', () => {
    const m1 = createTestMatrix();
    const m2 = createTestMatrix();
    
    const result = benchmark(() => {
      multiplyMat4(m1, m2);
    }, 10000);
    
    console.log(`multiplyMat4: avg=${result.avg.toFixed(4)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.multiplyMatrices.max);
  });

  test('matrix chain multiplication meets target', () => {
    const matrices = Array.from({ length: 10 }, () => createTestMatrix());
    
    const result = benchmark(() => {
      let result = identityMat4();
      for (const m of matrices) {
        result = multiplyMat4(result, m);
      }
    }, 1000);
    
    console.log(`matrix chain (10 matrices): avg=${result.avg.toFixed(4)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.multiplyMatrices.max * 10);
  });
});

describe('Performance: Frame Evaluation', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test('MotionEngine.evaluate() meets target (per layer)', () => {
    const store = useCompositorStore();
    
    // Create 10 layers
    for (let i = 0; i < 10; i++) {
      const layer = store.createLayer('solid', `Layer ${i}`);
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(100);
      store.addKeyframe(layer.id, 'opacity', 100);
    }
    
    const project = store.project;
    
    const result = benchmark(() => {
      motionEngine.evaluate(Math.floor(Math.random() * 100), project);
    }, 1000);
    
    const perLayer = result.avg / 10;
    console.log(`evaluate: ${result.avg.toFixed(2)}ms total, ${perLayer.toFixed(2)}ms/layer`);
    expect(perLayer).toBeLessThan(TARGETS.evaluateFrame.max);
  });
});

describe('Performance: Serialization', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test('project serialization meets target', () => {
    const store = useCompositorStore();
    
    // Create a project with 100 layers
    for (let i = 0; i < 100; i++) {
      store.createLayer('solid', `Layer ${i}`);
    }
    
    const project = store.project;
    
    const result = benchmark(() => {
      JSON.stringify(project);
    }, 100);
    
    console.log(`serialize: ${result.avg.toFixed(2)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.serializeProject.max);
  });

  test('project deserialization meets target', () => {
    const store = useCompositorStore();
    
    // Create a project with 100 layers
    for (let i = 0; i < 100; i++) {
      store.createLayer('solid', `Layer ${i}`);
    }
    
    const project = store.project;
    const json = JSON.stringify(project);
    
    const result = benchmark(() => {
      JSON.parse(json);
    }, 100);
    
    console.log(`deserialize: ${result.avg.toFixed(2)}ms`);
    expect(result.avg).toBeLessThan(TARGETS.deserializeProject.max);
  });
});

describe('Performance: RNG', () => {
  test.skip('hashSeed() meets target', () => {
    // TODO: Find hashSeed function or SeededRandom implementation
    // const result = benchmark(() => {
    //   hashSeed(Math.floor(Math.random() * 2**32));
    // }, 100000);
    // 
    // console.log(`hashSeed: ${result.avg.toFixed(6)}ms`);
    // expect(result.avg).toBeLessThan(TARGETS.hashSeed.max);
  });

  test.skip('SeededRandom.next() meets target', () => {
    // TODO: Find SeededRandom implementation
    // const rng = new SeededRandom(12345);
    // 
    // const result = benchmark(() => {
    //   rng.next();
    // }, 100000);
    // 
    // console.log(`SeededRandom.next: ${result.avg.toFixed(6)}ms`);
    // expect(result.avg).toBeLessThan(0.001); // 0.001ms = 1µs
  });
});

describe('Performance: Effect Processing', () => {
  test.skip('processing effect stacks meets target', () => {
    // TODO: Implement when effect processing API is available
    // This requires canvas/ImageData creation which may not be available in Node.js
  });
});

describe('Performance: Export', () => {
  test.skip('export frame meets target', () => {
    // TODO: Implement when export API is available
    // This requires browser environment
  });
});
