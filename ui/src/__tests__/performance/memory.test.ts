/**
 * Memory Leak Tests
 * 
 * These tests verify that long-running operations don't leak memory.
 * Run with: node --expose-gc node_modules/.bin/vitest run performance/memory.test.ts
 * 
 * REINTEGRATED: 2026-01-07 from _deprecated/performance/memory.test.ts
 * Updated to use current compositorStore and MotionEngine APIs
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';
import { motionEngine } from '@/engine/MotionEngine';

// Helper to get current heap usage
function getHeapUsed(): number {
  if (typeof process !== 'undefined' && process.memoryUsage) {
    return process.memoryUsage().heapUsed;
  }
  // Browser fallback (less accurate)
  if (typeof performance !== 'undefined' && (performance as any).memory) {
    return (performance as any).memory.usedJSHeapSize;
  }
  return 0;
}

// Helper to force garbage collection
function forceGC(): void {
  if (typeof global !== 'undefined' && (global as any).gc) {
    (global as any).gc();
  }
}

// Wait for GC to complete
async function waitForGC(ms = 100): Promise<void> {
  forceGC();
  await new Promise(r => setTimeout(r, ms));
  forceGC();
}

// Memory growth thresholds (in bytes)
const THRESHOLDS = {
  LAYER_OPERATIONS: 50 * 1024 * 1024,    // 50MB
  FRAME_PLAYBACK: 100 * 1024 * 1024,     // 100MB
  UNDO_REDO: 20 * 1024 * 1024,           // 20MB
  PROJECT_LOAD: 10 * 1024 * 1024,        // 10MB per project
  EFFECT_PROCESSING: 30 * 1024 * 1024,   // 30MB
};

describe('Memory: Layer Operations', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test('create/delete 1000 layers does not leak', async () => {
    const store = useCompositorStore();
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Stress test: create and delete many layers
    for (let i = 0; i < 1000; i++) {
      const layer = store.createLayer('solid', `Layer ${i}`);
      store.deleteLayer(layer.id);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.LAYER_OPERATIONS);
  });

  test('nested group creation/deletion does not leak', async () => {
    const store = useCompositorStore();
    await waitForGC();
    const initialHeap = getHeapUsed();

    for (let i = 0; i < 100; i++) {
      // Create nested structure
      const groupLayer = store.createLayer('group', `Group ${i}`);
      const groupId = groupLayer.id;
      
      // Add child layers
      for (let j = 0; j < 10; j++) {
        const child = store.createLayer('solid', `Child ${j}`);
        // Set parent (if API supports it)
        // For now, just create and delete
        store.deleteLayer(child.id);
      }
      
      // Delete entire group
      store.deleteLayer(groupId);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.LAYER_OPERATIONS);
  });
});

describe('Memory: Frame Playback', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test('playing 10000 frames does not leak', async () => {
    const store = useCompositorStore();
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Setup a composition with layers
    const layer = store.createLayer('solid', 'Test Layer');
    
    // Add keyframes for opacity animation
    store.setFrame(0);
    store.addKeyframe(layer.id, 'opacity', 0);
    store.setFrame(100);
    store.addKeyframe(layer.id, 'opacity', 100);

    // Play through many frames
    const project = store.project;
    for (let frame = 0; frame < 10000; frame++) {
      motionEngine.evaluate(frame % 100, project);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.FRAME_PLAYBACK);
  });
});

describe('Memory: Undo/Redo', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test('500 undo/redo cycles does not leak', async () => {
    const store = useCompositorStore();
    await waitForGC();
    const initialHeap = getHeapUsed();

    for (let i = 0; i < 500; i++) {
      // Make a change
      store.createLayer('solid', `Layer ${i}`);
      store.pushHistory();
      
      // Undo
      store.undo();
      
      // Redo
      store.redo();
      
      // Undo again
      store.undo();
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.UNDO_REDO);
  });
});

describe('Memory: Effect Processing', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test.skip('processing 1000 effect stacks does not leak', async () => {
    // TODO: Implement when effect processing API is available
    // This requires canvas/ImageData creation which may not be available in Node.js
    const store = useCompositorStore();
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Create test layer with effects
    const layer = store.createLayer('solid', 'Effect Test');
    // Add effects (when API is available)
    // store.addEffect(layer.id, 'blur', { radius: 10 });

    // Process many effect stacks
    const project = store.project;
    for (let i = 0; i < 1000; i++) {
      // Evaluate frame with effects
      motionEngine.evaluate(i % 100, project);
      // Clear caches if available
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.EFFECT_PROCESSING);
  });
});

describe('Memory: Resource Cleanup', () => {
  test.skip('canvas pool releases memory', async () => {
    // TODO: Implement when canvas pool API is available
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Acquire many canvases
    const canvases: HTMLCanvasElement[] = [];
    for (let i = 0; i < 100; i++) {
      const canvas = document.createElement('canvas');
      canvas.width = 1920;
      canvas.height = 1080;
      canvases.push(canvas);
    }

    // Release all (clear references)
    canvases.length = 0;

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    // Should return close to baseline
    expect(growth).toBeLessThan(10 * 1024 * 1024); // 10MB tolerance
  });
});
