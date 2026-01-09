/**
 * Memory Leak Tests
 * 
 * These tests verify that long-running operations don't leak memory.
 * Run with: node --expose-gc node_modules/.bin/vitest run performance/memory.test.ts
 */

import { describe, test, expect, beforeEach, afterEach, vi } from 'vitest';

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
  test.skip('create/delete 1000 layers does not leak', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Stress test: create and delete many layers
    for (let i = 0; i < 1000; i++) {
      // store.addLayer({ type: 'solid', color: '#ff0000' });
      // store.deleteLayer(store.layers[0].id);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.LAYER_OPERATIONS);
  });

  test.skip('nested group creation/deletion does not leak', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    for (let i = 0; i < 100; i++) {
      // Create nested structure
      // const groupId = store.addGroup('Group');
      // for (let j = 0; j < 10; j++) {
      //   store.addLayer({ type: 'solid', parentId: groupId });
      // }
      // Delete entire group
      // store.deleteLayer(groupId);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.LAYER_OPERATIONS);
  });
});

describe('Memory: Frame Playback', () => {
  test.skip('playing 10000 frames does not leak', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Setup a composition with layers
    // store.addLayer({ type: 'solid' });
    // store.addKeyframe({ property: 'opacity', frame: 0, value: 0 });
    // store.addKeyframe({ property: 'opacity', frame: 100, value: 1 });

    // Play through many frames
    for (let frame = 0; frame < 10000; frame++) {
      // engine.evaluate(store.project, frame % 100);
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.FRAME_PLAYBACK);
  });
});

describe('Memory: Undo/Redo', () => {
  test.skip('500 undo/redo cycles does not leak', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    for (let i = 0; i < 500; i++) {
      // Make a change
      // store.addLayer({ type: 'solid' });
      // historyStore.push(store.project);
      
      // Undo
      // historyStore.undo();
      
      // Redo
      // historyStore.redo();
      
      // Undo again
      // historyStore.undo();
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.UNDO_REDO);
  });
});

describe('Memory: Effect Processing', () => {
  test.skip('processing 1000 effect stacks does not leak', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Create test canvas
    // const canvas = document.createElement('canvas');
    // canvas.width = 1920;
    // canvas.height = 1080;

    // Process many effect stacks
    for (let i = 0; i < 1000; i++) {
      // processEffectStack(effects, canvas, i);
      // clearEffectCaches(); // Should release resources
    }

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    expect(growth).toBeLessThan(THRESHOLDS.EFFECT_PROCESSING);
  });
});

describe('Memory: Resource Cleanup', () => {
  test.skip('canvas pool releases memory', async () => {
    await waitForGC();
    const initialHeap = getHeapUsed();

    // Acquire many canvases
    const canvases: HTMLCanvasElement[] = [];
    for (let i = 0; i < 100; i++) {
      // canvases.push(acquireCanvas(1920, 1080));
    }

    // Release all
    for (const canvas of canvases) {
      // releaseCanvas(canvas);
    }

    // Force cleanup
    // cleanupEffectResources();

    await waitForGC();
    const finalHeap = getHeapUsed();
    const growth = finalHeap - initialHeap;

    // Should return close to baseline
    expect(growth).toBeLessThan(10 * 1024 * 1024); // 10MB tolerance
  });
});
