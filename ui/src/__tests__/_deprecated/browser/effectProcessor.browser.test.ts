/**
 * STRICT EffectProcessor Browser Tests
 * 
 * These tests run in REAL Chromium browser with full Canvas/WebGL support.
 * Run with: npm run test:browser
 * 
 * Tests ALL effectProcessor functionality including:
 * - Canvas pool allocation/release
 * - Effect cache hit/miss
 * - processEffectStack with real canvas
 * - GPU acceleration detection
 * - ImageData transformations
 */

import { describe, expect, test, beforeEach, afterEach } from 'vitest';
import { 
  processEffectStack,
  registerEffectRenderer,
  clearEffectCaches,
  getEffectProcessorStats,
  cleanupEffectResources,
  imageDataToCanvas,
  canvasToImageData,
  createMatchingCanvas,
  releaseCanvas,
  isGPUEffectProcessingAvailable,
  getGPUEffectCapabilities,
  type EffectStackResult,
  type EvaluatedEffectParams,
} from '@/services/effectProcessor';
import type { EffectInstance } from '@/types/effects';

// ============================================================================
// HELPERS
// ============================================================================

function createTestCanvas(width: number, height: number, fillColor: string = '#ff0000'): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;
  ctx.fillStyle = fillColor;
  ctx.fillRect(0, 0, width, height);
  return canvas;
}

function createMockEffect(
  effectKey: string,
  params: Record<string, any>,
  enabled: boolean = true,
): EffectInstance {
  const parameters: Record<string, any> = {};
  for (const [key, value] of Object.entries(params)) {
    parameters[key] = {
      id: `param-${key}`,
      name: key,
      type: typeof value,
      value,
      animated: false,
      keyframes: [],
    };
  }
  
  return {
    id: `effect-${Math.random()}`,
    name: 'Test Effect',
    effectKey,
    enabled,
    category: 'utility',
    expanded: false,
    parameters,
  };
}

// Simple test effect that inverts colors
function invertEffect(input: EffectStackResult, _params: EvaluatedEffectParams): EffectStackResult {
  const { canvas, ctx } = input;
  const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
  
  for (let i = 0; i < imageData.data.length; i += 4) {
    imageData.data[i] = 255 - imageData.data[i];     // R
    imageData.data[i + 1] = 255 - imageData.data[i + 1]; // G
    imageData.data[i + 2] = 255 - imageData.data[i + 2]; // B
    // Alpha unchanged
  }
  
  ctx.putImageData(imageData, 0, 0);
  return input;
}

// Effect that multiplies brightness
function brightnessEffect(input: EffectStackResult, params: EvaluatedEffectParams): EffectStackResult {
  const { canvas, ctx } = input;
  const multiplier = params.intensity ?? 1;
  const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
  
  for (let i = 0; i < imageData.data.length; i += 4) {
    imageData.data[i] = Math.min(255, imageData.data[i] * multiplier);
    imageData.data[i + 1] = Math.min(255, imageData.data[i + 1] * multiplier);
    imageData.data[i + 2] = Math.min(255, imageData.data[i + 2] * multiplier);
  }
  
  ctx.putImageData(imageData, 0, 0);
  return input;
}

describe('STRICT: EffectProcessor Browser Tests', () => {
  
  beforeEach(() => {
    clearEffectCaches();
    // Register test effects
    registerEffectRenderer('test-invert', invertEffect);
    registerEffectRenderer('test-brightness', brightnessEffect);
  });

  afterEach(() => {
    clearEffectCaches();
    cleanupEffectResources();
  });

  // =========================================================================
  // CANVAS CREATION
  // =========================================================================

  describe('canvas creation', () => {
    
    test('createMatchingCanvas creates canvas with correct dimensions', () => {
      const source = createTestCanvas(800, 600);
      const result = createMatchingCanvas(source);
      
      expect(result.canvas.width).toBe(800);
      expect(result.canvas.height).toBe(600);
      expect(result.ctx).toBeDefined();
      
      releaseCanvas(result.canvas);
    });

    test('createMatchingCanvas creates usable context', () => {
      const source = createTestCanvas(100, 100);
      const result = createMatchingCanvas(source);
      
      // Should be able to draw
      result.ctx.fillStyle = '#00ff00';
      result.ctx.fillRect(0, 0, 50, 50);
      
      const imageData = result.ctx.getImageData(25, 25, 1, 1);
      expect(imageData.data[1]).toBe(255); // Green channel
      
      releaseCanvas(result.canvas);
    });
  });

  // =========================================================================
  // IMAGE DATA CONVERSION
  // =========================================================================

  describe('ImageData conversion', () => {
    
    test('canvasToImageData extracts correct data', () => {
      const canvas = createTestCanvas(100, 100, '#ff0000');
      const imageData = canvasToImageData(canvas);
      
      expect(imageData.width).toBe(100);
      expect(imageData.height).toBe(100);
      expect(imageData.data[0]).toBe(255); // Red
      expect(imageData.data[1]).toBe(0);   // Green
      expect(imageData.data[2]).toBe(0);   // Blue
      expect(imageData.data[3]).toBe(255); // Alpha
    });

    test('imageDataToCanvas creates valid canvas', () => {
      const sourceCanvas = createTestCanvas(50, 50, '#0000ff');
      const imageData = canvasToImageData(sourceCanvas);
      const resultCanvas = imageDataToCanvas(imageData);
      
      expect(resultCanvas.width).toBe(50);
      expect(resultCanvas.height).toBe(50);
      
      const resultData = canvasToImageData(resultCanvas);
      expect(resultData.data[0]).toBe(0);   // Red
      expect(resultData.data[1]).toBe(0);   // Green
      expect(resultData.data[2]).toBe(255); // Blue
    });

    test('roundtrip: canvas → imageData → canvas preserves pixels', () => {
      const original = createTestCanvas(100, 100);
      const ctx = original.getContext('2d')!;
      
      // Draw a gradient
      for (let x = 0; x < 100; x++) {
        ctx.fillStyle = `rgb(${x * 2.55}, ${x * 2.55}, ${x * 2.55})`;
        ctx.fillRect(x, 0, 1, 100);
      }
      
      const imageData = canvasToImageData(original);
      const restored = imageDataToCanvas(imageData);
      const restoredData = canvasToImageData(restored);
      
      // Compare pixel by pixel
      for (let i = 0; i < imageData.data.length; i++) {
        expect(restoredData.data[i]).toBe(imageData.data[i]);
      }
    });
  });

  // =========================================================================
  // EFFECT PROCESSING
  // =========================================================================

  describe('processEffectStack', () => {
    
    test('empty effects array returns unmodified canvas', () => {
      const input = createTestCanvas(100, 100, '#ff0000');
      const result = processEffectStack([], input, 0);
      
      const imageData = result.ctx.getImageData(50, 50, 1, 1);
      expect(imageData.data[0]).toBe(255); // Still red
    });

    test('single effect is applied', () => {
      const input = createTestCanvas(100, 100, '#ff0000'); // Red
      const effects = [createMockEffect('test-invert', {})];
      
      const result = processEffectStack(effects, input, 0);
      
      const imageData = result.ctx.getImageData(50, 50, 1, 1);
      expect(imageData.data[0]).toBe(0);   // Inverted: Red → Cyan (no red)
      expect(imageData.data[1]).toBe(255); // Green component
      expect(imageData.data[2]).toBe(255); // Blue component
    });

    test('disabled effects are skipped', () => {
      const input = createTestCanvas(100, 100, '#ff0000');
      const effects = [createMockEffect('test-invert', {}, false)];
      
      const result = processEffectStack(effects, input, 0);
      
      const imageData = result.ctx.getImageData(50, 50, 1, 1);
      expect(imageData.data[0]).toBe(255); // Still red (not inverted)
    });

    test('multiple effects are applied in order', () => {
      const input = createTestCanvas(100, 100, '#808080'); // Gray (128, 128, 128)
      const effects = [
        createMockEffect('test-brightness', { intensity: 2 }), // Double brightness
        createMockEffect('test-invert', {}), // Then invert
      ];
      
      const result = processEffectStack(effects, input, 0);
      
      // 128 * 2 = 255 (clamped), then inverted = 0
      const imageData = result.ctx.getImageData(50, 50, 1, 1);
      expect(imageData.data[0]).toBe(0);
    });

    test('BUG-069 FIXED: unregistered effects throw LOUD errors', () => {
      const input = createTestCanvas(100, 100, '#ff0000');
      const effects = [createMockEffect('nonexistent-effect', {})];
      
      // FIXED: Now throws with explicit error message
      expect(() => processEffectStack(effects, input, 0)).toThrow(
        /EFFECT RENDERER NOT FOUND.*nonexistent-effect/
      );
    });
  });

  // =========================================================================
  // CANVAS POOL
  // =========================================================================

  describe('canvas pool', () => {
    
    test('pool statistics are tracked', () => {
      const stats = getEffectProcessorStats();
      
      expect(typeof stats.canvasPool.total).toBe('number');
      expect(typeof stats.canvasPool.inUse).toBe('number');
      expect(typeof stats.canvasPool.available).toBe('number');
    });

    test('acquire and release cycle works', () => {
      const source = createTestCanvas(200, 200);
      
      const canvas1 = createMatchingCanvas(source);
      const stats1 = getEffectProcessorStats();
      
      releaseCanvas(canvas1.canvas);
      const stats2 = getEffectProcessorStats();
      
      expect(stats2.canvasPool.inUse).toBeLessThanOrEqual(stats1.canvasPool.inUse);
    });

    test('clearEffectCaches resets pool', () => {
      const source = createTestCanvas(100, 100);
      createMatchingCanvas(source);
      createMatchingCanvas(source);
      
      clearEffectCaches();
      
      const stats = getEffectProcessorStats();
      expect(stats.canvasPool.total).toBe(0);
    });
  });

  // =========================================================================
  // EFFECT CACHE
  // =========================================================================

  describe('effect cache', () => {
    
    test('cache statistics are tracked', () => {
      const stats = getEffectProcessorStats();
      
      expect(typeof stats.effectCache.size).toBe('number');
      expect(typeof stats.effectCache.maxSize).toBe('number');
    });

    test('clearEffectCaches resets cache', () => {
      // Process some effects to populate cache
      const input = createTestCanvas(100, 100);
      const effects = [createMockEffect('test-invert', {})];
      processEffectStack(effects, input, 0);
      
      clearEffectCaches();
      
      const stats = getEffectProcessorStats();
      expect(stats.effectCache.size).toBe(0);
    });
  });

  // =========================================================================
  // GPU CAPABILITIES
  // =========================================================================

  describe('GPU capabilities', () => {
    
    test('isGPUEffectProcessingAvailable returns boolean', () => {
      const available = isGPUEffectProcessingAvailable();
      expect(typeof available).toBe('boolean');
    });

    test('getGPUEffectCapabilities returns capability info', () => {
      const caps = getGPUEffectCapabilities();
      
      expect(typeof caps.available).toBe('boolean');
      expect(typeof caps.webgpuAvailable).toBe('boolean');
      expect(typeof caps.webgl2Available).toBe('boolean');
      expect(['webgpu', 'webgl2', 'canvas2d']).toContain(caps.preferredPath);
    });
  });

  // =========================================================================
  // DETERMINISM
  // =========================================================================

  describe('determinism', () => {
    
    test('same input + same effects = identical output (100 runs)', () => {
      const input = createTestCanvas(100, 100, '#ff8800');
      const effects = [
        createMockEffect('test-brightness', { intensity: 1.5 }),
        createMockEffect('test-invert', {}),
      ];

      // Get reference result
      const referenceResult = processEffectStack(effects, input, 0);
      const referenceData = canvasToImageData(referenceResult.canvas);

      // Run 100 times and compare
      for (let i = 0; i < 100; i++) {
        const result = processEffectStack(effects, input, 0);
        const resultData = canvasToImageData(result.canvas);
        
        // Compare pixel by pixel
        for (let j = 0; j < referenceData.data.length; j++) {
          expect(resultData.data[j]).toBe(referenceData.data[j]);
        }
      }
    });
  });

  // =========================================================================
  // EDGE CASES
  // =========================================================================

  describe('edge cases', () => {
    
    test('handles 1x1 canvas', () => {
      const input = createTestCanvas(1, 1, '#ffffff');
      const effects = [createMockEffect('test-invert', {})];
      
      const result = processEffectStack(effects, input, 0);
      
      expect(result.canvas.width).toBe(1);
      expect(result.canvas.height).toBe(1);
      
      const imageData = result.ctx.getImageData(0, 0, 1, 1);
      expect(imageData.data[0]).toBe(0); // Inverted white = black
    });

    test('handles large canvas (4K)', () => {
      const input = createTestCanvas(3840, 2160, '#888888');
      const effects = [createMockEffect('test-brightness', { intensity: 1.2 })];
      
      const result = processEffectStack(effects, input, 0);
      
      expect(result.canvas.width).toBe(3840);
      expect(result.canvas.height).toBe(2160);
    });

    test('handles transparent canvas', () => {
      const canvas = document.createElement('canvas');
      canvas.width = 100;
      canvas.height = 100;
      // Don't fill - leave transparent
      
      const effects = [createMockEffect('test-invert', {})];
      const result = processEffectStack(effects, canvas, 0);
      
      const imageData = result.ctx.getImageData(50, 50, 1, 1);
      expect(imageData.data[3]).toBe(0); // Still transparent
    });
  });
});
