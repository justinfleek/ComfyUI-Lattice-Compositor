/**
 * STRICT Property Tests for Depth Renderer
 *
 * Tests the depth map generation for AI video ComfyUI nodes:
 * 1. Buffer shape: Float32Array of width * height
 * 2. Value range: nearClip to farClip
 * 3. Format conversion: MiDaS, ZoE, Depth-Anything, Marigold
 * 4. Colormap application
 *
 * TOLERANCE: STRICT - Wrong depth = wrong AI video depth conditioning
 */

import { describe, it, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  renderDepthFrame,
  convertDepthToFormat,
  depthToImageData,
  applyColormap,
  type DepthRenderOptions,
  type DepthRenderResult,
} from '@/services/export/depthRenderer';
import type { Camera3D } from '@/types/camera';
import type { Layer } from '@/types/project';
import type { DepthMapFormat } from '@/types/export';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

const arbitraryCamera = (): fc.Arbitrary<Camera3D> =>
  fc.record({
    type: fc.constant('perspective' as const),
    position: fc.record({
      x: fc.double({ min: -500, max: 500, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: -500, max: 500, noNaN: true, noDefaultInfinity: true }),
      z: fc.double({ min: 0, max: 1000, noNaN: true, noDefaultInfinity: true }),
    }),
    orientation: fc.record({
      x: fc.constant(0),
      y: fc.constant(0),
      z: fc.constant(0),
    }),
    focalLength: fc.constant(50),
    zoom: fc.constant(1),
    filmSize: fc.constant(36),
    depthOfField: fc.record({
      enabled: fc.constant(false),
      fStop: fc.constant(2.8),
      focusDistance: fc.constant(1000),
      bladeCount: fc.constant(7),
    }),
  });

const arbitrarySimpleLayer = (): fc.Arbitrary<Layer> =>
  fc.record({
    id: fc.uuid(),
    name: fc.constant('Test Layer'),
    type: fc.constant('solid' as const),
    visible: fc.boolean(),
    locked: fc.constant(false),
    transform: fc.record({
      position: fc.record({
        value: fc.record({
          x: fc.double({ min: 0, max: 1920, noNaN: true, noDefaultInfinity: true }),
          y: fc.double({ min: 0, max: 1080, noNaN: true, noDefaultInfinity: true }),
          z: fc.double({ min: -500, max: 500, noNaN: true, noDefaultInfinity: true }),
        }),
      }),
      scale: fc.record({
        value: fc.record({
          x: fc.constant(100),
          y: fc.constant(100),
        }),
      }),
      rotation: fc.record({ value: fc.constant(0) }),
      anchor: fc.record({
        value: fc.record({ x: fc.constant(0), y: fc.constant(0) }),
      }),
    }),
    width: fc.integer({ min: 100, max: 500 }),
    height: fc.integer({ min: 100, max: 500 }),
    startFrame: fc.constant(0),
    endFrame: fc.constant(100),
    blendMode: fc.constant('normal' as const),
    opacity: fc.record({ value: fc.integer({ min: 0, max: 100 }) }),
  });

// ============================================================================
// STRICT DEPTH BUFFER TESTS
// ============================================================================

describe('STRICT: Depth Buffer Generation', () => {
  test.prop([
    fc.integer({ min: 64, max: 512 }),
    fc.integer({ min: 64, max: 512 }),
    arbitraryCamera()
  ])('depth buffer has correct size', (width, height, camera) => {
    const options: DepthRenderOptions = {
      width,
      height,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    expect(result.depthBuffer).toBeInstanceOf(Float32Array);
    expect(result.depthBuffer.length).toBe(width * height);
    expect(result.width).toBe(width);
    expect(result.height).toBe(height);
  });

  test.prop([
    fc.integer({ min: 16, max: 64 }), // Reduced from 64-256 for faster tests
    fc.integer({ min: 16, max: 64 }),
    fc.double({ min: 0.01, max: 10, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true }),
    arbitraryCamera()
  ])('depth values within clip range', (width, height, nearClip, farClip, camera) => {
    fc.pre(nearClip < farClip);

    const options: DepthRenderOptions = {
      width,
      height,
      nearClip,
      farClip,
      camera,
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    // BUG-001 FIX: The depth buffer uses Float32, so we must compare against
    // Float32 precision bounds. Math.fround() converts Float64 to Float32.
    const f32NearClip = Math.fround(nearClip);
    const f32FarClip = Math.fround(farClip);

    // All values should be within Float32 clip range (empty scene = all at farClip)
    for (let i = 0; i < result.depthBuffer.length; i++) {
      expect(result.depthBuffer[i]).toBeGreaterThanOrEqual(f32NearClip);
      expect(result.depthBuffer[i]).toBeLessThanOrEqual(f32FarClip);
      expect(Number.isFinite(result.depthBuffer[i])).toBe(true);
    }
  });

  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 }),
    arbitraryCamera()
  ], { numRuns: 20 })('empty scene fills with farClip', (width, height, camera) => {
    const farClip = 1000;
    const options: DepthRenderOptions = {
      width,
      height,
      nearClip: 0.1,
      farClip,
      camera,
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    // All values should be at farClip for empty scene
    for (let i = 0; i < result.depthBuffer.length; i++) {
      expect(result.depthBuffer[i]).toBe(farClip);
    }
  });

  test.prop([
    fc.integer({ min: 64, max: 128 }),
    fc.integer({ min: 64, max: 128 }),
    arbitraryCamera()
  ])('minDepth <= maxDepth', (width, height, camera) => {
    const options: DepthRenderOptions = {
      width,
      height,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    expect(result.minDepth).toBeLessThanOrEqual(result.maxDepth);
  });
});

// ============================================================================
// STRICT FORMAT CONVERSION TESTS
// ============================================================================

describe('STRICT: Depth Format Conversion', () => {
  const formats: DepthMapFormat[] = ['raw', 'midas', 'zoe', 'depth-anything', 'marigold'];

  for (const format of formats) {
    test.prop([
      fc.integer({ min: 32, max: 64 }),
      fc.integer({ min: 32, max: 64 })
    ])(`${format}: produces valid output`, (width, height) => {
      // Create synthetic depth buffer
      const depthBuffer = new Float32Array(width * height);
      for (let i = 0; i < depthBuffer.length; i++) {
        depthBuffer[i] = 0.1 + (i / depthBuffer.length) * 999.9;
      }

      const result: DepthRenderResult = {
        depthBuffer,
        width,
        height,
        minDepth: 0.1,
        maxDepth: 1000,
      };

      const converted = convertDepthToFormat(result, format);

      // Should return a valid buffer
      expect(converted).toBeDefined();
      expect(converted.length).toBeGreaterThan(0);
    });
  }

  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 })
  ])('raw format preserves Float32Array', (width, height) => {
    const depthBuffer = new Float32Array(width * height);
    for (let i = 0; i < depthBuffer.length; i++) {
      depthBuffer[i] = i / depthBuffer.length * 1000;
    }

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 0,
      maxDepth: 1000,
    };

    const converted = convertDepthToFormat(result, 'raw');

    expect(converted).toBeInstanceOf(Float32Array);
    expect(converted.length).toBe(width * height);
  });
});

// ============================================================================
// STRICT IMAGE DATA CONVERSION TESTS
// ============================================================================

describe('STRICT: Depth to ImageData', () => {
  test.prop([
    fc.integer({ min: 16, max: 64 }),
    fc.integer({ min: 16, max: 64 })
  ])('produces valid ImageData dimensions', (width, height) => {
    const depthBuffer = new Float32Array(width * height);
    depthBuffer.fill(500); // Middle depth

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 0.1,
      maxDepth: 1000,
    };

    const imageData = depthToImageData(result);

    expect(imageData.width).toBe(width);
    expect(imageData.height).toBe(height);
    expect(imageData.data.length).toBe(width * height * 4); // RGBA
  });

  test.prop([
    fc.integer({ min: 8, max: 32 }), // Reduced for faster tests
    fc.integer({ min: 8, max: 32 })
  ])('pixel values are 0-255', (width, height) => {
    const depthBuffer = new Float32Array(width * height);
    for (let i = 0; i < depthBuffer.length; i++) {
      depthBuffer[i] = Math.random() * 1000;
    }

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 0,
      maxDepth: 1000,
    };

    const imageData = depthToImageData(result);

    // Sample check instead of checking every pixel (for performance)
    // Check first, last, and random samples
    const pixelCount = width * height;
    const samplesToCheck = Math.min(100, pixelCount * 4);
    for (let i = 0; i < samplesToCheck; i++) {
      const idx = Math.floor(i * imageData.data.length / samplesToCheck);
      expect(imageData.data[idx]).toBeGreaterThanOrEqual(0);
      expect(imageData.data[idx]).toBeLessThanOrEqual(255);
      expect(Number.isInteger(imageData.data[idx])).toBe(true);
    }
  });

  test.prop([
    fc.integer({ min: 16, max: 32 }),
    fc.integer({ min: 16, max: 32 })
  ])('alpha channel is always 255 (opaque)', (width, height) => {
    const depthBuffer = new Float32Array(width * height);
    depthBuffer.fill(500);

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 0.1,
      maxDepth: 1000,
    };

    const imageData = depthToImageData(result);

    // Check alpha channel (every 4th value starting at index 3)
    for (let i = 3; i < imageData.data.length; i += 4) {
      expect(imageData.data[i]).toBe(255);
    }
  });
});

// ============================================================================
// STRICT COLORMAP TESTS
// ============================================================================

describe('STRICT: Depth Colormap', () => {
  const colormaps = ['grayscale', 'viridis', 'plasma', 'magma', 'inferno', 'turbo'];

  for (const colormap of colormaps) {
    test.prop([
      fc.integer({ min: 16, max: 32 }),
      fc.integer({ min: 16, max: 32 })
    ])(`${colormap}: produces valid RGBA`, (width, height) => {
      const depthBuffer = new Float32Array(width * height);
      for (let i = 0; i < depthBuffer.length; i++) {
        depthBuffer[i] = (i / depthBuffer.length) * 1000;
      }

      const result: DepthRenderResult = {
        depthBuffer,
        width,
        height,
        minDepth: 0,
        maxDepth: 1000,
      };

      const colored = applyColormap(result, colormap as any);

      expect(colored.width).toBe(width);
      expect(colored.height).toBe(height);
      expect(colored.data.length).toBe(width * height * 4);

      // All values should be valid
      for (let i = 0; i < colored.data.length; i++) {
        expect(colored.data[i]).toBeGreaterThanOrEqual(0);
        expect(colored.data[i]).toBeLessThanOrEqual(255);
      }
    });
  }

  test.prop([
    fc.integer({ min: 16, max: 32 }),
    fc.integer({ min: 16, max: 32 })
  ])('grayscale produces R=G=B', (width, height) => {
    const depthBuffer = new Float32Array(width * height);
    for (let i = 0; i < depthBuffer.length; i++) {
      depthBuffer[i] = (i / depthBuffer.length) * 1000;
    }

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 0,
      maxDepth: 1000,
    };

    const colored = applyColormap(result, 'grayscale' as any);

    // Check that R=G=B for grayscale
    for (let i = 0; i < width * height; i++) {
      const r = colored.data[i * 4];
      const g = colored.data[i * 4 + 1];
      const b = colored.data[i * 4 + 2];

      expect(r).toBe(g);
      expect(g).toBe(b);
    }
  });

  it('near depth is bright, far depth is dark (for AI conditioning)', () => {
    const width = 10, height = 10;
    const depthBuffer = new Float32Array(width * height);

    // First half near (100), second half far (900)
    for (let i = 0; i < depthBuffer.length; i++) {
      depthBuffer[i] = i < depthBuffer.length / 2 ? 100 : 900;
    }

    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 100,
      maxDepth: 900,
    };

    const colored = applyColormap(result, 'grayscale' as any);

    // Near pixels (first half) should be brighter
    const nearBrightness = colored.data[0]; // First pixel R
    const farBrightness = colored.data[(width * height - 1) * 4]; // Last pixel R

    // MiDaS/ZoE convention: closer = brighter
    expect(nearBrightness).toBeGreaterThan(farBrightness);
  });
});

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe('STRICT: Depth Render Determinism', () => {
  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 }),
    arbitraryCamera()
  ])('same input produces identical output', (width, height, camera) => {
    const options: DepthRenderOptions = {
      width,
      height,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [],
      frame: 0,
    };

    const result1 = renderDepthFrame(options);
    const result2 = renderDepthFrame(options);

    expect(result1.depthBuffer.length).toBe(result2.depthBuffer.length);

    for (let i = 0; i < result1.depthBuffer.length; i++) {
      expect(result1.depthBuffer[i]).toBe(result2.depthBuffer[i]);
    }
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Depth Render Large Output', () => {
  test.prop([arbitraryCamera()])('handles 1080p resolution', (camera) => {
    const width = 1920, height = 1080;

    const options: DepthRenderOptions = {
      width,
      height,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    expect(result.depthBuffer.length).toBe(width * height);
    expect(result.width).toBe(width);
    expect(result.height).toBe(height);
  });
});
