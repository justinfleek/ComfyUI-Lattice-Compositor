/**
 * Property Tests: depthRenderer.ts
 * 
 * Testing depth map generation for AI video generation.
 * NO loosening tests to pass - failures are bugs.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  renderDepthFrame,
  convertDepthToFormat,
  depthToImageData,
  applyColormap,
  generateDepthMetadata,
  type DepthRenderOptions,
  type DepthRenderResult,
} from '@/services/export/depthRenderer';
import type { Camera3D } from '@/types/camera';
import type { Layer } from '@/types/project';
import type { DepthMapFormat } from '@/types/export';

// ============================================================================
// Custom Arbitraries
// ============================================================================

const vec3Arb = fc.record({
  x: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
  y: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
  z: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
});

const camera3DArb: fc.Arbitrary<Camera3D> = fc.record({
  id: fc.uuid(),
  name: fc.string({ minLength: 1, maxLength: 50 }),
  type: fc.constantFrom('perspective', 'orthographic') as fc.Arbitrary<'perspective' | 'orthographic'>,
  position: vec3Arb,
  orientation: fc.record({
    x: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
    y: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
    z: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
  }),
  focalLength: fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
  zoom: fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
  filmSize: fc.float({ min: Math.fround(10), max: Math.fround(100), noNaN: true }),
  depthOfField: fc.record({
    enabled: fc.boolean(),
    focusDistance: fc.float({ min: Math.fround(0.1), max: Math.fround(10000), noNaN: true }),
    aperture: fc.float({ min: Math.fround(0.5), max: Math.fround(32), noNaN: true }),
    blurAmount: fc.float({ min: Math.fround(0), max: Math.fround(100), noNaN: true }),
  }),
});

// Simple layer for testing
const simpleLayerArb: fc.Arbitrary<Layer> = fc.record({
  id: fc.uuid(),
  name: fc.string({ minLength: 1, maxLength: 50 }),
  type: fc.constantFrom('solid', 'shape', 'text') as fc.Arbitrary<Layer['type']>,
  visible: fc.boolean(),
  locked: fc.boolean(),
  inFrame: fc.integer({ min: 0, max: 100 }),
  outFrame: fc.integer({ min: 100, max: 1000 }),
  opacity: fc.record({
    id: fc.uuid(),
    name: fc.constant('opacity'),
    value: fc.float({ min: Math.fround(0), max: Math.fround(100), noNaN: true }),
    keyframes: fc.constant([]),
    expression: fc.constant(null),
  }),
  transform: fc.record({
    position: fc.record({
      id: fc.uuid(),
      name: fc.constant('position'),
      value: fc.tuple(
        fc.float({ min: Math.fround(-500), max: Math.fround(500), noNaN: true }),
        fc.float({ min: Math.fround(-500), max: Math.fround(500), noNaN: true }),
        fc.float({ min: Math.fround(-500), max: Math.fround(500), noNaN: true }),
      ),
      keyframes: fc.constant([]),
      expression: fc.constant(null),
    }),
    scale: fc.record({
      id: fc.uuid(),
      name: fc.constant('scale'),
      value: fc.tuple(
        fc.float({ min: Math.fround(10), max: Math.fround(200), noNaN: true }),
        fc.float({ min: Math.fround(10), max: Math.fround(200), noNaN: true }),
      ),
      keyframes: fc.constant([]),
      expression: fc.constant(null),
    }),
    rotation: fc.record({
      id: fc.uuid(),
      name: fc.constant('rotation'),
      value: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
      keyframes: fc.constant([]),
      expression: fc.constant(null),
    }),
    anchorPoint: fc.record({
      id: fc.uuid(),
      name: fc.constant('anchorPoint'),
      value: fc.tuple(
        fc.float({ min: Math.fround(-100), max: Math.fround(100), noNaN: true }),
        fc.float({ min: Math.fround(-100), max: Math.fround(100), noNaN: true }),
      ),
      keyframes: fc.constant([]),
      expression: fc.constant(null),
    }),
  }),
  effects: fc.constant([]),
  styles: fc.constant({}),
  mask: fc.constant(null),
  parentId: fc.constant(null),
  blendMode: fc.constant('normal' as const),
  motionBlur: fc.constant(false),
  motionBlurSamples: fc.constant(16),
  motionBlurShutterAngle: fc.constant(180),
}) as fc.Arbitrary<Layer>;

// Valid formats from types/export.ts: 'midas' | 'zoe' | 'depth-pro' | 'normalized'
const depthFormatArb = fc.constantFrom(
  'midas',
  'zoe',
  'depth-pro',
  'normalized',
) as fc.Arbitrary<DepthMapFormat>;

const colormapArb = fc.constantFrom('grayscale', 'viridis', 'magma', 'plasma') as fc.Arbitrary<'grayscale' | 'viridis' | 'magma' | 'plasma'>;

// ============================================================================
// Test: renderDepthFrame
// ============================================================================

describe('renderDepthFrame', () => {
  // BUG-004: This test times out at 5s with standard dimensions
  // This is a P2-HIGH performance bug - renderDepthFrame is O(width * height * layers)
  // and takes 54+ seconds for 512x512 with 5 layers
  // DO NOT reduce dimensions - this documents the real performance issue
  test.prop([
    camera3DArb,
    fc.array(simpleLayerArb, { minLength: 0, maxLength: 5 }),
    fc.integer({ min: 64, max: 512 }),
    fc.integer({ min: 64, max: 512 }),
    fc.integer({ min: 0, max: 100 }),
  ])(
    'returns valid DepthRenderResult',
    (camera, layers, width, height, frame) => {
      const options: DepthRenderOptions = {
        width,
        height,
        nearClip: 0.1,
        farClip: 1000,
        camera,
        layers,
        frame,
      };
      
      const result = renderDepthFrame(options);
      
      // Must return correct structure
      expect(result.depthBuffer).toBeInstanceOf(Float32Array);
      expect(result.depthBuffer.length).toBe(width * height);
      expect(result.width).toBe(width);
      expect(result.height).toBe(height);
      expect(typeof result.minDepth).toBe('number');
      expect(typeof result.maxDepth).toBe('number');
      
      // No NaN values in depth buffer
      for (let i = 0; i < result.depthBuffer.length; i++) {
        expect(Number.isNaN(result.depthBuffer[i])).toBe(false);
        expect(Number.isFinite(result.depthBuffer[i])).toBe(true);
      }
    }
  );

  test.prop([camera3DArb])(
    'with empty layers returns buffer filled with farClip',
    (camera) => {
      const options: DepthRenderOptions = {
        width: 100,
        height: 100,
        nearClip: 0.1,
        farClip: 1000,
        camera,
        layers: [],
        frame: 0,
      };
      
      const result = renderDepthFrame(options);
      
      // All values should be farClip (initial fill)
      for (let i = 0; i < result.depthBuffer.length; i++) {
        expect(result.depthBuffer[i]).toBe(1000);
      }
    }
  );

  test('depth values stay within clip range', () => {
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: true,
      locked: false,
      inFrame: 0,
      outFrame: 100,
      opacity: { id: '1', name: 'opacity', value: 100, keyframes: [], expression: null },
      transform: {
        position: { id: '2', name: 'position', value: [0, 0, 5000], keyframes: [], expression: null }, // Way beyond farClip
        scale: { id: '3', name: 'scale', value: [100, 100], keyframes: [], expression: null },
        rotation: { id: '4', name: 'rotation', value: 0, keyframes: [], expression: null },
        anchorPoint: { id: '5', name: 'anchorPoint', value: [0, 0], keyframes: [], expression: null },
      },
      effects: [],
      styles: {},
      mask: null,
      parentId: null,
      blendMode: 'normal',
      motionBlur: false,
      motionBlurSamples: 16,
      motionBlurShutterAngle: 180,
    } as Layer;
    
    const options: DepthRenderOptions = {
      width: 100,
      height: 100,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [layer],
      frame: 0,
    };
    
    const result = renderDepthFrame(options);
    
    // All values should be clamped to clip range
    for (let i = 0; i < result.depthBuffer.length; i++) {
      expect(result.depthBuffer[i]).toBeGreaterThanOrEqual(0.1);
      expect(result.depthBuffer[i]).toBeLessThanOrEqual(1000);
    }
  });
});

// ============================================================================
// Test: convertDepthToFormat
// ============================================================================

describe('convertDepthToFormat', () => {
  test.prop([
    fc.float({ min: Math.fround(0.1), max: Math.fround(100), noNaN: true }),
    fc.float({ min: Math.fround(100), max: Math.fround(1000), noNaN: true }),
    depthFormatArb,
  ])(
    'returns valid Uint8Array or Uint16Array',
    (minDepth, maxDepth, format) => {
      const width = 100;
      const height = 100;
      const depthBuffer = new Float32Array(width * height);
      
      // Fill with values between min and max
      for (let i = 0; i < depthBuffer.length; i++) {
        depthBuffer[i] = minDepth + Math.random() * (maxDepth - minDepth);
      }
      
      const result: DepthRenderResult = {
        depthBuffer,
        width,
        height,
        minDepth,
        maxDepth,
      };
      
      const output = convertDepthToFormat(result, format);
      
      // Must be Uint8Array or Uint16Array
      expect(
        output instanceof Uint8Array || output instanceof Uint16Array
      ).toBe(true);
      
      expect(output.length).toBe(width * height);
      
      // All values must be valid (no NaN after integer conversion)
      for (let i = 0; i < output.length; i++) {
        expect(Number.isNaN(output[i])).toBe(false);
        expect(Number.isFinite(output[i])).toBe(true);
      }
    }
  );

  // BUG TEST: Division by zero when minDepth === maxDepth
  test('handles minDepth === maxDepth without division by zero', () => {
    const width = 10;
    const height = 10;
    const depthBuffer = new Float32Array(width * height);
    depthBuffer.fill(500); // All same depth
    
    const result: DepthRenderResult = {
      depthBuffer,
      width,
      height,
      minDepth: 500, // Same as max!
      maxDepth: 500,
    };
    
    // This should NOT throw or produce NaN - using valid format 'midas'
    const output = convertDepthToFormat(result, 'midas');
    
    // Check no NaN or Infinity
    // BUG: This WILL produce NaN due to division by (maxDepth - minDepth) = 0
    for (let i = 0; i < output.length; i++) {
      expect(Number.isNaN(output[i])).toBe(false);
      expect(Number.isFinite(output[i])).toBe(true);
    }
  });
});

// ============================================================================
// Test: depthToImageData
// ============================================================================

describe('depthToImageData', () => {
  test.prop([
    fc.integer({ min: 10, max: 200 }),
    fc.integer({ min: 10, max: 200 }),
  ])(
    'returns ImageData with correct dimensions',
    (width, height) => {
      const depthData = new Uint8Array(width * height);
      for (let i = 0; i < depthData.length; i++) {
        depthData[i] = Math.floor(Math.random() * 256);
      }
      
      const imageData = depthToImageData(depthData, width, height);
      
      expect(imageData.width).toBe(width);
      expect(imageData.height).toBe(height);
      expect(imageData.data.length).toBe(width * height * 4);
    }
  );

  test('pixel values are grayscale (R=G=B)', () => {
    const width = 10;
    const height = 10;
    const depthData = new Uint8Array(width * height);
    for (let i = 0; i < depthData.length; i++) {
      depthData[i] = i % 256;
    }
    
    const imageData = depthToImageData(depthData, width, height);
    
    for (let i = 0; i < width * height; i++) {
      const pixelIdx = i * 4;
      const r = imageData.data[pixelIdx];
      const g = imageData.data[pixelIdx + 1];
      const b = imageData.data[pixelIdx + 2];
      const a = imageData.data[pixelIdx + 3];
      
      expect(r).toBe(g);
      expect(g).toBe(b);
      expect(a).toBe(255); // Alpha always 255
    }
  });

  test('16-bit depth data is properly downsampled to 8-bit', () => {
    const width = 10;
    const height = 10;
    const depthData = new Uint16Array(width * height);
    depthData.fill(32768); // Mid-range 16-bit value
    
    const imageData = depthToImageData(depthData, width, height);
    
    // 32768 / 256 = 128
    for (let i = 0; i < width * height; i++) {
      const pixelIdx = i * 4;
      expect(imageData.data[pixelIdx]).toBe(128);
    }
  });
});

// ============================================================================
// Test: applyColormap
// ============================================================================

describe('applyColormap', () => {
  test.prop([colormapArb])(
    'returns valid ImageData for all colormaps',
    (colormap) => {
      const width = 10;
      const height = 10;
      const depthData = new Uint8Array(width * height);
      for (let i = 0; i < depthData.length; i++) {
        depthData[i] = i % 256;
      }
      
      const imageData = applyColormap(depthData, width, height, colormap);
      
      expect(imageData.width).toBe(width);
      expect(imageData.height).toBe(height);
      expect(imageData.data.length).toBe(width * height * 4);
      
      // All pixel values should be valid 0-255
      for (let i = 0; i < imageData.data.length; i++) {
        expect(imageData.data[i]).toBeGreaterThanOrEqual(0);
        expect(imageData.data[i]).toBeLessThanOrEqual(255);
      }
    }
  );

  test('grayscale colormap produces R=G=B', () => {
    const width = 10;
    const height = 10;
    const depthData = new Uint8Array(width * height);
    for (let i = 0; i < depthData.length; i++) {
      depthData[i] = i % 256;
    }
    
    const imageData = applyColormap(depthData, width, height, 'grayscale');
    
    for (let i = 0; i < width * height; i++) {
      const pixelIdx = i * 4;
      const r = imageData.data[pixelIdx];
      const g = imageData.data[pixelIdx + 1];
      const b = imageData.data[pixelIdx + 2];
      
      expect(r).toBe(g);
      expect(g).toBe(b);
    }
  });

  test('alpha channel is always 255', () => {
    const width = 10;
    const height = 10;
    const depthData = new Uint8Array(width * height);
    depthData.fill(128);
    
    const colormaps: Array<'grayscale' | 'viridis' | 'magma' | 'plasma'> = ['grayscale', 'viridis', 'magma', 'plasma'];
    
    for (const colormap of colormaps) {
      const imageData = applyColormap(depthData, width, height, colormap);
      
      for (let i = 0; i < width * height; i++) {
        const pixelIdx = i * 4;
        expect(imageData.data[pixelIdx + 3]).toBe(255);
      }
    }
  });
});

// ============================================================================
// Test: generateDepthMetadata
// ============================================================================

describe('generateDepthMetadata', () => {
  test.prop([
    depthFormatArb,
    fc.integer({ min: 1, max: 1000 }),
    fc.integer({ min: 100, max: 4096 }),
    fc.integer({ min: 100, max: 4096 }),
    fc.float({ min: Math.fround(0.1), max: Math.fround(100), noNaN: true }),
    fc.float({ min: Math.fround(100), max: Math.fround(10000), noNaN: true }),
  ])(
    'returns valid metadata object',
    (format, frameCount, width, height, minDepth, maxDepth) => {
      const metadata = generateDepthMetadata(
        format,
        frameCount,
        width,
        height,
        minDepth,
        maxDepth,
      );
      
      expect(metadata).toHaveProperty('format', format);
      expect(metadata).toHaveProperty('frameCount', frameCount);
      expect(metadata).toHaveProperty('width', width);
      expect(metadata).toHaveProperty('height', height);
      expect(metadata).toHaveProperty('actualRange');
      expect((metadata as any).actualRange.min).toBe(minDepth);
      expect((metadata as any).actualRange.max).toBe(maxDepth);
      expect(metadata).toHaveProperty('generatedAt');
      expect(metadata).toHaveProperty('generator', 'Lattice Compositor');
    }
  );
});

// ============================================================================
// Edge Case Tests
// ============================================================================

describe('Edge Cases', () => {
  test('renderDepthFrame with invisible layers ignores them', () => {
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: false, // INVISIBLE
      locked: false,
      inFrame: 0,
      outFrame: 100,
      opacity: { id: '1', name: 'opacity', value: 100, keyframes: [], expression: null },
      transform: {
        position: { id: '2', name: 'position', value: [0, 0, 100], keyframes: [], expression: null },
        scale: { id: '3', name: 'scale', value: [100, 100], keyframes: [], expression: null },
        rotation: { id: '4', name: 'rotation', value: 0, keyframes: [], expression: null },
        anchorPoint: { id: '5', name: 'anchorPoint', value: [0, 0], keyframes: [], expression: null },
      },
      effects: [],
      styles: {},
      mask: null,
      parentId: null,
      blendMode: 'normal',
      motionBlur: false,
      motionBlurSamples: 16,
      motionBlurShutterAngle: 180,
    } as Layer;
    
    const options: DepthRenderOptions = {
      width: 100,
      height: 100,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [layer],
      frame: 0,
    };
    
    const result = renderDepthFrame(options);
    
    // Should be same as empty layers (all farClip)
    for (let i = 0; i < result.depthBuffer.length; i++) {
      expect(result.depthBuffer[i]).toBe(1000);
    }
  });

  test('renderDepthFrame with zero opacity layer ignores it', () => {
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: true,
      locked: false,
      inFrame: 0,
      outFrame: 100,
      opacity: { id: '1', name: 'opacity', value: 0, keyframes: [], expression: null }, // ZERO OPACITY
      transform: {
        position: { id: '2', name: 'position', value: [0, 0, 100], keyframes: [], expression: null },
        scale: { id: '3', name: 'scale', value: [100, 100], keyframes: [], expression: null },
        rotation: { id: '4', name: 'rotation', value: 0, keyframes: [], expression: null },
        anchorPoint: { id: '5', name: 'anchorPoint', value: [0, 0], keyframes: [], expression: null },
      },
      effects: [],
      styles: {},
      mask: null,
      parentId: null,
      blendMode: 'normal',
      motionBlur: false,
      motionBlurSamples: 16,
      motionBlurShutterAngle: 180,
    } as Layer;
    
    const options: DepthRenderOptions = {
      width: 100,
      height: 100,
      nearClip: 0.1,
      farClip: 1000,
      camera,
      layers: [layer],
      frame: 0,
    };
    
    const result = renderDepthFrame(options);
    
    // Should be same as empty layers (all farClip)
    for (let i = 0; i < result.depthBuffer.length; i++) {
      expect(result.depthBuffer[i]).toBe(1000);
    }
  });
});
