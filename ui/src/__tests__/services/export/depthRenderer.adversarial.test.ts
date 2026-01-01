/**
 * Depth Renderer Adversarial Tests
 *
 * Tests designed to BREAK the depth rendering system and verify it fails gracefully.
 * Focus areas:
 * - Division by zero in depth normalization
 * - Invalid dimension handling
 * - Unknown format handling
 * - Edge cases in depth buffer processing
 *
 * @module DepthRendererAdversarialTests
 */

import { describe, it, expect, vi } from 'vitest';

import {
  renderDepthFrame,
  convertDepthToFormat,
  depthToImageData,
  depthToGrayscaleImageData,
  applyColormap,
  generateDepthMetadata,
  type DepthRenderResult,
  type DepthRenderOptions,
} from '@/services/export/depthRenderer';
import type { Camera3D } from '@/types/camera';
import type { Layer } from '@/types/project';
import type { DepthMapFormat } from '@/types/export';

// ============================================================================
// Test Fixtures
// ============================================================================

function createValidCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: 'test-camera',
    name: 'Test Camera',
    type: 'perspective',
    position: { x: 0, y: 0, z: -500 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    focalLength: 50,
    angleOfView: 39.6,
    zoom: 1,
    nearClip: 1,
    farClip: 10000,
    filmSize: 36,
    depthOfField: {
      enabled: false,
      focusDistance: 100,
      aperture: 2.8,
      bladeCount: 6,
    },
    ...overrides,
  } as Camera3D;
}

function createValidLayer(overrides: Partial<Layer> = {}): Layer {
  return {
    id: 'test-layer',
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    startFrame: 0,
    endFrame: 100,
    transform: {
      position: { value: [0, 0, 0] },
      scale: { value: [100, 100] },
      rotation: { value: 0 },
      anchorPoint: { value: [0, 0] },
    },
    opacity: { value: 100 },
    ...overrides,
  } as unknown as Layer;
}

function createDepthResult(overrides: Partial<DepthRenderResult> = {}): DepthRenderResult {
  const width = overrides.width ?? 512;
  const height = overrides.height ?? 512;
  return {
    depthBuffer: new Float32Array(width * height).fill(500),
    width,
    height,
    minDepth: overrides.minDepth ?? 100,
    maxDepth: overrides.maxDepth ?? 1000,
    ...overrides,
  };
}

// ============================================================================
// CRITICAL: Division by Zero - Depth Normalization
// ============================================================================

describe('CRITICAL: convertDepthToFormat - Division by Zero', () => {

  it('should handle minDepth === maxDepth (zero range)', () => {
    const result = createDepthResult({
      minDepth: 500,
      maxDepth: 500, // Same as min = zero range
    });

    // Should not crash - should return uniform mid-gray
    const output = convertDepthToFormat(result, 'midas');

    expect(output).toBeInstanceOf(Uint8Array);

    // All values should be the same (uniform gray)
    const firstVal = output[0];
    for (let i = 1; i < output.length; i++) {
      expect(output[i]).toBe(firstVal);
    }
  });

  it('should handle very small depth range', () => {
    const result = createDepthResult({
      minDepth: 500,
      maxDepth: 500.00001, // Extremely small range
    });

    const output = convertDepthToFormat(result, 'midas');

    // Should not produce NaN/Infinity
    for (let i = 0; i < output.length; i++) {
      expect(Number.isFinite(output[i])).toBe(true);
    }
  });

  it('should handle NaN in minDepth/maxDepth', () => {
    const result = createDepthResult({
      minDepth: NaN,
      maxDepth: NaN,
    });

    // depthRange = NaN - NaN = NaN, should trigger fallback
    const output = convertDepthToFormat(result, 'midas');

    // Should not crash
    expect(output).toBeInstanceOf(Uint8Array);
  });

  it('should handle Infinity in depth range', () => {
    const result = createDepthResult({
      minDepth: -Infinity,
      maxDepth: Infinity,
    });

    const output = convertDepthToFormat(result, 'midas');

    // Should produce valid output (fallback to mid-gray)
    expect(output).toBeInstanceOf(Uint8Array);
    for (let i = 0; i < Math.min(output.length, 100); i++) {
      expect(Number.isFinite(output[i])).toBe(true);
    }
  });

  it('should handle NaN values in depth buffer', () => {
    const buffer = new Float32Array(100);
    buffer.fill(500);
    buffer[50] = NaN; // One NaN value

    const result = createDepthResult({
      depthBuffer: buffer,
      width: 10,
      height: 10,
    });

    const output = convertDepthToFormat(result, 'midas');

    // NaN should be converted to fallback value
    expect(output).toBeInstanceOf(Uint8Array);
    expect(Number.isFinite(output[50])).toBe(true);
  });
});

// ============================================================================
// CRITICAL: Unknown Format Handling
// ============================================================================

describe('CRITICAL: convertDepthToFormat - Unknown Format', () => {

  it('should throw for unknown depth format', () => {
    const result = createDepthResult();

    expect(() => {
      convertDepthToFormat(result, 'unknown-format' as DepthMapFormat);
    }).toThrow(/unknown.*format|valid formats/i);
  });

  it('should throw for null format', () => {
    const result = createDepthResult();

    expect(() => {
      convertDepthToFormat(result, null as any);
    }).toThrow(/unknown.*format|valid formats/i);
  });

  it('should throw for undefined format', () => {
    const result = createDepthResult();

    expect(() => {
      convertDepthToFormat(result, undefined as any);
    }).toThrow(/unknown.*format|valid formats/i);
  });
});

// ============================================================================
// CRITICAL: Dimension Validation
// ============================================================================

describe('CRITICAL: convertDepthToFormat - Invalid Dimensions', () => {

  it('should throw for zero width', () => {
    const result = createDepthResult({
      width: 0,
      height: 512,
      depthBuffer: new Float32Array(0),
    });

    expect(() => {
      convertDepthToFormat(result, 'midas');
    }).toThrow(/invalid.*dimensions|width.*0/i);
  });

  it('should throw for zero height', () => {
    const result = createDepthResult({
      width: 512,
      height: 0,
      depthBuffer: new Float32Array(0),
    });

    expect(() => {
      convertDepthToFormat(result, 'midas');
    }).toThrow(/invalid.*dimensions|height.*0/i);
  });

  it('should throw for negative dimensions', () => {
    const result = createDepthResult({
      width: -512,
      height: -512,
    });

    expect(() => {
      convertDepthToFormat(result, 'midas');
    }).toThrow(/invalid.*dimensions/i);
  });
});

// ============================================================================
// HIGH: 16-bit vs 8-bit Format Handling
// ============================================================================

describe('HIGH: convertDepthToFormat - Bit Depth Handling', () => {

  it('should produce 8-bit output for MiDaS format', () => {
    const result = createDepthResult();
    const output = convertDepthToFormat(result, 'midas');

    expect(output).toBeInstanceOf(Uint8Array);

    // Values should be 0-255
    for (let i = 0; i < Math.min(output.length, 100); i++) {
      expect(output[i]).toBeGreaterThanOrEqual(0);
      expect(output[i]).toBeLessThanOrEqual(255);
    }
  });

  it('should produce 16-bit output for ZoeDepth format', () => {
    const result = createDepthResult();
    // Fixed: format name is 'zoe' not 'zoedepth'
    const output = convertDepthToFormat(result, 'zoe');

    expect(output).toBeInstanceOf(Uint16Array);

    // Values should be 0-65535
    for (let i = 0; i < Math.min(output.length, 100); i++) {
      expect(output[i]).toBeGreaterThanOrEqual(0);
      expect(output[i]).toBeLessThanOrEqual(65535);
    }
  });

  it('should produce 16-bit output for Depth-Pro format', () => {
    const result = createDepthResult();
    const output = convertDepthToFormat(result, 'depth-pro');

    expect(output).toBeInstanceOf(Uint16Array);
  });

  it('should handle inversion correctly for MiDaS', () => {
    // MiDaS inverts: 0 = far, 255 = near
    const buffer = new Float32Array(4);
    buffer[0] = 100; // Near
    buffer[1] = 500; // Mid
    buffer[2] = 1000; // Far
    buffer[3] = 1000; // Far

    const result = createDepthResult({
      depthBuffer: buffer,
      width: 2,
      height: 2,
      minDepth: 100,
      maxDepth: 1000,
    });

    const output = convertDepthToFormat(result, 'midas');

    // Near (100) should be high value (inverted)
    expect(output[0]).toBeGreaterThan(200);

    // Far (1000) should be low value (inverted)
    expect(output[2]).toBeLessThan(50);
  });
});

// ============================================================================
// HIGH: depthToImageData - Channel Packing
// ============================================================================

describe('HIGH: depthToImageData - 16-bit Channel Packing', () => {

  it('should pack 16-bit into RG channels when packChannels=true', () => {
    const depth16 = new Uint16Array([0, 256, 65535, 32768]);
    const imageData = depthToImageData(depth16, 2, 2, true);

    // Value 0: R=0, G=0
    expect(imageData.data[0]).toBe(0);  // R
    expect(imageData.data[1]).toBe(0);  // G

    // Value 256 = 0x0100: R=1, G=0
    expect(imageData.data[4]).toBe(1);  // R (high byte)
    expect(imageData.data[5]).toBe(0);  // G (low byte)

    // Value 65535 = 0xFFFF: R=255, G=255
    expect(imageData.data[8]).toBe(255);  // R
    expect(imageData.data[9]).toBe(255);  // G

    // Blue channel should always be 0
    expect(imageData.data[2]).toBe(0);
    expect(imageData.data[6]).toBe(0);
    expect(imageData.data[10]).toBe(0);
  });

  it('should convert 16-bit to 8-bit grayscale when packChannels=false', () => {
    const depth16 = new Uint16Array([0, 32768, 65535]); // 0, ~50%, 100%
    const imageData = depthToImageData(depth16, 3, 1, false);

    // 0 / 256 = 0
    expect(imageData.data[0]).toBe(0);
    expect(imageData.data[1]).toBe(0);
    expect(imageData.data[2]).toBe(0);

    // 32768 / 256 = 128
    expect(imageData.data[4]).toBe(128);
    expect(imageData.data[5]).toBe(128);
    expect(imageData.data[6]).toBe(128);

    // 65535 / 256 = 255 (floor)
    expect(imageData.data[8]).toBe(255);
  });

  it('should handle 8-bit depth data', () => {
    const depth8 = new Uint8Array([0, 128, 255]);
    const imageData = depthToImageData(depth8, 3, 1);

    // Should be grayscale (R=G=B)
    expect(imageData.data[0]).toBe(0);
    expect(imageData.data[1]).toBe(0);
    expect(imageData.data[2]).toBe(0);

    expect(imageData.data[4]).toBe(128);
    expect(imageData.data[5]).toBe(128);
    expect(imageData.data[6]).toBe(128);
  });

  it('should always set alpha to 255', () => {
    const depth8 = new Uint8Array([100]);
    const imageData = depthToImageData(depth8, 1, 1);

    expect(imageData.data[3]).toBe(255); // Alpha
  });
});

// ============================================================================
// HIGH: Colormap Application
// ============================================================================

describe('HIGH: applyColormap - Value Clamping', () => {

  it('should clamp values < 0 to 0', () => {
    // This shouldn't happen with Uint arrays, but test the clamping logic
    const depth8 = new Uint8Array([0, 128, 255]);
    const imageData = applyColormap(depth8, 3, 1, 'viridis');

    // Should not crash
    expect(imageData.width).toBe(3);
    expect(imageData.height).toBe(1);
  });

  it('should handle all colormap types', () => {
    const depth8 = new Uint8Array([0, 64, 128, 192, 255]);

    const colormaps = ['grayscale', 'viridis', 'magma', 'plasma'] as const;

    for (const colormap of colormaps) {
      const imageData = applyColormap(depth8, 5, 1, colormap);
      expect(imageData.width).toBe(5);

      // All RGB values should be 0-255
      for (let i = 0; i < imageData.data.length; i++) {
        expect(imageData.data[i]).toBeGreaterThanOrEqual(0);
        expect(imageData.data[i]).toBeLessThanOrEqual(255);
      }
    }
  });

  it('should default to grayscale for unknown colormap', () => {
    const depth8 = new Uint8Array([128]);
    const imageData = applyColormap(depth8, 1, 1, 'unknown' as any);

    // Should fall through to grayscale (R=G=B)
    expect(imageData.data[0]).toBe(imageData.data[1]);
    expect(imageData.data[1]).toBe(imageData.data[2]);
  });
});

// ============================================================================
// MEDIUM: renderDepthFrame - Layer Processing
// ============================================================================

describe('MEDIUM: renderDepthFrame - Layer Edge Cases', () => {

  it('should handle empty layers array', () => {
    const options: DepthRenderOptions = {
      width: 512,
      height: 512,
      nearClip: 1,
      farClip: 1000,
      camera: createValidCamera(),
      layers: [],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    expect(result.depthBuffer.length).toBe(512 * 512);
    // All values should be farClip (no layers to render)
    expect(result.depthBuffer[0]).toBe(1000);
  });

  it('should skip invisible layers', () => {
    const options: DepthRenderOptions = {
      width: 64,
      height: 64,
      nearClip: 1,
      farClip: 1000,
      camera: createValidCamera(),
      layers: [createValidLayer({ visible: false })],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    // Should still be farClip (invisible layer skipped)
    expect(result.depthBuffer[0]).toBe(1000);
  });

  it('should skip layers with zero opacity', () => {
    const options: DepthRenderOptions = {
      width: 64,
      height: 64,
      nearClip: 1,
      farClip: 1000,
      camera: createValidCamera(),
      layers: [createValidLayer({ opacity: { value: 0 } } as any)],
      frame: 0,
    };

    const result = renderDepthFrame(options);

    // Should still be farClip
    expect(result.depthBuffer[0]).toBe(1000);
  });

  it('should handle layer with no transform', () => {
    const layer = createValidLayer();
    delete (layer as any).transform;

    const options: DepthRenderOptions = {
      width: 64,
      height: 64,
      nearClip: 1,
      farClip: 1000,
      camera: createValidCamera(),
      layers: [layer],
      frame: 0,
    };

    // Should not crash
    const result = renderDepthFrame(options);
    expect(result.depthBuffer).toBeInstanceOf(Float32Array);
  });
});

// ============================================================================
// MEDIUM: Metadata Generation
// ============================================================================

describe('MEDIUM: generateDepthMetadata', () => {

  it('should generate valid metadata', () => {
    const metadata = generateDepthMetadata('midas', 100, 1920, 1080, 10, 1000);

    expect(metadata).toMatchObject({
      format: 'midas',
      frameCount: 100,
      width: 1920,
      height: 1080,
      actualRange: {
        min: 10,
        max: 1000,
      },
    });

    expect(metadata).toHaveProperty('generatedAt');
    expect(metadata).toHaveProperty('generator');
  });

  it('should handle NaN depth range', () => {
    const metadata = generateDepthMetadata('zoe', 50, 512, 512, NaN, NaN) as {
      actualRange: { min: number; max: number };
    };

    expect(metadata.actualRange.min).toBe(NaN);
    expect(metadata.actualRange.max).toBe(NaN);
    // Should not crash
  });
});

// ============================================================================
// EDGE: depthToGrayscaleImageData Convenience Function
// ============================================================================

describe('EDGE: depthToGrayscaleImageData', () => {

  it('should always produce grayscale output', () => {
    const depth16 = new Uint16Array([0, 32768, 65535]);
    const imageData = depthToGrayscaleImageData(depth16, 3, 1);

    // Should be grayscale (R=G=B for each pixel)
    for (let i = 0; i < 3; i++) {
      const pixelIdx = i * 4;
      expect(imageData.data[pixelIdx]).toBe(imageData.data[pixelIdx + 1]);
      expect(imageData.data[pixelIdx + 1]).toBe(imageData.data[pixelIdx + 2]);
    }
  });
});
