/**
 * Property tests for ui/src/services/export/depthRenderer.ts
 * Tests: convertDepthToFormat, generateDepthMetadata
 * 
 * Browser-only (skipped): renderDepthFrame, depthToImageData, applyColormap
 * 
 * Audit: 2026-01-06
 * 
 * CRITICAL: These tests verify depth map format compatibility for AI video generation
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  convertDepthToFormat,
  generateDepthMetadata,
  type DepthRenderResult,
} from "@/services/export/depthRenderer";
import type { DepthMapFormat } from "@/types/export";
import { DEPTH_FORMAT_SPECS } from "@/config/exportPresets";

// ============================================================
// TEST FIXTURES
// ============================================================

function createDepthRenderResult(
  width: number,
  height: number,
  minVal: number,
  maxVal: number,
): DepthRenderResult {
  const pixelCount = width * height;
  const depthBuffer = new Float32Array(pixelCount);
  
  // Fill with gradient from min to max
  for (let i = 0; i < pixelCount; i++) {
    const t = i / (pixelCount - 1 || 1);
    depthBuffer[i] = minVal + (maxVal - minVal) * t;
  }
  
  return {
    depthBuffer,
    width,
    height,
    minDepth: minVal,
    maxDepth: maxVal,
  };
}

// ============================================================
// ARBITRARIES
// ============================================================

const validDepthFormats: DepthMapFormat[] = Object.keys(DEPTH_FORMAT_SPECS) as DepthMapFormat[];

const depthFormatArb = fc.constantFrom(...validDepthFormats);

const depthRenderResultArb = fc.record({
  width: fc.integer({ min: 8, max: 64 }),
  height: fc.integer({ min: 8, max: 64 }),
  minDepth: fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
  maxDepth: fc.float({ min: Math.fround(11), max: Math.fround(100), noNaN: true }),
}).map(({ width, height, minDepth, maxDepth }) => 
  createDepthRenderResult(width, height, minDepth, maxDepth)
);

// ============================================================
// convertDepthToFormat TESTS - CRITICAL FOR ML MODEL COMPATIBILITY
// ============================================================

describe("PROPERTY: convertDepthToFormat", () => {
  it("returns Float32Array for 'raw' format", () => {
    fc.assert(
      fc.property(depthRenderResultArb, (result) => {
        const output = convertDepthToFormat(result, "raw");
        expect(output).toBeInstanceOf(Float32Array);
      })
    );
  });

  it("returns Uint16Array for 16-bit formats", () => {
    const format16bitFormats = validDepthFormats.filter(
      (f) => DEPTH_FORMAT_SPECS[f].bitDepth === 16 && f !== "raw"
    );
    
    for (const format of format16bitFormats) {
      const result = createDepthRenderResult(16, 16, 0.5, 50);
      const output = convertDepthToFormat(result, format);
      expect(output).toBeInstanceOf(Uint16Array);
    }
  });

  it("returns Uint8Array for 8-bit formats", () => {
    const format8bitFormats = validDepthFormats.filter(
      (f) => DEPTH_FORMAT_SPECS[f].bitDepth === 8
    );
    
    for (const format of format8bitFormats) {
      const result = createDepthRenderResult(16, 16, 0.5, 50);
      const output = convertDepthToFormat(result, format);
      expect(output).toBeInstanceOf(Uint8Array);
    }
  });

  it("output length matches input pixel count", () => {
    fc.assert(
      fc.property(depthRenderResultArb, depthFormatArb, (result, format) => {
        const output = convertDepthToFormat(result, format);
        expect(output.length).toBe(result.width * result.height);
      })
    );
  });

  // NOTE: Array iteration over all pixels is slow - extend timeout
  it("8-bit output values are in range 0-255", () => {
    const format8bitFormats = validDepthFormats.filter(
      (f) => DEPTH_FORMAT_SPECS[f].bitDepth === 8
    );

    if (format8bitFormats.length === 0) return;

    fc.assert(
      fc.property(
        depthRenderResultArb,
        fc.constantFrom(...format8bitFormats),
        (result, format) => {
          const output = convertDepthToFormat(result, format) as Uint8Array;
          for (let i = 0; i < output.length; i++) {
            expect(output[i]).toBeGreaterThanOrEqual(0);
            expect(output[i]).toBeLessThanOrEqual(255);
          }
        }
      )
    );
  }, 30000);

  // NOTE: Array iteration over all pixels is slow - extend timeout
  it("16-bit output values are in range 0-65535", () => {
    const format16bitFormats = validDepthFormats.filter(
      (f) => DEPTH_FORMAT_SPECS[f].bitDepth === 16 && f !== "raw"
    );

    if (format16bitFormats.length === 0) return;

    fc.assert(
      fc.property(
        depthRenderResultArb,
        fc.constantFrom(...format16bitFormats),
        (result, format) => {
          const output = convertDepthToFormat(result, format) as Uint16Array;
          for (let i = 0; i < output.length; i++) {
            expect(output[i]).toBeGreaterThanOrEqual(0);
            expect(output[i]).toBeLessThanOrEqual(65535);
          }
        }
      )
    );
  }, 30000);

  it("raw format preserves Float32 values", () => {
    fc.assert(
      fc.property(depthRenderResultArb, (result) => {
        const output = convertDepthToFormat(result, "raw") as Float32Array;
        
        // Should be a copy, not the same reference
        expect(output).not.toBe(result.depthBuffer);
        
        // Values should match
        for (let i = 0; i < output.length; i++) {
          expect(output[i]).toBeCloseTo(result.depthBuffer[i], 5);
        }
      })
    );
  });

  it("handles constant depth (min === max) without division by zero", () => {
    const result = createDepthRenderResult(16, 16, 10, 10);
    result.minDepth = 10;
    result.maxDepth = 10;
    
    // Fill with constant value
    result.depthBuffer.fill(10);
    
    // Should not throw
    for (const format of validDepthFormats) {
      expect(() => convertDepthToFormat(result, format)).not.toThrow();
    }
  });

  it("throws for unknown format", () => {
    const result = createDepthRenderResult(16, 16, 0.5, 50);
    expect(() => convertDepthToFormat(result, "unknown-format" as DepthMapFormat)).toThrow();
  });

  it("inversion works correctly (near=bright for MiDaS compatibility)", () => {
    // Find an inverted format
    const invertedFormats = validDepthFormats.filter(
      (f) => DEPTH_FORMAT_SPECS[f].invert === true
    );
    
    if (invertedFormats.length === 0) return;
    
    for (const format of invertedFormats) {
      const result = createDepthRenderResult(2, 1, 0, 100);
      // First pixel is min depth (0), second is max depth (100)
      result.depthBuffer[0] = 0;
      result.depthBuffer[1] = 100;
      
      const output = convertDepthToFormat(result, format);
      
      // For inverted format: near (low depth) should produce HIGH values
      // far (high depth) should produce LOW values
      expect(output[0]).toBeGreaterThan(output[1]);
    }
  });
});

// ============================================================
// generateDepthMetadata TESTS
// ============================================================

describe("PROPERTY: generateDepthMetadata", () => {
  it("includes all required fields", () => {
    fc.assert(
      fc.property(
        depthFormatArb,
        fc.integer({ min: 1, max: 1000 }),
        fc.integer({ min: 64, max: 2048 }),
        fc.integer({ min: 64, max: 2048 }),
        fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
        fc.float({ min: Math.fround(11), max: Math.fround(100), noNaN: true }),
        (format, frameCount, width, height, minDepth, maxDepth) => {
          const metadata = generateDepthMetadata(
            format, frameCount, width, height, minDepth, maxDepth
          );
          
          expect(metadata).toHaveProperty("format");
          expect(metadata).toHaveProperty("bitDepth");
          expect(metadata).toHaveProperty("nearClip");
          expect(metadata).toHaveProperty("farClip");
          expect(metadata).toHaveProperty("inverted");
          expect(metadata).toHaveProperty("normalized");
          expect(metadata).toHaveProperty("frameCount");
          expect(metadata).toHaveProperty("width");
          expect(metadata).toHaveProperty("height");
          expect(metadata).toHaveProperty("actualRange");
          expect(metadata).toHaveProperty("generatedAt");
          expect(metadata).toHaveProperty("generator");
        }
      )
    );
  });

  it("returns correct format", () => {
    for (const format of validDepthFormats) {
      const metadata = generateDepthMetadata(format, 60, 512, 512, 0.5, 50) as { format: string };
      expect(metadata.format).toBe(format);
    }
  });

  it("returns correct bitDepth from spec", () => {
    for (const format of validDepthFormats) {
      const metadata = generateDepthMetadata(format, 60, 512, 512, 0.5, 50) as { bitDepth: number };
      expect(metadata.bitDepth).toBe(DEPTH_FORMAT_SPECS[format].bitDepth);
    }
  });

  it("returns correct dimensions", () => {
    fc.assert(
      fc.property(
        depthFormatArb,
        fc.integer({ min: 64, max: 2048 }),
        fc.integer({ min: 64, max: 2048 }),
        (format, width, height) => {
          const metadata = generateDepthMetadata(format, 60, width, height, 0.5, 50) as { width: number; height: number };
          expect(metadata.width).toBe(width);
          expect(metadata.height).toBe(height);
        }
      )
    );
  });

  it("returns correct frameCount", () => {
    fc.assert(
      fc.property(
        depthFormatArb,
        fc.integer({ min: 1, max: 1000 }),
        (format, frameCount) => {
          const metadata = generateDepthMetadata(format, frameCount, 512, 512, 0.5, 50) as { frameCount: number };
          expect(metadata.frameCount).toBe(frameCount);
        }
      )
    );
  });

  it("returns correct actualRange", () => {
    fc.assert(
      fc.property(
        depthFormatArb,
        fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
        fc.float({ min: Math.fround(11), max: Math.fround(100), noNaN: true }),
        (format, minDepth, maxDepth) => {
          const metadata = generateDepthMetadata(format, 60, 512, 512, minDepth, maxDepth) as { actualRange: { min: number; max: number } };
          expect(metadata.actualRange.min).toBeCloseTo(minDepth, 5);
          expect(metadata.actualRange.max).toBeCloseTo(maxDepth, 5);
        }
      )
    );
  });

  it("generatedAt is valid ISO date string", () => {
    const metadata = generateDepthMetadata("raw", 60, 512, 512, 0.5, 50) as { generatedAt: string };
    expect(() => new Date(metadata.generatedAt)).not.toThrow();
    expect(new Date(metadata.generatedAt).toISOString()).toBe(metadata.generatedAt);
  });

  it("generator is 'Lattice Compositor'", () => {
    const metadata = generateDepthMetadata("raw", 60, 512, 512, 0.5, 50) as { generator: string };
    expect(metadata.generator).toBe("Lattice Compositor");
  });
});

// ============================================================
// BROWSER-ONLY TESTS
// ============================================================
//
// The following browser-dependent functionality is tested in E2E:
//
// Location: /ui/e2e/export/depth-renderer.spec.ts
//
// Covered:
// - depthToImageData (E2E lines 22-102)
//   - convert depth buffer to RGBA ImageData
//   - produce grayscale values for depth
//   - handle empty depth buffer
// - applyColormap (E2E lines 104-185)
//   - apply viridis/plasma/inferno/magma/turbo colormaps
//   - produce different colors for different depths
// - exportDepthSequence (E2E lines 187-263)
//   - export sequence of depth frames
//   - include frame numbers in sequence
//   - respect format specification
//
// Run E2E tests with: bunx playwright test depth-renderer.spec.ts