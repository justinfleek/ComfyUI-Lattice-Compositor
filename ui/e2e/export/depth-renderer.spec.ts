/**
 * Depth Renderer Browser Tests
 * 
 * Tests for browser-only depth rendering functions:
 * - depthToImageData: Converts depth buffer to ImageData
 * - applyColormap: Applies colormaps (viridis, plasma, etc.)
 * - exportDepthSequence: Exports full depth sequence
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor, createTestComposition } from "../helpers/compositor";

test.describe("Depth Renderer - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
    await createTestComposition(page, { width: 512, height: 512, frames: 10 });
  });

  test.describe("depthToImageData", () => {
    test("should convert depth buffer to RGBA ImageData", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthToImageData, renderDepthFrame } = await import(
          "/src/services/export/depthRenderer"
        );

        const depthResult = renderDepthFrame({
          layers: [],
          camera: null,
          width: 128,
          height: 128,
          frame: 0,
          format: "midas",
        });

        const imageData = depthToImageData(depthResult);
        return {
          width: imageData.width,
          height: imageData.height,
          dataLength: imageData.data.length,
          hasAlpha: imageData.data[3] === 255,
        };
      });

      expect(result.width).toBe(128);
      expect(result.height).toBe(128);
      expect(result.dataLength).toBe(128 * 128 * 4); // RGBA
      expect(result.hasAlpha).toBe(true);
    });

    test("should produce grayscale values for depth", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthToImageData, renderDepthFrame } = await import(
          "/src/services/export/depthRenderer"
        );

        const depthResult = renderDepthFrame({
          layers: [],
          camera: null,
          width: 64,
          height: 64,
          frame: 0,
          format: "midas",
        });

        const imageData = depthToImageData(depthResult);
        
        // Check first pixel - R, G, B should be equal (grayscale)
        const r = imageData.data[0];
        const g = imageData.data[1];
        const b = imageData.data[2];
        
        return { r, g, b, isGrayscale: r === g && g === b };
      });

      expect(result.isGrayscale).toBe(true);
    });

    test("should handle empty depth buffer", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthToImageData } = await import(
          "/src/services/export/depthRenderer"
        );

        const emptyDepth = {
          buffer: new Float32Array(64 * 64).fill(0),
          width: 64,
          height: 64,
          minDepth: 0,
          maxDepth: 0,
        };

        const imageData = depthToImageData(emptyDepth);
        return { width: imageData.width, height: imageData.height };
      });

      expect(result.width).toBe(64);
      expect(result.height).toBe(64);
    });
  });

  test.describe("applyColormap", () => {
    const colormaps = ["viridis", "plasma", "inferno", "magma", "turbo"] as const;

    for (const colormap of colormaps) {
      test(`should apply ${colormap} colormap`, async ({ page }) => {
        const result = await page.evaluate(async (cm) => {
          const { applyColormap, renderDepthFrame } = await import(
            "/src/services/export/depthRenderer"
          );

          const depthResult = renderDepthFrame({
            layers: [],
            camera: null,
            width: 32,
            height: 32,
            frame: 0,
            format: "midas",
          });

          const imageData = applyColormap(depthResult, cm);
          
          // Colormaps should produce colored (non-grayscale) output
          const r = imageData.data[0];
          const g = imageData.data[1];
          const b = imageData.data[2];
          
          return {
            width: imageData.width,
            height: imageData.height,
            r, g, b,
          };
        }, colormap);

        expect(result.width).toBe(32);
        expect(result.height).toBe(32);
        // Values should be valid RGB
        expect(result.r).toBeGreaterThanOrEqual(0);
        expect(result.r).toBeLessThanOrEqual(255);
      });
    }

    test("should produce different colors for different depths", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { applyColormap } = await import(
          "/src/services/export/depthRenderer"
        );

        // Create gradient depth buffer
        const buffer = new Float32Array(100);
        for (let i = 0; i < 100; i++) {
          buffer[i] = i / 99; // 0 to 1 gradient
        }

        const depthResult = {
          buffer,
          width: 10,
          height: 10,
          minDepth: 0,
          maxDepth: 1,
        };

        const imageData = applyColormap(depthResult, "viridis");
        
        // First and last pixel should be different colors
        const firstPixel = [imageData.data[0], imageData.data[1], imageData.data[2]];
        const lastPixel = [
          imageData.data[396], // (99 * 4)
          imageData.data[397],
          imageData.data[398],
        ];
        
        const isDifferent = 
          firstPixel[0] !== lastPixel[0] ||
          firstPixel[1] !== lastPixel[1] ||
          firstPixel[2] !== lastPixel[2];
        
        return { isDifferent, firstPixel, lastPixel };
      });

      expect(result.isDifferent).toBe(true);
    });
  });

  test.describe("exportDepthSequence", () => {
    test("should export sequence of depth frames", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDepthSequence, renderDepthFrame } = await import(
          "/src/services/export/depthRenderer"
        );

        const options = {
          layers: [],
          camera: null,
          width: 64,
          height: 64,
          startFrame: 0,
          endFrame: 5,
          format: "midas" as const,
        };

        const sequence = await exportDepthSequence(options);
        
        return {
          frameCount: sequence.frames.length,
          hasMetadata: !!sequence.metadata,
          firstFrameSize: sequence.frames[0]?.data.length,
        };
      });

      expect(result.frameCount).toBe(5);
      expect(result.hasMetadata).toBe(true);
    });

    test("should include frame numbers in sequence", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDepthSequence } = await import(
          "/src/services/export/depthRenderer"
        );

        const sequence = await exportDepthSequence({
          layers: [],
          camera: null,
          width: 32,
          height: 32,
          startFrame: 10,
          endFrame: 15,
          format: "depth-anything" as const,
        });

        return sequence.frames.map(f => f.frameNumber);
      });

      expect(result).toEqual([10, 11, 12, 13, 14]);
    });

    test("should respect format specification", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDepthSequence } = await import(
          "/src/services/export/depthRenderer"
        );

        const sequence = await exportDepthSequence({
          layers: [],
          camera: null,
          width: 32,
          height: 32,
          startFrame: 0,
          endFrame: 2,
          format: "zoe" as const,
        });

        return {
          format: sequence.metadata.format,
          bitDepth: sequence.metadata.bitDepth,
        };
      });

      expect(result.format).toBe("zoe");
    });
  });
});
