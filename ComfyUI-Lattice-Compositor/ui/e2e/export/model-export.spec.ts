/**
 * Model Export Browser Tests
 * 
 * Tests for browser-only model export functions:
 * - exportTTMLayer: Exports TTM format with canvas rendering
 * - generateMotionMask: Generates motion masks on canvas
 * - generateCombinedMotionMask: Combines multiple motion masks
 * - imageDataToBase64: Converts ImageData to base64
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor, createTestComposition, addTestLayer } from "../helpers/compositor";

test.describe("Model Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("exportTTMLayer", () => {
    test("should export layer with TTM metadata", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportTTMLayer } = await import("/src/services/modelExport");

        const layer = {
          id: "test-layer",
          name: "Test Layer",
          type: "solid",
          transform: {
            position: { x: 256, y: 256, animated: true },
            scale: { x: 1, y: 1, animated: false },
            rotation: 0,
            opacity: 1,
          },
          bounds: { x: 0, y: 0, width: 100, height: 100 },
        };

        const getPositionAtFrame = (layerId: string, frame: number) => ({
          x: 256 + frame * 5,
          y: 256,
        });

        const result = await exportTTMLayer(layer as any, {
          startFrame: 0,
          endFrame: 10,
          width: 512,
          height: 512,
          getPositionAtFrame,
        });

        return {
          hasTrajectory: !!result.trajectory,
          hasMask: !!result.mask,
          hasMetadata: !!result.metadata,
          trajectoryLength: result.trajectory?.length,
        };
      });

      expect(result.hasTrajectory).toBe(true);
      expect(result.trajectoryLength).toBe(10);
    });

    test("should include bounding box when provided", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportTTMLayer } = await import("/src/services/modelExport");

        const layer = {
          id: "bounded-layer",
          name: "Bounded",
          type: "solid",
          transform: {
            position: { x: 100, y: 100, animated: false },
            scale: { x: 1, y: 1, animated: false },
            rotation: 0,
            opacity: 1,
          },
          bounds: { x: 50, y: 50, width: 100, height: 100 },
        };

        const result = await exportTTMLayer(layer as any, {
          startFrame: 0,
          endFrame: 1,
          width: 512,
          height: 512,
          includeBoundingBox: true,
        });

        return {
          hasBbox: !!result.boundingBox,
          bboxX: result.boundingBox?.x,
          bboxWidth: result.boundingBox?.width,
        };
      });

      expect(result.hasBbox).toBe(true);
    });
  });

  test.describe("generateMotionMask", () => {
    test("should generate binary mask from layer motion", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateMotionMask } = await import("/src/services/modelExport");

        const trajectoryPoints = [
          { x: 100, y: 100 },
          { x: 150, y: 120 },
          { x: 200, y: 100 },
        ];

        const mask = generateMotionMask(trajectoryPoints, {
          width: 256,
          height: 256,
          brushSize: 20,
          blur: 2,
        });

        // Check mask is ImageData
        const isImageData = mask instanceof ImageData;
        
        // Check for non-zero values (motion areas)
        let hasMotion = false;
        for (let i = 0; i < mask.data.length; i += 4) {
          if (mask.data[i] > 0) {
            hasMotion = true;
            break;
          }
        }

        return {
          isImageData,
          width: mask.width,
          height: mask.height,
          hasMotion,
        };
      });

      expect(result.isImageData).toBe(true);
      expect(result.width).toBe(256);
      expect(result.height).toBe(256);
      expect(result.hasMotion).toBe(true);
    });

    test("should respect brush size", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateMotionMask } = await import("/src/services/modelExport");

        const points = [{ x: 128, y: 128 }];

        const smallMask = generateMotionMask(points, {
          width: 256,
          height: 256,
          brushSize: 10,
          blur: 0,
        });

        const largeMask = generateMotionMask(points, {
          width: 256,
          height: 256,
          brushSize: 50,
          blur: 0,
        });

        const countNonZero = (mask: ImageData) => {
          let count = 0;
          for (let i = 0; i < mask.data.length; i += 4) {
            if (mask.data[i] > 0) count++;
          }
          return count;
        };

        return {
          smallCount: countNonZero(smallMask),
          largeCount: countNonZero(largeMask),
          largeIsBigger: countNonZero(largeMask) > countNonZero(smallMask),
        };
      });

      expect(result.largeIsBigger).toBe(true);
    });

    test("should create continuous path between points", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateMotionMask } = await import("/src/services/modelExport");

        const points = [
          { x: 50, y: 128 },
          { x: 200, y: 128 }, // Horizontal line
        ];

        const mask = generateMotionMask(points, {
          width: 256,
          height: 256,
          brushSize: 10,
          blur: 0,
        });

        // Check middle of path
        const middleY = 128;
        const middleX = 125;
        const idx = (middleY * 256 + middleX) * 4;

        return {
          hasMiddle: mask.data[idx] > 0,
        };
      });

      expect(result.hasMiddle).toBe(true);
    });
  });

  test.describe("generateCombinedMotionMask", () => {
    test("should combine multiple layer masks", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateCombinedMotionMask } = await import("/src/services/modelExport");

        const layerTrajectories = [
          { layerId: "layer1", points: [{ x: 50, y: 50 }, { x: 100, y: 50 }] },
          { layerId: "layer2", points: [{ x: 200, y: 200 }, { x: 150, y: 200 }] },
        ];

        const mask = generateCombinedMotionMask(layerTrajectories, {
          width: 256,
          height: 256,
          brushSize: 15,
        });

        // Check both regions have motion
        const topLeft = mask.data[(50 * 256 + 75) * 4];
        const bottomRight = mask.data[(200 * 256 + 175) * 4];

        return {
          width: mask.width,
          height: mask.height,
          hasTopLeft: topLeft > 0,
          hasBottomRight: bottomRight > 0,
        };
      });

      expect(result.hasTopLeft).toBe(true);
      expect(result.hasBottomRight).toBe(true);
    });

    test("should handle overlapping trajectories", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateCombinedMotionMask } = await import("/src/services/modelExport");

        const layerTrajectories = [
          { layerId: "layer1", points: [{ x: 100, y: 100 }, { x: 150, y: 100 }] },
          { layerId: "layer2", points: [{ x: 125, y: 100 }, { x: 175, y: 100 }] }, // Overlaps
        ];

        const mask = generateCombinedMotionMask(layerTrajectories, {
          width: 256,
          height: 256,
          brushSize: 20,
        });

        // Check overlap region
        const overlapIdx = (100 * 256 + 137) * 4;

        return {
          overlapValue: mask.data[overlapIdx],
          hasOverlap: mask.data[overlapIdx] > 0,
        };
      });

      expect(result.hasOverlap).toBe(true);
    });

    test("should handle empty trajectories", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { generateCombinedMotionMask } = await import("/src/services/modelExport");

        const mask = generateCombinedMotionMask([], {
          width: 128,
          height: 128,
          brushSize: 10,
        });

        // Should be all zeros
        let isEmpty = true;
        for (let i = 0; i < mask.data.length; i += 4) {
          if (mask.data[i] > 0) {
            isEmpty = false;
            break;
          }
        }

        return { isEmpty, width: mask.width };
      });

      expect(result.isEmpty).toBe(true);
      expect(result.width).toBe(128);
    });
  });

  test.describe("imageDataToBase64", () => {
    test("should convert ImageData to base64 PNG", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { imageDataToBase64 } = await import("/src/services/modelExport");

        const canvas = document.createElement("canvas");
        canvas.width = 64;
        canvas.height = 64;
        const ctx = canvas.getContext("2d")!;
        
        // Draw something
        ctx.fillStyle = "#FF0000";
        ctx.fillRect(0, 0, 64, 64);
        
        const imageData = ctx.getImageData(0, 0, 64, 64);
        const base64 = imageDataToBase64(imageData);

        return {
          startsWithDataUrl: base64.startsWith("data:image/png;base64,"),
          hasContent: base64.length > 50,
        };
      });

      expect(result.startsWithDataUrl).toBe(true);
      expect(result.hasContent).toBe(true);
    });

    test("should preserve image dimensions", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { imageDataToBase64 } = await import("/src/services/modelExport");

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 50; // Non-square
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#00FF00";
        ctx.fillRect(0, 0, 100, 50);
        
        const imageData = ctx.getImageData(0, 0, 100, 50);
        const base64 = imageDataToBase64(imageData);

        // Decode and check dimensions
        return new Promise((resolve) => {
          const img = new Image();
          img.onload = () => {
            resolve({
              width: img.width,
              height: img.height,
            });
          };
          img.src = base64;
        });
      });

      expect(result.width).toBe(100);
      expect(result.height).toBe(50);
    });

    test("should preserve pixel colors", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { imageDataToBase64 } = await import("/src/services/modelExport");

        const canvas = document.createElement("canvas");
        canvas.width = 10;
        canvas.height = 10;
        const ctx = canvas.getContext("2d")!;
        
        // Draw specific colors
        ctx.fillStyle = "#FF0000"; // Red
        ctx.fillRect(0, 0, 5, 10);
        ctx.fillStyle = "#0000FF"; // Blue
        ctx.fillRect(5, 0, 5, 10);
        
        const imageData = ctx.getImageData(0, 0, 10, 10);
        const base64 = imageDataToBase64(imageData);

        // Decode and check colors
        return new Promise((resolve) => {
          const img = new Image();
          img.onload = () => {
            const testCanvas = document.createElement("canvas");
            testCanvas.width = 10;
            testCanvas.height = 10;
            const testCtx = testCanvas.getContext("2d")!;
            testCtx.drawImage(img, 0, 0);
            
            const data = testCtx.getImageData(0, 0, 10, 10).data;
            const leftRed = data[0]; // First pixel red channel
            const rightBlue = data[(5 * 4) + 2]; // Pixel at x=5, blue channel
            
            resolve({
              leftIsRed: leftRed > 200,
              rightIsBlue: rightBlue > 200,
            });
          };
          img.src = base64;
        });
      });

      expect(result.leftIsRed).toBe(true);
      expect(result.rightIsBlue).toBe(true);
    });

    test("should handle transparent pixels", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { imageDataToBase64 } = await import("/src/services/modelExport");

        const canvas = document.createElement("canvas");
        canvas.width = 10;
        canvas.height = 10;
        const ctx = canvas.getContext("2d")!;
        
        // Leave canvas transparent (default)
        const imageData = ctx.getImageData(0, 0, 10, 10);
        const base64 = imageDataToBase64(imageData);

        // Decode and check alpha
        return new Promise((resolve) => {
          const img = new Image();
          img.onload = () => {
            const testCanvas = document.createElement("canvas");
            testCanvas.width = 10;
            testCanvas.height = 10;
            const testCtx = testCanvas.getContext("2d")!;
            testCtx.drawImage(img, 0, 0);
            
            const data = testCtx.getImageData(0, 0, 10, 10).data;
            const alpha = data[3]; // First pixel alpha
            
            resolve({
              isTransparent: alpha === 0,
            });
          };
          img.src = base64;
        });
      });

      expect(result.isTransparent).toBe(true);
    });
  });
});
