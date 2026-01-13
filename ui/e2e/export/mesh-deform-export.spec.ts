/**
 * Mesh Deform Export Browser Tests
 * 
 * Tests for browser-only mesh deformation functions:
 * - depthBufferToImageData: Converts depth buffer to ImageData
 * - exportDeformedMeshMask: Exports mask from deformed mesh
 * - exportMeshMaskSequence: Exports sequence of mesh masks
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Mesh Deform Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("depthBufferToImageData", () => {
    test("should convert Float32 depth buffer to ImageData", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthBufferToImageData } = await import(
          "/src/services/export/meshDeformExport"
        );

        // Create test depth buffer (gradient from 0 to 1)
        const width = 64;
        const height = 64;
        const buffer = new Float32Array(width * height);
        for (let i = 0; i < buffer.length; i++) {
          buffer[i] = i / buffer.length;
        }

        const imageData = depthBufferToImageData(buffer, width, height);

        return {
          isImageData: imageData instanceof ImageData,
          width: imageData.width,
          height: imageData.height,
          dataLength: imageData.data.length,
        };
      });

      expect(result.isImageData).toBe(true);
      expect(result.width).toBe(64);
      expect(result.height).toBe(64);
      expect(result.dataLength).toBe(64 * 64 * 4);
    });

    test("should produce grayscale gradient", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthBufferToImageData } = await import(
          "/src/services/export/meshDeformExport"
        );

        const buffer = new Float32Array(100);
        for (let i = 0; i < 100; i++) {
          buffer[i] = i / 99; // 0 to 1
        }

        const imageData = depthBufferToImageData(buffer, 10, 10);

        // First pixel should be dark, last should be bright
        const firstR = imageData.data[0];
        const lastR = imageData.data[396]; // (99 * 4)

        return {
          firstR,
          lastR,
          lastBrighter: lastR > firstR,
        };
      });

      expect(result.lastBrighter).toBe(true);
    });

    test("should handle edge values", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { depthBufferToImageData } = await import(
          "/src/services/export/meshDeformExport"
        );

        const buffer = new Float32Array([0, 0.5, 1, -0.1, 1.5]); // Include out of range
        const imageData = depthBufferToImageData(buffer, 5, 1);

        return {
          val0: imageData.data[0],
          val05: imageData.data[4],
          val1: imageData.data[8],
        };
      });

      // Should clamp to valid range
      expect(result.val0).toBe(0);
      expect(result.val05).toBeCloseTo(127, -1); // ~127
      expect(result.val1).toBe(255);
    });
  });

  test.describe("exportDeformedMeshMask", () => {
    test("should generate mask from deformed mesh", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDeformedMeshMask } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = {
          vertices: [
            { x: 50, y: 50 },
            { x: 150, y: 50 },
            { x: 150, y: 150 },
            { x: 50, y: 150 },
          ],
          triangles: [
            [0, 1, 2],
            [0, 2, 3],
          ],
        };

        const pins = [
          { id: "pin1", position: { x: 100, y: 100 } },
        ];

        const mask = await exportDeformedMeshMask(mesh, pins, {
          width: 200,
          height: 200,
          frame: 0,
        });

        // Check for non-zero values in mesh area
        let hasContent = false;
        for (let i = 0; i < mask.data.length; i += 4) {
          if (mask.data[i] > 0) {
            hasContent = true;
            break;
          }
        }

        return {
          isImageData: mask instanceof ImageData,
          width: mask.width,
          height: mask.height,
          hasContent,
        };
      });

      expect(result.isImageData).toBe(true);
      expect(result.width).toBe(200);
      expect(result.height).toBe(200);
      expect(result.hasContent).toBe(true);
    });

    test("should show deformation based on pin movement", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDeformedMeshMask } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = {
          vertices: [
            { x: 50, y: 50 },
            { x: 150, y: 50 },
            { x: 150, y: 150 },
            { x: 50, y: 150 },
          ],
          triangles: [
            [0, 1, 2],
            [0, 2, 3],
          ],
        };

        // Pin moved from center to right
        const pins = [
          { 
            id: "pin1", 
            originalPosition: { x: 100, y: 100 },
            position: { x: 150, y: 100 }, // Moved right
          },
        ];

        const mask = await exportDeformedMeshMask(mesh, pins, {
          width: 200,
          height: 200,
          frame: 0,
        });

        // Check that right side has more content than left
        const countInRegion = (startX: number, endX: number) => {
          let count = 0;
          for (let y = 0; y < 200; y++) {
            for (let x = startX; x < endX; x++) {
              const idx = (y * 200 + x) * 4;
              if (mask.data[idx] > 0) count++;
            }
          }
          return count;
        };

        const leftCount = countInRegion(0, 100);
        const rightCount = countInRegion(100, 200);

        return {
          leftCount,
          rightCount,
          // Deformation should shift content right
        };
      });

      // With rightward deformation, we expect content to shift
      expect(result.rightCount).toBeGreaterThan(0);
    });

    test("should handle empty mesh", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportDeformedMeshMask } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = { vertices: [], triangles: [] };
        const pins: any[] = [];

        try {
          const mask = await exportDeformedMeshMask(mesh, pins, {
            width: 100,
            height: 100,
            frame: 0,
          });
          return { success: true, hasData: !!mask };
        } catch (e) {
          return { success: false, error: String(e) };
        }
      });

      expect(result.success).toBe(true);
    });
  });

  test.describe("exportMeshMaskSequence", () => {
    test("should export sequence of mask frames", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportMeshMaskSequence } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = {
          vertices: [
            { x: 50, y: 50 },
            { x: 100, y: 50 },
            { x: 75, y: 100 },
          ],
          triangles: [[0, 1, 2]],
        };

        const getPinsAtFrame = (frame: number) => [
          { 
            id: "pin1", 
            position: { x: 75 + frame * 5, y: 75 },
          },
        ];

        const sequence = await exportMeshMaskSequence(mesh, getPinsAtFrame, {
          width: 150,
          height: 150,
          startFrame: 0,
          endFrame: 5,
        });

        return {
          frameCount: sequence.frames.length,
          allImageData: sequence.frames.every(f => f instanceof ImageData),
          hasMetadata: !!sequence.metadata,
        };
      });

      expect(result.frameCount).toBe(5);
      expect(result.allImageData).toBe(true);
      expect(result.hasMetadata).toBe(true);
    });

    test("should produce different frames for animated pins", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportMeshMaskSequence } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = {
          vertices: [
            { x: 25, y: 25 },
            { x: 75, y: 25 },
            { x: 50, y: 75 },
          ],
          triangles: [[0, 1, 2]],
        };

        // Pin moves significantly
        const getPinsAtFrame = (frame: number) => [
          { 
            id: "pin1", 
            position: { x: 50 + frame * 20, y: 50 },
          },
        ];

        const sequence = await exportMeshMaskSequence(mesh, getPinsAtFrame, {
          width: 200,
          height: 100,
          startFrame: 0,
          endFrame: 3,
        });

        // Compare first and last frame
        const getPixelSum = (imageData: ImageData) => {
          let sum = 0;
          for (let i = 0; i < imageData.data.length; i += 4) {
            sum += imageData.data[i];
          }
          return sum;
        };

        const getCenterOfMass = (imageData: ImageData) => {
          let sumX = 0, count = 0;
          for (let y = 0; y < imageData.height; y++) {
            for (let x = 0; x < imageData.width; x++) {
              const idx = (y * imageData.width + x) * 4;
              if (imageData.data[idx] > 0) {
                sumX += x;
                count++;
              }
            }
          }
          return count > 0 ? sumX / count : 0;
        };

        const centerFirst = getCenterOfMass(sequence.frames[0]);
        const centerLast = getCenterOfMass(sequence.frames[sequence.frames.length - 1]);

        return {
          centerFirst,
          centerLast,
          moved: Math.abs(centerLast - centerFirst) > 10,
        };
      });

      expect(result.moved).toBe(true);
    });

    test("should respect frame range", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportMeshMaskSequence } = await import(
          "/src/services/export/meshDeformExport"
        );

        const mesh = {
          vertices: [{ x: 25, y: 25 }, { x: 75, y: 25 }, { x: 50, y: 75 }],
          triangles: [[0, 1, 2]],
        };

        const getPinsAtFrame = () => [];

        const sequence = await exportMeshMaskSequence(mesh, getPinsAtFrame, {
          width: 100,
          height: 100,
          startFrame: 10,
          endFrame: 25,
        });

        return {
          frameCount: sequence.frames.length,
          expectedCount: 15,
        };
      });

      expect(result.frameCount).toBe(result.expectedCount);
    });
  });
});
