/**
 * Wan-Move Export Browser Tests
 * 
 * Tests for browser-only trajectory rendering:
 * - renderTrajectoryFrame: Renders single frame to canvas
 * - renderTrajectorySequence: Renders all frames
 * - exportWanMovePackage: Full export with OffscreenCanvas
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Wan-Move Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("renderTrajectoryFrame", () => {
    test("should render trajectory points on canvas", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectoryFrame, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 512;
        canvas.height = 512;

        const trajectory = generateFromPreset("neural-flow", 50, 10, 512, 512, 12345);
        
        renderTrajectoryFrame(canvas, trajectory, 5, {
          pointSize: 3,
          trailLength: 5,
          trailOpacity: 0.5,
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(0, 0, 512, 512);
        
        // Count non-black pixels
        let nonBlackPixels = 0;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 0 || imageData.data[i + 1] > 0 || imageData.data[i + 2] > 0) {
            nonBlackPixels++;
          }
        }

        return { nonBlackPixels, hasContent: nonBlackPixels > 0 };
      });

      expect(result.hasContent).toBe(true);
      expect(result.nonBlackPixels).toBeGreaterThan(10); // Should have visible points
    });

    test("should render trails for moving points", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectoryFrame } = await import(
          "/src/services/export/wanMoveExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        // Create trajectory with clear movement
        const trajectory = {
          tracks: [
            [[10, 50], [30, 50], [50, 50], [70, 50], [90, 50]], // Point moving right
          ],
          visibility: [[true, true, true, true, true]],
          metadata: { numPoints: 1, numFrames: 5, width: 100, height: 100 },
        };

        renderTrajectoryFrame(canvas, trajectory, 4, {
          pointSize: 5,
          trailLength: 4,
          trailOpacity: 0.8,
        });

        const ctx = canvas.getContext("2d");
        
        // Check for trail at previous positions
        const checkPixel = (x: number, y: number) => {
          const data = ctx!.getImageData(x, y, 1, 1).data;
          return data[0] > 0 || data[1] > 0 || data[2] > 0;
        };

        return {
          hasCurrentPoint: checkPixel(90, 50),
          hasTrail1: checkPixel(70, 50),
          hasTrail2: checkPixel(50, 50),
        };
      });

      expect(result.hasCurrentPoint).toBe(true);
      expect(result.hasTrail1).toBe(true);
    });

    test("should respect visibility mask", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectoryFrame } = await import(
          "/src/services/export/wanMoveExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        const trajectory = {
          tracks: [
            [[50, 50], [50, 50], [50, 50]],
          ],
          visibility: [[true, false, true]], // Invisible at frame 1
          metadata: { numPoints: 1, numFrames: 3, width: 100, height: 100 },
        };

        // Render invisible frame
        renderTrajectoryFrame(canvas, trajectory, 1, {
          pointSize: 20,
          trailLength: 0,
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(40, 40, 20, 20);
        
        let isEmpty = true;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 0 || imageData.data[i + 1] > 0 || imageData.data[i + 2] > 0) {
            isEmpty = false;
            break;
          }
        }

        return { isEmpty };
      });

      expect(result.isEmpty).toBe(true);
    });

    test("should handle colored trajectories", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectoryFrame, addColorToTrajectory, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 256;
        canvas.height = 256;

        let trajectory = generateFromPreset("neural-flow", 20, 5, 256, 256, 12345);
        trajectory = addColorToTrajectory(trajectory, "plasma");

        renderTrajectoryFrame(canvas, trajectory, 2, {
          pointSize: 10,
          useColors: true,
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(0, 0, 256, 256);
        
        // Check for non-grayscale pixels (colored)
        let hasColor = false;
        for (let i = 0; i < imageData.data.length; i += 4) {
          const r = imageData.data[i];
          const g = imageData.data[i + 1];
          const b = imageData.data[i + 2];
          if (r > 0 && (r !== g || g !== b)) {
            hasColor = true;
            break;
          }
        }

        return { hasColor };
      });

      expect(result.hasColor).toBe(true);
    });
  });

  test.describe("renderTrajectorySequence", () => {
    test("should render all frames in sequence", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectorySequence, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const trajectory = generateFromPreset("neural-flow", 10, 5, 128, 128, 12345);
        
        const frames = await renderTrajectorySequence(trajectory, {
          width: 128,
          height: 128,
          pointSize: 3,
        });

        return {
          frameCount: frames.length,
          firstFrameWidth: frames[0]?.width,
          firstFrameHeight: frames[0]?.height,
        };
      });

      expect(result.frameCount).toBe(5);
      expect(result.firstFrameWidth).toBe(128);
      expect(result.firstFrameHeight).toBe(128);
    });

    test("should produce unique frames for animated trajectories", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderTrajectorySequence, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const trajectory = generateFromPreset("cosmic-spiral", 5, 10, 64, 64, 12345);
        
        const frames = await renderTrajectorySequence(trajectory, {
          width: 64,
          height: 64,
          pointSize: 5,
        });

        // Compare first and last frame
        const getPixelSum = (imageData: ImageData) => {
          let sum = 0;
          for (let i = 0; i < imageData.data.length; i += 4) {
            sum += imageData.data[i] + imageData.data[i + 1] + imageData.data[i + 2];
          }
          return sum;
        };

        const ctx1 = frames[0].getContext("2d");
        const ctx2 = frames[frames.length - 1].getContext("2d");
        
        const data1 = ctx1!.getImageData(0, 0, 64, 64);
        const data2 = ctx2!.getImageData(0, 0, 64, 64);

        const sum1 = getPixelSum(data1);
        const sum2 = getPixelSum(data2);

        return { areDifferent: sum1 !== sum2, sum1, sum2 };
      });

      expect(result.areDifferent).toBe(true);
    });
  });

  test.describe("exportWanMovePackage", () => {
    test("should export complete package with frames and JSON", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportWanMovePackage, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const trajectory = generateFromPreset("neural-flow", 5, 3, 128, 128, 12345);
        
        const pkg = await exportWanMovePackage(trajectory, {
          width: 128,
          height: 128,
          format: "png",
        });

        return {
          hasFrames: pkg.frames.length > 0,
          hasJson: typeof pkg.trajectoryJson === "string",
          hasMetadata: !!pkg.metadata,
          frameCount: pkg.frames.length,
        };
      });

      expect(result.hasFrames).toBe(true);
      expect(result.hasJson).toBe(true);
      expect(result.hasMetadata).toBe(true);
      expect(result.frameCount).toBe(3);
    });

    test("should include valid JSON trajectory data", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportWanMovePackage, generateFromPreset } = await import(
          "/src/services/export/wanMoveExport"
        );

        const trajectory = generateFromPreset("singularity", 10, 5, 256, 256, 99999);
        
        const pkg = await exportWanMovePackage(trajectory, {
          width: 256,
          height: 256,
        });

        const parsed = JSON.parse(pkg.trajectoryJson);

        return {
          hasTracks: Array.isArray(parsed.tracks),
          hasVisibility: Array.isArray(parsed.visibility),
          numPoints: parsed.metadata?.numPoints,
          numFrames: parsed.metadata?.numFrames,
        };
      });

      expect(result.hasTracks).toBe(true);
      expect(result.hasVisibility).toBe(true);
      expect(result.numPoints).toBe(10);
      expect(result.numFrames).toBe(5);
    });

    test("should support different output formats", async ({ page }) => {
      const formats = ["png", "jpeg", "webp"];

      for (const format of formats) {
        const result = await page.evaluate(async (fmt) => {
          const { exportWanMovePackage, generateFromPreset } = await import(
            "/src/services/export/wanMoveExport"
          );

          const trajectory = generateFromPreset("neural-flow", 3, 2, 64, 64, 12345);
          
          const pkg = await exportWanMovePackage(trajectory, {
            width: 64,
            height: 64,
            format: fmt as "png" | "jpeg" | "webp",
          });

          return {
            format: fmt,
            hasFrames: pkg.frames.length > 0,
            frameType: pkg.frames[0] instanceof Blob ? "blob" : typeof pkg.frames[0],
          };
        }, format);

        expect(result.hasFrames).toBe(true);
      }
    });
  });
});
