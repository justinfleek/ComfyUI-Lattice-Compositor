/**
 * Pose Export Browser Tests
 * 
 * Tests for browser-only pose rendering:
 * - renderPoseFrame: Renders OpenPose skeleton to canvas
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor, createTestComposition } from "../helpers/compositor";

test.describe("Pose Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("renderPoseFrame", () => {
    test("should render pose keypoints to canvas", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderPoseFrame } = await import(
          "/src/services/export/poseExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 512;
        canvas.height = 512;

        const pose = {
          keypoints: [
            { x: 256, y: 100, confidence: 1.0, name: "nose" },
            { x: 200, y: 200, confidence: 0.9, name: "left_shoulder" },
            { x: 312, y: 200, confidence: 0.9, name: "right_shoulder" },
            { x: 180, y: 350, confidence: 0.8, name: "left_hip" },
            { x: 332, y: 350, confidence: 0.8, name: "right_hip" },
          ],
          bones: [
            { start: "left_shoulder", end: "right_shoulder" },
            { start: "left_shoulder", end: "left_hip" },
            { start: "right_shoulder", end: "right_hip" },
          ],
        };

        renderPoseFrame(canvas, pose, {
          pointRadius: 5,
          boneWidth: 3,
          colorScheme: "openpose",
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(0, 0, 512, 512);
        
        // Check that something was drawn (not all black)
        let hasContent = false;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 0 || imageData.data[i + 1] > 0 || imageData.data[i + 2] > 0) {
            hasContent = true;
            break;
          }
        }

        return { hasContent, width: canvas.width, height: canvas.height };
      });

      expect(result.hasContent).toBe(true);
      expect(result.width).toBe(512);
      expect(result.height).toBe(512);
    });

    test("should render with custom colors", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderPoseFrame } = await import(
          "/src/services/export/poseExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        const pose = {
          keypoints: [{ x: 50, y: 50, confidence: 1.0, name: "center" }],
          bones: [],
        };

        renderPoseFrame(canvas, pose, {
          pointRadius: 10,
          pointColor: "#FF0000", // Red
          colorScheme: "custom",
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(45, 45, 10, 10);
        
        // Check for red pixels
        let hasRed = false;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 200 && imageData.data[i + 1] < 50) {
            hasRed = true;
            break;
          }
        }

        return { hasRed };
      });

      expect(result.hasRed).toBe(true);
    });

    test("should skip low confidence keypoints", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderPoseFrame } = await import(
          "/src/services/export/poseExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        const pose = {
          keypoints: [
            { x: 50, y: 50, confidence: 0.1, name: "low_conf" }, // Below threshold
          ],
          bones: [],
        };

        renderPoseFrame(canvas, pose, {
          pointRadius: 20,
          confidenceThreshold: 0.5,
        });

        const ctx = canvas.getContext("2d");
        const imageData = ctx!.getImageData(0, 0, 100, 100);
        
        // Should be all black (nothing drawn)
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

    test("should render bones between keypoints", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderPoseFrame } = await import(
          "/src/services/export/poseExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        const pose = {
          keypoints: [
            { x: 10, y: 50, confidence: 1.0, name: "left" },
            { x: 90, y: 50, confidence: 1.0, name: "right" },
          ],
          bones: [{ start: "left", end: "right" }],
        };

        renderPoseFrame(canvas, pose, {
          pointRadius: 3,
          boneWidth: 5,
        });

        const ctx = canvas.getContext("2d");
        // Check middle of bone (x=50, y=50)
        const imageData = ctx!.getImageData(48, 48, 4, 4);
        
        let hasBone = false;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 0 || imageData.data[i + 1] > 0 || imageData.data[i + 2] > 0) {
            hasBone = true;
            break;
          }
        }

        return { hasBone };
      });

      expect(result.hasBone).toBe(true);
    });

    test("should handle empty pose gracefully", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { renderPoseFrame } = await import(
          "/src/services/export/poseExport"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;

        const pose = { keypoints: [], bones: [] };

        // Should not throw
        try {
          renderPoseFrame(canvas, pose, {});
          return { success: true };
        } catch (e) {
          return { success: false, error: String(e) };
        }
      });

      expect(result.success).toBe(true);
    });
  });
});
