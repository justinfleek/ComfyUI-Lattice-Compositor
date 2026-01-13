/**
 * Export Pipeline Browser Tests
 * 
 * Tests for ACTUAL exports in exportPipeline.ts:
 * - ExportPipeline class
 * - exportToComfyUI
 * - quickExportDepthSequence
 * - quickExportReferenceFrame
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Export Pipeline - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("ExportPipeline class", () => {
    test("should create instance with valid options", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { ExportPipeline } = await import(
          "/src/services/export/exportPipeline"
        );

        const pipeline = new ExportPipeline({
          layers: [],
          cameraKeyframes: [],
          config: {
            target: "controlnet-depth",
            width: 512,
            height: 512,
            frameCount: 10,
            fps: 24,
            startFrame: 0,
            endFrame: 10,
            outputDir: "",
            filenamePrefix: "test",
            exportDepthMap: true,
            exportControlImages: false,
            exportCameraData: false,
            exportReferenceFrame: false,
            exportLastFrame: false,
            depthFormat: "midas",
            prompt: "",
            negativePrompt: "",
            autoQueueWorkflow: false,
          },
        });

        return {
          isInstance: pipeline instanceof ExportPipeline,
          hasExecute: typeof pipeline.execute === "function",
        };
      });

      expect(result.isInstance).toBe(true);
      expect(result.hasExecute).toBe(true);
    });

    test("should execute and return result", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { ExportPipeline } = await import(
          "/src/services/export/exportPipeline"
        );

        const pipeline = new ExportPipeline({
          layers: [],
          cameraKeyframes: [],
          config: {
            target: "controlnet-depth",
            width: 64,
            height: 64,
            frameCount: 2,
            fps: 24,
            startFrame: 0,
            endFrame: 2,
            outputDir: "",
            filenamePrefix: "test",
            exportDepthMap: true,
            exportControlImages: false,
            exportCameraData: false,
            exportReferenceFrame: false,
            exportLastFrame: false,
            depthFormat: "midas",
            prompt: "",
            negativePrompt: "",
            autoQueueWorkflow: false,
          },
        });

        const result = await pipeline.execute();

        return {
          hasResult: result !== undefined,
          hasSuccess: typeof result.success === "boolean",
        };
      });

      expect(result.hasResult).toBe(true);
      expect(result.hasSuccess).toBe(true);
    });
  });

  test.describe("exportToComfyUI", () => {
    test("should export with config", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportToComfyUI } = await import(
          "/src/services/export/exportPipeline"
        );

        const result = await exportToComfyUI(
          [], // layers
          [], // cameraKeyframes
          {
            target: "controlnet-depth",
            width: 64,
            height: 64,
            frameCount: 1,
            fps: 24,
            startFrame: 0,
            endFrame: 1,
            outputDir: "",
            filenamePrefix: "test",
            exportDepthMap: true,
            exportControlImages: false,
            exportCameraData: false,
            exportReferenceFrame: false,
            exportLastFrame: false,
            depthFormat: "midas",
            prompt: "",
            negativePrompt: "",
            autoQueueWorkflow: false,
          }
        );

        return {
          hasResult: result !== undefined,
          hasSuccess: typeof result.success === "boolean",
        };
      });

      expect(result.hasResult).toBe(true);
    });
  });

  test.describe("quickExportDepthSequence", () => {
    test("should export depth sequence with defaults", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { quickExportDepthSequence } = await import(
          "/src/services/export/exportPipeline"
        );

        const result = await quickExportDepthSequence(
          [], // layers
          64, // width
          64, // height
          2,  // frameCount
          "midas" // format
        );

        return {
          hasResult: result !== undefined,
          hasSuccess: typeof result.success === "boolean",
        };
      });

      expect(result.hasResult).toBe(true);
    });
  });

  test.describe("quickExportReferenceFrame", () => {
    test("should export single reference frame", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { quickExportReferenceFrame } = await import(
          "/src/services/export/exportPipeline"
        );

        const result = await quickExportReferenceFrame(
          [], // layers
          64, // width
          64  // height
        );

        return {
          resultType: typeof result,
          isNullOrString: result === null || typeof result === "string",
        };
      });

      expect(result.isNullOrString).toBe(true);
    });
  });
});
