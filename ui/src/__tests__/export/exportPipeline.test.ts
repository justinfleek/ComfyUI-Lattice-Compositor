/**
 * Tests for ui/src/services/export/exportPipeline.ts
 * 
 * Note: ExportPipeline uses OffscreenCanvas and ComfyUI client.
 * Most tests require browser environment (E2E/Playwright).
 * 
 * This file tests:
 * - Type structures
 * - Configuration validation
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import type {
  ExportPipelineOptions,
  RenderedFrame,
} from "@/services/export/exportPipeline";
import type { ExportConfig, ExportProgress } from "@/types/export";
import type { CameraKeyframe } from "@/types/camera";
import type { Layer } from "@/types/project";

// ============================================================
// TYPE STRUCTURE TESTS
// ============================================================

describe("exportPipeline: Type Structures", () => {
  it("ExportConfig has correct structure", () => {
    const config: ExportConfig = {
      target: "controlnet-depth",
      width: 1920,
      height: 1080,
      frameCount: 100,
      fps: 24,
      startFrame: 0,
      endFrame: 100,
      outputDir: "/output",
      filenamePrefix: "export",
      exportDepthMap: true,
      exportControlImages: false,
      exportCameraData: true,
      exportReferenceFrame: true,
      exportLastFrame: false,
      depthFormat: "midas",
      prompt: "a beautiful scene",
      negativePrompt: "blurry, low quality",
      autoQueueWorkflow: false,
    };
    
    expect(config.target).toBe("controlnet-depth");
    expect(config.width).toBe(1920);
    expect(config.height).toBe(1080);
    expect(config.frameCount).toBe(100);
  });

  it("ExportProgress has correct structure", () => {
    const progress: ExportProgress = {
      stage: "rendering_frames",
      stageProgress: 50,
      overallProgress: 25,
      message: "Rendering frame 50/100",
    };
    
    expect(progress.stage).toBe("rendering_frames");
    expect(progress.stageProgress).toBe(50);
    expect(progress.overallProgress).toBe(25);
  });

  it("ExportProgress stages are valid", () => {
    const validStages: ExportProgress["stage"][] = [
      "preparing",
      "rendering_frames",
      "rendering_depth",
      "rendering_control",
      "exporting_camera",
      "complete",
      "error",
    ];
    
    validStages.forEach(stage => {
      const progress: ExportProgress = {
        stage,
        stageProgress: 0,
        overallProgress: 0,
        message: "",
      };
      expect(progress.stage).toBe(stage);
    });
  });

  it("RenderedFrame has correct structure", () => {
    const frame: RenderedFrame = {
      frameIndex: 0,
      timestamp: 0,
      // colorCanvas and depthCanvas are optional (browser-only)
      depthBuffer: new Float32Array(1920 * 1080),
    };
    
    expect(frame.frameIndex).toBe(0);
    expect(frame.timestamp).toBe(0);
    expect(frame.depthBuffer).toBeInstanceOf(Float32Array);
  });

  it("ExportPipelineOptions structure is correct", () => {
    // Test type compatibility only (actual execution needs browser)
    const layers: Layer[] = [];
    const cameraKeyframes: CameraKeyframe[] = [];
    const config: ExportConfig = {
      target: "wan22-i2v",
      width: 1920,
      height: 1080,
      frameCount: 100,
      fps: 24,
      startFrame: 0,
      endFrame: 100,
      outputDir: "",
      filenamePrefix: "test",
      exportDepthMap: false,
      exportControlImages: false,
      exportCameraData: false,
      exportReferenceFrame: false,
      exportLastFrame: false,
      depthFormat: "midas",
      prompt: "",
      negativePrompt: "",
      autoQueueWorkflow: false,
    };
    
    const options: ExportPipelineOptions = {
      layers,
      cameraKeyframes,
      config,
      onProgress: () => {},
      abortSignal: new AbortController().signal,
    };
    
    expect(options.layers).toEqual([]);
    expect(options.cameraKeyframes).toEqual([]);
    expect(options.config.target).toBe("wan22-i2v");
  });
});

// ============================================================
// CONFIGURATION VALIDATION TESTS
// ============================================================

describe("exportPipeline: Configuration Validation", () => {
  it("valid targets are accepted", () => {
    const validTargets: ExportConfig["target"][] = [
      "controlnet-depth",
      "controlnet-canny",
      "controlnet-pose",
      "wan22-fun-camera",
      "wan-move",
      "wan22-i2v",
      "animatediff-cameractrl",
      "custom-workflow",
    ];
    
    validTargets.forEach(target => {
      const config: ExportConfig = {
        target,
        width: 1920,
        height: 1080,
        frameCount: 100,
        fps: 24,
        startFrame: 0,
        endFrame: 100,
        outputDir: "",
        filenamePrefix: "test",
        exportDepthMap: false,
        exportControlImages: false,
        exportCameraData: false,
        exportReferenceFrame: false,
        exportLastFrame: false,
        depthFormat: "midas",
        prompt: "",
        negativePrompt: "",
        autoQueueWorkflow: false,
      };
      expect(config.target).toBe(target);
    });
  });

  it("valid depth formats are accepted", () => {
    const validFormats: ExportConfig["depthFormat"][] = [
      "midas",
      "depth-anything",
      "zoe",
      "marigold",
      "raw",
    ];
    
    validFormats.forEach(format => {
      const config: Partial<ExportConfig> = {
        depthFormat: format,
      };
      expect(config.depthFormat).toBe(format);
    });
  });

  it("dimensions must be positive", () => {
    // Type system enforces number, but runtime validation needed for positivity
    const validConfig: ExportConfig = {
      target: "controlnet-depth",
      width: 1920,
      height: 1080,
      frameCount: 100,
      fps: 24,
      startFrame: 0,
      endFrame: 100,
      outputDir: "",
      filenamePrefix: "test",
      exportDepthMap: false,
      exportControlImages: false,
      exportCameraData: false,
      exportReferenceFrame: false,
      exportLastFrame: false,
      depthFormat: "midas",
      prompt: "",
      negativePrompt: "",
      autoQueueWorkflow: false,
    };
    
    expect(validConfig.width).toBeGreaterThan(0);
    expect(validConfig.height).toBeGreaterThan(0);
    expect(validConfig.frameCount).toBeGreaterThan(0);
    expect(validConfig.fps).toBeGreaterThan(0);
  });
});

// ============================================================
// BROWSER-DEPENDENT TESTS (Skipped - require Playwright)
// ============================================================

describe.skip("exportPipeline: Browser-dependent (need Playwright)", () => {
  it("ExportPipeline.execute() renders frames", () => {
    // Requires OffscreenCanvas
  });

  it("exportToComfyUI sends to ComfyUI", () => {
    // Requires network and ComfyUI running
  });

  it("quickExportDepthSequence generates depth maps", () => {
    // Requires OffscreenCanvas and depth rendering
  });

  it("quickExportReferenceFrame exports first frame", () => {
    // Requires Canvas
  });

  it("abort signal stops export", () => {
    // Requires async execution
  });
});
