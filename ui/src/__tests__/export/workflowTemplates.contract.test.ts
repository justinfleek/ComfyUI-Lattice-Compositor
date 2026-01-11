/**
 * Workflow Templates Contract Tests
 *
 * CRITICAL: These tests verify that generated ComfyUI workflows match the
 * exact requirements of target AI models. Failing tests indicate exports
 * that will cause model failures.
 *
 * Evidence Sources:
 * - SCAIL paper (arXiv:2512.05905): "with 2× downsampling the pose following ability is nearly unaffected"
 * - Kijai WanVideoWrapper: https://github.com/kijai/ComfyUI-WanVideoWrapper
 * - Official SCAIL repo: https://github.com/zai-org/SCAIL
 *
 * @audit P0 CRITICAL - Export workflow compliance
 */

import { describe, it, expect, beforeEach } from "vitest";

import {
  generateSCAILWorkflow,
  generateTTMWorkflow,
  generateUni3CWorkflow,
  generateLightXWorkflow,
  generateWanMoveWorkflow,
  generateATIWorkflow,
  generateCameraComfyUIWorkflow,
  generateControlNetWorkflow,
  generateWorkflowForTarget,
  validateWorkflow,
  type WorkflowParams,
} from "@/services/comfyui/workflowTemplates";
import type { ExportTarget } from "@/types/export";

// ============================================================================
// Test Fixtures
// ============================================================================

function createValidParams(overrides: Partial<WorkflowParams> = {}): WorkflowParams {
  return {
    prompt: "test prompt",
    negativePrompt: "bad quality",
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 16,
    referenceImage: "test.png",
    seed: 12345,
    steps: 30,
    cfgScale: 5,
    ...overrides,
  };
}

// ============================================================================
// 1. SCAIL WORKFLOW CONTRACT TESTS
// ============================================================================

describe("SCAIL Workflow Contract Tests", () => {
  /**
   * SCAIL Requirements (from paper arXiv:2512.05905):
   * - Pose resolution: EXACTLY HALF of generation resolution
   * - "with 2× downsampling the pose following ability is nearly unaffected"
   * - Dimensions must be divisible by 32
   * - Uses WanVideoAddSCAILReferenceEmbeds and WanVideoAddSCAILPoseEmbeds nodes
   */

  describe("SCAIL is a valid export target", () => {
    it("should generate workflow for 'scail' target", () => {
      const params = createValidParams({
        scailReferenceImage: "reference.png",
        scailPoseVideo: "pose.mp4",
      });

      const workflow = generateWorkflowForTarget("scail", params);

      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });

    it("should generate valid workflow structure", () => {
      const params = createValidParams({
        scailReferenceImage: "reference.png",
        scailPoseVideo: "pose.mp4",
      });

      const workflow = generateWorkflowForTarget("scail", params);
      const validation = validateWorkflow(workflow);

      expect(validation.valid).toBe(true);
      expect(validation.errors).toHaveLength(0);
    });
  });

  describe("SCAIL pose resolution - HALF of generation resolution", () => {
    /**
     * CRITICAL CONTRACT:
     * Pose images MUST be exactly half the generation resolution.
     * From SCAIL paper: "with 2× downsampling the pose following ability is nearly unaffected"
     */

    const resolutionCases = [
      { gen: { w: 832, h: 480 }, pose: { w: 416, h: 240 } },
      { gen: { w: 1280, h: 720 }, pose: { w: 640, h: 360 } },
      { gen: { w: 512, h: 512 }, pose: { w: 256, h: 256 } },
      { gen: { w: 768, h: 1024 }, pose: { w: 384, h: 512 } },
    ];

    it.each(resolutionCases)(
      "should resize pose from $gen.wx$gen.h to $pose.wx$pose.h (half resolution)",
      ({ gen, pose }) => {
        const params = createValidParams({
          width: gen.w,
          height: gen.h,
          scailPoseVideo: "pose.mp4",
        });

        const workflow = generateSCAILWorkflow(params);

        // Find the ImageResize node that resizes pose (not reference)
        const nodes = Object.entries(workflow);
        const resizeNodes = nodes.filter(
          ([_, node]) => node.class_type === "ImageResize",
        );

        // There should be exactly 2 resize nodes: one for reference (gen res), one for pose (half res)
        expect(resizeNodes.length).toBe(2);

        // Find the pose resize node (the one with half resolution)
        const poseResizeNode = resizeNodes.find(
          ([_, node]) =>
            node.inputs.width === pose.w && node.inputs.height === pose.h,
        );

        expect(poseResizeNode).toBeDefined();
        expect(poseResizeNode![1].inputs.width).toBe(pose.w);
        expect(poseResizeNode![1].inputs.height).toBe(pose.h);
      },
    );

    it("should resize reference to generation resolution", () => {
      const params = createValidParams({
        width: 832,
        height: 480,
        scailReferenceImage: "ref.png",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      // Find reference resize node (should be gen resolution)
      const refResizeNode = nodes.find(
        (node) =>
          node.class_type === "ImageResize" &&
          node.inputs.width === 832 &&
          node.inputs.height === 480,
      );

      expect(refResizeNode).toBeDefined();
    });
  });

  describe("SCAIL required WanVideoWrapper nodes", () => {
    /**
     * SCAIL uses specific WanVideoWrapper nodes:
     * - WanVideoAddSCAILReferenceEmbeds: Encodes identity from reference image
     * - WanVideoAddSCAILPoseEmbeds: Encodes motion from pose video
     */

    it("should include WanVideoAddSCAILReferenceEmbeds node", () => {
      const params = createValidParams({
        scailReferenceImage: "ref.png",
        scailPoseVideo: "pose.mp4",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const refEmbedsNode = nodes.find(
        (node) => node.class_type === "WanVideoAddSCAILReferenceEmbeds",
      );

      expect(refEmbedsNode).toBeDefined();
      expect(refEmbedsNode!.inputs).toHaveProperty("wan_model");
      expect(refEmbedsNode!.inputs).toHaveProperty("reference_image");
      expect(refEmbedsNode!.inputs).toHaveProperty("strength");
    });

    it("should include WanVideoAddSCAILPoseEmbeds node", () => {
      const params = createValidParams({
        scailReferenceImage: "ref.png",
        scailPoseVideo: "pose.mp4",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const poseEmbedsNode = nodes.find(
        (node) => node.class_type === "WanVideoAddSCAILPoseEmbeds",
      );

      expect(poseEmbedsNode).toBeDefined();
      expect(poseEmbedsNode!.inputs).toHaveProperty("wan_model");
      expect(poseEmbedsNode!.inputs).toHaveProperty("pose_images");
      expect(poseEmbedsNode!.inputs).toHaveProperty("strength");
    });

    it("should chain SCAIL nodes correctly: Reference → Pose → I2V", () => {
      const params = createValidParams({
        scailReferenceImage: "ref.png",
        scailPoseVideo: "pose.mp4",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.entries(workflow);

      // Find node IDs
      const refEmbedsEntry = nodes.find(
        ([_, node]) => node.class_type === "WanVideoAddSCAILReferenceEmbeds",
      );
      const poseEmbedsEntry = nodes.find(
        ([_, node]) => node.class_type === "WanVideoAddSCAILPoseEmbeds",
      );
      const i2vEntry = nodes.find(
        ([_, node]) => node.class_type === "WanImageToVideo",
      );

      expect(refEmbedsEntry).toBeDefined();
      expect(poseEmbedsEntry).toBeDefined();
      expect(i2vEntry).toBeDefined();

      const [refEmbedsId] = refEmbedsEntry!;
      const [poseEmbedsId, poseEmbedsNode] = poseEmbedsEntry!;
      const [_, i2vNode] = i2vEntry!;

      // Pose embeds should reference RefEmbeds output
      expect(poseEmbedsNode.inputs.wan_model[0]).toBe(refEmbedsId);

      // I2V should reference PoseEmbeds output
      expect(i2vNode.inputs.wan_model[0]).toBe(poseEmbedsId);
    });
  });

  describe("SCAIL divisibility by 32 validation", () => {
    /**
     * From SCAIL docs: "H and W should be both divisible by 32"
     */

    it("should warn when generation resolution is not divisible by 32", () => {
      const consoleSpy = vi.spyOn(console, "warn").mockImplementation(() => {});

      const params = createValidParams({
        width: 830, // Not divisible by 32
        height: 479, // Not divisible by 32
      });

      generateSCAILWorkflow(params);

      expect(consoleSpy).toHaveBeenCalledWith(
        expect.stringContaining("should be divisible by 32"),
      );

      consoleSpy.mockRestore();
    });

    it("should not warn when generation resolution is divisible by 32", () => {
      const consoleSpy = vi.spyOn(console, "warn").mockImplementation(() => {});

      const params = createValidParams({
        width: 832, // Divisible by 32
        height: 480, // Divisible by 32
      });

      generateSCAILWorkflow(params);

      // Should not have warned about divisibility
      const div32Warning = consoleSpy.mock.calls.some(
        (call) => call[0]?.includes?.("divisible by 32"),
      );
      expect(div32Warning).toBe(false);

      consoleSpy.mockRestore();
    });
  });

  describe("SCAIL input handling", () => {
    it("should handle pose video input", () => {
      const params = createValidParams({
        scailPoseVideo: "custom_pose.mp4",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const loadVideoNode = nodes.find(
        (node) => node.class_type === "VHS_LoadVideo",
      );

      expect(loadVideoNode).toBeDefined();
      expect(loadVideoNode!.inputs.video).toBe("custom_pose.mp4");
    });

    it("should handle pose directory input", () => {
      const params = createValidParams({
        scailPoseDirectory: "/path/to/pose/frames",
        scailPoseVideo: undefined,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const loadImagesNode = nodes.find(
        (node) => node.class_type === "VHS_LoadImages",
      );

      expect(loadImagesNode).toBeDefined();
      expect(loadImagesNode!.inputs.directory).toBe("/path/to/pose/frames");
    });

    it("should use custom reference image", () => {
      const params = createValidParams({
        scailReferenceImage: "custom_ref.png",
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const loadImageNode = nodes.find(
        (node) =>
          node.class_type === "LoadImage" &&
          node.inputs.image === "custom_ref.png",
      );

      expect(loadImageNode).toBeDefined();
    });

    it("should fall back to referenceImage when scailReferenceImage not provided", () => {
      const params = createValidParams({
        referenceImage: "fallback_ref.png",
        scailReferenceImage: undefined,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const loadImageNode = nodes.find(
        (node) =>
          node.class_type === "LoadImage" &&
          node.inputs.image === "fallback_ref.png",
      );

      expect(loadImageNode).toBeDefined();
    });
  });

  describe("SCAIL generation parameters", () => {
    it("should use specified frame count", () => {
      const params = createValidParams({
        frameCount: 81,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const i2vNode = nodes.find(
        (node) => node.class_type === "WanImageToVideo",
      );

      expect(i2vNode).toBeDefined();
      expect(i2vNode!.inputs.length).toBe(81);
    });

    it("should use specified dimensions for generation", () => {
      const params = createValidParams({
        width: 1280,
        height: 720,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const i2vNode = nodes.find(
        (node) => node.class_type === "WanImageToVideo",
      );

      expect(i2vNode).toBeDefined();
      expect(i2vNode!.inputs.width).toBe(1280);
      expect(i2vNode!.inputs.height).toBe(720);
    });

    it("should use specified steps", () => {
      const params = createValidParams({
        steps: 50,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const i2vNode = nodes.find(
        (node) => node.class_type === "WanImageToVideo",
      );

      expect(i2vNode).toBeDefined();
      expect(i2vNode!.inputs.steps).toBe(50);
    });

    it("should use specified CFG scale", () => {
      const params = createValidParams({
        cfgScale: 7.5,
      });

      const workflow = generateSCAILWorkflow(params);
      const nodes = Object.values(workflow);

      const i2vNode = nodes.find(
        (node) => node.class_type === "WanImageToVideo",
      );

      expect(i2vNode).toBeDefined();
      expect(i2vNode!.inputs.cfg).toBe(7.5);
    });
  });
});

// ============================================================================
// 2. TTM WORKFLOW CONTRACT TESTS
// ============================================================================

describe("TTM Workflow Contract Tests", () => {
  /**
   * TTM (Time-to-Move) Requirements:
   * - Uses TTM_TrajectoryFromPoints for trajectory encoding
   * - Uses TTM_CombineLayers for multi-layer motion
   * - Requires ttmLayers or ttmCombinedMask
   */

  it("should create trajectory nodes for each layer", () => {
    const params = createValidParams({
      ttmLayers: [
        {
          layerId: "1",
          layerName: "Test",
          motionMask: "mask.png",
          trajectory: [
            { frame: 0, x: 100, y: 100 },
            { frame: 50, x: 200, y: 200 },
          ],
        },
      ],
    });

    const workflow = generateTTMWorkflow(params);
    const nodes = Object.values(workflow);

    const trajNode = nodes.find(
      (node) => node.class_type === "TTM_TrajectoryFromPoints",
    );

    expect(trajNode).toBeDefined();
  });

  it("should combine layers when multiple layers provided", () => {
    const params = createValidParams({
      ttmLayers: [
        { layerId: "1", layerName: "Layer1", motionMask: "mask1.png", trajectory: [] },
        { layerId: "2", layerName: "Layer2", motionMask: "mask2.png", trajectory: [] },
      ],
    });

    const workflow = generateTTMWorkflow(params);
    const nodes = Object.values(workflow);

    const combineNode = nodes.find(
      (node) => node.class_type === "TTM_CombineLayers",
    );

    expect(combineNode).toBeDefined();
  });

  it("should accept ttmCombinedMask", () => {
    const params = createValidParams({
      ttmCombinedMask: "combined_mask.png",
    });

    expect(() => generateTTMWorkflow(params)).not.toThrow();
  });
});

// ============================================================================
// 3. UNI3C WORKFLOW CONTRACT TESTS
// ============================================================================

describe("Uni3C Workflow Contract Tests", () => {
  /**
   * Uni3C Requirements:
   * - Uses DownloadAndLoadUni3CModel for model loading
   * - Uses Uni3CPresetTrajectory or Uni3CCustomTrajectory for camera path
   * - Requires camera data for custom trajectories
   */

  it("should include Uni3C model loader", () => {
    const params = createValidParams({
      cameraData: { matrices: [] },
    }) as WorkflowParams;

    const workflow = generateUni3CWorkflow(params);
    const nodes = Object.values(workflow);

    const uni3cLoader = nodes.find(
      (node) => node.class_type === "DownloadAndLoadUni3CModel",
    );

    expect(uni3cLoader).toBeDefined();
  });

  it("should use preset trajectory by default", () => {
    const params = createValidParams({}) as WorkflowParams;

    const workflow = generateUni3CWorkflow(params);
    const nodes = Object.values(workflow);

    const presetTrajNode = nodes.find(
      (node) => node.class_type === "Uni3CPresetTrajectory",
    );

    expect(presetTrajNode).toBeDefined();
  });

  it("should use custom trajectory when cameraData.trajectory is provided", () => {
    const params = createValidParams({
      trajType: "custom",
      cameraData: { trajectory: [{ x: 0, y: 0 }] },
    }) as WorkflowParams;

    const workflow = generateUni3CWorkflow(params);
    const nodes = Object.values(workflow);

    const customTrajNode = nodes.find(
      (node) => node.class_type === "Uni3CCustomTrajectory",
    );

    expect(customTrajNode).toBeDefined();
  });
});

// ============================================================================
// 3.5. LIGHT-X WORKFLOW CONTRACT TESTS
// ============================================================================

describe("Light-X Workflow Contract Tests", () => {
  /**
   * Light-X Requirements:
   * - Uses WanVideoLoraSelect for applying Light-X LoRA
   * - LoRA controls relighting effects in generated video
   */

  it("should include WanVideoLoraSelect node", () => {
    const params = createValidParams({
      loraModel: "light_x_relight.safetensors",
    }) as WorkflowParams;

    const workflow = generateLightXWorkflow(params);
    const nodes = Object.values(workflow);

    const loraNode = nodes.find(
      (node) => node.class_type === "WanVideoLoraSelect",
    );

    expect(loraNode).toBeDefined();
  });

  it("should use specified LoRA model", () => {
    const params = createValidParams({
      loraModel: "custom_light_lora.safetensors",
    }) as WorkflowParams;

    const workflow = generateLightXWorkflow(params);
    const nodes = Object.values(workflow);

    const loraNode = nodes.find(
      (node) => node.class_type === "WanVideoLoraSelect",
    );

    expect(loraNode).toBeDefined();
    expect(loraNode!.inputs.lora).toBe("custom_light_lora.safetensors");
  });

  it("should use default LoRA model when not specified", () => {
    const params = createValidParams({}) as WorkflowParams;

    const workflow = generateLightXWorkflow(params);
    const nodes = Object.values(workflow);

    const loraNode = nodes.find(
      (node) => node.class_type === "WanVideoLoraSelect",
    );

    expect(loraNode).toBeDefined();
    expect(loraNode!.inputs.lora).toBe("light_x_relight.safetensors");
  });

  it("should use specified LoRA strength", () => {
    const params = createValidParams({
      loraStrength: 0.8,
    }) as WorkflowParams;

    const workflow = generateLightXWorkflow(params);
    const nodes = Object.values(workflow);

    const loraNode = nodes.find(
      (node) => node.class_type === "WanVideoLoraSelect",
    );

    expect(loraNode).toBeDefined();
    expect(loraNode!.inputs.strength).toBe(0.8);
  });
});

// ============================================================================
// 3.6. WAN-MOVE WORKFLOW CONTRACT TESTS
// ============================================================================

describe("Wan-Move Workflow Contract Tests", () => {
  /**
   * Wan-Move Requirements:
   * - Uses WanVideoAddWanMoveTracks for point trajectory control
   * - Accepts array of point tracks for motion guidance
   */

  it("should include WanVideoAddWanMoveTracks node", () => {
    const params = createValidParams({
      motionData: { tracks: [] },
    }) as WorkflowParams;

    const workflow = generateWanMoveWorkflow(params);
    const nodes = Object.values(workflow);

    const wanMoveNode = nodes.find(
      (node) => node.class_type === "WanVideoAddWanMoveTracks",
    );

    expect(wanMoveNode).toBeDefined();
  });

  it("should pass tracks data to WanVideoAddWanMoveTracks", () => {
    const testTracks = [[{ x: 100, y: 100 }, { x: 200, y: 200 }]];
    const params = createValidParams({
      motionData: { tracks: testTracks },
    }) as WorkflowParams;

    const workflow = generateWanMoveWorkflow(params);
    const nodes = Object.values(workflow);

    const wanMoveNode = nodes.find(
      (node) => node.class_type === "WanVideoAddWanMoveTracks",
    );

    expect(wanMoveNode).toBeDefined();
    expect(wanMoveNode!.inputs.tracks).toBe(JSON.stringify(testTracks));
  });

  it("should include frame count in WanVideoAddWanMoveTracks", () => {
    const params = createValidParams({
      frameCount: 81,
      motionData: { tracks: [] },
    }) as WorkflowParams;

    const workflow = generateWanMoveWorkflow(params);
    const nodes = Object.values(workflow);

    const wanMoveNode = nodes.find(
      (node) => node.class_type === "WanVideoAddWanMoveTracks",
    );

    expect(wanMoveNode).toBeDefined();
    expect(wanMoveNode!.inputs.num_frames).toBe(81);
  });
});

// ============================================================================
// 3.7. ATI WORKFLOW CONTRACT TESTS
// ============================================================================

describe("ATI Workflow Contract Tests", () => {
  /**
   * ATI (Any Trajectory Instruction) Requirements:
   * - Uses WanVideoATITracks for trajectory-based motion control
   * - Accepts trajectory data for object motion guidance
   */

  it("should include WanVideoATITracks node", () => {
    const params = createValidParams({
      motionData: { trajectories: [] },
    }) as WorkflowParams;

    const workflow = generateATIWorkflow(params);
    const nodes = Object.values(workflow);

    const atiNode = nodes.find(
      (node) => node.class_type === "WanVideoATITracks",
    );

    expect(atiNode).toBeDefined();
  });

  it("should pass trajectory data to WanVideoATITracks", () => {
    const testTrajectories = [{ startPoint: { x: 0, y: 0 }, endPoint: { x: 100, y: 100 } }];
    const params = createValidParams({
      motionData: { trajectories: testTrajectories },
    }) as WorkflowParams;

    const workflow = generateATIWorkflow(params);
    const nodes = Object.values(workflow);

    const atiNode = nodes.find(
      (node) => node.class_type === "WanVideoATITracks",
    );

    expect(atiNode).toBeDefined();
    expect(atiNode!.inputs.trajectories).toBe(JSON.stringify(testTrajectories));
  });

  it("should include dimensions in WanVideoATITracks", () => {
    const params = createValidParams({
      width: 832,
      height: 480,
      motionData: { trajectories: [] },
    }) as WorkflowParams;

    const workflow = generateATIWorkflow(params);
    const nodes = Object.values(workflow);

    const atiNode = nodes.find(
      (node) => node.class_type === "WanVideoATITracks",
    );

    expect(atiNode).toBeDefined();
    expect(atiNode!.inputs.width).toBe(832);
    expect(atiNode!.inputs.height).toBe(480);
  });
});

// ============================================================================
// 3.8. CAMERA-COMFYUI WORKFLOW CONTRACT TESTS
// ============================================================================

describe("Camera-ComfyUI Workflow Contract Tests", () => {
  /**
   * Camera-ComfyUI Requirements:
   * - Uses CameraComfyUI_LoadMatrices for loading 4x4 camera matrices
   * - Uses CameraComfyUI_ApplyCamera for applying camera control
   * - Expects matrices in 4x4 format (16 floats per frame)
   */

  it("should include CameraComfyUI_LoadMatrices node", () => {
    const params = createValidParams({
      cameraData: { matrices: [] },
    }) as WorkflowParams;

    const workflow = generateCameraComfyUIWorkflow(params);
    const nodes = Object.values(workflow);

    const loadMatricesNode = nodes.find(
      (node) => node.class_type === "CameraComfyUI_LoadMatrices",
    );

    expect(loadMatricesNode).toBeDefined();
  });

  it("should include CameraComfyUI_ApplyCamera node", () => {
    const params = createValidParams({
      cameraData: { matrices: [] },
    }) as WorkflowParams;

    const workflow = generateCameraComfyUIWorkflow(params);
    const nodes = Object.values(workflow);

    const applyCameraNode = nodes.find(
      (node) => node.class_type === "CameraComfyUI_ApplyCamera",
    );

    expect(applyCameraNode).toBeDefined();
  });

  it("should pass matrices data to CameraComfyUI_LoadMatrices", () => {
    // Identity matrix (16 floats)
    const testMatrices = [[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]];
    const params = createValidParams({
      cameraData: { matrices: testMatrices },
    }) as WorkflowParams;

    const workflow = generateCameraComfyUIWorkflow(params);
    const nodes = Object.values(workflow);

    const loadMatricesNode = nodes.find(
      (node) => node.class_type === "CameraComfyUI_LoadMatrices",
    );

    expect(loadMatricesNode).toBeDefined();
    expect(loadMatricesNode!.inputs.matrices).toBe(JSON.stringify(testMatrices));
  });

  it("should connect LoadMatrices output to ApplyCamera input", () => {
    const params = createValidParams({
      cameraData: { matrices: [] },
    }) as WorkflowParams;

    const workflow = generateCameraComfyUIWorkflow(params);
    const entries = Object.entries(workflow);

    const loadMatricesEntry = entries.find(
      ([_, node]) => node.class_type === "CameraComfyUI_LoadMatrices",
    );
    const applyCameraEntry = entries.find(
      ([_, node]) => node.class_type === "CameraComfyUI_ApplyCamera",
    );

    expect(loadMatricesEntry).toBeDefined();
    expect(applyCameraEntry).toBeDefined();

    const [loadMatricesId] = loadMatricesEntry!;
    const [_, applyCameraNode] = applyCameraEntry!;

    // The camera_matrices input should reference the LoadMatrices node
    expect(applyCameraNode.inputs.camera_matrices).toEqual([loadMatricesId, 0]);
  });
});

// ============================================================================
// 3.9. CONTROLNET-POSE WORKFLOW CONTRACT TESTS
// ============================================================================

describe("ControlNet Pose Workflow Contract Tests", () => {
  /**
   * ControlNet Pose Requirements:
   * - Uses control_v11p_sd15_openpose.pth model
   * - Loads pose skeleton sequence from control images
   */

  it("should use openpose controlnet model for pose", () => {
    const params = createValidParams({}) as WorkflowParams;

    const workflow = generateControlNetWorkflow(params, "pose");
    const nodes = Object.values(workflow);

    const controlnetLoader = nodes.find(
      (node) => node.class_type === "ControlNetLoader",
    );

    expect(controlnetLoader).toBeDefined();
    expect(controlnetLoader!.inputs.control_net_name).toBe(
      "control_v11p_sd15_openpose.pth",
    );
  });

  it("should generate valid workflow structure", () => {
    const params = createValidParams({}) as WorkflowParams;

    const workflow = generateControlNetWorkflow(params, "pose");

    // Should have at least basic nodes
    expect(Object.keys(workflow).length).toBeGreaterThan(0);

    // Should validate without errors
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });
});

// ============================================================================
// 4. ALL EXPORT TARGETS GENERATE VALID WORKFLOWS
// ============================================================================

describe("All Export Targets Generate Valid Workflows", () => {
  // Targets that are fully implemented and should work
  const implementedTargets: Array<{
    target: ExportTarget;
    extraParams?: Partial<WorkflowParams>;
  }> = [
    { target: "wan22-i2v" },
    { target: "wan22-t2v" },
    { target: "wan22-fun-camera" },
    { target: "wan22-first-last" },
    { target: "uni3c-camera", extraParams: { cameraData: { matrices: [] } } },
    { target: "uni3c-motion", extraParams: { cameraData: { matrices: [] } } },
    { target: "motionctrl" },
    { target: "motionctrl-svd" },
    { target: "cogvideox" },
    { target: "controlnet-depth" },
    { target: "controlnet-canny" },
    { target: "controlnet-lineart" },
    { target: "animatediff-cameractrl" },
    // TTM targets all share the same workflow generator
    {
      target: "ttm",
      extraParams: {
        ttmLayers: [
          { layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] },
        ],
      },
    },
    {
      target: "ttm-wan",
      extraParams: {
        ttmLayers: [
          { layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] },
        ],
      },
    },
    {
      target: "ttm-cogvideox",
      extraParams: {
        ttmLayers: [
          { layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] },
        ],
      },
    },
    {
      target: "ttm-svd",
      extraParams: {
        ttmLayers: [
          { layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] },
        ],
      },
    },
    { target: "scail", extraParams: { scailPoseVideo: "pose.mp4" } },
    // Newly implemented targets (Jan 2026)
    { target: "light-x", extraParams: { loraModel: "light_x_relight.safetensors" } },
    { target: "wan-move", extraParams: { motionData: { tracks: [] } } },
    { target: "ati", extraParams: { motionData: { trajectories: [] } } },
    { target: "controlnet-pose", extraParams: {} },
    { target: "camera-comfyui", extraParams: { cameraData: { matrices: [] } } },
  ];

  for (const { target, extraParams } of implementedTargets) {
    it(`should generate valid workflow for ${target}`, () => {
      const params = createValidParams(extraParams);
      const workflow = generateWorkflowForTarget(target, params);

      // Should have at least one node (except custom-workflow)
      expect(Object.keys(workflow).length).toBeGreaterThan(0);

      // Should validate without errors
      const validation = validateWorkflow(workflow);
      expect(validation.valid).toBe(true);
    });
  }

  // All export targets are now implemented (as of Jan 2026)
  // The only remaining unimplemented target is 'custom-workflow' which returns empty
});

// ============================================================================
// 5. WORKFLOW PARAMETER VALIDATION
// ============================================================================

describe("Workflow Parameter Validation", () => {
  /**
   * NOTE: Parameter validation is NOT YET IMPLEMENTED in workflowTemplates.ts
   * These tests document the DESIRED behavior that should be added.
   * Currently, invalid params will produce invalid workflows that fail at runtime.
   *
   * TODO: Add validateWorkflowParams() function and call it in generateWorkflowForTarget()
   */

  describe("Unknown target handling (implemented)", () => {
    it("should throw for unknown target", () => {
      const params = createValidParams();
      expect(() =>
        generateWorkflowForTarget("unknown-target" as ExportTarget, params),
      ).toThrow(/unknown.*target/i);
    });
  });

  describe("Dimension validation", () => {
    it("should throw for width = 0", () => {
      const params = createValidParams({ width: 0 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid width/);
    });

    it("should throw for negative dimensions", () => {
      const params = createValidParams({ width: -512, height: -480 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid width.*Invalid height/s);
    });

    it("should throw for NaN dimensions", () => {
      const params = createValidParams({ width: NaN });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid width/);
    });

    it("should throw for Infinity dimensions", () => {
      const params = createValidParams({ width: Infinity });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid width/);
    });
  });

  describe("Frame count validation", () => {
    it("should throw for frameCount = 0", () => {
      const params = createValidParams({ frameCount: 0 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid frameCount/);
    });

    it("should throw for negative frameCount", () => {
      const params = createValidParams({ frameCount: -10 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid frameCount/);
    });
  });

  describe("FPS validation", () => {
    it("should throw for fps = 0", () => {
      const params = createValidParams({ fps: 0 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid fps/);
    });

    it("should throw for negative fps", () => {
      const params = createValidParams({ fps: -16 });
      expect(() => generateWorkflowForTarget("wan22-i2v", params)).toThrow(/Invalid fps/);
    });
  });
});

// ============================================================================
// 6. WORKFLOW NODE CONNECTION VALIDATION
// ============================================================================

describe("Workflow Node Connections", () => {
  it("should have all node references point to valid nodes", () => {
    const params = createValidParams({ scailPoseVideo: "pose.mp4" });
    const workflow = generateSCAILWorkflow(params);

    const nodeIds = Object.keys(workflow);

    for (const [nodeId, node] of Object.entries(workflow)) {
      for (const [inputName, inputValue] of Object.entries(node.inputs)) {
        if (Array.isArray(inputValue) && inputValue.length === 2) {
          const [refNodeId, outputIndex] = inputValue;
          if (typeof refNodeId === "string") {
            expect(nodeIds).toContain(refNodeId);
            expect(typeof outputIndex).toBe("number");
          }
        }
      }
    }
  });
});

// Need to import vi for mocking
import { vi } from "vitest";
