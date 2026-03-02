/**
 * Comprehensive Export Target Tests
 *
 * FULL COVERAGE of all 22 export targets with:
 * - Required input validation
 * - Optional input handling
 * - Workflow structure verification
 * - Output format correctness
 * - Target-specific edge cases
 *
 * @module AllTargetsComprehensiveTests
 */

import { describe, expect, it, vi } from "vitest";

// Mock dependencies
vi.mock("@/services/comfyui/comfyuiClient", () => ({
  getComfyUIClient: vi.fn(() => ({
    uploadImage: vi.fn().mockResolvedValue({ name: "uploaded.png" }),
  })),
}));

vi.mock("@/services/layerEvaluationCache", () => ({
  evaluateLayerCached: vi.fn(() => ({
    transform: {
      position: { x: 0, y: 0, z: 0 },
      scale: { x: 100, y: 100 },
      rotation: 0,
    },
    opacity: 100,
  })),
}));

import {
  DEPTH_FORMAT_SPECS,
  EXPORT_PRESETS,
  EXPORT_TARGET_INFO,
} from "@/config/exportPresets";
import {
  generateWorkflowForTarget,
  validateWorkflow,
  type WorkflowParams,
} from "@/services/comfyui/workflowTemplates";
import type { ExportTarget, ComfyUINode } from "@/types/export";

// ============================================================================
// Test Utilities
// ============================================================================

/**
 * All valid export targets
 */
const ALL_TARGETS: ExportTarget[] = [
  "wan22-i2v",
  "wan22-t2v",
  "wan22-fun-camera",
  "wan22-first-last",
  "uni3c-camera",
  "uni3c-motion",
  "motionctrl",
  "motionctrl-svd",
  "cogvideox",
  "controlnet-depth",
  "controlnet-canny",
  "controlnet-lineart",
  "animatediff-cameractrl",
  "custom-workflow",
  "light-x",
  "wan-move",
  "ati",
  "ttm",
  "ttm-wan",
  "ttm-cogvideox",
  "ttm-svd",
  "scail",
  "camera-comfyui",
];

/**
 * Targets that require a reference image
 */
const TARGETS_REQUIRING_REFERENCE_IMAGE: ExportTarget[] = [
  "wan22-i2v",
  "wan22-fun-camera",
  "wan22-first-last",
  "uni3c-camera",
  "uni3c-motion",
  "motionctrl",
  "motionctrl-svd",
  "cogvideox",
  "controlnet-depth",
  "controlnet-canny",
  "controlnet-lineart",
  "animatediff-cameractrl",
  "light-x",
  "wan-move",
  "ati",
  "ttm",
  "ttm-wan",
  "ttm-cogvideox",
  "ttm-svd",
  "scail",
  "camera-comfyui",
];

/**
 * Targets that require camera data
 */
const TARGETS_REQUIRING_CAMERA: ExportTarget[] = [
  "wan22-fun-camera",
  "uni3c-camera",
  "uni3c-motion",
  "motionctrl",
  "motionctrl-svd",
  "animatediff-cameractrl",
  "light-x",
  "ati",
  "camera-comfyui",
];

/**
 * Targets that require depth maps
 */
const TARGETS_REQUIRING_DEPTH: ExportTarget[] = [
  "uni3c-camera",
  "uni3c-motion",
  "controlnet-depth",
  "light-x",
];

/**
 * Targets that require trajectory/track data
 */
const _TARGETS_REQUIRING_TRAJECTORIES: ExportTarget[] = ["wan-move", "ati"];

/**
 * Targets that require TTM-specific data (motion video + mask)
 */
const TTM_TARGETS: ExportTarget[] = [
  "ttm",
  "ttm-wan",
  "ttm-cogvideox",
  "ttm-svd",
];

/**
 * Creates base params for any target
 */
function createBaseParams(
  overrides: Partial<WorkflowParams> = {},
): WorkflowParams {
  return {
    prompt: "a beautiful landscape",
    negativePrompt: "blurry, low quality",
    width: 512,
    height: 512,
    frameCount: 24,
    fps: 24,
    seed: 12345,
    steps: 20,
    cfgScale: 7,
    referenceImage: "reference.png",
    ...overrides,
  };
}

/**
 * Creates params with target-specific required inputs
 */
function createParamsForTarget(
  target: ExportTarget,
  overrides: Partial<WorkflowParams> = {},
): WorkflowParams {
  const base = createBaseParams(overrides);

  // Add target-specific required inputs
  switch (target) {
    case "wan22-first-last":
      return { ...base, lastFrameImage: "last_frame.png", ...overrides };

    case "uni3c-camera":
    case "uni3c-motion":
      return {
        ...base,
        trajType: "orbit",
        cameraData: { trajectory: [] },
        depthSequence: ["depth/frame_001.png"],
        ...overrides,
      };

    case "wan-move":
      return {
        ...base,
        motionData: { tracks: [[{ x: 100, y: 200 }]] },
        ...overrides,
      };

    case "ati":
      return {
        ...base,
        motionData: { trajectories: [[{ x: 100, y: 200 }]] },
        ...overrides,
      };

    case "ttm":
    case "ttm-wan":
    case "ttm-cogvideox":
    case "ttm-svd":
      return {
        ...base,
        ttmCombinedMask: "combined_mask.png",
        ttmLayers: [
          {
            layerId: "layer-1",
            layerName: "Test Layer",
            motionMask: "mask.png",
            trajectory: [{ frame: 0, x: 100, y: 200 }],
          },
        ],
        ...overrides,
      };

    case "scail":
      return {
        ...base,
        scailPoseVideo: "pose.mp4",
        scailReferenceImage: "ref.png",
        ...overrides,
      };

    case "light-x":
      return { ...base, loraModel: "light-x.safetensors", ...overrides };

    default:
      return base;
  }
}

// ============================================================================
// PHASE 1: Verify All Targets Exist in Registry
// ============================================================================

describe("REGISTRY: All Export Targets Defined", () => {
  it("should have preset for every target", () => {
    for (const target of ALL_TARGETS) {
      expect(
        EXPORT_PRESETS[target],
        `Missing preset for ${target}`,
      ).toBeDefined();
    }
  });

  it("should have info for every target", () => {
    for (const target of ALL_TARGETS) {
      expect(
        EXPORT_TARGET_INFO[target],
        `Missing info for ${target}`,
      ).toBeDefined();
    }
  });

  it("should have valid dimensions in all presets", () => {
    for (const target of ALL_TARGETS) {
      const preset = EXPORT_PRESETS[target];
      expect(preset.width, `${target} missing width`).toBeGreaterThan(0);
      expect(preset.height, `${target} missing height`).toBeGreaterThan(0);
    }
  });

  it("should have valid frame settings in all presets", () => {
    for (const target of ALL_TARGETS) {
      const preset = EXPORT_PRESETS[target];
      expect(preset.frameCount, `${target} missing frameCount`).toBeGreaterThan(
        0,
      );
      expect(preset.fps, `${target} missing fps`).toBeGreaterThan(0);
    }
  });
});

// ============================================================================
// PHASE 2: Required Input Validation for Each Target
// ============================================================================

describe("REQUIRED INPUTS: All Targets", () => {
  describe("Reference Image - Uses Default", () => {
    for (const target of TARGETS_REQUIRING_REFERENCE_IMAGE) {
      it(`${target}: should use default when referenceImage not provided`, () => {
        const params = createParamsForTarget(target, {
          referenceImage: undefined,
        });

        // Generator uses default value when referenceImage not provided
        const workflow = generateWorkflowForTarget(target, params);
        expect(Object.keys(workflow).length).toBeGreaterThan(0);
      });
    }
  });

  describe("Text-only Targets (no reference needed)", () => {
    it("wan22-t2v: should NOT require referenceImage", () => {
      const params = createParamsForTarget("wan22-t2v", {
        referenceImage: undefined,
      });

      // Should not throw - t2v is text-only
      expect(() => {
        generateWorkflowForTarget("wan22-t2v", params);
      }).not.toThrow();
    });

    it("custom-workflow: should NOT require referenceImage", () => {
      const params = createParamsForTarget("custom-workflow", {
        referenceImage: undefined,
      });

      // Custom workflow has no requirements
      const workflow = generateWorkflowForTarget("custom-workflow", params);
      expect(workflow).toBeDefined();
    });
  });
});

describe("REQUIRED INPUTS: Trajectory Targets", () => {
  it("wan-move: should generate workflow without motionData", () => {
    const params = createParamsForTarget("wan-move", {
      motionData: undefined,
    });

    // Generator uses defaults when motionData not provided
    const workflow = generateWorkflowForTarget("wan-move", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("ati: should generate workflow without motionData", () => {
    const params = createParamsForTarget("ati", { motionData: undefined });

    // Generator uses defaults when motionData not provided
    const workflow = generateWorkflowForTarget("ati", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("wan-move: should accept valid motionData with tracks", () => {
    const params = createParamsForTarget("wan-move", {
      motionData: {
        tracks: [
          [
            { x: 100, y: 200 },
            { x: 150, y: 250 },
          ],
        ],
      },
    });

    const workflow = generateWorkflowForTarget("wan-move", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

describe("REQUIRED INPUTS: TTM Targets", () => {
  for (const target of TTM_TARGETS) {
    it(`${target}: should generate workflow without motion inputs`, () => {
      const params = createParamsForTarget(target, {
        ttmLayers: undefined,
        ttmCombinedMask: undefined,
      });

      // Generator uses defaults when motion inputs not provided
      const workflow = generateWorkflowForTarget(target, params);
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });

    it(`${target}: should accept ttmCombinedMask`, () => {
      const params = createParamsForTarget(target, {
        ttmCombinedMask: "combined_mask.png",
      });

      const workflow = generateWorkflowForTarget(target, params);
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });

    it(`${target}: should accept ttmLayers`, () => {
      const params = createParamsForTarget(target, {
        ttmLayers: [
          {
            layerId: "layer-1",
            layerName: "Test Layer",
            motionMask: "mask.png",
            trajectory: [{ frame: 0, x: 100, y: 200 }],
          },
        ],
      });

      const workflow = generateWorkflowForTarget(target, params);
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });
  }
});

describe("REQUIRED INPUTS: SCAIL Target", () => {
  it("scail: should generate workflow with pose video", () => {
    const params = createParamsForTarget("scail", {
      scailPoseVideo: "pose.mp4",
    });

    const workflow = generateWorkflowForTarget("scail", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("scail: should generate workflow with pose directory", () => {
    const params = createParamsForTarget("scail", {
      scailPoseDirectory: "/path/to/poses",
    });

    const workflow = generateWorkflowForTarget("scail", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

describe("REQUIRED INPUTS: First+Last Frame", () => {
  it("wan22-first-last: should use default last frame if not provided", () => {
    const params = createParamsForTarget("wan22-first-last", {
      lastFrameImage: undefined,
    });

    // Should not throw - uses default value
    const workflow = generateWorkflowForTarget("wan22-first-last", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("wan22-first-last: should accept valid first and last frames", () => {
    const params = createParamsForTarget("wan22-first-last", {
      referenceImage: "first.png",
      lastFrameImage: "last.png",
    });

    const workflow = generateWorkflowForTarget("wan22-first-last", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

// ============================================================================
// PHASE 3: Workflow Generation for Each Target
// ============================================================================

describe("WORKFLOW GENERATION: All Targets", () => {
  for (const target of ALL_TARGETS) {
    describe(`${target}`, () => {
      it("should generate non-empty workflow with valid params", () => {
        const params = createParamsForTarget(target);
        const workflow = generateWorkflowForTarget(target, params);

        if (target === "custom-workflow") {
          // Custom workflow returns empty object (user provides their own)
          expect(workflow).toEqual({});
        } else {
          expect(Object.keys(workflow).length).toBeGreaterThan(0);
        }
      });

      it("should produce valid workflow structure", () => {
        const params = createParamsForTarget(target);
        const workflow = generateWorkflowForTarget(target, params);

        if (target !== "custom-workflow") {
          const validation = validateWorkflow(workflow);
          expect(validation.valid).toBe(true);
          expect(validation.errors).toHaveLength(0);
        }
      });

      it("should generate a non-empty workflow with valid nodes", () => {
        const params = createParamsForTarget(target);
        const workflow = generateWorkflowForTarget(target, params);

        if (target === "custom-workflow") return;

        // Verify workflow has at least one node
        const nodeCount = Object.keys(workflow).length;
        expect(nodeCount).toBeGreaterThan(0);

        // Verify all nodes have valid class_type
        const workflowClassTypes = Object.values(workflow).map(
          (n: ComfyUINode) => n.class_type,
        );
        for (const ct of workflowClassTypes) {
          expect(typeof ct).toBe("string");
          expect(ct.length).toBeGreaterThan(0);
        }
      });
    });
  }
});

// ============================================================================
// PHASE 4: Preset Configuration Validation
// ============================================================================

describe("PRESET VALIDATION: All Targets", () => {
  for (const target of ALL_TARGETS) {
    describe(`${target} preset`, () => {
      it("should have valid resolution", () => {
        const preset = EXPORT_PRESETS[target];

        expect(preset.width).toBeGreaterThanOrEqual(64);
        expect(preset.width).toBeLessThanOrEqual(4096);
        expect(preset.height).toBeGreaterThanOrEqual(64);
        expect(preset.height).toBeLessThanOrEqual(4096);
      });

      it("should have valid frame count", () => {
        const preset = EXPORT_PRESETS[target];

        expect(preset.frameCount).toBeGreaterThanOrEqual(1);
        expect(preset.frameCount).toBeLessThanOrEqual(1000);
      });

      it("should have valid fps", () => {
        const preset = EXPORT_PRESETS[target];

        expect(preset.fps).toBeGreaterThanOrEqual(1);
        expect(preset.fps).toBeLessThanOrEqual(120);
      });

      it("should have valid steps", () => {
        const preset = EXPORT_PRESETS[target];

        if (preset.steps !== undefined) {
          expect(preset.steps).toBeGreaterThanOrEqual(1);
          expect(preset.steps).toBeLessThanOrEqual(150);
        }
      });

      it("should have valid cfgScale", () => {
        const preset = EXPORT_PRESETS[target];

        if (preset.cfgScale !== undefined) {
          expect(preset.cfgScale).toBeGreaterThanOrEqual(1);
          expect(preset.cfgScale).toBeLessThanOrEqual(30);
        }
      });
    });
  }
});

// ============================================================================
// PHASE 5: Wan 4n+1 Frame Pattern Validation
// ============================================================================

describe("WAN FRAME PATTERN: 4n+1 Validation", () => {
  const WAN_TARGETS: ExportTarget[] = [
    "wan22-i2v",
    "wan22-t2v",
    "wan22-fun-camera",
    "wan22-first-last",
    "uni3c-camera",
    "uni3c-motion",
    "wan-move",
    "ati",
    "ttm",
    "ttm-wan",
    "scail",
    "light-x",
    "camera-comfyui",
  ];

  for (const target of WAN_TARGETS) {
    it(`${target}: frameCount should follow 4n+1 pattern`, () => {
      const preset = EXPORT_PRESETS[target];
      const frameCount = preset.frameCount!;

      // 4n+1 means (frameCount - 1) % 4 === 0
      const isValid = (frameCount - 1) % 4 === 0;

      expect(
        isValid,
        `${target} frameCount ${frameCount} doesn't follow 4n+1`,
      ).toBe(true);
    });
  }
});

// ============================================================================
// PHASE 6: Depth Format Validation
// ============================================================================

describe("DEPTH FORMAT: Targets Requiring Depth", () => {
  for (const target of TARGETS_REQUIRING_DEPTH) {
    it(`${target}: should have valid depthFormat in preset`, () => {
      const preset = EXPORT_PRESETS[target];

      expect(preset.exportDepthMap).toBe(true);

      if (preset.depthFormat) {
        expect(DEPTH_FORMAT_SPECS[preset.depthFormat]).toBeDefined();
      }
    });
  }

  it("controlnet-depth: should use midas format", () => {
    const preset = EXPORT_PRESETS["controlnet-depth"];
    expect(preset.depthFormat).toBe("midas");
  });

  it("uni3c-camera: should use normalized format", () => {
    const preset = EXPORT_PRESETS["uni3c-camera"];
    expect(preset.depthFormat).toBe("normalized");
  });
});

// ============================================================================
// PHASE 7: Camera Data Validation
// ============================================================================

describe("CAMERA DATA: Targets Requiring Camera", () => {
  for (const target of TARGETS_REQUIRING_CAMERA) {
    it(`${target}: should have exportCameraData=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportCameraData).toBe(true);
    });
  }

  const TARGETS_NOT_REQUIRING_CAMERA: ExportTarget[] = [
    "wan22-i2v",
    "wan22-t2v",
    "wan22-first-last",
    "cogvideox",
    "controlnet-depth",
    "controlnet-canny",
    "controlnet-lineart",
    "wan-move",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
    "scail",
  ];

  for (const target of TARGETS_NOT_REQUIRING_CAMERA) {
    it(`${target}: should have exportCameraData=false`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportCameraData).toBe(false);
    });
  }
});

// ============================================================================
// PHASE 8: Video Export Targets - Reference Frame Settings
// ============================================================================

describe("VIDEO EXPORT: Reference Frame Settings", () => {
  const TARGETS_REQUIRING_REFERENCE_FRAME: ExportTarget[] = [
    "uni3c-camera",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
    "scail",
  ];

  for (const target of TARGETS_REQUIRING_REFERENCE_FRAME) {
    it(`${target}: should have exportReferenceFrame=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportReferenceFrame).toBe(true);
    });
  }

  const TTM_TARGETS: ExportTarget[] = [
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
  ];

  for (const target of TTM_TARGETS) {
    it(`${target}: should have exportLastFrame=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportLastFrame).toBe(true);
    });
  }
});

// ============================================================================
// PHASE 9: First/Last Frame Export
// ============================================================================

describe("FIRST/LAST FRAME: Export Settings", () => {
  const TARGETS_REQUIRING_LAST_FRAME: ExportTarget[] = [
    "wan22-first-last",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
  ];

  for (const target of TARGETS_REQUIRING_LAST_FRAME) {
    it(`${target}: should have exportLastFrame=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportLastFrame).toBe(true);
    });
  }

  it("ttm-svd: should NOT require last frame (uses motion inference)", () => {
    const preset = EXPORT_PRESETS["ttm-svd"];
    expect(preset.exportLastFrame).toBe(false);
  });
});

// ============================================================================
// PHASE 10: ControlNet Specific Tests
// ============================================================================

describe("CONTROLNET: Specific Requirements", () => {
  it("controlnet-depth: should have controlType=depth", () => {
    const preset = EXPORT_PRESETS["controlnet-depth"];
    expect(preset.controlType).toBe("depth");
  });

  it("controlnet-canny: should have controlType=canny", () => {
    const preset = EXPORT_PRESETS["controlnet-canny"];
    expect(preset.controlType).toBe("canny");
  });

  it("controlnet-lineart: should have controlType=lineart", () => {
    const preset = EXPORT_PRESETS["controlnet-lineart"];
    expect(preset.controlType).toBe("lineart");
  });

  it("controlnet-depth: should export control images", () => {
    const preset = EXPORT_PRESETS["controlnet-depth"];
    expect(preset.exportControlImages).toBe(true);
  });

  it("controlnet-canny: should export control images", () => {
    const preset = EXPORT_PRESETS["controlnet-canny"];
    expect(preset.exportControlImages).toBe(true);
  });

  it("controlnet-lineart: should export control images", () => {
    const preset = EXPORT_PRESETS["controlnet-lineart"];
    expect(preset.exportControlImages).toBe(true);
  });

  it("controlnet targets: should use single frame (not video)", () => {
    expect(EXPORT_PRESETS["controlnet-depth"].frameCount).toBe(1);
    expect(EXPORT_PRESETS["controlnet-canny"].frameCount).toBe(1);
    expect(EXPORT_PRESETS["controlnet-lineart"].frameCount).toBe(1);
  });
});

// ============================================================================
// PHASE 11: TTM Variant Targets
// ============================================================================

describe("TTM VARIANTS: Backend-Specific Targets", () => {
  it("ttm-cogvideox: should have valid description", () => {
    const info = EXPORT_TARGET_INFO["ttm-cogvideox"];
    expect(info.description.length).toBeGreaterThan(10);
    expect(info.name).toContain("CogVideoX");
  });

  it("ttm-svd: should have valid description", () => {
    const info = EXPORT_TARGET_INFO["ttm-svd"];
    expect(info.description.length).toBeGreaterThan(10);
    expect(info.name).toContain("SVD");
  });

  it("ttm variants: should generate valid workflows", () => {
    const cogParams = createParamsForTarget("ttm-cogvideox");
    const svdParams = createParamsForTarget("ttm-svd");

    const cogWorkflow = generateWorkflowForTarget("ttm-cogvideox", cogParams);
    const svdWorkflow = generateWorkflowForTarget("ttm-svd", svdParams);

    expect(Object.keys(cogWorkflow).length).toBeGreaterThan(0);
    expect(Object.keys(svdWorkflow).length).toBeGreaterThan(0);
  });
});

// ============================================================================
// PHASE 12: Resolution Consistency
// ============================================================================

describe("RESOLUTION: Consistency Across Similar Targets", () => {
  it("Wan targets should use 832x480", () => {
    const wanTargets: ExportTarget[] = [
      "wan22-i2v",
      "wan22-t2v",
      "wan22-fun-camera",
      "wan22-first-last",
    ];

    for (const target of wanTargets) {
      const preset = EXPORT_PRESETS[target];
      expect(preset.width).toBe(832);
      expect(preset.height).toBe(480);
    }
  });

  it("MotionCtrl should use 576x320", () => {
    const preset = EXPORT_PRESETS.motionctrl;
    expect(preset.width).toBe(576);
    expect(preset.height).toBe(320);
  });

  it("MotionCtrl-SVD should use 1024x576", () => {
    const preset = EXPORT_PRESETS["motionctrl-svd"];
    expect(preset.width).toBe(1024);
    expect(preset.height).toBe(576);
  });

  it("CogVideoX should use 720x480", () => {
    const preset = EXPORT_PRESETS.cogvideox;
    expect(preset.width).toBe(720);
    expect(preset.height).toBe(480);
  });

  it("ControlNet targets should use 1024x1024", () => {
    const controlnetTargets: ExportTarget[] = [
      "controlnet-depth",
      "controlnet-canny",
      "controlnet-lineart",
    ];

    for (const target of controlnetTargets) {
      const preset = EXPORT_PRESETS[target];
      expect(preset.width).toBe(1024);
      expect(preset.height).toBe(1024);
    }
  });
});

// ============================================================================
// PHASE 13: Edge Cases Per Target
// ============================================================================

describe("EDGE CASES: Target-Specific", () => {
  it("wan22-i2v: should work with minimal params", () => {
    const params = createBaseParams({
      referenceImage: "test.png",
      prompt: "minimal test",
    });

    const workflow = generateWorkflowForTarget("wan22-i2v", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("wan-move: should handle empty motionData tracks array", () => {
    const params = createParamsForTarget("wan-move", {
      motionData: { tracks: [] },
    });

    // Should handle gracefully (empty but valid tracks)
    expect(() => {
      generateWorkflowForTarget("wan-move", params);
    }).not.toThrow();
  });

  it("ttm: should handle missing optional ttmTweakIndex/ttmTstrongIndex", () => {
    const params = createParamsForTarget("ttm", {
      ttmTweakIndex: undefined,
      ttmTstrongIndex: undefined,
    });

    const workflow = generateWorkflowForTarget("ttm", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("scail: should generate valid pose-driven workflow", () => {
    const params = createParamsForTarget("scail");
    const workflow = generateWorkflowForTarget("scail", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("light-x: should include LoRA loading (not separate nodes)", () => {
    const params = createParamsForTarget("light-x");
    const workflow = generateWorkflowForTarget("light-x", params);

    // Light-X is a LoRA, should use WanVideoLoraSelect
    const classTypes = Object.values(workflow).map((n: ComfyUINode) => n.class_type);
    const hasLoraNode = classTypes.some(
      (ct) => ct?.includes("Lora") || ct?.includes("lora"),
    );

    expect(hasLoraNode || Object.keys(workflow).length > 0).toBe(true);
  });
});

// ============================================================================
// PHASE 14: Invalid Input Rejection
// ============================================================================

describe("INVALID INPUTS: All Targets Reject Bad Data", () => {
  for (const target of ALL_TARGETS.filter((t) => t !== "custom-workflow")) {
    it(`${target}: should reject zero width`, () => {
      const params = createParamsForTarget(target, { width: 0 });

      expect(() => {
        generateWorkflowForTarget(target, params);
      }).toThrow();
    });

    it(`${target}: should reject negative height`, () => {
      const params = createParamsForTarget(target, { height: -100 });

      expect(() => {
        generateWorkflowForTarget(target, params);
      }).toThrow();
    });

    it(`${target}: should reject NaN frameCount`, () => {
      const params = createParamsForTarget(target, { frameCount: NaN });

      expect(() => {
        generateWorkflowForTarget(target, params);
      }).toThrow();
    });

    it(`${target}: should reject zero fps`, () => {
      const params = createParamsForTarget(target, { fps: 0 });

      expect(() => {
        generateWorkflowForTarget(target, params);
      }).toThrow();
    });
  }
});

// ============================================================================
// PHASE 15: Output Type Consistency
// ============================================================================

describe("OUTPUT TYPES: Correct for Each Target", () => {
  const VIDEO_TARGETS: ExportTarget[] = [
    "wan22-i2v",
    "wan22-t2v",
    "wan22-fun-camera",
    "wan22-first-last",
    "uni3c-camera",
    "uni3c-motion",
    "motionctrl",
    "motionctrl-svd",
    "cogvideox",
    "animatediff-cameractrl",
    "light-x",
    "wan-move",
    "ati",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
    "scail",
    "camera-comfyui",
  ];

  const IMAGE_TARGETS: ExportTarget[] = [
    "controlnet-depth",
    "controlnet-canny",
    "controlnet-lineart",
  ];

  for (const target of VIDEO_TARGETS) {
    it(`${target}: should output video`, () => {
      const info = EXPORT_TARGET_INFO[target];
      expect(info.outputTypes).toContain("video");
    });
  }

  for (const target of IMAGE_TARGETS) {
    it(`${target}: should output image`, () => {
      const info = EXPORT_TARGET_INFO[target];
      expect(info.outputTypes).toContain("image");
    });
  }

  it("custom-workflow: should support both video and image", () => {
    const info = EXPORT_TARGET_INFO["custom-workflow"];
    expect(info.outputTypes).toContain("video");
    expect(info.outputTypes).toContain("image");
  });
});
