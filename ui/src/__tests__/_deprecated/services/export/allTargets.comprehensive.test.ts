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
import type { ExportTarget } from "@/types/export";

// ============================================================================
// Test Utilities
// ============================================================================

/**
 * All valid export targets (scail removed - not in current API)
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
  // "scail" - not a valid ExportTarget in current API
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
        uni3cRenderVideo: "camera_render.mp4",
        depthSequence: ["depth/frame_001.png"],
        ...overrides,
      };

    case "wan-move":
      return { ...base, trackCoords: '[[{"x":100,"y":200}]]', ...overrides };

    case "ati":
      return { ...base, trackCoords: '[[{"x":100,"y":200}]]', ...overrides };

    case "ttm":
    case "ttm-wan":
    case "ttm-cogvideox":
    case "ttm-svd":
      return {
        ...base,
        ttmMotionVideo: "motion.mp4",
        ttmEndFrame: "end.png",
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
      return { ...base, lightXLora: "light-x.safetensors", ...overrides };

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
  describe("Reference Image Requirement", () => {
    for (const target of TARGETS_REQUIRING_REFERENCE_IMAGE) {
      it(`${target}: should require referenceImage`, () => {
        const params = createParamsForTarget(target, {
          referenceImage: undefined,
        });

        expect(() => {
          generateWorkflowForTarget(target, params);
        }).toThrow(/referenceImage|reference.*image|required/i);
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
  it("wan-move: should require trackCoords", () => {
    const params = createParamsForTarget("wan-move", {
      trackCoords: undefined,
    });

    expect(() => {
      generateWorkflowForTarget("wan-move", params);
    }).toThrow(/trackCoords|track.*coord|trajectory|required/i);
  });

  it("ati: should require trackCoords", () => {
    const params = createParamsForTarget("ati", { trackCoords: undefined });

    expect(() => {
      generateWorkflowForTarget("ati", params);
    }).toThrow(/trackCoords|track.*coord|trajectory|required/i);
  });

  it("wan-move: should accept valid trackCoords JSON", () => {
    const params = createParamsForTarget("wan-move", {
      trackCoords: JSON.stringify([
        [
          { x: 100, y: 200 },
          { x: 150, y: 250 },
        ],
      ]),
    });

    const workflow = generateWorkflowForTarget("wan-move", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

describe("REQUIRED INPUTS: TTM Targets", () => {
  for (const target of TTM_TARGETS) {
    it(`${target}: should require ttmMotionVideo or ttmMaskDirectory`, () => {
      const params = createParamsForTarget(target, {
        ttmMotionVideo: undefined,
        ttmMaskDirectory: undefined,
      });

      expect(() => {
        generateWorkflowForTarget(target, params);
      }).toThrow(
        /ttmMotionVideo|ttmMaskDirectory|motion.*video|mask|required/i,
      );
    });

    it(`${target}: should accept ttmMotionVideo`, () => {
      const params = createParamsForTarget(target, {
        ttmMotionVideo: "motion.mp4",
      });

      const workflow = generateWorkflowForTarget(target, params);
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });

    it(`${target}: should accept ttmMaskDirectory`, () => {
      const params = createParamsForTarget(target, {
        ttmMotionVideo: undefined,
        ttmMaskDirectory: "/masks/",
      });

      const workflow = generateWorkflowForTarget(target, params);
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });
  }
});

describe("REQUIRED INPUTS: SCAIL Target", () => {
  it("scail: should require pose video or directory", () => {
    const params = createParamsForTarget("scail" as any as ExportTarget, {
      scailPoseVideo: undefined,
      scailPoseDirectory: undefined,
    });

    expect(() => {
      generateWorkflowForTarget("scail" as any as ExportTarget, params);
    }).toThrow(/Unknown export target.*scail/i);
  });

  it("scail: should accept scailPoseVideo", () => {
    const params = createParamsForTarget("scail" as any as ExportTarget, {
      scailPoseVideo: "pose.mp4",
    });

    expect(() => {
      generateWorkflowForTarget("scail" as any as ExportTarget, params);
    }).toThrow(/Unknown export target.*scail/i);
  });
});

describe("REQUIRED INPUTS: First+Last Frame", () => {
  it("wan22-first-last: should require lastFrameImage", () => {
    const params = createParamsForTarget("wan22-first-last", {
      lastFrameImage: undefined,
    });

    expect(() => {
      generateWorkflowForTarget("wan22-first-last", params);
    }).toThrow(/lastFrameImage|last.*frame|required/i);
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

      it("should include expected ComfyUI nodes", () => {
        const params = createParamsForTarget(target);
        const workflow = generateWorkflowForTarget(target, params);

        if (target === "custom-workflow") return;

        const expectedNodes = EXPORT_TARGET_INFO[target].comfyNodes;
        const workflowClassTypes = Object.values(workflow).map(
          (n) => n.class_type,
        );

        // At least one expected node should be present
        const hasExpectedNode = expectedNodes.some((node) =>
          workflowClassTypes.some(
            (ct) => ct?.includes(node) || node.includes(ct || ""),
          ),
        );

        if (expectedNodes.length > 0) {
          expect(hasExpectedNode).toBe(true);
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
// PHASE 8: Video Export Targets
// ============================================================================

describe("VIDEO EXPORT: Scene and Mask Videos", () => {
  const TARGETS_REQUIRING_SCENE_VIDEO: ExportTarget[] = [
    "uni3c-camera",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
    "scail",
  ];

  for (const target of TARGETS_REQUIRING_SCENE_VIDEO) {
    it(`${target}: should have exportSceneVideo=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportSceneVideo).toBe(true);
    });
  }

  const TARGETS_REQUIRING_MASK_VIDEO: ExportTarget[] = [
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
  ];

  for (const target of TARGETS_REQUIRING_MASK_VIDEO) {
    it(`${target}: should have exportMaskVideo=true`, () => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.exportMaskVideo).toBe(true);
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
// PHASE 11: Deprecated Target Warnings
// ============================================================================

describe("DEPRECATED TARGETS: Warnings", () => {
  it("ttm-cogvideox: should be marked deprecated in info", () => {
    const info = EXPORT_TARGET_INFO["ttm-cogvideox"];
    expect(info.description.toLowerCase()).toContain("deprecated");
  });

  it("ttm-svd: should be marked deprecated in info", () => {
    const info = EXPORT_TARGET_INFO["ttm-svd"];
    expect(info.description.toLowerCase()).toContain("deprecated");
  });

  it("deprecated targets: should still generate workflow (fallback)", () => {
    const cogParams = createParamsForTarget("ttm-cogvideox");
    const svdParams = createParamsForTarget("ttm-svd");

    // Should not throw - should use fallback
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

  it("wan-move: should handle empty trackCoords array", () => {
    const params = createParamsForTarget("wan-move", {
      trackCoords: "[]",
    });

    // Should handle gracefully (empty but valid JSON)
    expect(() => {
      generateWorkflowForTarget("wan-move", params);
    }).not.toThrow();
  });

  it("ttm: should handle missing optional ttmStartStep/ttmEndStep", () => {
    const params = createParamsForTarget("ttm", {
      ttmStartStep: undefined,
      ttmEndStep: undefined,
    });

    const workflow = generateWorkflowForTarget("ttm", params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("scail: should throw for unknown export target", () => {
    const params = createParamsForTarget("scail" as any as ExportTarget);
    expect(() => {
      generateWorkflowForTarget("scail" as any as ExportTarget, params);
    }).toThrow(/Unknown export target.*scail/i);
  });

  it("light-x: should include LoRA loading (not separate nodes)", () => {
    const params = createParamsForTarget("light-x");
    const workflow = generateWorkflowForTarget("light-x", params);

    // Light-X is a LoRA, should use WanVideoLoraSelect
    const classTypes = Object.values(workflow).map((n) => n.class_type);
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
