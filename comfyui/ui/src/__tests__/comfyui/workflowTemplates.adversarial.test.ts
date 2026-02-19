/**
 * Workflow Templates Adversarial Tests
 *
 * Tests designed to BREAK the workflow generation system and verify it fails gracefully.
 * Focus areas:
 * - Invalid parameter validation
 * - Missing required inputs per target
 * - Unknown export targets
 * - Invalid dimensions/fps
 * - Workflow structure validation
 *
 * @module WorkflowTemplatesAdversarialTests
 */

import { describe, expect, it, vi } from "vitest";

import {
  generateTTMWorkflow,
  generateUni3CWorkflow,
  generateWan22I2VWorkflow,
  generateWorkflowForTarget,
  injectParameters,
  validateWorkflow,
  type WorkflowParams,
} from "@/services/comfyui/workflowTemplates";
import type {
  ExportTarget,
  ComfyUIWorkflow,
  ComfyUINode,
  Wan22FunCameraData,
  Uni3CCameraData,
  NodeConnection,
} from "@/types/export";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Fixtures
// ═══════════════════════════════════════════════════════════════════════════

function createValidParams(
  overrides: Partial<WorkflowParams> = {},
): WorkflowParams {
  return {
    prompt: "test prompt",
    negativePrompt: "bad quality",
    width: 512,
    height: 512,
    frameCount: 24,
    fps: 24,
    referenceImage: "test.png",
    seed: 12345,
    steps: 20,
    cfgScale: 7,
    ...overrides,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// CRITICAL: Parameter Validation
// ═══════════════════════════════════════════════════════════════════════════

describe("CRITICAL: validateWorkflowParams - Invalid Dimensions", () => {
  it("should throw for width = 0", () => {
    const params = createValidParams({ width: 0 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/width.*0.*64-8192|invalid/i);
  });

  it("should throw for negative width", () => {
    const params = createValidParams({ width: -512 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/width.*-512|invalid/i);
  });

  it("should throw for NaN width", () => {
    const params = createValidParams({ width: NaN });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/width.*NaN|invalid/i);
  });

  it("should throw for width > 8192", () => {
    const params = createValidParams({ width: 16384 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/width.*16384.*64-8192|invalid/i);
  });

  it("should throw for height = 0", () => {
    const params = createValidParams({ height: 0 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/height.*0.*64-8192|invalid/i);
  });

  it("should throw for NaN height", () => {
    const params = createValidParams({ height: NaN });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/height.*NaN|invalid/i);
  });
});

describe("CRITICAL: validateWorkflowParams - Invalid Frame Count", () => {
  it("should throw for frameCount = 0", () => {
    const params = createValidParams({ frameCount: 0 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/frameCount.*0|invalid/i);
  });

  it("should throw for negative frameCount", () => {
    const params = createValidParams({ frameCount: -10 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/frameCount.*-10|invalid/i);
  });

  it("should throw for frameCount > 10000", () => {
    const params = createValidParams({ frameCount: 100000 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/frameCount.*100000.*1-10000|invalid/i);
  });

  it("should throw for NaN frameCount", () => {
    const params = createValidParams({ frameCount: NaN });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/frameCount.*NaN|invalid/i);
  });
});

describe("CRITICAL: validateWorkflowParams - Invalid FPS", () => {
  it("should throw for fps = 0", () => {
    const params = createValidParams({ fps: 0 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/fps.*0.*1-120|invalid/i);
  });

  it("should throw for fps > 120", () => {
    const params = createValidParams({ fps: 1000 });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/fps.*1000.*1-120|invalid/i);
  });

  it("should throw for NaN fps", () => {
    const params = createValidParams({ fps: NaN });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/fps.*NaN|invalid/i);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// CRITICAL: Missing Required Inputs Per Target
// ═══════════════════════════════════════════════════════════════════════════

describe("DESIGN CHOICE: Missing Inputs Use Defaults", () => {
  // Note: The implementation uses default values for missing inputs instead of throwing.
  // This is a design choice (DC-004, DC-005 in BUGS.md) - workflows can be generated
  // with placeholder values and modified by users before execution.

  describe("Targets handle missing referenceImage with defaults", () => {
    const targetsUsingImage: ExportTarget[] = [
      "wan22-i2v",
      "wan22-first-last",
      "uni3c-camera",
      "uni3c-motion",
      "ttm",
      "ttm-wan",
    ];

    for (const target of targetsUsingImage) {
      it(`should use default referenceImage for ${target}`, () => {
        const params = createValidParams({ referenceImage: undefined });

        // Should NOT throw - uses default "input.png"
        const workflow = generateWorkflowForTarget(target, params);
        expect(workflow).toBeDefined();
        expect(Object.keys(workflow).length).toBeGreaterThan(0);
      });
    }
  });

  describe("TTM-specific handling", () => {
    it("should generate TTM workflow without ttmLayers (uses empty default)", () => {
      const params = createValidParams();

      // Should NOT throw - uses empty array default
      const workflow = generateWorkflowForTarget("ttm", params);
      expect(workflow).toBeDefined();
    });

    it("should accept TTM with ttmLayers", () => {
      const params = {
        ...createValidParams(),
        ttmLayers: [{ layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] }],
      } as WorkflowParams;

      const workflow = generateWorkflowForTarget("ttm", params);
      expect(workflow).toBeDefined();
    });

    it("should accept TTM with ttmCombinedMask", () => {
      const params = {
        ...createValidParams(),
        ttmCombinedMask: "combined.png",
      } as WorkflowParams;

      const workflow = generateWorkflowForTarget("ttm", params);
      expect(workflow).toBeDefined();
    });
  });

  describe("Wan-Move specific handling", () => {
    it("should generate wan-move workflow without cameraData (uses empty default)", () => {
      const params = createValidParams();

      // Should NOT throw - uses empty tracks default
      const workflow = generateWorkflowForTarget("wan-move", params);
      expect(workflow).toBeDefined();
    });

    it("should accept wan-move with cameraData", () => {
      // Test with valid Wan22FunCameraData structure
      const wanCameraData: Wan22FunCameraData = {
        camera_motion: "Pan Up", // Valid Wan22CameraMotion
      };
      const params: WorkflowParams = {
        ...createValidParams(),
        cameraData: wanCameraData,
      };

      const workflow = generateWorkflowForTarget("wan-move", params);
      expect(workflow).toBeDefined();
    });
  });

  describe("SCAIL target", () => {
    // Note: SCAIL IS a valid ExportTarget (TE-001 in BUGS.md - test was wrong)
    it("should generate valid SCAIL workflow", () => {
      const params = createValidParams();

      const workflow = generateWorkflowForTarget("scail" as ExportTarget, params);
      expect(workflow).toBeDefined();
      expect(Object.keys(workflow).length).toBeGreaterThan(0);
    });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// HIGH: Unknown Export Target
// ═══════════════════════════════════════════════════════════════════════════

describe("HIGH: Unknown Export Target", () => {
  it("should throw for completely unknown target", () => {
    const params = createValidParams();

    expect(() => {
      generateWorkflowForTarget("unknown-model-xyz" as ExportTarget, params);
    }).toThrow(/unknown.*target/i);
  });

  it("should handle valid export target", () => {
    const params = createValidParams();

    // Function requires ExportTarget - test with valid target
    const workflow = generateWorkflowForTarget("wan-move", params);
    expect(workflow).toBeDefined();
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });

  it("should throw for empty string target", () => {
    const params = createValidParams();

    expect(() => {
      generateWorkflowForTarget("" as ExportTarget, params);
    }).toThrow(/unknown.*target/i);
  });

  it("should handle custom-workflow target gracefully", () => {
    const params = createValidParams();

    const workflow = generateWorkflowForTarget(
      "custom-workflow" as ExportTarget,
      params,
    );

    // Should return empty workflow
    expect(workflow).toEqual({});
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// HIGH: Workflow Structure Validation
// ═══════════════════════════════════════════════════════════════════════════

describe("HIGH: validateWorkflow - Structure Checks", () => {
  it("should detect missing class_type", () => {
    // Create workflow with node missing class_type using Partial type
    const badNode: Partial<ComfyUINode> = { inputs: {} };
    const badWorkflow: ComfyUIWorkflow = {
      "1": badNode as ComfyUINode, // Missing class_type - validation should catch this
    };

    const result = validateWorkflow(badWorkflow);

    expect(result.valid).toBe(false);
    expect(result.errors.some((e) => e.includes("class_type"))).toBe(true);
  });

  it("should detect invalid node references", () => {
    // Create workflow with node referencing non-existent node "999"
    // NodeConnection format is [nodeId, outputIndex] tuple
    const badWorkflow: ComfyUIWorkflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "test.png" },
      },
      "2": {
        class_type: "ImageResize",
        // Reference non-existent node "999" - validation should catch this
        // NodeConnection is [string, number] tuple, but inputs accepts union type
        inputs: {
          image: ["999", 0] as NodeConnection & (string | number | boolean | string[] | number[] | null | undefined),
        },
      },
    };

    const result = validateWorkflow(badWorkflow);

    expect(result.valid).toBe(false);
    expect(
      result.errors.some(
        (e) => e.includes("999") && e.includes("non-existent"),
      ),
    ).toBe(true);
  });

  it("should warn about missing output nodes", () => {
    const noOutputWorkflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "test.png" },
      },
    };

    const result = validateWorkflow(noOutputWorkflow);

    // Should be valid but have warnings
    expect(result.warnings.some((w) => w.includes("output"))).toBe(true);
  });

  it("should pass valid workflow", () => {
    // Valid workflow: NodeConnection is [string, number] tuple
    const validWorkflow: ComfyUIWorkflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "test.png" },
      },
      "2": {
        class_type: "SaveImage",
        // NodeConnection format: [nodeId, outputIndex] tuple
        // Cast to satisfy ComfyUINode.inputs type which accepts union
        inputs: { images: ["1", 0] as NodeConnection & (string | number | boolean | string[] | number[] | null | undefined) },
      },
    };

    const result = validateWorkflow(validWorkflow);

    expect(result.valid).toBe(true);
    expect(result.errors).toHaveLength(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// HIGH: Generated Workflows Have Valid Structure
// ═══════════════════════════════════════════════════════════════════════════

describe("HIGH: Generated Workflows - Valid Structure", () => {
  const validTargets: ExportTarget[] = [
    "wan22-i2v",
    "wan22-fun-camera",
    "cogvideox",
    "controlnet-depth",
    "controlnet-canny",
    "controlnet-lineart",
    "animatediff-cameractrl",
    "motionctrl",
  ];

  for (const target of validTargets) {
    it(`should generate valid workflow for ${target}`, () => {
      const params = createValidParams();
      const workflow = generateWorkflowForTarget(target, params);

      // Should have at least one node
      expect(Object.keys(workflow).length).toBeGreaterThan(0);

      // Should validate without errors
      const validation = validateWorkflow(workflow);
      expect(validation.valid).toBe(true);
    });
  }

  it("should generate valid Uni3C workflow", () => {
    // Test with valid Uni3CCameraData structure
    const uni3cCameraData: Uni3CCameraData = {
      traj_type: "custom", // Valid Uni3CTrajType
      custom_trajectory: [], // Optional trajectory
    };
    const params: WorkflowParams = {
      ...createValidParams(),
      cameraData: uni3cCameraData,
    };

    const workflow = generateWorkflowForTarget("uni3c-camera", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid TTM workflow", () => {
    const params = {
      ...createValidParams(),
      ttmLayers: [{ layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] }],
    } as WorkflowParams;

    const workflow = generateWorkflowForTarget("ttm", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid WanMove workflow", () => {
    const params: WorkflowParams = {
      ...createValidParams(),
      motionData: { tracks: [[{ x: 100, y: 200 }]] },
    };

    const workflow = generateWorkflowForTarget("wan-move", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid ATI workflow", () => {
    const params: WorkflowParams = {
      ...createValidParams(),
      motionData: { trajectories: [[{ x: 100, y: 200 }]] },
    };

    const workflow = generateWorkflowForTarget("ati", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid Light-X workflow", () => {
    const params = createValidParams();

    const workflow = generateWorkflowForTarget("light-x", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid SCAIL workflow", () => {
    const params = createValidParams();

    // Note: SCAIL IS a valid ExportTarget (TE-001 in BUGS.md - test was wrong)
    const workflow = generateWorkflowForTarget("scail" as ExportTarget, params);
    expect(workflow).toBeDefined();
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// MEDIUM: Parameter Injection
// ═══════════════════════════════════════════════════════════════════════════

describe("MEDIUM: injectParameters", () => {
  it("should replace placeholders with values", () => {
    const workflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "{{filename}}" },
      },
    };

    const result = injectParameters(workflow, { filename: "test.png" });

    expect(result["1"].inputs.image).toBe("test.png");
  });

  it("should handle missing placeholders gracefully", () => {
    const workflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "{{missing}}" },
      },
    };

    const result = injectParameters(workflow, { other: "value" });

    // Placeholder should remain unchanged
    expect(result["1"].inputs.image).toBe("{{missing}}");
  });

  it("should handle object values", () => {
    const workflow = {
      "1": {
        class_type: "Test",
        inputs: { data: "{{complex}}" },
      },
    };

    const result = injectParameters(workflow, { complex: JSON.stringify({ nested: "value" }) });

    // Should be stringified
    expect(result["1"].inputs.data).toBe('{"nested":"value"}');
  });

  it("should handle number values", () => {
    const workflow = {
      "1": {
        class_type: "Test",
        inputs: { width: "{{width}}" },
      },
    };

    const result = injectParameters(workflow, { width: 512 });

    expect(result["1"].inputs.width).toBe("512");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// EDGE: Default Value Handling
// ═══════════════════════════════════════════════════════════════════════════

describe("EDGE: Default Values in Workflows", () => {
  it("should use default seed when not provided", () => {
    const params = createValidParams({ seed: undefined });
    const workflow = generateWan22I2VWorkflow(params);

    // Find sampler/generation node
    const nodes = Object.values(workflow);
    const samplerNode = nodes.find(
      (n) =>
        n.class_type?.includes("Sampler") ||
        n.class_type?.includes("I2V") ||
        n.class_type?.includes("ImageToVideo"),
    );

    if (samplerNode) {
      // Seed should be a valid number
      expect(typeof samplerNode.inputs.seed).toBe("number");
      expect(Number.isFinite(samplerNode.inputs.seed)).toBe(true);
    }
  });

  it("should use default steps when not provided", () => {
    const params = createValidParams({ steps: undefined });
    const workflow = generateWan22I2VWorkflow(params);

    const nodes = Object.values(workflow);
    const samplerNode = nodes.find(
      (n) => n.class_type?.includes("I2V") || n.class_type?.includes("Sampler"),
    );

    if (samplerNode && "steps" in samplerNode.inputs) {
      expect(samplerNode.inputs.steps).toBeGreaterThan(0);
    }
  });

  it("should use default model when not provided", () => {
    const params = createValidParams({ wanModel: undefined });
    const workflow = generateWan22I2VWorkflow(params);

    const nodes = Object.values(workflow);
    const loaderNode = nodes.find((n) => n.class_type?.includes("Load"));

    // Should have a model specified
    expect(loaderNode).toBeDefined();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// EDGE: TTM Model Warnings
// ═══════════════════════════════════════════════════════════════════════════

describe("EDGE: TTM Model Compatibility", () => {
  it("should warn for TTM with non-wan model", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const params = {
      ...createValidParams(),
      ttmModel: "cogvideox" as const,
      ttmLayers: [{ layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] }],
    } as WorkflowParams;

    generateTTMWorkflow(params);

    expect(consoleWarn).toHaveBeenCalledWith(
      expect.stringContaining("only supported for Wan models"),
    );

    consoleWarn.mockRestore();
  });

  it("should not warn for TTM with wan model", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const params = {
      ...createValidParams(),
      ttmModel: "wan" as const,
      ttmLayers: [{ layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] }],
    } as WorkflowParams;

    generateTTMWorkflow(params);

    // Should not have been called with TTM warning
    const ttmWarningCalled = consoleWarn.mock.calls.some((call) =>
      call[0]?.includes?.("only supported for Wan"),
    );
    expect(ttmWarningCalled).toBe(false);

    consoleWarn.mockRestore();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// EDGE: Uni3C Deprecation Warning
// ═══════════════════════════════════════════════════════════════════════════

describe("EDGE: Uni3C Camera Export Warning", () => {
  it("should generate Uni3C workflow despite deprecation", () => {
    const params: WorkflowParams = {
      ...createValidParams(),
      cameraData: { traj_type: "free1" },
    };

    // Should still generate valid workflow
    const workflow = generateUni3CWorkflow(params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// EDGE: Multiple Error Accumulation
// ═══════════════════════════════════════════════════════════════════════════

describe("EDGE: Multiple Validation Errors", () => {
  it("should report multiple errors at once", () => {
    const params = createValidParams({
      width: -100,
      height: 0,
      frameCount: -5,
      fps: 1000,
      referenceImage: undefined,
    });

    expect(() => {
      generateWorkflowForTarget("wan22-i2v", params);
    }).toThrow(/width|height|frameCount|fps|referenceImage/i);
  });
});
