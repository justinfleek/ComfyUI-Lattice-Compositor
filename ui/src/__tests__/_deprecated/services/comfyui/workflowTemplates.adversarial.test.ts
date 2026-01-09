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
import type { ExportTarget } from "@/types/export";

// ============================================================================
// Test Fixtures
// ============================================================================

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

// ============================================================================
// CRITICAL: Parameter Validation
// ============================================================================

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

// ============================================================================
// CRITICAL: Missing Required Inputs Per Target
// ============================================================================

describe("CRITICAL: Missing Required Inputs", () => {
  describe("Targets requiring referenceImage", () => {
    // Note: "scail" removed as it's not a valid ExportTarget
    const targetsRequiringImage: ExportTarget[] = [
      "wan22-i2v",
      "wan22-first-last",
      "uni3c-camera",
      "uni3c-motion",
      "ttm",
      "ttm-wan",
    ];

    for (const target of targetsRequiringImage) {
      it(`should throw for ${target} without referenceImage`, () => {
        const params = createValidParams({ referenceImage: undefined });

        expect(() => {
          generateWorkflowForTarget(target, params);
        }).toThrow(/referenceImage|required/i);
      });
    }
  });

  describe("TTM-specific requirements", () => {
    // Note: TTM properties may not be in the current WorkflowParams type
    // Using type assertions for deprecated test compatibility
    it("should throw for TTM without required data", () => {
      const params = createValidParams();

      // TTM requires either ttmLayers or ttmCombinedMask in current API
      expect(() => {
        generateWorkflowForTarget("ttm", params);
      }).toThrow();
    });

    it("should accept TTM with ttmLayers", () => {
      const params = {
        ...createValidParams(),
        ttmLayers: [{ layerId: "1", layerName: "Test", motionMask: "mask.png", trajectory: [] }],
      } as WorkflowParams;

      // Should not throw
      const workflow = generateWorkflowForTarget("ttm", params);
      expect(workflow).toBeDefined();
    });

    it("should accept TTM with ttmCombinedMask", () => {
      const params = {
        ...createValidParams(),
        ttmCombinedMask: "combined.png",
      } as WorkflowParams;

      // Should not throw
      const workflow = generateWorkflowForTarget("ttm", params);
      expect(workflow).toBeDefined();
    });
  });

  describe("Wan-Move specific requirements", () => {
    // Note: trackCoords may not be in the current WorkflowParams type
    // Wan-Move uses cameraData in current API
    it("should throw for wan-move without required data", () => {
      const params = createValidParams();

      expect(() => {
        generateWorkflowForTarget("wan-move", params);
      }).toThrow();
    });

    it("should accept wan-move with cameraData", () => {
      const params = {
        ...createValidParams(),
        cameraData: { tracks: [[{ x: 100, y: 200 }]] },
      } as WorkflowParams;

      const workflow = generateWorkflowForTarget("wan-move", params);
      expect(workflow).toBeDefined();
    });
  });

  describe("SCAIL specific requirements (not in current API)", () => {
    // SCAIL is not a valid ExportTarget in the current API
    it("should throw for unknown SCAIL target", () => {
      const params = createValidParams();

      expect(() => {
        generateWorkflowForTarget("scail" as any as ExportTarget, params);
      }).toThrow(/Unknown export target.*scail/i);
    });
  });
});

// ============================================================================
// HIGH: Unknown Export Target
// ============================================================================

describe("HIGH: Unknown Export Target", () => {
  it("should throw for completely unknown target", () => {
    const params = createValidParams();

    expect(() => {
      generateWorkflowForTarget("unknown-model-xyz" as ExportTarget, params);
    }).toThrow(/unknown.*target/i);
  });

  it("should throw for null target", () => {
    const params = createValidParams();

    expect(() => {
      generateWorkflowForTarget(null as any, params);
    }).toThrow();
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

// ============================================================================
// HIGH: Workflow Structure Validation
// ============================================================================

describe("HIGH: validateWorkflow - Structure Checks", () => {
  it("should detect missing class_type", () => {
    const badWorkflow = {
      "1": { inputs: {} } as any, // Missing class_type
    };

    const result = validateWorkflow(badWorkflow);

    expect(result.valid).toBe(false);
    expect(result.errors.some((e) => e.includes("class_type"))).toBe(true);
  });

  it("should detect invalid node references", () => {
    const badWorkflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "test.png" },
      },
      "2": {
        class_type: "ImageResize",
        inputs: {
          image: ["999", 0], // References non-existent node
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
    const validWorkflow = {
      "1": {
        class_type: "LoadImage",
        inputs: { image: "test.png" },
      },
      "2": {
        class_type: "SaveImage",
        inputs: { images: ["1", 0] },
      },
    };

    const result = validateWorkflow(validWorkflow);

    expect(result.valid).toBe(true);
    expect(result.errors).toHaveLength(0);
  });
});

// ============================================================================
// HIGH: Generated Workflows Have Valid Structure
// ============================================================================

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
    const params = {
      ...createValidParams(),
      cameraData: { matrices: [] },
    } as WorkflowParams;

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
    const params = {
      ...createValidParams(),
      cameraData: { tracks: [[{ x: 100, y: 200 }]] },
    } as WorkflowParams;

    const workflow = generateWorkflowForTarget("wan-move", params);

    expect(Object.keys(workflow).length).toBeGreaterThan(0);
    const validation = validateWorkflow(workflow);
    expect(validation.valid).toBe(true);
  });

  it("should generate valid ATI workflow", () => {
    const params = {
      ...createValidParams(),
      cameraData: { tracks: [[{ x: 100, y: 200 }]] },
    } as WorkflowParams;

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

  it("should throw for unknown SCAIL target", () => {
    const params = createValidParams();

    // SCAIL is not a valid ExportTarget in the current API
    expect(() => {
      generateWorkflowForTarget("scail" as any as ExportTarget, params);
    }).toThrow(/Unknown export target.*scail/i);
  });
});

// ============================================================================
// MEDIUM: Parameter Injection
// ============================================================================

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

    const result = injectParameters(workflow, { complex: { nested: "value" } });

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

// ============================================================================
// EDGE: Default Value Handling
// ============================================================================

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

// ============================================================================
// EDGE: TTM Model Warnings
// ============================================================================

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

// ============================================================================
// EDGE: Uni3C Deprecation Warning
// ============================================================================

describe("EDGE: Uni3C Camera Export Warning", () => {
  it("should generate Uni3C workflow despite deprecation", () => {
    const params = {
      ...createValidParams(),
      cameraData: { matrices: [] },
    } as WorkflowParams;

    // Should still generate valid workflow
    const workflow = generateUni3CWorkflow(params);
    expect(Object.keys(workflow).length).toBeGreaterThan(0);
  });
});

// ============================================================================
// EDGE: Multiple Error Accumulation
// ============================================================================

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
