/**
 * Expression Validator Tests
 *
 * Tests the DoS protection system that blocks infinite loops
 * in user expressions via Worker-based timeout.
 */

import { describe, expect, it } from "vitest";
import {
  isExpressionSafe,
  validateProjectExpressions,
} from "@/services/expressions/expressionValidator";
import type { AnimatableProperty, PropertyExpression } from "@/types/animation";
import type {
  Composition,
  CompositionSettings,
  LatticeProject,
  Layer,
  SolidLayerData,
} from "@/types/project";
import type { LayerTransform } from "@/types/transform";

// Helper to create a minimal AnimatableProperty
function createAnimatableProperty<T>(
  value: T,
  type: "number" | "position" | "color" | "enum" | "vector3" = "number",
  expression?: PropertyExpression,
): AnimatableProperty<T> {
  return {
    id: `prop_${Math.random().toString(36).slice(2)}`,
    name: "Test Property",
    type,
    value,
    animated: false,
    keyframes: [],
    expression,
  };
}

// Helper to create a minimal layer transform
function createTransform(
  positionExpression?: PropertyExpression,
): LayerTransform {
  return {
    position: createAnimatableProperty(
      { x: 0, y: 0, z: 0 },
      "position",
      positionExpression,
    ),
    scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }, "position"),
    rotation: createAnimatableProperty(0, "number"),
    origin: createAnimatableProperty({ x: 0.5, y: 0.5, z: 0 }, "position"),
  };
}

// Helper to create a minimal solid layer
function createSolidLayer(
  id: string,
  name: string,
  positionExpression?: PropertyExpression,
): Layer {
  const solidData: SolidLayerData = {
    color: "#ff0000",
    width: 1920,
    height: 1080,
  };

  return {
    id,
    name,
    type: "solid",
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 300,
    parentId: null,
    blendMode: "normal",
    opacity: createAnimatableProperty(100, "number"),
    transform: createTransform(positionExpression),
    properties: [],
    effects: [],
    data: solidData,
  };
}

// Helper to create a minimal composition
function createComposition(
  id: string,
  name: string,
  layers: Layer[],
): Composition {
  const settings: CompositionSettings = {
    width: 1920,
    height: 1080,
    frameCount: 300,
    fps: 30,
    duration: 10,
    backgroundColor: "#000000",
    autoResizeToContent: false,
    frameBlendingEnabled: false,
  };

  return {
    id,
    name,
    settings,
    layers,
    currentFrame: 0,
    isNestedComp: false,
  };
}

// Helper to create a minimal project
function createProject(layers: Layer[]): LatticeProject {
  const comp = createComposition("main", "Main Composition", layers);
  const settings: CompositionSettings = {
    width: 1920,
    height: 1080,
    frameCount: 300,
    fps: 30,
    duration: 10,
    backgroundColor: "#000000",
    autoResizeToContent: false,
    frameBlendingEnabled: false,
  };

  return {
    version: "1.0.0",
    meta: {
      name: "Test Project",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    compositions: { main: comp },
    mainCompositionId: "main",
    composition: settings,
    assets: {},
    layers, // Legacy
    currentFrame: 0,
  };
}

// Helper to create malicious expression
function createMaliciousExpression(code: string): PropertyExpression {
  return {
    enabled: true,
    type: "custom",
    name: "Malicious",
    params: { code },
  };
}

// Skip tests in non-browser environment (Workers not available in Node)
const describeIfWorker =
  typeof Worker !== "undefined" ? describe : describe.skip;

describeIfWorker("Expression Validator - DoS Protection", () => {
  describe("isExpressionSafe - Infinite Loops", () => {
    it("should BLOCK while(true){}", async () => {
      const result = await isExpressionSafe("while(true){}");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK while(1){}", async () => {
      const result = await isExpressionSafe("while(1){}");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK for(;;){}", async () => {
      const result = await isExpressionSafe("for(;;){}");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK do{}while(true)", async () => {
      const result = await isExpressionSafe("do{}while(true)");
      expect(result).toBe(false);
    }, 10000);
  });

  describe("isExpressionSafe - Recursion Bombs", () => {
    it("should BLOCK (function f(){f()})()", async () => {
      const result = await isExpressionSafe("(function f(){f()})()");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK arrow recursion", async () => {
      const result = await isExpressionSafe("let f=()=>f();f()");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK Y-combinator style", async () => {
      const result = await isExpressionSafe("(f=>f(f))(f=>f(f))");
      expect(result).toBe(false);
    }, 10000);
  });

  describe("isExpressionSafe - Memory Bombs", () => {
    // Note: 1e7 completes in <100ms (not a DoS), 1e8 takes ~18s (real DoS)
    it("should ALLOW small string repeat (1e7 completes fast)", async () => {
      const result = await isExpressionSafe('"a".repeat(1e7)');
      expect(result).toBe(true); // 1e7 completes in <1ms, not a threat
    }, 10000);

    it("should ALLOW small array allocation (1e7 completes fast)", async () => {
      const result = await isExpressionSafe("Array(1e7).fill(0)");
      expect(result).toBe(true); // 1e7 completes in ~36ms, not a threat
    }, 10000);

    it("should BLOCK large array allocation (1e8 takes 18+ seconds)", async () => {
      const result = await isExpressionSafe("Array(1e8).fill(0)");
      expect(result).toBe(false); // 1e8 takes ~18s, will timeout
    }, 10000);
  });

  describe("isExpressionSafe - SES Escape Attempts", () => {
    it("should BLOCK Function constructor", async () => {
      const result = await isExpressionSafe('Function("return 1")()');
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK new Function", async () => {
      const result = await isExpressionSafe('new Function("return 1")()');
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK eval", async () => {
      const result = await isExpressionSafe('eval("1")');
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK setTimeout", async () => {
      const result = await isExpressionSafe("setTimeout(()=>{},0)");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK globalThis access", async () => {
      const result = await isExpressionSafe("globalThis.constructor");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK window access", async () => {
      const result = await isExpressionSafe("window.location");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK constructor escape", async () => {
      const result = await isExpressionSafe(
        'this.constructor.constructor("return this")()',
      );
      expect(result).toBe(false);
    }, 10000);
  });

  describe("isExpressionSafe - Obfuscation Bypasses", () => {
    it("should BLOCK while with comment", async () => {
      const result = await isExpressionSafe("while/**/(true){}");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK while with expression", async () => {
      const result = await isExpressionSafe("while(1+0){}");
      expect(result).toBe(false);
    }, 10000);

    it("should BLOCK variable indirection", async () => {
      const result = await isExpressionSafe("let x=true;while(x){}");
      expect(result).toBe(false);
    }, 10000);
  });

  describe("isExpressionSafe - Valid Expressions (must ALLOW)", () => {
    it("should ALLOW value * 2", async () => {
      const result = await isExpressionSafe("value * 2");
      expect(result).toBe(true);
    });

    it("should ALLOW sin(time * PI)", async () => {
      const result = await isExpressionSafe("sin(time * PI)");
      expect(result).toBe(true);
    });

    it("should ALLOW frame / 30", async () => {
      const result = await isExpressionSafe("frame / 30");
      expect(result).toBe(true);
    });

    it("should ALLOW bounded loop", async () => {
      const result = await isExpressionSafe(
        "let sum=0;for(let i=0;i<10;i++)sum+=i;sum",
      );
      expect(result).toBe(true);
    });

    it("should ALLOW ternary operator", async () => {
      const result = await isExpressionSafe("value > 0 ? 1 : 0");
      expect(result).toBe(true);
    });

    it("should ALLOW random() (seeded)", async () => {
      const result = await isExpressionSafe("random() * 100");
      expect(result).toBe(true);
    });

    it("should ALLOW small array operations", async () => {
      const result = await isExpressionSafe("[1,2,3].reduce((a,b)=>a+b,0)");
      expect(result).toBe(true);
    });

    it("should ALLOW small string operations", async () => {
      const result = await isExpressionSafe('"ab".repeat(5)');
      expect(result).toBe(true);
    });
  });

  describe("validateProjectExpressions", () => {
    it("should BLOCK project with malicious expression in position", async () => {
      const maliciousExpr = createMaliciousExpression("while(true){}");
      const layer = createSolidLayer(
        "layer1",
        "Malicious Layer",
        maliciousExpr,
      );
      const project = createProject([layer]);

      const result = await validateProjectExpressions(project);

      expect(result.valid).toBe(false);
      expect(result.dangerous.length).toBeGreaterThan(0);
      expect(result.dangerous[0].reason).toBe("timeout");
    }, 15000);

    it("should BLOCK project with recursive bomb", async () => {
      const maliciousExpr = createMaliciousExpression("(function f(){f()})()");
      const layer = createSolidLayer(
        "layer1",
        "Recursive Layer",
        maliciousExpr,
      );
      const project = createProject([layer]);

      const result = await validateProjectExpressions(project);

      expect(result.valid).toBe(false);
      expect(result.dangerous.length).toBeGreaterThan(0);
    }, 15000);

    it("should ALLOW project with safe expressions", async () => {
      const safeExpr: PropertyExpression = {
        enabled: true,
        type: "custom",
        name: "Wiggle",
        params: { code: "sin(time * PI) * 100" },
      };
      const layer = createSolidLayer("layer1", "Safe Layer", safeExpr);
      const project = createProject([layer]);

      const result = await validateProjectExpressions(project);

      expect(result.valid).toBe(true);
      expect(result.dangerous.length).toBe(0);
    }, 10000);

    it("should ALLOW project with no custom expressions", async () => {
      const layer = createSolidLayer("layer1", "Plain Layer");
      const project = createProject([layer]);

      const result = await validateProjectExpressions(project);

      expect(result.valid).toBe(true);
      expect(result.dangerous.length).toBe(0);
    });

    it("should ALLOW project with preset expressions (not custom)", async () => {
      const presetExpr: PropertyExpression = {
        enabled: true,
        type: "preset", // Presets are hardcoded, safe
        name: "wiggle",
        params: { frequency: 2, amplitude: 10 },
      };
      const layer = createSolidLayer("layer1", "Preset Layer", presetExpr);
      const project = createProject([layer]);

      const result = await validateProjectExpressions(project);

      expect(result.valid).toBe(true);
    });

    it("should count total expressions validated", async () => {
      const expr1 = createMaliciousExpression("value * 2"); // safe
      const expr2 = createMaliciousExpression("frame + 1"); // safe
      const layer1 = createSolidLayer("layer1", "Layer 1", expr1);
      const layer2 = createSolidLayer("layer2", "Layer 2", expr2);
      const project = createProject([layer1, layer2]);

      const result = await validateProjectExpressions(project);

      expect(result.total).toBe(2);
      expect(result.validated).toBe(2);
      expect(result.valid).toBe(true);
    });
  });
});

// Fallback tests for Node environment
describe("Expression Validator - Node Environment Fallback", () => {
  it("should gracefully handle missing Worker support", async () => {
    if (typeof Worker === "undefined") {
      // In Node, isWorkerAvailable() returns false
      // isExpressionSafe returns true (can't validate without workers)
      const result = await isExpressionSafe("while(true){}");
      expect(result).toBe(true); // Optimistic when can't validate
    }
  });
});
