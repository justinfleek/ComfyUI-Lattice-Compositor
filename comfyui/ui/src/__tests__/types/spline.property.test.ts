/**
 * Property tests for ui/src/types/spline.ts
 * Tests: controlPointToAnimatable, animatableToControlPoint,
 *        createDefaultSplineData, createDefaultPathLayerData
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  controlPointToAnimatable,
  animatableToControlPoint,
  createDefaultSplineData,
  createDefaultPathLayerData,
  type ControlPoint,
} from "@/types/spline";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const handleArb = fc.oneof(
  fc.constant(null),
  fc.record({
    x: fc.double({ min: -1000, max: 1000, noNaN: true }),
    y: fc.double({ min: -1000, max: 1000, noNaN: true }),
  })
);

const pointTypeArb = fc.constantFrom("corner", "smooth", "symmetric") as fc.Arbitrary<"corner" | "smooth" | "symmetric">;

const controlPointArb: fc.Arbitrary<ControlPoint> = fc.record({
  id: fc.string({ minLength: 1, maxLength: 20 }),
  x: fc.double({ min: -10000, max: 10000, noNaN: true }),
  y: fc.double({ min: -10000, max: 10000, noNaN: true }),
  depth: fc.option(fc.double({ min: 0, max: 1, noNaN: true }), { nil: undefined }),
  handleIn: handleArb,
  handleOut: handleArb,
  type: pointTypeArb,
  group: fc.option(fc.string({ minLength: 1, maxLength: 20 }), { nil: undefined }),
});

// ════════════════════════════════════════════════════════════════════════════
// controlPointToAnimatable TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: controlPointToAnimatable", () => {
  it("preserves id", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.id).toBe(cp.id);
      })
    );
  });

  it("preserves x value", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.x.value).toBe(cp.x);
      })
    );
  });

  it("preserves y value", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.y.value).toBe(cp.y);
      })
    );
  });

  it("preserves type", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.type).toBe(cp.type);
      })
    );
  });

  it("preserves group", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.group).toBe(cp.group);
      })
    );
  });

  it("converts depth to AnimatableProperty when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        if (cp.depth !== undefined) {
          expect(acp.depth).toBeDefined();
          expect(acp.depth?.value).toBe(cp.depth);
        } else {
          expect(acp.depth).toBeUndefined();
        }
      })
    );
  });

  it("converts handleIn to AnimatableHandle when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        if (cp.handleIn) {
          expect(acp.handleIn).not.toBeNull();
          expect(acp.handleIn?.x.value).toBe(cp.handleIn.x);
          expect(acp.handleIn?.y.value).toBe(cp.handleIn.y);
        } else {
          expect(acp.handleIn).toBeNull();
        }
      })
    );
  });

  it("converts handleOut to AnimatableHandle when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        if (cp.handleOut) {
          expect(acp.handleOut).not.toBeNull();
          expect(acp.handleOut?.x.value).toBe(cp.handleOut.x);
          expect(acp.handleOut?.y.value).toBe(cp.handleOut.y);
        } else {
          expect(acp.handleOut).toBeNull();
        }
      })
    );
  });

  it("x property is not animated by default", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.x.animated).toBe(false);
        expect(acp.x.keyframes).toEqual([]);
      })
    );
  });

  it("y property is not animated by default", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        expect(acp.y.animated).toBe(false);
        expect(acp.y.keyframes).toEqual([]);
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// animatableToControlPoint TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: animatableToControlPoint", () => {
  it("preserves id", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.id).toBe(cp.id);
      })
    );
  });

  it("preserves type", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.type).toBe(cp.type);
      })
    );
  });

  it("preserves group", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.group).toBe(cp.group);
      })
    );
  });

  it("extracts current x value", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.x).toBe(cp.x);
      })
    );
  });

  it("extracts current y value", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.y).toBe(cp.y);
      })
    );
  });

  it("extracts depth when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        expect(result.depth).toBe(cp.depth);
      })
    );
  });

  it("extracts handleIn when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        if (cp.handleIn) {
          expect(result.handleIn).toEqual(cp.handleIn);
        } else {
          expect(result.handleIn).toBeNull();
        }
      })
    );
  });

  it("extracts handleOut when present", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        if (cp.handleOut) {
          expect(result.handleOut).toEqual(cp.handleOut);
        } else {
          expect(result.handleOut).toBeNull();
        }
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // round
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: Round-trip conversion", () => {
  it("controlPoint → animatable → controlPoint preserves all data", () => {
    fc.assert(
      fc.property(controlPointArb, (cp) => {
        const acp = controlPointToAnimatable(cp);
        const result = animatableToControlPoint(acp);
        
        expect(result.id).toBe(cp.id);
        expect(result.x).toBe(cp.x);
        expect(result.y).toBe(cp.y);
        expect(result.depth).toBe(cp.depth);
        expect(result.type).toBe(cp.type);
        expect(result.group).toBe(cp.group);
        
        if (cp.handleIn) {
          expect(result.handleIn).toEqual(cp.handleIn);
        } else {
          expect(result.handleIn).toBeNull();
        }
        
        if (cp.handleOut) {
          expect(result.handleOut).toEqual(cp.handleOut);
        } else {
          expect(result.handleOut).toBeNull();
        }
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultSplineData TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultSplineData", () => {
  it("returns SplineData with all required properties", () => {
    const spline = createDefaultSplineData();
    
    expect(spline).toHaveProperty("pathData");
    expect(spline).toHaveProperty("controlPoints");
    expect(spline).toHaveProperty("closed");
    expect(spline).toHaveProperty("stroke");
    expect(spline).toHaveProperty("strokeWidth");
    expect(spline).toHaveProperty("fill");
  });

  it("pathData defaults to empty string", () => {
    const spline = createDefaultSplineData();
    expect(spline.pathData).toBe("");
  });

  it("controlPoints defaults to empty array", () => {
    const spline = createDefaultSplineData();
    expect(spline.controlPoints).toEqual([]);
  });

  it("closed defaults to false", () => {
    const spline = createDefaultSplineData();
    expect(spline.closed).toBe(false);
  });

  it("stroke defaults to white (#ffffff)", () => {
    const spline = createDefaultSplineData();
    expect(spline.stroke).toBe("#ffffff");
  });

  it("strokeWidth defaults to 2", () => {
    const spline = createDefaultSplineData();
    expect(spline.strokeWidth).toBe(2);
  });

  it("fill defaults to empty string (no fill)", () => {
    const spline = createDefaultSplineData();
    expect(spline.fill).toBe("");
  });

  it("is deterministic", () => {
    const s1 = createDefaultSplineData();
    const s2 = createDefaultSplineData();
    expect(s1).toEqual(s2);
  });

  it("returns new object each call", () => {
    const s1 = createDefaultSplineData();
    const s2 = createDefaultSplineData();
    expect(s1).not.toBe(s2);
    expect(s1.controlPoints).not.toBe(s2.controlPoints);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultPathLayerData TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultPathLayerData", () => {
  it("returns PathLayerData with all required properties", () => {
    const path = createDefaultPathLayerData();
    
    expect(path).toHaveProperty("pathData");
    expect(path).toHaveProperty("controlPoints");
    expect(path).toHaveProperty("closed");
    expect(path).toHaveProperty("showGuide");
    expect(path).toHaveProperty("guideColor");
    expect(path).toHaveProperty("guideDashPattern");
  });

  it("pathData defaults to empty string", () => {
    const path = createDefaultPathLayerData();
    expect(path.pathData).toBe("");
  });

  it("controlPoints defaults to empty array", () => {
    const path = createDefaultPathLayerData();
    expect(path.controlPoints).toEqual([]);
  });

  it("closed defaults to false", () => {
    const path = createDefaultPathLayerData();
    expect(path.closed).toBe(false);
  });

  it("showGuide defaults to true", () => {
    const path = createDefaultPathLayerData();
    expect(path.showGuide).toBe(true);
  });

  it("guideColor defaults to cyan (#00FFFF)", () => {
    const path = createDefaultPathLayerData();
    expect(path.guideColor).toBe("#00FFFF");
  });

  it("guideDashPattern defaults to [5, 5]", () => {
    const path = createDefaultPathLayerData();
    expect(path.guideDashPattern).toEqual([5, 5]);
  });

  it("is deterministic", () => {
    const p1 = createDefaultPathLayerData();
    const p2 = createDefaultPathLayerData();
    expect(p1).toEqual(p2);
  });

  it("returns new object each call", () => {
    const p1 = createDefaultPathLayerData();
    const p2 = createDefaultPathLayerData();
    expect(p1).not.toBe(p2);
    expect(p1.controlPoints).not.toBe(p2.controlPoints);
    expect(p1.guideDashPattern).not.toBe(p2.guideDashPattern);
  });
});
