/**
 * Property tests for ui/src/types/shapes.ts
 * Tests: All 30 factory functions for shapes and operators
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultAnimatablePoint,
  createDefaultAnimatableNumber,
  createDefaultAnimatableColor,
  createDefaultAnimatablePath,
  createDefaultAnimatableNumberArray,
  createDefaultShapeTransform,
  createDefaultRectangle,
  createDefaultEllipse,
  createDefaultPolygon,
  createDefaultStar,
  createDefaultPath,
  createDefaultFill,
  createDefaultStroke,
  createDefaultTrimPaths,
  createDefaultMergePaths,
  createDefaultOffsetPaths,
  createDefaultPuckerBloat,
  createDefaultWigglePaths,
  createDefaultZigZag,
  createDefaultTwist,
  createDefaultRoundedCorners,
  createDefaultRepeater,
  createDefaultGroup,
  createDefaultExtrude,
  createDefaultTrace,
  createDefaultSimplifyPath,
  createDefaultSmoothPath,
  createDefaultGradientFill,
  createDefaultGradientStroke,
  createDefaultShapeLayerData,
} from "@/types/shapes";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// // helper // function // to // verify // animatable // property // structure
// ═══════════════════════════════════════════════════════════════════════════

import type { AnimatableProperty, PropertyValue } from "@/types/animation";

function verifyAnimatableProperty(prop: AnimatableProperty<PropertyValue>, expectedType?: string) {
  expect(prop).toHaveProperty("id");
  expect(prop).toHaveProperty("name");
  expect(prop).toHaveProperty("type");
  expect(prop).toHaveProperty("value");
  expect(prop).toHaveProperty("animated");
  expect(prop).toHaveProperty("keyframes");
  expect(prop.animated).toBe(false);
  expect(prop.keyframes).toEqual([]);
  if (expectedType) {
    expect(prop.type).toBe(expectedType);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultAnimatablePoint TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultAnimatablePoint", () => {
  it("returns AnimatableProperty with position type", () => {
    const prop = createDefaultAnimatablePoint();
    verifyAnimatableProperty(prop, "position");
  });

  it("value defaults to { x: 0, y: 0 }", () => {
    const prop = createDefaultAnimatablePoint();
    expect(prop.value).toEqual({ x: 0, y: 0 });
  });

  it("name defaults to 'Point'", () => {
    const prop = createDefaultAnimatablePoint();
    expect(prop.name).toBe("Point");
  });

  it("accepts custom name", () => {
    fc.assert(
      fc.property(fc.string({ minLength: 1, maxLength: 50 }), (name) => {
        const prop = createDefaultAnimatablePoint(name);
        expect(prop.name).toBe(name);
      })
    );
  });

  it("generates unique ids", () => {
    const ids = new Set<string>();
    for (let i = 0; i < 100; i++) {
      ids.add(createDefaultAnimatablePoint().id);
    }
    expect(ids.size).toBe(100);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultAnimatableNumber TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultAnimatableNumber", () => {
  it("returns AnimatableProperty with number type", () => {
    const prop = createDefaultAnimatableNumber();
    verifyAnimatableProperty(prop, "number");
  });

  it("value defaults to 0", () => {
    const prop = createDefaultAnimatableNumber();
    expect(prop.value).toBe(0);
  });

  it("accepts custom value", () => {
    fc.assert(
      fc.property(fc.double({ noNaN: true, min: -1e6, max: 1e6 }), (value) => {
        const prop = createDefaultAnimatableNumber(value);
        expect(prop.value).toBe(value);
      })
    );
  });

  it("accepts custom name", () => {
    fc.assert(
      fc.property(fc.string({ minLength: 1, maxLength: 50 }), (name) => {
        const prop = createDefaultAnimatableNumber(0, name);
        expect(prop.name).toBe(name);
      })
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultAnimatableColor TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultAnimatableColor", () => {
  it("returns AnimatableProperty with color type", () => {
    const prop = createDefaultAnimatableColor();
    verifyAnimatableProperty(prop, "color");
  });

  it("defaults to white (255, 255, 255, 1)", () => {
    const prop = createDefaultAnimatableColor();
    expect(prop.value).toEqual({ r: 255, g: 255, b: 255, a: 1 });
  });

  it("accepts custom RGBA values", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        fc.double({ min: 0, max: 1, noNaN: true }),
        (r, g, b, a) => {
          const prop = createDefaultAnimatableColor(r, g, b, a);
          expect(prop.value).toEqual({ r, g, b, a });
        }
      )
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultAnimatablePath TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultAnimatablePath", () => {
  it("returns AnimatableProperty with position type", () => {
    const prop = createDefaultAnimatablePath();
    verifyAnimatableProperty(prop, "position");
  });

  it("defaults to empty path", () => {
    const prop = createDefaultAnimatablePath();
    expect(prop.value).toEqual({ vertices: [], closed: false });
  });

  it("accepts custom name", () => {
    fc.assert(
      fc.property(fc.string({ minLength: 1, maxLength: 50 }), (name) => {
        const prop = createDefaultAnimatablePath(name);
        expect(prop.name).toBe(name);
      })
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultAnimatableNumberArray TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultAnimatableNumberArray", () => {
  it("returns AnimatableProperty with number type", () => {
    const prop = createDefaultAnimatableNumberArray();
    verifyAnimatableProperty(prop, "number");
  });

  it("defaults to empty array", () => {
    const prop = createDefaultAnimatableNumberArray();
    expect(prop.value).toEqual([]);
  });

  it("accepts custom array", () => {
    fc.assert(
      fc.property(fc.array(fc.double({ noNaN: true }), { maxLength: 10 }), (arr) => {
        const prop = createDefaultAnimatableNumberArray(arr);
        expect(prop.value).toEqual(arr);
      })
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultShapeTransform TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultShapeTransform", () => {
  it("has type 'transform'", () => {
    const t = createDefaultShapeTransform();
    expect(t.type).toBe("transform");
  });

  it("has all required properties", () => {
    const t = createDefaultShapeTransform();
    expect(t).toHaveProperty("anchorPoint");
    expect(t).toHaveProperty("position");
    expect(t).toHaveProperty("scale");
    expect(t).toHaveProperty("rotation");
    expect(t).toHaveProperty("skew");
    expect(t).toHaveProperty("skewAxis");
    expect(t).toHaveProperty("opacity");
  });

  it("scale defaults to (100, 100)", () => {
    const t = createDefaultShapeTransform();
    expect(t.scale.value).toEqual({ x: 100, y: 100 });
  });

  it("opacity defaults to 100", () => {
    const t = createDefaultShapeTransform();
    expect(t.opacity.value).toBe(100);
  });

  it("rotation defaults to 0", () => {
    const t = createDefaultShapeTransform();
    expect(t.rotation.value).toBe(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultRectangle TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultRectangle", () => {
  it("has type 'rectangle'", () => {
    const r = createDefaultRectangle();
    expect(r.type).toBe("rectangle");
  });

  it("has all required properties", () => {
    const r = createDefaultRectangle();
    expect(r).toHaveProperty("position");
    expect(r).toHaveProperty("size");
    expect(r).toHaveProperty("roundness");
    expect(r).toHaveProperty("direction");
  });

  it("size defaults to (100, 100)", () => {
    const r = createDefaultRectangle();
    expect(r.size.value).toEqual({ x: 100, y: 100 });
  });

  it("roundness defaults to 0", () => {
    const r = createDefaultRectangle();
    expect(r.roundness.value).toBe(0);
  });

  it("direction defaults to 1", () => {
    const r = createDefaultRectangle();
    expect(r.direction).toBe(1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultEllipse TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultEllipse", () => {
  it("has type 'ellipse'", () => {
    const e = createDefaultEllipse();
    expect(e.type).toBe("ellipse");
  });

  it("size defaults to (100, 100)", () => {
    const e = createDefaultEllipse();
    expect(e.size.value).toEqual({ x: 100, y: 100 });
  });

  it("direction defaults to 1", () => {
    const e = createDefaultEllipse();
    expect(e.direction).toBe(1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultPolygon TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultPolygon", () => {
  it("has type 'polygon'", () => {
    const p = createDefaultPolygon();
    expect(p.type).toBe("polygon");
  });

  it("points defaults to 6", () => {
    const p = createDefaultPolygon();
    expect(p.points.value).toBe(6);
  });

  it("outerRadius defaults to 50", () => {
    const p = createDefaultPolygon();
    expect(p.outerRadius.value).toBe(50);
  });

  it("outerRoundness defaults to 0", () => {
    const p = createDefaultPolygon();
    expect(p.outerRoundness.value).toBe(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultStar TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultStar", () => {
  it("has type 'star'", () => {
    const s = createDefaultStar();
    expect(s.type).toBe("star");
  });

  it("points defaults to 5", () => {
    const s = createDefaultStar();
    expect(s.points.value).toBe(5);
  });

  it("outerRadius defaults to 50", () => {
    const s = createDefaultStar();
    expect(s.outerRadius.value).toBe(50);
  });

  it("innerRadius defaults to 25", () => {
    const s = createDefaultStar();
    expect(s.innerRadius.value).toBe(25);
  });

  it("innerRadius is half of outerRadius", () => {
    const s = createDefaultStar();
    expect(s.innerRadius.value).toBe(s.outerRadius.value / 2);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultPath TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultPath", () => {
  it("has type 'path'", () => {
    const p = createDefaultPath();
    expect(p.type).toBe("path");
  });

  it("path is empty bezier path", () => {
    const p = createDefaultPath();
    expect(p.path.value).toEqual({ vertices: [], closed: false });
  });

  it("direction defaults to 1", () => {
    const p = createDefaultPath();
    expect(p.direction).toBe(1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultFill TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultFill", () => {
  it("has type 'fill'", () => {
    const f = createDefaultFill();
    expect(f.type).toBe("fill");
  });

  it("color defaults to white", () => {
    const f = createDefaultFill();
    expect(f.color.value).toEqual({ r: 255, g: 255, b: 255, a: 1 });
  });

  it("opacity defaults to 100", () => {
    const f = createDefaultFill();
    expect(f.opacity.value).toBe(100);
  });

  it("fillRule defaults to 'nonzero'", () => {
    const f = createDefaultFill();
    expect(f.fillRule).toBe("nonzero");
  });

  it("blendMode defaults to 'normal'", () => {
    const f = createDefaultFill();
    expect(f.blendMode).toBe("normal");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultStroke TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultStroke", () => {
  it("has type 'stroke'", () => {
    const s = createDefaultStroke();
    expect(s.type).toBe("stroke");
  });

  it("color defaults to white", () => {
    const s = createDefaultStroke();
    expect(s.color.value).toEqual({ r: 255, g: 255, b: 255, a: 1 });
  });

  it("width defaults to 2", () => {
    const s = createDefaultStroke();
    expect(s.width.value).toBe(2);
  });

  it("lineCap defaults to 'round'", () => {
    const s = createDefaultStroke();
    expect(s.lineCap).toBe("round");
  });

  it("lineJoin defaults to 'round'", () => {
    const s = createDefaultStroke();
    expect(s.lineJoin).toBe("round");
  });

  it("has taper properties", () => {
    const s = createDefaultStroke();
    expect(s.taperEnabled).toBe(false);
    expect(s.taperStartLength).toBeDefined();
    expect(s.taperEndLength).toBeDefined();
    expect(s.taperStartWidth).toBeDefined();
    expect(s.taperEndWidth).toBeDefined();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultTrimPaths TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultTrimPaths", () => {
  it("has type 'trimPaths'", () => {
    const t = createDefaultTrimPaths();
    expect(t.type).toBe("trimPaths");
  });

  it("start defaults to 0", () => {
    const t = createDefaultTrimPaths();
    expect(t.start.value).toBe(0);
  });

  it("end defaults to 100", () => {
    const t = createDefaultTrimPaths();
    expect(t.end.value).toBe(100);
  });

  it("offset defaults to 0", () => {
    const t = createDefaultTrimPaths();
    expect(t.offset.value).toBe(0);
  });

  it("mode defaults to 'simultaneously'", () => {
    const t = createDefaultTrimPaths();
    expect(t.mode).toBe("simultaneously");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultMergePaths TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultMergePaths", () => {
  it("has type 'mergePaths'", () => {
    const m = createDefaultMergePaths();
    expect(m.type).toBe("mergePaths");
  });

  it("mode defaults to 'add'", () => {
    const m = createDefaultMergePaths();
    expect(m.mode).toBe("add");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultOffsetPaths TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultOffsetPaths", () => {
  it("has type 'offsetPaths'", () => {
    const o = createDefaultOffsetPaths();
    expect(o.type).toBe("offsetPaths");
  });

  it("amount defaults to 0", () => {
    const o = createDefaultOffsetPaths();
    expect(o.amount.value).toBe(0);
  });

  it("lineJoin defaults to 'miter'", () => {
    const o = createDefaultOffsetPaths();
    expect(o.lineJoin).toBe("miter");
  });

  it("copies defaults to 1", () => {
    const o = createDefaultOffsetPaths();
    expect(o.copies.value).toBe(1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultPuckerBloat TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultPuckerBloat", () => {
  it("has type 'puckerBloat'", () => {
    const p = createDefaultPuckerBloat();
    expect(p.type).toBe("puckerBloat");
  });

  it("amount defaults to 0", () => {
    const p = createDefaultPuckerBloat();
    expect(p.amount.value).toBe(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultWigglePaths TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultWigglePaths", () => {
  it("has type 'wigglePaths'", () => {
    const w = createDefaultWigglePaths();
    expect(w.type).toBe("wigglePaths");
  });

  it("size defaults to 10", () => {
    const w = createDefaultWigglePaths();
    expect(w.size.value).toBe(10);
  });

  it("detail defaults to 3", () => {
    const w = createDefaultWigglePaths();
    expect(w.detail.value).toBe(3);
  });

  it("points defaults to 'smooth'", () => {
    const w = createDefaultWigglePaths();
    expect(w.points).toBe("smooth");
  });

  it("has randomSeed", () => {
    const w = createDefaultWigglePaths();
    expect(w.randomSeed).toBe(12345);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultZigZag TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultZigZag", () => {
  it("has type 'zigZag'", () => {
    const z = createDefaultZigZag();
    expect(z.type).toBe("zigZag");
  });

  it("size defaults to 10", () => {
    const z = createDefaultZigZag();
    expect(z.size.value).toBe(10);
  });

  it("ridgesPerSegment defaults to 5", () => {
    const z = createDefaultZigZag();
    expect(z.ridgesPerSegment.value).toBe(5);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultTwist TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultTwist", () => {
  it("has type 'twist'", () => {
    const t = createDefaultTwist();
    expect(t.type).toBe("twist");
  });

  it("angle defaults to 0", () => {
    const t = createDefaultTwist();
    expect(t.angle.value).toBe(0);
  });

  it("has center point", () => {
    const t = createDefaultTwist();
    expect(t.center.value).toEqual({ x: 0, y: 0 });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultRoundedCorners TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultRoundedCorners", () => {
  it("has type 'roundedCorners'", () => {
    const r = createDefaultRoundedCorners();
    expect(r.type).toBe("roundedCorners");
  });

  it("radius defaults to 10", () => {
    const r = createDefaultRoundedCorners();
    expect(r.radius.value).toBe(10);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultRepeater TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultRepeater", () => {
  it("has type 'repeater'", () => {
    const r = createDefaultRepeater();
    expect(r.type).toBe("repeater");
  });

  it("copies defaults to 3", () => {
    const r = createDefaultRepeater();
    expect(r.copies.value).toBe(3);
  });

  it("offset defaults to 0", () => {
    const r = createDefaultRepeater();
    expect(r.offset.value).toBe(0);
  });

  it("composite defaults to 'below'", () => {
    const r = createDefaultRepeater();
    expect(r.composite).toBe("below");
  });

  it("transform position defaults to (100, 0)", () => {
    const r = createDefaultRepeater();
    expect(r.transform.position.value).toEqual({ x: 100, y: 0 });
  });

  it("transform scale defaults to (100, 100)", () => {
    const r = createDefaultRepeater();
    expect(r.transform.scale.value).toEqual({ x: 100, y: 100 });
  });

  it("has start and end opacity", () => {
    const r = createDefaultRepeater();
    expect(r.transform.startOpacity.value).toBe(100);
    expect(r.transform.endOpacity.value).toBe(100);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultGroup TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultGroup", () => {
  it("has type 'group'", () => {
    const g = createDefaultGroup();
    expect(g.type).toBe("group");
  });

  it("contents defaults to empty array", () => {
    const g = createDefaultGroup();
    expect(g.contents).toEqual([]);
  });

  it("has transform", () => {
    const g = createDefaultGroup();
    expect(g.transform).toBeDefined();
    expect(g.transform.type).toBe("transform");
  });

  it("blendMode defaults to 'normal'", () => {
    const g = createDefaultGroup();
    expect(g.blendMode).toBe("normal");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultExtrude TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultExtrude", () => {
  it("has type 'extrude'", () => {
    const e = createDefaultExtrude();
    expect(e.type).toBe("extrude");
  });

  it("depth defaults to 50", () => {
    const e = createDefaultExtrude();
    expect(e.depth.value).toBe(50);
  });

  it("bevelDepth defaults to 5", () => {
    const e = createDefaultExtrude();
    expect(e.bevelDepth.value).toBe(5);
  });

  it("bevelSegments defaults to 3", () => {
    const e = createDefaultExtrude();
    expect(e.bevelSegments).toBe(3);
  });

  it("capType defaults to 'flat'", () => {
    const e = createDefaultExtrude();
    expect(e.capType).toBe("flat");
  });

  it("has material with colors", () => {
    const e = createDefaultExtrude();
    expect(e.material).toBeDefined();
    expect(e.material.frontColor.value).toEqual({ r: 255, g: 255, b: 255, a: 1 });
    expect(e.material.sideColor.value).toEqual({ r: 200, g: 200, b: 200, a: 1 });
    expect(e.material.bevelColor.value).toEqual({ r: 180, g: 180, b: 180, a: 1 });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultTrace TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultTrace", () => {
  it("has type 'trace'", () => {
    const t = createDefaultTrace();
    expect(t.type).toBe("trace");
  });

  it("mode defaults to 'blackAndWhite'", () => {
    const t = createDefaultTrace();
    expect(t.mode).toBe("blackAndWhite");
  });

  it("threshold defaults to 128", () => {
    const t = createDefaultTrace();
    expect(t.threshold.value).toBe(128);
  });

  it("colors defaults to 16", () => {
    const t = createDefaultTrace();
    expect(t.colors).toBe(16);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultSimplifyPath TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultSimplifyPath", () => {
  it("has type 'simplifyPath'", () => {
    const s = createDefaultSimplifyPath();
    expect(s.type).toBe("simplifyPath");
  });

  it("tolerance defaults to 50", () => {
    const s = createDefaultSimplifyPath();
    expect(s.tolerance.value).toBe(50);
  });

  it("angleTolerance defaults to 10", () => {
    const s = createDefaultSimplifyPath();
    expect(s.angleTolerance.value).toBe(10);
  });

  it("straightLines defaults to false", () => {
    const s = createDefaultSimplifyPath();
    expect(s.straightLines).toBe(false);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultSmoothPath TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultSmoothPath", () => {
  it("has type 'smoothPath'", () => {
    const s = createDefaultSmoothPath();
    expect(s.type).toBe("smoothPath");
  });

  it("amount defaults to 50", () => {
    const s = createDefaultSmoothPath();
    expect(s.amount.value).toBe(50);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultGradientFill TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultGradientFill", () => {
  it("has type 'gradientFill'", () => {
    const g = createDefaultGradientFill();
    expect(g.type).toBe("gradientFill");
  });

  it("has linear gradient with 2 stops", () => {
    const g = createDefaultGradientFill();
    expect(g.gradient.value.type).toBe("linear");
    expect(g.gradient.value.stops.length).toBe(2);
  });

  it("gradient goes from black to white", () => {
    const g = createDefaultGradientFill();
    expect(g.gradient.value.stops[0].color).toEqual({ r: 0, g: 0, b: 0, a: 1 });
    expect(g.gradient.value.stops[1].color).toEqual({ r: 255, g: 255, b: 255, a: 1 });
  });

  it("opacity defaults to 100", () => {
    const g = createDefaultGradientFill();
    expect(g.opacity.value).toBe(100);
  });

  it("fillRule defaults to 'nonzero'", () => {
    const g = createDefaultGradientFill();
    expect(g.fillRule).toBe("nonzero");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultGradientStroke TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultGradientStroke", () => {
  it("has type 'gradientStroke'", () => {
    const g = createDefaultGradientStroke();
    expect(g.type).toBe("gradientStroke");
  });

  it("has linear gradient with 2 stops", () => {
    const g = createDefaultGradientStroke();
    expect(g.gradient.value.type).toBe("linear");
    expect(g.gradient.value.stops.length).toBe(2);
  });

  it("gradient goes from white to black", () => {
    const g = createDefaultGradientStroke();
    expect(g.gradient.value.stops[0].color).toEqual({ r: 255, g: 255, b: 255, a: 1 });
    expect(g.gradient.value.stops[1].color).toEqual({ r: 0, g: 0, b: 0, a: 1 });
  });

  it("width defaults to 2", () => {
    const g = createDefaultGradientStroke();
    expect(g.width.value).toBe(2);
  });

  it("lineCap defaults to 'round'", () => {
    const g = createDefaultGradientStroke();
    expect(g.lineCap).toBe("round");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultShapeLayerData TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultShapeLayerData", () => {
  it("has empty contents array", () => {
    const d = createDefaultShapeLayerData();
    expect(d.contents).toEqual([]);
  });

  it("blendMode defaults to 'normal'", () => {
    const d = createDefaultShapeLayerData();
    expect(d.blendMode).toBe("normal");
  });

  it("quality defaults to 'normal'", () => {
    const d = createDefaultShapeLayerData();
    expect(d.quality).toBe("normal");
  });

  it("gpuAccelerated defaults to true", () => {
    const d = createDefaultShapeLayerData();
    expect(d.gpuAccelerated).toBe(true);
  });
});
