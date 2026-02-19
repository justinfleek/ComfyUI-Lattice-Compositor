/**
 * Property tests for ui/src/types/masks.ts
 * Tests: createDefaultMask, createEllipseMask
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultMask,
  createEllipseMask,
  type LayerMask,
} from "@/types/masks";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                              // arbitraries
// ═══════════════════════════════════════════════════════════════════════════

const maskIdArb = fc.string({ minLength: 1, maxLength: 50 });
const dimensionArb = fc.integer({ min: 1, max: 8192 });
const positionArb = fc.double({ min: -10000, max: 10000, noNaN: true });
const radiusArb = fc.double({ min: 1, max: 5000, noNaN: true });

// ═══════════════════════════════════════════════════════════════════════════
// createDefaultMask TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultMask", () => {
  it("returns LayerMask object with all required fields", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);

        expect(mask).toHaveProperty("id");
        expect(mask).toHaveProperty("name");
        expect(mask).toHaveProperty("enabled");
        expect(mask).toHaveProperty("locked");
        expect(mask).toHaveProperty("mode");
        expect(mask).toHaveProperty("inverted");
        expect(mask).toHaveProperty("path");
        expect(mask).toHaveProperty("opacity");
        expect(mask).toHaveProperty("feather");
        expect(mask).toHaveProperty("expansion");
      })
    );
  });

  it("id matches input", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.id).toBe(id);
      })
    );
  });

  it("name is 'Mask 1'", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.name).toBe("Mask 1");
      })
    );
  });

  it("enabled is true by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.enabled).toBe(true);
      })
    );
  });

  it("locked is false by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.locked).toBe(false);
      })
    );
  });

  it("mode is 'add' by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.mode).toBe("add");
      })
    );
  });

  it("inverted is false by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.inverted).toBe(false);
      })
    );
  });

  it("path is an AnimatableProperty", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.path).toHaveProperty("id");
        expect(mask.path).toHaveProperty("name");
        expect(mask.path).toHaveProperty("type");
        expect(mask.path).toHaveProperty("value");
        expect(mask.path).toHaveProperty("animated");
        expect(mask.path).toHaveProperty("keyframes");
      })
    );
  });

  it("path value is a closed path", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.path.value.closed).toBe(true);
      })
    );
  });

  it("path has 4 vertices (rectangular)", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.path.value.vertices).toHaveLength(4);
      })
    );
  });

  it("opacity value is 100 by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.opacity.value).toBe(100);
      })
    );
  });

  it("feather value is 0 by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.feather.value).toBe(0);
      })
    );
  });

  it("expansion value is 0 by default", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask = createDefaultMask(id, width, height);
        expect(mask.expansion.value).toBe(0);
      })
    );
  });

  it("is deterministic (same inputs = same output except IDs)", () => {
    fc.assert(
      fc.property(maskIdArb, dimensionArb, dimensionArb, (id, width, height) => {
        const mask1 = createDefaultMask(id, width, height);
        const mask2 = createDefaultMask(id, width, height);
        
        // Same structure (excluding generated IDs in nested objects)
        expect(mask1.id).toBe(mask2.id);
        expect(mask1.name).toBe(mask2.name);
        expect(mask1.enabled).toBe(mask2.enabled);
        expect(mask1.mode).toBe(mask2.mode);
      })
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createEllipseMask TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createEllipseMask", () => {
  it("returns LayerMask object with all required fields", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);

        expect(mask).toHaveProperty("id");
        expect(mask).toHaveProperty("name");
        expect(mask).toHaveProperty("enabled");
        expect(mask).toHaveProperty("locked");
        expect(mask).toHaveProperty("mode");
        expect(mask).toHaveProperty("inverted");
        expect(mask).toHaveProperty("path");
        expect(mask).toHaveProperty("opacity");
        expect(mask).toHaveProperty("feather");
        expect(mask).toHaveProperty("expansion");
      })
    );
  });

  it("id matches input", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);
        expect(mask.id).toBe(id);
      })
    );
  });

  it("path value is a closed path", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);
        expect(mask.path.value.closed).toBe(true);
      })
    );
  });

  it("path has 4 vertices (bezier ellipse approximation)", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);
        expect(mask.path.value.vertices).toHaveLength(4);
      })
    );
  });

  it("vertices form a pattern around center", () => {
    const mask = createEllipseMask("test", 100, 100, 50, 50);
    const verts = mask.path.value.vertices;
    
    // Top vertex
    expect(verts[0].x).toBe(100);
    expect(verts[0].y).toBe(50);
    
    // Right vertex
    expect(verts[1].x).toBe(150);
    expect(verts[1].y).toBe(100);
    
    // Bottom vertex
    expect(verts[2].x).toBe(100);
    expect(verts[2].y).toBe(150);
    
    // Left vertex
    expect(verts[3].x).toBe(50);
    expect(verts[3].y).toBe(100);
  });

  it("ellipse vertices scale with radius", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);
        const verts = mask.path.value.vertices;
        
        // Top vertex should be at (cx, cy - ry)
        expect(verts[0].x).toBeCloseTo(cx, 5);
        expect(verts[0].y).toBeCloseTo(cy - ry, 5);
        
        // Right vertex should be at (cx + rx, cy)
        expect(verts[1].x).toBeCloseTo(cx + rx, 5);
        expect(verts[1].y).toBeCloseTo(cy, 5);
        
        // Bottom vertex should be at (cx, cy + ry)
        expect(verts[2].x).toBeCloseTo(cx, 5);
        expect(verts[2].y).toBeCloseTo(cy + ry, 5);
        
        // Left vertex should be at (cx - rx, cy)
        expect(verts[3].x).toBeCloseTo(cx - rx, 5);
        expect(verts[3].y).toBeCloseTo(cy, 5);
      })
    );
  });

  it("has bezier tangents for smooth curves", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask = createEllipseMask(id, cx, cy, rx, ry);
        const verts = mask.path.value.vertices;
        
        // All vertices should have non-zero tangents for ellipse
        for (const v of verts) {
          const hasTangents = 
            v.inTangentX !== 0 || v.inTangentY !== 0 ||
            v.outTangentX !== 0 || v.outTangentY !== 0;
          expect(hasTangents).toBe(true);
        }
      })
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(maskIdArb, positionArb, positionArb, radiusArb, radiusArb, (id, cx, cy, rx, ry) => {
        const mask1 = createEllipseMask(id, cx, cy, rx, ry);
        const mask2 = createEllipseMask(id, cx, cy, rx, ry);
        
        expect(mask1.id).toBe(mask2.id);
        expect(mask1.path.value.vertices).toEqual(mask2.path.value.vertices);
      })
    );
  });
});
