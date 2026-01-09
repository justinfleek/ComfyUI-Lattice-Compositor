/**
 * Property tests for ui/src/types/transform.ts
 * Tests: createDefaultTransform, normalizeLayerTransform, createFollowPathConstraint,
 *        separatePositionDimensions, linkPositionDimensions, 
 *        separateScaleDimensions, linkScaleDimensions
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultTransform,
  normalizeLayerTransform,
  createFollowPathConstraint,
  separatePositionDimensions,
  linkPositionDimensions,
  separateScaleDimensions,
  linkScaleDimensions,
  type LayerTransform,
} from "@/types/transform";
import { createAnimatableProperty, createKeyframe } from "@/types/animation";

// ============================================================
// ARBITRARIES
// ============================================================

const layerIdArb = fc.string({ minLength: 1, maxLength: 50 });
const positionArb = fc.record({
  x: fc.double({ min: -10000, max: 10000, noNaN: true }),
  y: fc.double({ min: -10000, max: 10000, noNaN: true }),
  z: fc.double({ min: -10000, max: 10000, noNaN: true }),
});

// ============================================================
// createDefaultTransform TESTS
// ============================================================

describe("PROPERTY: createDefaultTransform", () => {
  it("returns LayerTransform with all required properties", () => {
    const transform = createDefaultTransform();
    
    expect(transform).toHaveProperty("position");
    expect(transform).toHaveProperty("origin");
    expect(transform).toHaveProperty("anchorPoint");
    expect(transform).toHaveProperty("scale");
    expect(transform).toHaveProperty("rotation");
    expect(transform).toHaveProperty("orientation");
    expect(transform).toHaveProperty("rotationX");
    expect(transform).toHaveProperty("rotationY");
    expect(transform).toHaveProperty("rotationZ");
  });

  it("position defaults to (0, 0, 0)", () => {
    const transform = createDefaultTransform();
    expect(transform.position.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  it("origin defaults to (0, 0, 0)", () => {
    const transform = createDefaultTransform();
    expect(transform.origin.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  it("scale defaults to (100, 100, 100)", () => {
    const transform = createDefaultTransform();
    expect(transform.scale.value).toEqual({ x: 100, y: 100, z: 100 });
  });

  it("rotation defaults to 0", () => {
    const transform = createDefaultTransform();
    expect(transform.rotation.value).toBe(0);
  });

  it("orientation defaults to (0, 0, 0)", () => {
    const transform = createDefaultTransform();
    expect(transform.orientation.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  it("rotationX, rotationY, rotationZ default to 0", () => {
    const transform = createDefaultTransform();
    expect(transform.rotationX.value).toBe(0);
    expect(transform.rotationY.value).toBe(0);
    expect(transform.rotationZ.value).toBe(0);
  });

  it("origin and anchorPoint reference same object (backwards compat)", () => {
    const transform = createDefaultTransform();
    expect(transform.origin).toBe(transform.anchorPoint);
  });

  it("all properties are AnimatableProperty with correct structure", () => {
    const transform = createDefaultTransform();
    
    const props = [
      transform.position,
      transform.origin,
      transform.scale,
      transform.rotation,
      transform.orientation,
      transform.rotationX,
      transform.rotationY,
      transform.rotationZ,
    ];
    
    for (const prop of props) {
      expect(prop).toHaveProperty("id");
      expect(prop).toHaveProperty("name");
      expect(prop).toHaveProperty("type");
      expect(prop).toHaveProperty("value");
      expect(prop).toHaveProperty("animated");
      expect(prop).toHaveProperty("keyframes");
      expect(prop.animated).toBe(false);
      expect(prop.keyframes).toEqual([]);
    }
  });

  it("is deterministic (same structure every call)", () => {
    const t1 = createDefaultTransform();
    const t2 = createDefaultTransform();
    
    expect(t1.position.value).toEqual(t2.position.value);
    expect(t1.scale.value).toEqual(t2.scale.value);
    expect(t1.rotation.value).toBe(t2.rotation.value);
  });
});

// ============================================================
// normalizeLayerTransform TESTS
// ============================================================

describe("PROPERTY: normalizeLayerTransform", () => {
  it("returns the same transform object", () => {
    const transform = createDefaultTransform();
    const result = normalizeLayerTransform(transform);
    expect(result).toBe(transform);
  });

  it("copies anchorPoint to origin if origin missing", () => {
    const transform = createDefaultTransform();
    delete (transform as any).origin;
    transform.anchorPoint = createAnimatableProperty("test", { x: 10, y: 20, z: 30 }, "vector3");
    
    normalizeLayerTransform(transform);
    
    expect(transform.origin).toBe(transform.anchorPoint);
  });

  it("copies origin to anchorPoint if anchorPoint missing", () => {
    const transform = createDefaultTransform();
    delete (transform as any).anchorPoint;
    transform.origin = createAnimatableProperty("test", { x: 10, y: 20, z: 30 }, "vector3");
    
    normalizeLayerTransform(transform);
    
    expect(transform.anchorPoint).toBe(transform.origin);
  });

  it("preserves both if both exist", () => {
    const transform = createDefaultTransform();
    const originalOrigin = transform.origin;
    const originalAnchor = transform.anchorPoint;
    
    normalizeLayerTransform(transform);
    
    expect(transform.origin).toBe(originalOrigin);
    expect(transform.anchorPoint).toBe(originalAnchor);
  });
});

// ============================================================
// createFollowPathConstraint TESTS
// ============================================================

describe("PROPERTY: createFollowPathConstraint", () => {
  it("returns FollowPathConstraint with all required properties", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        
        expect(constraint).toHaveProperty("enabled");
        expect(constraint).toHaveProperty("pathLayerId");
        expect(constraint).toHaveProperty("progress");
        expect(constraint).toHaveProperty("offset");
        expect(constraint).toHaveProperty("tangentOffset");
        expect(constraint).toHaveProperty("autoOrient");
        expect(constraint).toHaveProperty("rotationOffset");
        expect(constraint).toHaveProperty("banking");
        expect(constraint).toHaveProperty("loopMode");
      })
    );
  });

  it("pathLayerId matches input", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.pathLayerId).toBe(pathLayerId);
      })
    );
  });

  it("enabled defaults to true", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.enabled).toBe(true);
      })
    );
  });

  it("progress defaults to 0", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.progress.value).toBe(0);
      })
    );
  });

  it("offset defaults to 0", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.offset.value).toBe(0);
      })
    );
  });

  it("autoOrient defaults to true", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.autoOrient).toBe(true);
      })
    );
  });

  it("loopMode defaults to 'clamp'", () => {
    fc.assert(
      fc.property(layerIdArb, (pathLayerId) => {
        const constraint = createFollowPathConstraint(pathLayerId);
        expect(constraint.loopMode).toBe("clamp");
      })
    );
  });
});

// ============================================================
// separatePositionDimensions TESTS
// ============================================================

describe("PROPERTY: separatePositionDimensions", () => {
  it("creates positionX, positionY, positionZ properties", () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    expect(transform.positionX).toBeDefined();
    expect(transform.positionY).toBeDefined();
    expect(transform.positionZ).toBeDefined();
  });

  it("positionX matches original x value", () => {
    fc.assert(
      fc.property(positionArb, (pos) => {
        const transform = createDefaultTransform();
        transform.position.value = pos;
        
        separatePositionDimensions(transform);
        
        expect(transform.positionX?.value).toBe(pos.x);
      })
    );
  });

  it("positionY matches original y value", () => {
    fc.assert(
      fc.property(positionArb, (pos) => {
        const transform = createDefaultTransform();
        transform.position.value = pos;
        
        separatePositionDimensions(transform);
        
        expect(transform.positionY?.value).toBe(pos.y);
      })
    );
  });

  it("positionZ matches original z value", () => {
    fc.assert(
      fc.property(positionArb, (pos) => {
        const transform = createDefaultTransform();
        transform.position.value = pos;
        
        separatePositionDimensions(transform);
        
        expect(transform.positionZ?.value).toBe(pos.z);
      })
    );
  });

  it("sets separateDimensions.position to true", () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(true);
  });

  it("copies keyframes to separate properties", () => {
    const transform = createDefaultTransform();
    transform.position.animated = true;
    transform.position.keyframes = [
      createKeyframe(0, { x: 0, y: 0, z: 0 }),
      createKeyframe(10, { x: 100, y: 200, z: 300 }),
    ];
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.keyframes.length).toBe(2);
    expect(transform.positionY?.keyframes.length).toBe(2);
    expect(transform.positionZ?.keyframes.length).toBe(2);
    expect(transform.positionX?.animated).toBe(true);
  });
});

// ============================================================
// linkPositionDimensions TESTS
// ============================================================

describe("PROPERTY: linkPositionDimensions", () => {
  it("merges separate dimensions back to combined position", () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 10, y: 20, z: 30 };
    
    separatePositionDimensions(transform);
    
    // Modify separate values
    transform.positionX!.value = 100;
    transform.positionY!.value = 200;
    transform.positionZ!.value = 300;
    
    linkPositionDimensions(transform);
    
    expect(transform.position.value).toEqual({ x: 100, y: 200, z: 300 });
  });

  it("removes positionX, positionY, positionZ after linking", () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    expect(transform.positionX).toBeUndefined();
    expect(transform.positionY).toBeUndefined();
    expect(transform.positionZ).toBeUndefined();
  });

  it("sets separateDimensions.position to false", () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(false);
  });

  it("does nothing if positionX or positionY missing", () => {
    const transform = createDefaultTransform();
    const originalValue = { ...transform.position.value };
    
    linkPositionDimensions(transform);
    
    expect(transform.position.value).toEqual(originalValue);
  });

  it("round-trip preserves position value", () => {
    fc.assert(
      fc.property(positionArb, (pos) => {
        const transform = createDefaultTransform();
        transform.position.value = pos;
        
        separatePositionDimensions(transform);
        linkPositionDimensions(transform);
        
        expect(transform.position.value.x).toBeCloseTo(pos.x, 10);
        expect(transform.position.value.y).toBeCloseTo(pos.y, 10);
        expect(transform.position.value.z).toBeCloseTo(pos.z, 10);
      })
    );
  });
});

// ============================================================
// separateScaleDimensions TESTS
// ============================================================

describe("PROPERTY: separateScaleDimensions", () => {
  it("creates scaleX, scaleY, scaleZ properties", () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    expect(transform.scaleX).toBeDefined();
    expect(transform.scaleY).toBeDefined();
    expect(transform.scaleZ).toBeDefined();
  });

  it("scaleX matches original x value", () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 50, y: 75, z: 100 };
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleX?.value).toBe(50);
  });

  it("scaleY matches original y value", () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 50, y: 75, z: 100 };
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleY?.value).toBe(75);
  });

  it("scaleZ matches original z value", () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 50, y: 75, z: 100 };
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleZ?.value).toBe(100);
  });

  it("sets separateDimensions.scale to true", () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    expect(transform.separateDimensions?.scale).toBe(true);
  });
});

// ============================================================
// linkScaleDimensions TESTS
// ============================================================

describe("PROPERTY: linkScaleDimensions", () => {
  it("merges separate dimensions back to combined scale", () => {
    const transform = createDefaultTransform();
    
    separateScaleDimensions(transform);
    
    transform.scaleX!.value = 50;
    transform.scaleY!.value = 75;
    transform.scaleZ!.value = 125;
    
    linkScaleDimensions(transform);
    
    expect(transform.scale.value).toEqual({ x: 50, y: 75, z: 125 });
  });

  it("removes scaleX, scaleY, scaleZ after linking", () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    linkScaleDimensions(transform);
    
    expect(transform.scaleX).toBeUndefined();
    expect(transform.scaleY).toBeUndefined();
    expect(transform.scaleZ).toBeUndefined();
  });

  it("sets separateDimensions.scale to false", () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    linkScaleDimensions(transform);
    
    expect(transform.separateDimensions?.scale).toBe(false);
  });

  it("does nothing if scaleX or scaleY missing", () => {
    const transform = createDefaultTransform();
    const originalValue = { ...transform.scale.value };
    
    linkScaleDimensions(transform);
    
    expect(transform.scale.value).toEqual(originalValue);
  });

  it("round-trip preserves scale value", () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 50, y: 75, z: 125 };
    
    separateScaleDimensions(transform);
    linkScaleDimensions(transform);
    
    expect(transform.scale.value.x).toBe(50);
    expect(transform.scale.value.y).toBe(75);
    expect(transform.scale.value.z).toBe(125);
  });
});
