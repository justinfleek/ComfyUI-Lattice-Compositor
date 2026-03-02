/**
 * Property tests for ui/src/types/meshWarp.ts
 * Tests: createDefaultWarpPin, createEmptyWarpMesh
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultWarpPin,
  createEmptyWarpMesh,
  type WarpPinType,
} from "@/types/meshWarp";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const pinIdArb = fc.string({ minLength: 1, maxLength: 50 });
const layerIdArb = fc.string({ minLength: 1, maxLength: 50 });
const positionArb = fc.double({ min: -10000, max: 10000, noNaN: true });
const pinTypeArb = fc.constantFrom<WarpPinType>("position", "starch", "overlap", "bend");

// ════════════════════════════════════════════════════════════════════════════
// createDefaultWarpPin TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultWarpPin", () => {
  it("returns WarpPin object with required fields", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, pinTypeArb, (id, x, y, type) => {
        const pin = createDefaultWarpPin(id, x, y, type);

        expect(pin).toHaveProperty("id");
        expect(pin).toHaveProperty("name");
        expect(pin).toHaveProperty("type");
        expect(pin).toHaveProperty("position");
      })
    );
  });

  it("id matches input", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, pinTypeArb, (id, x, y, type) => {
        const pin = createDefaultWarpPin(id, x, y, type);
        expect(pin.id).toBe(id);
      })
    );
  });

  it("type matches input", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, pinTypeArb, (id, x, y, type) => {
        const pin = createDefaultWarpPin(id, x, y, type);
        expect(pin.type).toBe(type);
      })
    );
  });

  it("position value matches input coordinates", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, pinTypeArb, (id, x, y, type) => {
        const pin = createDefaultWarpPin(id, x, y, type);
        expect(pin.position.value.x).toBe(x);
        expect(pin.position.value.y).toBe(y);
      })
    );
  });

  it("position is an AnimatableProperty", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, (id, x, y) => {
        const pin = createDefaultWarpPin(id, x, y);
        expect(pin.position).toHaveProperty("id");
        expect(pin.position).toHaveProperty("name");
        expect(pin.position).toHaveProperty("type");
        expect(pin.position).toHaveProperty("value");
        expect(pin.position).toHaveProperty("animated");
        expect(pin.position).toHaveProperty("keyframes");
      })
    );
  });

  it("defaults to 'position' type when not specified", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, (id, x, y) => {
        const pin = createDefaultWarpPin(id, x, y);
        expect(pin.type).toBe("position");
      })
    );
  });

  it("position is not animated by default", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, (id, x, y) => {
        const pin = createDefaultWarpPin(id, x, y);
        expect(pin.position.animated).toBe(false);
      })
    );
  });

  it("position has empty keyframes by default", () => {
    fc.assert(
      fc.property(pinIdArb, positionArb, positionArb, (id, x, y) => {
        const pin = createDefaultWarpPin(id, x, y);
        expect(pin.position.keyframes).toEqual([]);
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createEmptyWarpMesh TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createEmptyWarpMesh", () => {
  it("returns WarpMesh object with required fields", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);

        expect(mesh).toHaveProperty("layerId");
        expect(mesh).toHaveProperty("pins");
        expect(mesh).toHaveProperty("triangulation");
        expect(mesh).toHaveProperty("weights");
        expect(mesh).toHaveProperty("originalVertices");
        expect(mesh).toHaveProperty("pinRestStates");
        expect(mesh).toHaveProperty("vertexCount");
        expect(mesh).toHaveProperty("dirty");
      })
    );
  });

  it("layerId matches input", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.layerId).toBe(layerId);
      })
    );
  });

  it("pins is empty array", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.pins).toEqual([]);
      })
    );
  });

  it("triangulation is empty array", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.triangulation).toEqual([]);
      })
    );
  });

  it("weights is empty Float32Array", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.weights).toBeInstanceOf(Float32Array);
        expect(mesh.weights.length).toBe(0);
      })
    );
  });

  it("originalVertices is empty Float32Array", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.originalVertices).toBeInstanceOf(Float32Array);
        expect(mesh.originalVertices.length).toBe(0);
      })
    );
  });

  it("pinRestStates is empty array", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.pinRestStates).toEqual([]);
      })
    );
  });

  it("vertexCount is 0", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.vertexCount).toBe(0);
      })
    );
  });

  it("dirty is true (needs initialization)", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh = createEmptyWarpMesh(layerId);
        expect(mesh.dirty).toBe(true);
      })
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(layerIdArb, (layerId) => {
        const mesh1 = createEmptyWarpMesh(layerId);
        const mesh2 = createEmptyWarpMesh(layerId);
        expect(mesh1.layerId).toBe(mesh2.layerId);
        expect(mesh1.vertexCount).toBe(mesh2.vertexCount);
        expect(mesh1.dirty).toBe(mesh2.dirty);
      })
    );
  });
});
