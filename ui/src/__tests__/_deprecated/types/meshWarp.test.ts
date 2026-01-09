/**
 * Tests for meshWarp type extensions (Tutorial 03)
 */
import { describe, expect, it } from "vitest";
import { createDefaultWarpPin, type WarpPinType } from "@/types/meshWarp";

describe("createDefaultWarpPin - new pin types", () => {
  const allTypes: WarpPinType[] = [
    "position",
    "starch",
    "rotation",
    "overlap",
    "bend",
    "advanced",
  ];

  allTypes.forEach((type) => {
    it(`creates ${type} pin correctly`, () => {
      const pin = createDefaultWarpPin(`test_${type}`, 100, 200, type);

      // Basic properties
      expect(pin.type).toBe(type);
      expect(pin.position.value).toEqual({ x: 100, y: 200 });
      expect(pin.rotation.value).toBe(0);
      expect(pin.scale.value).toBe(1);
      expect(pin.radius).toBe(50);

      // Type-specific properties
      if (type === "overlap") {
        expect(pin.inFront).toBeDefined();
        expect(pin.inFront?.value).toBe(0);
        expect(pin.inFront?.animated).toBe(false);
      } else {
        expect(pin.inFront).toBeUndefined();
      }

      if (type === "starch") {
        expect(pin.stiffness).toBe(1.0);
      } else {
        expect(pin.stiffness).toBe(0.0);
      }
    });
  });

  it("overlap pin has animatable inFront property", () => {
    const pin = createDefaultWarpPin("overlap_test", 50, 50, "overlap");

    expect(pin.inFront).toBeDefined();
    expect(pin.inFront?.id).toBe("pin_infront_overlap_test");
    expect(pin.inFront?.name).toBe("In Front");
    expect(pin.inFront?.type).toBe("number");
    expect(pin.inFront?.keyframes).toEqual([]);
  });

  it("pins have descriptive names based on type", () => {
    expect(createDefaultWarpPin("a", 0, 0, "position").name).toContain(
      "Deform",
    );
    expect(createDefaultWarpPin("b", 0, 0, "starch").name).toContain(
      "Stiffness",
    );
    expect(createDefaultWarpPin("c", 0, 0, "overlap").name).toContain(
      "Overlap",
    );
    expect(createDefaultWarpPin("d", 0, 0, "bend").name).toContain("Bend");
    expect(createDefaultWarpPin("e", 0, 0, "advanced").name).toContain(
      "Advanced",
    );
  });
});
