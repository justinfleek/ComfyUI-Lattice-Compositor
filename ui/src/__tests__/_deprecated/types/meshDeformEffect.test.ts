/**
 * Tests for mesh-deform effect definition
 */
import { describe, expect, it } from "vitest";
import {
  createEffectInstance,
  createMeshDeformEffectInstance,
  EFFECT_DEFINITIONS,
  type EffectInstance,
  isMeshDeformEffect,
} from "@/types/effects";
import { createDefaultWarpPin } from "@/types/meshWarp";

describe("mesh-deform effect definition", () => {
  it("is defined in EFFECT_DEFINITIONS", () => {
    const def = EFFECT_DEFINITIONS["mesh-deform"];
    expect(def).toBeDefined();
    expect(def.name).toBe("Mesh Deform");
    expect(def.category).toBe("distort");
  });

  it("has required parameters", () => {
    const def = EFFECT_DEFINITIONS["mesh-deform"];
    const paramNames = def.parameters.map((p) => p.name);

    expect(paramNames).toContain("Triangle Count");
    expect(paramNames).toContain("Expansion");
    expect(paramNames).toContain("Alpha Threshold");
    expect(paramNames).toContain("Show Mesh");
    expect(paramNames).toContain("Show Pins");
    expect(paramNames).toContain("Pin Falloff");
    expect(paramNames).toContain("Falloff Power");
    expect(paramNames).toContain("Enable Overlap");
  });

  it("has correct default values", () => {
    const def = EFFECT_DEFINITIONS["mesh-deform"];
    const params = Object.fromEntries(
      def.parameters.map((p) => [p.name, p.defaultValue]),
    );

    expect(params["Triangle Count"]).toBe(200);
    expect(params.Expansion).toBe(3);
    expect(params["Alpha Threshold"]).toBe(128);
    expect(params["Show Mesh"]).toBe(false);
    expect(params["Show Pins"]).toBe(true);
    expect(params["Pin Falloff"]).toBe("inverse-distance");
    expect(params["Falloff Power"]).toBe(2);
    expect(params["Enable Overlap"]).toBe(false);
  });
});

describe("createMeshDeformEffectInstance", () => {
  it("creates instance with pins array", () => {
    const effect = createMeshDeformEffectInstance();
    expect(effect).not.toBeNull();
    expect(effect?.effectKey).toBe("mesh-deform");
    expect(effect?.pins).toEqual([]);
    expect(effect?.meshDirty).toBe(true);
  });

  it("has all parameters from definition", () => {
    const effect = createMeshDeformEffectInstance();
    expect(effect).not.toBeNull();

    // Check parameter keys exist (converted to snake_case)
    expect(effect?.parameters).toHaveProperty("triangle_count");
    expect(effect?.parameters).toHaveProperty("expansion");
    expect(effect?.parameters).toHaveProperty("alpha_threshold");
    expect(effect?.parameters).toHaveProperty("show_mesh");
    expect(effect?.parameters).toHaveProperty("show_pins");
    expect(effect?.parameters).toHaveProperty("pin_falloff");
    expect(effect?.parameters).toHaveProperty("falloff_power");
    expect(effect?.parameters).toHaveProperty("enable_overlap");
  });

  it("generates unique IDs", () => {
    const effect1 = createMeshDeformEffectInstance();
    const effect2 = createMeshDeformEffectInstance();
    expect(effect1?.id).not.toBe(effect2?.id);
  });
});

describe("isMeshDeformEffect type guard", () => {
  it("returns true for MeshDeformEffectInstance", () => {
    const effect = createMeshDeformEffectInstance();
    expect(isMeshDeformEffect(effect!)).toBe(true);
  });

  it("returns false for regular EffectInstance", () => {
    const effect = createEffectInstance("gaussian-blur");
    expect(isMeshDeformEffect(effect!)).toBe(false);
  });

  it("returns false for effect with same key but no pins", () => {
    // Simulate a corrupted/incomplete mesh-deform effect
    const fakeEffect: EffectInstance = {
      id: "fake",
      effectKey: "mesh-deform",
      name: "Mesh Deform",
      category: "distort",
      enabled: true,
      expanded: true,
      parameters: {},
    };
    expect(isMeshDeformEffect(fakeEffect)).toBe(false);
  });
});

describe("MeshDeformEffectInstance with pins", () => {
  it("can add position pins", () => {
    const effect = createMeshDeformEffectInstance()!;

    const pin = createDefaultWarpPin("pin1", 50, 50, "position");
    effect.pins.push(pin);

    expect(effect.pins.length).toBe(1);
    expect(effect.pins[0].type).toBe("position");
    expect(effect.pins[0].position.value).toEqual({ x: 50, y: 50 });
  });

  it("can add multiple pin types", () => {
    const effect = createMeshDeformEffectInstance()!;

    effect.pins.push(createDefaultWarpPin("pos1", 30, 30, "position"));
    effect.pins.push(createDefaultWarpPin("bend1", 50, 50, "bend"));
    effect.pins.push(createDefaultWarpPin("starch1", 70, 70, "starch"));
    effect.pins.push(createDefaultWarpPin("overlap1", 90, 90, "overlap"));
    effect.pins.push(createDefaultWarpPin("adv1", 100, 100, "advanced"));

    expect(effect.pins.length).toBe(5);
    expect(effect.pins.map((p) => p.type)).toEqual([
      "position",
      "bend",
      "starch",
      "overlap",
      "advanced",
    ]);
  });

  it("tracks meshDirty state", () => {
    const effect = createMeshDeformEffectInstance()!;
    expect(effect.meshDirty).toBe(true);

    // Simulate mesh generation
    effect.meshDirty = false;

    // Adding a pin should mark dirty (in real usage, this would be done by the store)
    effect.pins.push(createDefaultWarpPin("pin1", 50, 50, "position"));
    effect.meshDirty = true;

    expect(effect.meshDirty).toBe(true);
  });
});
