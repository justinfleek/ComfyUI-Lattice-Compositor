/**
 * Property tests for ui/src/types/effects.ts
 * Tests: getAnimatableType, createEffect, createEffectInstance, 
 *        createMeshDeformEffectInstance, isMeshDeformEffect
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  getAnimatableType,
  createEffect,
  createEffectInstance,
  createMeshDeformEffectInstance,
  isMeshDeformEffect,
  EFFECT_DEFINITIONS,
  type EffectParameterType,
  type EffectInstance,
} from "@/types/effects";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // constants // for // testing
// ════════════════════════════════════════════════════════════════════════════

// All valid effect parameter types
const PARAM_TYPES: EffectParameterType[] = [
  "number",
  "angle",
  "point",
  "point3d",
  "color",
  "checkbox",
  "dropdown",
  "layer",
  "string",
  "curve",
  "data",
];

// Get all valid effect definition keys
const EFFECT_KEYS = Object.keys(EFFECT_DEFINITIONS);

// ════════════════════════════════════════════════════════════════════════════
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const paramTypeArb = fc.constantFrom(...PARAM_TYPES);
const effectKeyArb = fc.constantFrom(...EFFECT_KEYS);
// Generate clearly invalid keys that won't match any effect definition
const invalidKeyArb = fc.string({ minLength: 1, maxLength: 50 }).map(
  (s) => `__invalid__${s}__`
);

// ════════════════════════════════════════════════════════════════════════════
// getAnimatableType TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: getAnimatableType", () => {
  it("returns valid animatable type for all parameter types", () => {
    fc.assert(
      fc.property(paramTypeArb, (paramType) => {
        const result = getAnimatableType(paramType);
        expect(["number", "position", "color", "enum", "vector3"]).toContain(result);
      })
    );
  });

  it("returns 'number' for 'number' type", () => {
    expect(getAnimatableType("number")).toBe("number");
  });

  it("returns 'number' for 'angle' type", () => {
    expect(getAnimatableType("angle")).toBe("number");
  });

  it("returns 'position' for 'point' type", () => {
    expect(getAnimatableType("point")).toBe("position");
  });

  it("returns 'vector3' for 'point3d' type", () => {
    expect(getAnimatableType("point3d")).toBe("vector3");
  });

  it("returns 'color' for 'color' type", () => {
    expect(getAnimatableType("color")).toBe("color");
  });

  it("returns 'enum' for checkbox/dropdown/layer/string/curve/data types", () => {
    const enumTypes: EffectParameterType[] = ["checkbox", "dropdown", "layer", "string", "curve", "data"];
    for (const type of enumTypes) {
      expect(getAnimatableType(type)).toBe("enum");
    }
  });

  it("is deterministic (same input = same output)", () => {
    fc.assert(
      fc.property(paramTypeArb, (paramType) => {
        const result1 = getAnimatableType(paramType);
        const result2 = getAnimatableType(paramType);
        expect(result1).toBe(result2);
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createEffect TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createEffect", () => {
  it("returns null for invalid definition keys", () => {
    fc.assert(
      fc.property(invalidKeyArb, (key) => {
        const result = createEffect(key);
        expect(result).toBeNull();
      })
    );
  });

  it("returns Effect object for valid definition keys", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        expect(result).not.toBeNull();
        expect(result).toHaveProperty("id");
        expect(result).toHaveProperty("name");
        expect(result).toHaveProperty("category");
        expect(result).toHaveProperty("enabled");
        expect(result).toHaveProperty("parameters");
      })
    );
  });

  it("id starts with 'effect-'", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        expect(result?.id.startsWith("effect-")).toBe(true);
      })
    );
  });

  it("name matches definition name", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        const def = EFFECT_DEFINITIONS[key];
        expect(result?.name).toBe(def.name);
      })
    );
  });

  it("category matches definition category", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        const def = EFFECT_DEFINITIONS[key];
        expect(result?.category).toBe(def.category);
      })
    );
  });

  it("enabled defaults to true", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        expect(result?.enabled).toBe(true);
      })
    );
  });

  it("expanded defaults to true", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        expect(result?.expanded).toBe(true);
      })
    );
  });

  it("parameters array length matches definition", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffect(key);
        const def = EFFECT_DEFINITIONS[key];
        expect(result?.parameters.length).toBe(def.parameters.length);
      })
    );
  });

  it("consecutive calls produce unique IDs", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result1 = createEffect(key);
        const result2 = createEffect(key);
        expect(result1?.id).not.toBe(result2?.id);
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createEffectInstance TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createEffectInstance", () => {
  it("returns null for invalid definition keys", () => {
    fc.assert(
      fc.property(invalidKeyArb, (key) => {
        const result = createEffectInstance(key);
        expect(result).toBeNull();
      })
    );
  });

  it("returns EffectInstance object for valid definition keys", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        expect(result).not.toBeNull();
        expect(result).toHaveProperty("id");
        expect(result).toHaveProperty("effectKey");
        expect(result).toHaveProperty("name");
        expect(result).toHaveProperty("category");
        expect(result).toHaveProperty("enabled");
        expect(result).toHaveProperty("parameters");
      })
    );
  });

  it("effectKey matches input key", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        expect(result?.effectKey).toBe(key);
      })
    );
  });

  it("parameters is an object (Record)", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        expect(typeof result?.parameters).toBe("object");
        expect(result?.parameters).not.toBeNull();
      })
    );
  });

  it("each parameter has AnimatableProperty structure", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        if (!result) return;

        for (const paramKey of Object.keys(result.parameters)) {
          const param = result.parameters[paramKey];
          expect(param).toHaveProperty("id");
          expect(param).toHaveProperty("name");
          expect(param).toHaveProperty("type");
          expect(param).toHaveProperty("value");
          expect(param).toHaveProperty("animated");
          expect(param).toHaveProperty("keyframes");
        }
      })
    );
  });

  it("all parameters have animated=false initially", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        if (!result) return;

        for (const paramKey of Object.keys(result.parameters)) {
          expect(result.parameters[paramKey].animated).toBe(false);
        }
      })
    );
  });

  it("all parameters have empty keyframes array initially", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result = createEffectInstance(key);
        if (!result) return;

        for (const paramKey of Object.keys(result.parameters)) {
          expect(result.parameters[paramKey].keyframes).toEqual([]);
        }
      })
    );
  });

  it("consecutive calls produce unique IDs", () => {
    fc.assert(
      fc.property(effectKeyArb, (key) => {
        const result1 = createEffectInstance(key);
        const result2 = createEffectInstance(key);
        expect(result1?.id).not.toBe(result2?.id);
      })
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createMeshDeformEffectInstance TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createMeshDeformEffectInstance", () => {
  it("returns MeshDeformEffectInstance or null", () => {
    const result = createMeshDeformEffectInstance();
    // Should return non-null if mesh-deform is defined
    if (EFFECT_DEFINITIONS["mesh-deform"]) {
      expect(result).not.toBeNull();
    } else {
      expect(result).toBeNull();
    }
  });

  it("has effectKey 'mesh-deform'", () => {
    const result = createMeshDeformEffectInstance();
    if (result) {
      expect(result.effectKey).toBe("mesh-deform");
    }
  });

  it("has pins array", () => {
    const result = createMeshDeformEffectInstance();
    if (result) {
      expect(result).toHaveProperty("pins");
      expect(Array.isArray(result.pins)).toBe(true);
    }
  });

  it("pins array is empty initially", () => {
    const result = createMeshDeformEffectInstance();
    if (result) {
      expect(result.pins).toHaveLength(0);
    }
  });

  it("has meshDirty flag", () => {
    const result = createMeshDeformEffectInstance();
    if (result) {
      expect(result).toHaveProperty("meshDirty");
    }
  });

  it("meshDirty is true initially", () => {
    const result = createMeshDeformEffectInstance();
    if (result) {
      expect(result.meshDirty).toBe(true);
    }
  });

  it("consecutive calls produce unique IDs", () => {
    const result1 = createMeshDeformEffectInstance();
    const result2 = createMeshDeformEffectInstance();
    if (result1 && result2) {
      expect(result1.id).not.toBe(result2.id);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
// isMeshDeformEffect TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: isMeshDeformEffect", () => {
  it("returns true for MeshDeformEffectInstance", () => {
    const meshEffect = createMeshDeformEffectInstance();
    if (meshEffect) {
      expect(isMeshDeformEffect(meshEffect)).toBe(true);
    }
  });

  it("returns false for regular EffectInstance", () => {
    fc.assert(
      fc.property(
        effectKeyArb.filter((k) => k !== "mesh-deform"),
        (key) => {
          const effect = createEffectInstance(key);
          if (effect) {
            expect(isMeshDeformEffect(effect)).toBe(false);
          }
        }
      )
    );
  });

  it("returns false for effect with mesh-deform key but no pins", () => {
    const fakeEffect: EffectInstance = {
      id: "test",
      effectKey: "mesh-deform",
      name: "Mesh Deform",
      category: "distort",
      enabled: true,
      expanded: true,
      parameters: {},
    };
    // No 'pins' property, so should return false
    expect(isMeshDeformEffect(fakeEffect)).toBe(false);
  });

  it("is deterministic", () => {
    const meshEffect = createMeshDeformEffectInstance();
    if (meshEffect) {
      const result1 = isMeshDeformEffect(meshEffect);
      const result2 = isMeshDeformEffect(meshEffect);
      expect(result1).toBe(result2);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                            // effect // definitions // tests
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: EFFECT_DEFINITIONS", () => {
  it("has at least one effect defined", () => {
    expect(EFFECT_KEYS.length).toBeGreaterThan(0);
  });

  it("all definitions have required fields", () => {
    for (const key of EFFECT_KEYS) {
      const def = EFFECT_DEFINITIONS[key];
      expect(def).toHaveProperty("name");
      expect(def).toHaveProperty("category");
      expect(def).toHaveProperty("description");
      expect(def).toHaveProperty("parameters");
    }
  });

  it("all definitions have non-empty name", () => {
    for (const key of EFFECT_KEYS) {
      const def = EFFECT_DEFINITIONS[key];
      expect(def.name.length).toBeGreaterThan(0);
    }
  });

  it("all parameters in definitions have required fields", () => {
    for (const key of EFFECT_KEYS) {
      const def = EFFECT_DEFINITIONS[key];
      for (const param of def.parameters) {
        expect(param).toHaveProperty("name");
        expect(param).toHaveProperty("type");
        expect(param).toHaveProperty("defaultValue");
      }
    }
  });
});
