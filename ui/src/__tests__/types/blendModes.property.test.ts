/**
 * Property tests for ui/src/types/blendModes.ts
 * Tests: getBlendModeCategory, getBlendModesInCategory, getAllBlendModes
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  type BlendMode,
  BLEND_MODE_CATEGORIES,
  getBlendModeCategory,
  getBlendModesInCategory,
  getAllBlendModes,
} from "@/types/blendModes";

// ============================================================
// CONSTANTS FOR TESTING
// ============================================================

const ALL_BLEND_MODES: BlendMode[] = [
  // Normal
  "normal", "dissolve",
  // Darken
  "darken", "multiply", "color-burn", "linear-burn", "darker-color",
  // Lighten
  "lighten", "screen", "color-dodge", "linear-dodge", "lighter-color", "add",
  // Contrast
  "overlay", "soft-light", "hard-light", "vivid-light", "linear-light", "pin-light", "hard-mix",
  // Inversion
  "difference", "exclusion", "subtract", "divide",
  // Component
  "hue", "saturation", "color", "luminosity",
  // Utility
  "stencil-alpha", "stencil-luma", "silhouette-alpha", "silhouette-luma", "alpha-add", "luminescent-premul",
];

const CATEGORY_KEYS = ["normal", "darken", "lighten", "contrast", "inversion", "component", "utility"] as const;

// ============================================================
// ARBITRARIES
// ============================================================

const blendModeArb = fc.constantFrom(...ALL_BLEND_MODES);
const categoryArb = fc.constantFrom(...CATEGORY_KEYS);

// ============================================================
// getBlendModeCategory TESTS
// ============================================================

describe("PROPERTY: getBlendModeCategory", () => {
  it("returns a valid category key for all blend modes", () => {
    fc.assert(
      fc.property(blendModeArb, (mode) => {
        const category = getBlendModeCategory(mode);
        expect(CATEGORY_KEYS).toContain(category);
      })
    );
  });

  it("returns 'normal' for 'normal' mode", () => {
    expect(getBlendModeCategory("normal")).toBe("normal");
  });

  it("returns 'normal' for 'dissolve' mode", () => {
    expect(getBlendModeCategory("dissolve")).toBe("normal");
  });

  it("returns 'darken' for darken category modes", () => {
    const darkenModes: BlendMode[] = ["darken", "multiply", "color-burn", "linear-burn", "darker-color"];
    for (const mode of darkenModes) {
      expect(getBlendModeCategory(mode)).toBe("darken");
    }
  });

  it("returns 'lighten' for lighten category modes", () => {
    const lightenModes: BlendMode[] = ["lighten", "screen", "color-dodge", "linear-dodge", "lighter-color", "add"];
    for (const mode of lightenModes) {
      expect(getBlendModeCategory(mode)).toBe("lighten");
    }
  });

  it("returns 'contrast' for contrast category modes", () => {
    const contrastModes: BlendMode[] = ["overlay", "soft-light", "hard-light", "vivid-light", "linear-light", "pin-light", "hard-mix"];
    for (const mode of contrastModes) {
      expect(getBlendModeCategory(mode)).toBe("contrast");
    }
  });

  it("returns 'inversion' for inversion category modes", () => {
    const inversionModes: BlendMode[] = ["difference", "exclusion", "subtract", "divide"];
    for (const mode of inversionModes) {
      expect(getBlendModeCategory(mode)).toBe("inversion");
    }
  });

  it("returns 'component' for component category modes", () => {
    const componentModes: BlendMode[] = ["hue", "saturation", "color", "luminosity"];
    for (const mode of componentModes) {
      expect(getBlendModeCategory(mode)).toBe("component");
    }
  });

  it("returns 'utility' for utility category modes", () => {
    const utilityModes: BlendMode[] = ["stencil-alpha", "stencil-luma", "silhouette-alpha", "silhouette-luma", "alpha-add", "luminescent-premul"];
    for (const mode of utilityModes) {
      expect(getBlendModeCategory(mode)).toBe("utility");
    }
  });

  it("is deterministic (same input = same output)", () => {
    fc.assert(
      fc.property(blendModeArb, (mode) => {
        const result1 = getBlendModeCategory(mode);
        const result2 = getBlendModeCategory(mode);
        expect(result1).toBe(result2);
      })
    );
  });
});

// ============================================================
// getBlendModesInCategory TESTS
// ============================================================

describe("PROPERTY: getBlendModesInCategory", () => {
  it("returns an array", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const result = getBlendModesInCategory(category);
        expect(Array.isArray(result)).toBe(true);
      })
    );
  });

  it("returns non-empty array for all categories", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const result = getBlendModesInCategory(category);
        expect(result.length).toBeGreaterThan(0);
      })
    );
  });

  it("all returned modes are valid BlendMode values", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const result = getBlendModesInCategory(category);
        for (const mode of result) {
          expect(ALL_BLEND_MODES).toContain(mode);
        }
      })
    );
  });

  it("returns correct count for 'normal' category (2 modes)", () => {
    expect(getBlendModesInCategory("normal")).toHaveLength(2);
  });

  it("returns correct count for 'darken' category (5 modes)", () => {
    expect(getBlendModesInCategory("darken")).toHaveLength(5);
  });

  it("returns correct count for 'lighten' category (6 modes)", () => {
    expect(getBlendModesInCategory("lighten")).toHaveLength(6);
  });

  it("returns correct count for 'contrast' category (7 modes)", () => {
    expect(getBlendModesInCategory("contrast")).toHaveLength(7);
  });

  it("returns correct count for 'inversion' category (4 modes)", () => {
    expect(getBlendModesInCategory("inversion")).toHaveLength(4);
  });

  it("returns correct count for 'component' category (4 modes)", () => {
    expect(getBlendModesInCategory("component")).toHaveLength(4);
  });

  it("returns correct count for 'utility' category (6 modes)", () => {
    expect(getBlendModesInCategory("utility")).toHaveLength(6);
  });

  it("returned modes map back to the same category", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const modes = getBlendModesInCategory(category);
        for (const mode of modes) {
          expect(getBlendModeCategory(mode)).toBe(category);
        }
      })
    );
  });

  it("is deterministic (same input = same output)", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const result1 = getBlendModesInCategory(category);
        const result2 = getBlendModesInCategory(category);
        expect(result1).toEqual(result2);
      })
    );
  });

  it("returns a new array each call (no mutation risk)", () => {
    fc.assert(
      fc.property(categoryArb, (category) => {
        const result1 = getBlendModesInCategory(category);
        const result2 = getBlendModesInCategory(category);
        expect(result1).not.toBe(result2); // Different array instances
        expect(result1).toEqual(result2);   // But same contents
      })
    );
  });
});

// ============================================================
// getAllBlendModes TESTS
// ============================================================

describe("PROPERTY: getAllBlendModes", () => {
  it("returns an array", () => {
    const result = getAllBlendModes();
    expect(Array.isArray(result)).toBe(true);
  });

  it("returns exactly 34 blend modes", () => {
    const result = getAllBlendModes();
    expect(result).toHaveLength(34);
  });

  it("contains no duplicates", () => {
    const result = getAllBlendModes();
    const unique = new Set(result);
    expect(unique.size).toBe(result.length);
  });

  it("all items are valid BlendMode values", () => {
    const result = getAllBlendModes();
    for (const mode of result) {
      expect(ALL_BLEND_MODES).toContain(mode);
    }
  });

  it("contains all expected blend modes", () => {
    const result = getAllBlendModes();
    for (const mode of ALL_BLEND_MODES) {
      expect(result).toContain(mode);
    }
  });

  it("is deterministic (same output every call)", () => {
    const result1 = getAllBlendModes();
    const result2 = getAllBlendModes();
    expect(result1).toEqual(result2);
  });

  it("returns a new array each call (no mutation risk)", () => {
    const result1 = getAllBlendModes();
    const result2 = getAllBlendModes();
    expect(result1).not.toBe(result2); // Different array instances
  });

  it("union of all categories equals all blend modes", () => {
    const fromCategories = new Set<BlendMode>();
    for (const category of CATEGORY_KEYS) {
      for (const mode of getBlendModesInCategory(category)) {
        fromCategories.add(mode);
      }
    }
    const allModes = getAllBlendModes();
    expect(fromCategories.size).toBe(allModes.length);
    for (const mode of allModes) {
      expect(fromCategories.has(mode)).toBe(true);
    }
  });
});
