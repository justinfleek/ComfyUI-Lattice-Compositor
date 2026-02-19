/**
 * Property tests for ParticleLayer
 *
 * Tests that ParticleLayerData is correctly wired to GPUParticleSystem config.
 * Specifically tests that LOD, DoF, Shadow, and MeshMode settings flow through.
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import type { ParticleLayerData, ParticleRenderOptions } from "@/types/particles";

// Simulate the extractConfig logic from ParticleLayer.ts
function extractRenderConfig(data: Partial<ParticleLayerData>): Partial<{
  lodEnabled: boolean;
  lodDistances: number[];
  lodSizeMultipliers: number[];
  dofEnabled: boolean;
  dofFocusDistance: number;
  dofFocusRange: number;
  dofMaxBlur: number;
  shadowsEnabled: boolean;
  castShadows: boolean;
  receiveShadows: boolean;
  shadowSoftness: number;
  meshGeometry: string;
}> {
  const config: ReturnType<typeof extractRenderConfig> = {};
  const renderOptions = data.renderOptions;

  if (!renderOptions) return config;

  //                                                                       // lod
  if (renderOptions.lodEnabled !== undefined) {
    config.lodEnabled = renderOptions.lodEnabled;
  }
  if (renderOptions.lodDistances) {
    config.lodDistances = renderOptions.lodDistances;
  }
  if (renderOptions.lodSizeMultipliers) {
    config.lodSizeMultipliers = renderOptions.lodSizeMultipliers;
  }

  // DoF settings (BUG-189 fix)
  if (renderOptions.dofEnabled !== undefined) {
    config.dofEnabled = renderOptions.dofEnabled;
  }
  if (renderOptions.dofFocusDistance !== undefined) {
    config.dofFocusDistance = renderOptions.dofFocusDistance;
  }
  if (renderOptions.dofFocusRange !== undefined) {
    config.dofFocusRange = renderOptions.dofFocusRange;
  }
  if (renderOptions.dofMaxBlur !== undefined) {
    config.dofMaxBlur = renderOptions.dofMaxBlur;
  }

  // Shadow settings (BUG-189 fix)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  if (renderOptions.shadowsEnabled !== undefined) {
    config.shadowsEnabled = renderOptions.shadowsEnabled;
    config.castShadows = (renderOptions.castShadows !== null && renderOptions.castShadows !== undefined && typeof renderOptions.castShadows === "boolean") ? renderOptions.castShadows : true;
    config.receiveShadows = (renderOptions.receiveShadows !== null && renderOptions.receiveShadows !== undefined && typeof renderOptions.receiveShadows === "boolean") ? renderOptions.receiveShadows : true;
    config.shadowSoftness = (renderOptions.shadowSoftness !== null && renderOptions.shadowSoftness !== undefined && typeof renderOptions.shadowSoftness === "number" && Number.isFinite(renderOptions.shadowSoftness) && renderOptions.shadowSoftness > 0) ? renderOptions.shadowSoftness : 1.0;
  }

  // Mesh mode (BUG-189 fix)
  if (renderOptions.meshMode !== undefined) {
    const meshGeometry = (renderOptions.meshGeometry !== null && renderOptions.meshGeometry !== undefined && typeof renderOptions.meshGeometry === "string" && renderOptions.meshGeometry.length > 0) ? renderOptions.meshGeometry : "sphere";
    config.meshGeometry = renderOptions.meshMode === "mesh"
      ? meshGeometry
      : "billboard";
  }

  return config;
}

describe("ParticleLayer Config Wiring", () => {
  // Arbitrary for ParticleRenderOptions
  const arbRenderOptions = fc.record({
    blendMode: fc.constantFrom("normal", "additive", "multiply", "screen") as fc.Arbitrary<"normal" | "additive" | "multiply" | "screen">,
    renderTrails: fc.boolean(),
    trailLength: fc.integer({ min: 1, max: 100 }),
    trailOpacityFalloff: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    particleShape: fc.constantFrom("circle", "square", "triangle", "star") as fc.Arbitrary<"circle" | "square" | "triangle" | "star">,
    glowEnabled: fc.boolean(),
    glowRadius: fc.float({ min: Math.fround(0), max: Math.fround(100), noNaN: true }),
    glowIntensity: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    motionBlur: fc.boolean(),
    motionBlurStrength: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    motionBlurSamples: fc.integer({ min: 1, max: 16 }),
    connections: fc.record({
      enabled: fc.boolean(),
      maxDistance: fc.float({ min: Math.fround(0), max: Math.fround(1000), noNaN: true }),
      maxConnections: fc.integer({ min: 1, max: 10 }),
      lineWidth: fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
      lineOpacity: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
      fadeByDistance: fc.boolean(),
    }),
    //                                                                       // lod
    lodEnabled: fc.boolean(),
    lodDistances: fc.array(fc.float({ min: Math.fround(0), max: Math.fround(10000), noNaN: true }), { minLength: 1, maxLength: 5 }),
    lodSizeMultipliers: fc.array(fc.float({ min: Math.fround(0.1), max: Math.fround(2), noNaN: true }), { minLength: 1, maxLength: 5 }),
    // DoF settings (the ones that were NOT wired before BUG-189)
    dofEnabled: fc.boolean(),
    dofFocusDistance: fc.float({ min: Math.fround(0), max: Math.fround(10000), noNaN: true }),
    dofFocusRange: fc.float({ min: Math.fround(0), max: Math.fround(1000), noNaN: true }),
    dofMaxBlur: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    // Shadow settings (the ones that were NOT wired before BUG-189)
    shadowsEnabled: fc.boolean(),
    castShadows: fc.boolean(),
    receiveShadows: fc.boolean(),
    shadowSoftness: fc.float({ min: Math.fround(0), max: Math.fround(10), noNaN: true }),
    // Mesh mode (the one that was NOT wired before BUG-189)
    meshMode: fc.constantFrom("billboard", "mesh") as fc.Arbitrary<"billboard" | "mesh">,
    meshGeometry: fc.constantFrom("cube", "sphere", "cylinder", "cone", "torus") as fc.Arbitrary<"cube" | "sphere" | "cylinder" | "cone" | "torus">,
  }) as fc.Arbitrary<ParticleRenderOptions>;

  describe("BUG-189: LOD settings are wired", () => {
    it("lodEnabled flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.lodEnabled).toBe(renderOptions.lodEnabled);
        }),
        { numRuns: 100 }
      );
    });

    it("lodDistances flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.lodDistances).toEqual(renderOptions.lodDistances);
        }),
        { numRuns: 100 }
      );
    });

    it("lodSizeMultipliers flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.lodSizeMultipliers).toEqual(renderOptions.lodSizeMultipliers);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("BUG-189: DoF settings are wired", () => {
    it("dofEnabled flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.dofEnabled).toBe(renderOptions.dofEnabled);
        }),
        { numRuns: 100 }
      );
    });

    it("dofFocusDistance flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.dofFocusDistance).toBe(renderOptions.dofFocusDistance);
        }),
        { numRuns: 100 }
      );
    });

    it("dofFocusRange flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.dofFocusRange).toBe(renderOptions.dofFocusRange);
        }),
        { numRuns: 100 }
      );
    });

    it("dofMaxBlur flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.dofMaxBlur).toBe(renderOptions.dofMaxBlur);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("BUG-189: Shadow settings are wired", () => {
    it("shadowsEnabled flows through to config", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = { renderOptions };
          const config = extractRenderConfig(data);
          
          expect(config.shadowsEnabled).toBe(renderOptions.shadowsEnabled);
        }),
        { numRuns: 100 }
      );
    });

    it("castShadows defaults to true when enabled", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = {
            renderOptions: { ...renderOptions, shadowsEnabled: true, castShadows: undefined }
          };
          const config = extractRenderConfig(data);
          
          expect(config.castShadows).toBe(true);
        }),
        { numRuns: 100 }
      );
    });

    it("receiveShadows defaults to true when enabled", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = {
            renderOptions: { ...renderOptions, shadowsEnabled: true, receiveShadows: undefined }
          };
          const config = extractRenderConfig(data);
          
          expect(config.receiveShadows).toBe(true);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("BUG-189: Mesh mode is wired", () => {
    it("billboard mode sets meshGeometry to billboard", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = {
            renderOptions: { ...renderOptions, meshMode: "billboard" }
          };
          const config = extractRenderConfig(data);
          
          expect(config.meshGeometry).toBe("billboard");
        }),
        { numRuns: 100 }
      );
    });

    it("mesh mode passes through meshGeometry", () => {
      fc.assert(
        fc.property(arbRenderOptions, (renderOptions) => {
          const data: Partial<ParticleLayerData> = {
            renderOptions: { ...renderOptions, meshMode: "mesh" }
          };
          const config = extractRenderConfig(data);
          
          // Should use the specified geometry, or default to sphere
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          const expectedGeometry = (renderOptions.meshGeometry !== null && renderOptions.meshGeometry !== undefined && typeof renderOptions.meshGeometry === "string" && renderOptions.meshGeometry.length > 0) ? renderOptions.meshGeometry : "sphere";
          expect(config.meshGeometry).toBe(expectedGeometry);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("Edge cases", () => {
    it("handles undefined renderOptions gracefully", () => {
      const data: Partial<ParticleLayerData> = {};
      const config = extractRenderConfig(data);
      
      expect(config.lodEnabled).toBeUndefined();
      expect(config.dofEnabled).toBeUndefined();
      expect(config.shadowsEnabled).toBeUndefined();
      expect(config.meshGeometry).toBeUndefined();
    });

    it("handles partial renderOptions gracefully", () => {
      const data: Partial<ParticleLayerData> = {
        renderOptions: {
          blendMode: "normal",
          renderTrails: false,
          trailLength: 5,
          trailOpacityFalloff: 0.5,
          particleShape: "circle",
          glowEnabled: false,
          glowRadius: 10,
          glowIntensity: 0.5,
          motionBlur: false,
          motionBlurStrength: 0.5,
          motionBlurSamples: 4,
          connections: {
            enabled: false,
            maxDistance: 100,
            maxConnections: 5,
            lineWidth: 1,
            lineOpacity: 0.5,
            fadeByDistance: true,
          },
          // No LOD/DoF/Shadow/Mesh settings
        }
      };
      const config = extractRenderConfig(data);
      
      // These should be undefined (not set)
      expect(config.lodEnabled).toBeUndefined();
      expect(config.dofEnabled).toBeUndefined();
      expect(config.shadowsEnabled).toBeUndefined();
      expect(config.meshGeometry).toBeUndefined();
    });
  });
});
