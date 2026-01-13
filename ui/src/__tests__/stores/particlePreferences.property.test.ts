/**
 * Property Tests for Particle Preferences Store
 *
 * Tests the particlePreferences store using fast-check for
 * comprehensive property-based testing.
 */

import { describe, it, expect, beforeEach, vi } from "vitest";
import * as fc from "fast-check";
import { setActivePinia, createPinia } from "pinia";
import {
  useParticlePreferencesStore,
  type ParticlePreferences,
  type RenderingBackend,
  type SimulationMode,
} from "../../stores/particlePreferences";

// Mock localStorage
const localStorageMock = (() => {
  let store: Record<string, string> = {};
  return {
    getItem: vi.fn((key: string) => store[key] ?? null),
    setItem: vi.fn((key: string, value: string) => {
      store[key] = value;
    }),
    removeItem: vi.fn((key: string) => {
      delete store[key];
    }),
    clear: vi.fn(() => {
      store = {};
    }),
    get length() {
      return Object.keys(store).length;
    },
    key: vi.fn((index: number) => Object.keys(store)[index] ?? null),
  };
})();

Object.defineProperty(global, "localStorage", {
  value: localStorageMock,
  writable: true,
});

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbRenderingBackend = fc.constantFrom<RenderingBackend>(
  "auto",
  "webgpu",
  "webgl2",
  "cpu",
);

const arbSimulationMode = fc.constantFrom<SimulationMode>(
  "realtime",
  "cached",
  "baked",
);

const arbValidMaxParticles = fc.integer({ min: 1000, max: 500000 });
const arbValidCacheMemory = fc.integer({ min: 128, max: 2048 });
const arbValidTargetFPS = fc.constantFrom(30, 60);
const arbValidCheckpointInterval = fc.integer({ min: 1, max: 120 });

const arbPartialPreferences = fc.record({
  renderingBackend: fc.option(arbRenderingBackend, { nil: undefined }),
  simulationMode: fc.option(arbSimulationMode, { nil: undefined }),
  cacheCheckpointInterval: fc.option(arbValidCheckpointInterval, { nil: undefined }),
  maxCacheMemoryMB: fc.option(arbValidCacheMemory, { nil: undefined }),
  maxParticlesPerLayer: fc.option(arbValidMaxParticles, { nil: undefined }),
  enableGPUCompute: fc.option(fc.boolean(), { nil: undefined }),
  targetFPS: fc.option(arbValidTargetFPS, { nil: undefined }),
  enableMotionBlur: fc.option(fc.boolean(), { nil: undefined }),
  enableSoftParticles: fc.option(fc.boolean(), { nil: undefined }),
  enableShadows: fc.option(fc.boolean(), { nil: undefined }),
  lodEnabled: fc.option(fc.boolean(), { nil: undefined }),
});

// ============================================================================
// TESTS
// ============================================================================

describe("Particle Preferences Store - Property Tests", () => {
  beforeEach(() => {
    // Create a fresh Pinia instance for each test
    setActivePinia(createPinia());
    // Clear localStorage mock to avoid cross-test contamination
    localStorageMock.clear();
    vi.clearAllMocks();
  });

  describe("Store Initialization", () => {
    it("should have valid default values", () => {
      const store = useParticlePreferencesStore();
      const prefs = store.preferences;

      expect(prefs.renderingBackend).toBe("auto");
      expect(prefs.simulationMode).toBe("cached");
      expect(prefs.cacheCheckpointInterval).toBe(30);
      expect(prefs.maxCacheMemoryMB).toBe(512);
      expect(prefs.maxParticlesPerLayer).toBe(100000);
      expect(prefs.enableGPUCompute).toBe(true);
      expect(prefs.targetFPS).toBe(60);
    });

    it("should never have NaN or Infinity in numeric preferences", () => {
      fc.assert(
        fc.property(arbPartialPreferences, (updates) => {
          const store = useParticlePreferencesStore();

          // Filter out undefined values
          const filteredUpdates = Object.fromEntries(
            Object.entries(updates).filter(([_, v]) => v !== undefined),
          ) as Partial<ParticlePreferences>;

          store.updatePreferences(filteredUpdates);

          const prefs = store.preferences;
          expect(Number.isFinite(prefs.cacheCheckpointInterval)).toBe(true);
          expect(Number.isFinite(prefs.maxCacheMemoryMB)).toBe(true);
          expect(Number.isFinite(prefs.maxParticlesPerLayer)).toBe(true);
          expect(Number.isFinite(prefs.targetFPS)).toBe(true);
        }),
      );
    });
  });

  describe("Preference Updates", () => {
    it("should persist updates correctly", () => {
      fc.assert(
        fc.property(arbRenderingBackend, arbSimulationMode, (backend, mode) => {
          const store = useParticlePreferencesStore();

          store.updatePreferences({
            renderingBackend: backend,
            simulationMode: mode,
          });

          expect(store.preferences.renderingBackend).toBe(backend);
          expect(store.preferences.simulationMode).toBe(mode);
        }),
      );
    });

    it("should not corrupt other preferences when updating one", () => {
      fc.assert(
        fc.property(
          arbValidMaxParticles,
          fc.boolean(),
          (maxParticles, motionBlur) => {
            const store = useParticlePreferencesStore();

            const originalBackend = store.preferences.renderingBackend;
            const originalMode = store.preferences.simulationMode;

            store.updatePreferences({
              maxParticlesPerLayer: maxParticles,
              enableMotionBlur: motionBlur,
            });

            // Other preferences should remain unchanged
            expect(store.preferences.renderingBackend).toBe(originalBackend);
            expect(store.preferences.simulationMode).toBe(originalMode);
          },
        ),
      );
    });

    it("should handle multiple rapid updates without data loss", () => {
      fc.assert(
        fc.property(
          fc.array(arbPartialPreferences, { minLength: 1, maxLength: 10 }),
          (updateSequence) => {
            const store = useParticlePreferencesStore();

            let expectedBackend = store.preferences.renderingBackend;
            let expectedMode = store.preferences.simulationMode;

            for (const update of updateSequence) {
              const filteredUpdate = Object.fromEntries(
                Object.entries(update).filter(([_, v]) => v !== undefined),
              ) as Partial<ParticlePreferences>;

              store.updatePreferences(filteredUpdate);

              if (filteredUpdate.renderingBackend !== undefined) {
                expectedBackend = filteredUpdate.renderingBackend;
              }
              if (filteredUpdate.simulationMode !== undefined) {
                expectedMode = filteredUpdate.simulationMode;
              }
            }

            expect(store.preferences.renderingBackend).toBe(expectedBackend);
            expect(store.preferences.simulationMode).toBe(expectedMode);
          },
        ),
      );
    });
  });

  describe("Backend Selection", () => {
    it("activeBackend should always return a valid backend", () => {
      fc.assert(
        fc.property(arbRenderingBackend, (backend) => {
          const store = useParticlePreferencesStore();
          store.updatePreferences({ renderingBackend: backend });

          const active = store.activeBackend;
          expect(["auto", "webgpu", "webgl2", "cpu"]).toContain(active);
        }),
      );
    });

    it("auto backend should fall back gracefully when GPU unavailable", () => {
      const store = useParticlePreferencesStore();
      store.updatePreferences({ renderingBackend: "auto" });

      // When no GPU detected, should fall back to cpu
      // (since detectCapabilities hasn't been called in test environment)
      const active = store.activeBackend;
      expect(["webgpu", "webgl2", "cpu"]).toContain(active);
    });
  });

  describe("Presets", () => {
    it("low-end preset should reduce resource usage", () => {
      const store = useParticlePreferencesStore();
      store.applyLowEndPreset();

      expect(store.preferences.maxParticlesPerLayer).toBeLessThanOrEqual(50000);
      expect(store.preferences.enableGPUCompute).toBe(false);
      expect(store.preferences.targetFPS).toBeLessThanOrEqual(30);
      expect(store.preferences.enableMotionBlur).toBe(false);
      expect(store.preferences.enableSoftParticles).toBe(false);
      expect(store.preferences.enableShadows).toBe(false);
    });

    it("high-end preset should maximize quality", () => {
      const store = useParticlePreferencesStore();
      store.applyHighEndPreset();

      expect(store.preferences.maxParticlesPerLayer).toBeGreaterThanOrEqual(100000);
      expect(store.preferences.enableGPUCompute).toBe(true);
      expect(store.preferences.targetFPS).toBe(60);
      expect(store.preferences.enableMotionBlur).toBe(true);
      expect(store.preferences.enableSoftParticles).toBe(true);
      expect(store.preferences.enableShadows).toBe(true);
    });

    it("reset should restore defaults", () => {
      fc.assert(
        fc.property(arbPartialPreferences, (updates) => {
          const store = useParticlePreferencesStore();

          // First apply random updates
          const filteredUpdates = Object.fromEntries(
            Object.entries(updates).filter(([_, v]) => v !== undefined),
          ) as Partial<ParticlePreferences>;
          store.updatePreferences(filteredUpdates);

          // Then reset
          store.resetToDefaults();

          // Should be back to defaults
          expect(store.preferences.renderingBackend).toBe("auto");
          expect(store.preferences.simulationMode).toBe("cached");
          expect(store.preferences.maxParticlesPerLayer).toBe(100000);
        }),
      );
    });
  });

  describe("LocalStorage Persistence", () => {
    it("should save and load preferences correctly", () => {
      fc.assert(
        fc.property(
          arbRenderingBackend,
          arbSimulationMode,
          arbValidMaxParticles,
          (backend, mode, maxParticles) => {
            // Create first store and update preferences
            const store1 = useParticlePreferencesStore();
            store1.updatePreferences({
              renderingBackend: backend,
              simulationMode: mode,
              maxParticlesPerLayer: maxParticles,
            });

            // Get raw localStorage value
            const saved = localStorage.getItem("lattice-particle-preferences");
            expect(saved).not.toBeNull();

            // Parse and verify
            const parsed = JSON.parse(saved!);
            expect(parsed.renderingBackend).toBe(backend);
            expect(parsed.simulationMode).toBe(mode);
            expect(parsed.maxParticlesPerLayer).toBe(maxParticles);
          },
        ),
      );
    });

    it("should handle corrupted localStorage gracefully", () => {
      // Corrupt localStorage
      localStorage.setItem("lattice-particle-preferences", "not valid json{{{");

      // Store should initialize with defaults without crashing
      const store = useParticlePreferencesStore();
      expect(store.preferences.renderingBackend).toBe("auto");
      expect(store.preferences.simulationMode).toBe("cached");
    });

    it("should handle partial localStorage data gracefully", () => {
      // Only partial data
      localStorage.setItem(
        "lattice-particle-preferences",
        JSON.stringify({ renderingBackend: "webgl2" }),
      );

      const store = useParticlePreferencesStore();
      expect(store.preferences.renderingBackend).toBe("webgl2");
      // Other values should be defaults
      expect(store.preferences.simulationMode).toBe("cached");
      expect(store.preferences.maxParticlesPerLayer).toBe(100000);
    });
  });

  describe("Computed Properties", () => {
    it("backendDescription should always be a non-empty string", () => {
      fc.assert(
        fc.property(arbRenderingBackend, (backend) => {
          const store = useParticlePreferencesStore();
          store.updatePreferences({ renderingBackend: backend });

          expect(typeof store.backendDescription).toBe("string");
          expect(store.backendDescription.length).toBeGreaterThan(0);
        }),
      );
    });

    it("supportsHighParticleCounts should be false for CPU backend", () => {
      const store = useParticlePreferencesStore();
      store.updatePreferences({ renderingBackend: "cpu" });

      // CPU backend should not support high particle counts
      expect(store.supportsHighParticleCounts).toBe(false);
    });
  });

  describe("Edge Cases", () => {
    it("should handle empty updates without crashing", () => {
      const store = useParticlePreferencesStore();
      const before = { ...store.preferences };

      store.updatePreferences({});

      expect(store.preferences.renderingBackend).toBe(before.renderingBackend);
    });

    it("should handle null/undefined values in updates gracefully", () => {
      const store = useParticlePreferencesStore();

      // @ts-expect-error - Testing runtime behavior with invalid input
      store.updatePreferences({ renderingBackend: null });

      // Should either keep old value or default, not crash
      expect(["auto", "webgpu", "webgl2", "cpu", null]).toContain(
        store.preferences.renderingBackend,
      );
    });
  });
});

describe("Preference Invariants", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    localStorageMock.clear();
    vi.clearAllMocks();
  });

  it("maxParticlesPerLayer should always be positive", () => {
    fc.assert(
      fc.property(fc.integer({ min: -1000000, max: 1000000 }), (value) => {
        const store = useParticlePreferencesStore();
        store.updatePreferences({ maxParticlesPerLayer: value });

        // Store may clamp or reject invalid values
        // But should never have negative particles
        if (value <= 0) {
          // Either rejected or clamped to a minimum
          expect(store.preferences.maxParticlesPerLayer).toBeGreaterThan(0);
        }
      }),
    );
  });

  it("targetFPS should be 30 or 60", () => {
    fc.assert(
      fc.property(fc.integer({ min: 1, max: 120 }), (value) => {
        const store = useParticlePreferencesStore();
        store.updatePreferences({ targetFPS: value as 30 | 60 });

        // FPS should be one of the valid values
        expect([30, 60]).toContain(store.preferences.targetFPS);
      }),
    );
  });

  it("cacheCheckpointInterval should be positive", () => {
    fc.assert(
      fc.property(fc.integer({ min: -100, max: 200 }), (value) => {
        const store = useParticlePreferencesStore();
        store.updatePreferences({ cacheCheckpointInterval: value });

        // Should always be positive
        expect(store.preferences.cacheCheckpointInterval).toBeGreaterThan(0);
      }),
    );
  });
});
