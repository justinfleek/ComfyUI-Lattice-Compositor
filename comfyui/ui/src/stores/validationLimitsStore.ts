/**
 * Validation Limits Store
 *
 * Configurable validation limits for schemas.
 * Allows power users to increase limits for high-performance systems
 * while maintaining security defaults.
 */

import { ref, computed } from "vue";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Default Limits (Security-Safe Defaults)
// ════════════════════════════════════════════════════════════════════════════

export interface ValidationLimits {
  // Dimensions
  maxDimension: number; // Max width/height (default: 8192)
  maxDimensionAbsolute: number; // Absolute max, never configurable (16384)

  // Frames
  maxFrameCount: number; // Max frames per composition (default: 10000)
  maxFrameCountAbsolute: number; // Absolute max, never configurable (50000)

  // Arrays
  maxArrayLength: number; // Max array length (default: 100000)
  maxArrayLengthAbsolute: number; // Absolute max, never configurable (1000000)

  // Particles
  maxParticles: number; // Max particles per system (default: 1000000)
  maxParticlesAbsolute: number; // Absolute max, never configurable (10000000)

  // Layers
  maxLayers: number; // Max layers per composition (default: 1000)
  maxLayersAbsolute: number; // Absolute max, never configurable (5000)

  // Keyframes
  maxKeyframesPerProperty: number; // Max keyframes per property (default: 10000)
  maxKeyframesPerPropertyAbsolute: number; // Absolute max, never configurable (50000)

  // Strings
  maxStringLength: number; // Max string length (default: 100000)
  maxStringLengthAbsolute: number; // Absolute max, never configurable (1000000)

  //                                                                       // fps
  maxFPS: number; // Max frame rate (default: 120)
  maxFPSAbsolute: number; // Absolute max, never configurable (240)
}

const DEFAULT_LIMITS: ValidationLimits = {
  // Dimensions - matches workflow validation
  maxDimension: 8192,
  maxDimensionAbsolute: 16384,

  // Frames - matches workflow validation
  maxFrameCount: 10000,
  maxFrameCountAbsolute: 50000,

  // Arrays - matches Python backend
  maxArrayLength: 100000,
  maxArrayLengthAbsolute: 1000000,

  // Particles - reasonable default
  maxParticles: 1000000,
  maxParticlesAbsolute: 10000000,

  // Layers - matches Python backend
  maxLayers: 1000,
  maxLayersAbsolute: 5000,

  // Keyframes - matches Python backend
  maxKeyframesPerProperty: 10000,
  maxKeyframesPerPropertyAbsolute: 50000,

  // Strings - matches Python backend
  maxStringLength: 100000,
  maxStringLengthAbsolute: 1000000,

  //                                                                       // fps
  maxFPS: 120,
  maxFPSAbsolute: 240,
};

// ════════════════════════════════════════════════════════════════════════════
// Store
// ════════════════════════════════════════════════════════════════════════════

const STORAGE_KEY = "lattice-validation-limits";

const limits = ref<ValidationLimits>({ ...DEFAULT_LIMITS });

/**
 * Load limits from localStorage
 */
function loadLimits(): void {
  try {
    const saved = localStorage.getItem(STORAGE_KEY);
    if (saved) {
      const parsed = JSON.parse(saved);
      // Merge with defaults, ensuring absolute limits are never exceeded
      const loaded: Partial<ValidationLimits> = {};
      for (const key in DEFAULT_LIMITS) {
        const k = key as keyof ValidationLimits;
        if (parsed[k] !== undefined) {
          // Check if this is an absolute limit (should never be changed)
          if (k.endsWith("Absolute")) {
            // Absolute limits are never configurable
            loaded[k] = DEFAULT_LIMITS[k];
          } else {
            // Configurable limits must be within absolute bounds
            const absoluteKey = `${k}Absolute` as keyof ValidationLimits;
            const absoluteValue = DEFAULT_LIMITS[absoluteKey];
            loaded[k] = Math.min(Math.max(parsed[k], 0), absoluteValue);
          }
        } else {
          loaded[k] = DEFAULT_LIMITS[k];
        }
      }
      limits.value = { ...DEFAULT_LIMITS, ...loaded };
    }
  } catch (e) {
    console.warn("Failed to load validation limits:", e);
    limits.value = { ...DEFAULT_LIMITS };
  }
}

/**
 * Save limits to localStorage
 */
function saveLimits(): void {
  try {
    // Only save configurable limits, not absolute ones
    const toSave: Partial<ValidationLimits> = {};
    for (const key in limits.value) {
      const k = key as keyof ValidationLimits;
      if (!k.endsWith("Absolute")) {
        toSave[k] = limits.value[k];
      }
    }
    localStorage.setItem(STORAGE_KEY, JSON.stringify(toSave));
  } catch (e) {
    console.warn("Failed to save validation limits:", e);
  }
}

/**
 * Update limits (with validation)
 */
function updateLimits(updates: Partial<ValidationLimits>): void {
  for (const key in updates) {
    const k = key as keyof ValidationLimits;
    const value = updates[k];
    if (value === undefined) continue;

    // Never allow changing absolute limits
    if (k.endsWith("Absolute")) {
      console.warn(`Cannot change absolute limit: ${k}`);
      continue;
    }

    // Validate against absolute limits
    const absoluteKey = `${k}Absolute` as keyof ValidationLimits;
    const absoluteValue = DEFAULT_LIMITS[absoluteKey];
    if (value > absoluteValue || value < 0) {
      console.warn(
        `Limit ${k} must be between 0 and ${absoluteValue}, got ${value}`
      );
      continue;
    }

    limits.value[k] = value;
  }
  saveLimits();
}

/**
 * Reset to defaults
 */
function resetToDefaults(): void {
  limits.value = { ...DEFAULT_LIMITS };
  saveLimits();
}

/**
 * Get current limits (read-only)
 */
function getLimits(): Readonly<ValidationLimits> {
  return limits.value;
}

// Initialize
loadLimits();

// Update shared-validation.ts limits when store changes
import { watch } from "vue";
watch(limits, () => {
  // Update shared-validation module limits
  try {
    import("../schemas/shared-validation").then((module) => {
      // Use the proper updateLimits function instead of accessing private variables
      module.updateLimits({
        maxDimension: limits.value.maxDimension,
        maxFrameCount: limits.value.maxFrameCount,
        maxArrayLength: limits.value.maxArrayLength,
        maxParticles: limits.value.maxParticles,
        maxLayers: limits.value.maxLayers,
        maxKeyframesPerProperty: limits.value.maxKeyframesPerProperty,
        maxStringLength: limits.value.maxStringLength,
        maxFPS: limits.value.maxFPS,
      });
    });
  } catch (e) {
    // Ignore - module may not be loaded yet
  }
}, { deep: true });

export function useValidationLimitsStore() {
  return {
    // State
    limits: computed(() => limits.value),

    // Actions
    updateLimits,
    resetToDefaults,
    getLimits,
  };
}
