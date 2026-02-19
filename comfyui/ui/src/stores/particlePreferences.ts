/**
 * Particle System Preferences Store
 *
 * Controls the hybrid CPU/GPU particle system:
 * - CPU: Handles simulation (deterministic, scrubbable, exportable)
 * - GPU: Handles rendering (beautiful, fast, 100k+ particles)
 *
 * Users without WebGPU still get GPU rendering via WebGL2 instanced rendering.
 * The CPU simulation is ALWAYS used for position calculation to ensure
 * determinism for timeline scrubbing and export.
 */

import { defineStore } from "pinia";
import { ref, computed } from "vue";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export type RenderingBackend = "auto" | "webgpu" | "webgl2" | "cpu";
export type SimulationMode = "realtime" | "cached" | "baked";

/**
 * Extended GPUAdapter interface for newer WebGPU APIs.
 * requestAdapterInfo was added to WebGPU spec but may not be in all TS type definitions.
 */
interface GPUAdapterWithInfo extends GPUAdapter {
  requestAdapterInfo?(): Promise<{ device?: string; description?: string; vendor?: string }>;
}

export interface ParticlePreferences {
  /**
   * Rendering backend preference
   * - "auto": Best available (WebGPU → WebGL2 → CPU)
   * - "webgpu": Force WebGPU (fails if unavailable)
   * - "webgl2": Force WebGL2 instanced rendering
   * - "cpu": Software rendering (Canvas2D fallback)
   */
  renderingBackend: RenderingBackend;

  /**
   * Simulation mode
   * - "realtime": Simulate on-the-fly during playback
   * - "cached": Simulate once, cache checkpoints for scrubbing
   * - "baked": Pre-bake all frames to keyframes (most deterministic)
   */
  simulationMode: SimulationMode;

  /**
   * Cache settings
   */
  cacheCheckpointInterval: number; // Frames between checkpoints (default: 30)
  maxCacheMemoryMB: number; // Max memory for particle cache (default: 512)

  /**
   * Performance settings
   */
  maxParticlesPerLayer: number; // Cap per layer (default: 100000)
  enableGPUCompute: boolean; // Use GPU for physics (WebGPU only)
  targetFPS: number; // Target framerate (30/60)

  /**
   * Quality settings
   */
  enableMotionBlur: boolean;
  enableSoftParticles: boolean;
  enableShadows: boolean;
  lodEnabled: boolean;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // defaults
// ═══════════════════════════════════════════════════════════════════════════

const defaultPreferences: ParticlePreferences = {
  renderingBackend: "auto",
  simulationMode: "cached",
  cacheCheckpointInterval: 30,
  maxCacheMemoryMB: 512,
  maxParticlesPerLayer: 100000,
  enableGPUCompute: true,
  targetFPS: 60,
  enableMotionBlur: true,
  enableSoftParticles: true,
  enableShadows: false,
  lodEnabled: true,
};

// ═══════════════════════════════════════════════════════════════════════════
//                                                                    // store
// ═══════════════════════════════════════════════════════════════════════════

export const useParticlePreferencesStore = defineStore("particlePreferences", () => {
  // State
  const preferences = ref<ParticlePreferences>({ ...defaultPreferences });

  // Detected capabilities
  const hasWebGPU = ref(false);
  const hasWebGL2 = ref(false);
  const detectedBackend = ref<RenderingBackend>("cpu");
  const gpuName = ref<string>("Unknown");
  const initialized = ref(false);

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                           // initialization
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Detect GPU capabilities
   * Called once on app startup
   */
  async function detectCapabilities(): Promise<void> {
    if (initialized.value) return;

    // Check WebGPU
    if (typeof navigator !== "undefined" && "gpu" in navigator) {
      try {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const navigatorGpu = (navigator != null && typeof navigator === "object" && "gpu" in navigator && navigator.gpu != null && typeof navigator.gpu === "object") ? navigator.gpu : undefined;
        const requestAdapter = (navigatorGpu != null && typeof navigatorGpu === "object" && typeof navigatorGpu.requestAdapter === "function") ? navigatorGpu.requestAdapter : undefined;
        const adapter = requestAdapter != null ? await requestAdapter() : undefined;
        if (adapter != null) {
          hasWebGPU.value = true;
          // requestAdapterInfo is not available in all implementations
          try {
            const adapterWithInfo = adapter as GPUAdapterWithInfo;
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const requestAdapterInfo = (adapterWithInfo != null && typeof adapterWithInfo === "object" && typeof adapterWithInfo.requestAdapterInfo === "function") ? adapterWithInfo.requestAdapterInfo : undefined;
            const info = requestAdapterInfo != null ? await requestAdapterInfo() : undefined;
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const infoDevice = (info != null && typeof info === "object" && "device" in info && typeof info.device === "string") ? info.device : undefined;
            const infoDescription = (info != null && typeof info === "object" && "description" in info && typeof info.description === "string") ? info.description : undefined;
            gpuName.value = infoDevice != null ? infoDevice : (infoDescription != null ? infoDescription : "WebGPU Device");
          } catch {
            gpuName.value = "WebGPU Device";
          }
        }
      } catch {
        hasWebGPU.value = false;
      }
    }

    // Check WebGL2
    if (typeof document !== "undefined") {
      try {
        const canvas = document.createElement("canvas");
        const gl = canvas.getContext("webgl2");
        hasWebGL2.value = !!gl;
        if (gl) {
          const debugInfo = gl.getExtension("WEBGL_debug_renderer_info");
          if (debugInfo) {
            gpuName.value = gl.getParameter(debugInfo.UNMASKED_RENDERER_WEBGL) || gpuName.value;
          }
        }
      } catch {
        hasWebGL2.value = false;
      }
    }

    // Determine best backend
    if (hasWebGPU.value) {
      detectedBackend.value = "webgpu";
    } else if (hasWebGL2.value) {
      detectedBackend.value = "webgl2";
    } else {
      detectedBackend.value = "cpu";
    }

    initialized.value = true;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                                 // computed
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Actual rendering backend to use
   */
  const activeBackend = computed<RenderingBackend>(() => {
    if (preferences.value.renderingBackend === "auto") {
      return detectedBackend.value;
    }

    // Validate forced backend is available
    const forced = preferences.value.renderingBackend;
    if (forced === "webgpu" && !hasWebGPU.value) {
      console.warn("WebGPU requested but not available, falling back to WebGL2");
      return hasWebGL2.value ? "webgl2" : "cpu";
    }
    if (forced === "webgl2" && !hasWebGL2.value) {
      console.warn("WebGL2 requested but not available, falling back to CPU");
      return "cpu";
    }

    return forced;
  });

  /**
   * Whether GPU compute is actually available and enabled
   */
  const gpuComputeActive = computed(() => {
    return preferences.value.enableGPUCompute && hasWebGPU.value;
  });

  /**
   * Human-readable backend description
   */
  const backendDescription = computed(() => {
    switch (activeBackend.value) {
      case "webgpu":
        return `WebGPU (${gpuName.value})`;
      case "webgl2":
        return `WebGL2 (${gpuName.value})`;
      case "cpu":
        return "Software Rendering";
      default:
        return "Unknown";
    }
  });

  /**
   * Whether the current setup supports high particle counts
   */
  const supportsHighParticleCounts = computed(() => {
    return activeBackend.value !== "cpu";
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                                  // actions
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Update preferences
   */
  function updatePreferences(updates: Partial<ParticlePreferences>): void {
    // Validate and sanitize numeric values
    const sanitized = { ...updates };

    // maxParticlesPerLayer: must be positive, between 1000 and 500000
    if (sanitized.maxParticlesPerLayer !== undefined) {
      const val = sanitized.maxParticlesPerLayer;
      if (!Number.isFinite(val) || val <= 0) {
        sanitized.maxParticlesPerLayer = defaultPreferences.maxParticlesPerLayer;
      } else {
        sanitized.maxParticlesPerLayer = Math.max(1000, Math.min(500000, Math.floor(val)));
      }
    }

    // cacheCheckpointInterval: must be positive, between 1 and 120
    if (sanitized.cacheCheckpointInterval !== undefined) {
      const val = sanitized.cacheCheckpointInterval;
      if (!Number.isFinite(val) || val <= 0) {
        sanitized.cacheCheckpointInterval = defaultPreferences.cacheCheckpointInterval;
      } else {
        sanitized.cacheCheckpointInterval = Math.max(1, Math.min(120, Math.floor(val)));
      }
    }

    // maxCacheMemoryMB: must be positive, between 128 and 2048
    if (sanitized.maxCacheMemoryMB !== undefined) {
      const val = sanitized.maxCacheMemoryMB;
      if (!Number.isFinite(val) || val <= 0) {
        sanitized.maxCacheMemoryMB = defaultPreferences.maxCacheMemoryMB;
      } else {
        sanitized.maxCacheMemoryMB = Math.max(128, Math.min(2048, Math.floor(val)));
      }
    }

    // targetFPS: must be 30 or 60
    if (sanitized.targetFPS !== undefined) {
      const val = sanitized.targetFPS;
      if (val !== 30 && val !== 60) {
        // Round to nearest valid value
        sanitized.targetFPS = val < 45 ? 30 : 60;
      }
    }

    preferences.value = { ...preferences.value, ...sanitized };
    saveToLocalStorage();
  }

  /**
   * Reset to defaults
   */
  function resetToDefaults(): void {
    preferences.value = { ...defaultPreferences };
    saveToLocalStorage();
  }

  /**
   * Save to local storage
   */
  function saveToLocalStorage(): void {
    try {
      localStorage.setItem("lattice-particle-preferences", JSON.stringify(preferences.value));
    } catch {
      console.warn("Failed to save particle preferences to localStorage");
    }
  }

  /**
   * Load from local storage
   */
  function loadFromLocalStorage(): void {
    try {
      const saved = localStorage.getItem("lattice-particle-preferences");
      if (saved) {
        const parsed = JSON.parse(saved);
        preferences.value = { ...defaultPreferences, ...parsed };
      }
    } catch {
      console.warn("Failed to load particle preferences from localStorage");
    }
  }

  /**
   * Get preset for low-end systems
   */
  function applyLowEndPreset(): void {
    updatePreferences({
      renderingBackend: "webgl2",
      maxParticlesPerLayer: 10000,
      enableGPUCompute: false,
      targetFPS: 30,
      enableMotionBlur: false,
      enableSoftParticles: false,
      enableShadows: false,
      lodEnabled: true,
    });
  }

  /**
   * Get preset for high-end systems
   */
  function applyHighEndPreset(): void {
    updatePreferences({
      renderingBackend: "auto",
      maxParticlesPerLayer: 500000,
      enableGPUCompute: true,
      targetFPS: 60,
      enableMotionBlur: true,
      enableSoftParticles: true,
      enableShadows: true,
      lodEnabled: true,
    });
  }

  // Initialize
  loadFromLocalStorage();

  return {
    // State
    preferences,
    hasWebGPU,
    hasWebGL2,
    detectedBackend,
    gpuName,
    initialized,

    // Computed
    activeBackend,
    gpuComputeActive,
    backendDescription,
    supportsHighParticleCounts,

    // Actions
    detectCapabilities,
    updatePreferences,
    resetToDefaults,
    applyLowEndPreset,
    applyHighEndPreset,
  };
});
