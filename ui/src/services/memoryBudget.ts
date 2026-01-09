/**
 * Memory Budget Tracking Service
 *
 * Tracks estimated GPU/VRAM usage across the compositor to prevent
 * out-of-memory errors in complex workflows. Provides warnings and
 * auto-cleanup suggestions when approaching limits.
 */

import { computed, reactive, ref } from "vue";
import { createLogger } from "@/utils/logger";

const logger = createLogger("MemoryBudget");

// ============================================================================
// Types
// ============================================================================

export interface MemoryAllocation {
  id: string;
  name: string;
  category: MemoryCategory;
  estimatedMB: number;
  timestamp: number;
  canUnload: boolean;
  unloadFn?: () => Promise<void>;
}

export type MemoryCategory =
  | "model" // AI models (decomposition, depth, etc.)
  | "texture" // Image/video textures
  | "framebuffer" // Render targets, frame cache
  | "particles" // Particle system buffers
  | "geometry" // 3D geometry (point clouds, models)
  | "audio" // Audio buffers
  | "other";

export interface MemoryWarning {
  level: "info" | "warning" | "critical";
  message: string;
  suggestions: string[];
}

export interface GPUInfo {
  vendor: string;
  renderer: string;
  estimatedVRAM: number; // MB
  tier: "low" | "medium" | "high" | "ultra";
}

// ============================================================================
// Constants
// ============================================================================

/** Estimated VRAM for common operations (in MB) */
export const VRAM_ESTIMATES = {
  // AI Models
  "model:qwen-image-layered": 28800, // 28.8GB
  "model:depth-anything-v2": 2500,
  "model:segment-anything": 4000,
  "model:clip": 1500,
  "model:starvector": 4000, // ~4GB for 1B parameter model

  // Per-layer estimates
  "texture:1080p": 8, // 1920x1080 RGBA
  "texture:4k": 32, // 3840x2160 RGBA
  "texture:720p": 4, // 1280x720 RGBA

  // Frame cache (per frame)
  "framebuffer:1080p": 8,
  "framebuffer:4k": 32,

  // Particles (per 10k particles)
  "particles:10k": 50,

  // Point clouds (per 1M points)
  "pointcloud:1m": 100,

  // Audio (per minute of audio)
  "audio:minute": 10,
} as const;

/** Warning thresholds as percentage of estimated VRAM */
const THRESHOLDS = {
  info: 0.5, // 50% - getting busy
  warning: 0.75, // 75% - should consider cleanup
  critical: 0.9, // 90% - likely to fail soon
};

// ============================================================================
// State
// ============================================================================

const allocations = reactive<Map<string, MemoryAllocation>>(new Map());
const gpuInfo = ref<GPUInfo | null>(null);
const isInitialized = ref(false);

// ============================================================================
// Computed Values
// ============================================================================

/** Total estimated VRAM usage in MB */
export const totalUsageMB = computed(() => {
  let total = 0;
  for (const alloc of allocations.values()) {
    total += alloc.estimatedMB;
  }
  return total;
});

/** Usage by category */
export const usageByCategory = computed(() => {
  const byCategory: Record<MemoryCategory, number> = {
    model: 0,
    texture: 0,
    framebuffer: 0,
    particles: 0,
    geometry: 0,
    audio: 0,
    other: 0,
  };

  for (const alloc of allocations.values()) {
    byCategory[alloc.category] += alloc.estimatedMB;
  }

  return byCategory;
});

/** Estimated available VRAM */
export const availableVRAM = computed(() => {
  if (!gpuInfo.value) return 8000; // Default 8GB assumption
  return gpuInfo.value.estimatedVRAM;
});

/** Usage percentage (0-1) */
export const usagePercent = computed(() => {
  return totalUsageMB.value / availableVRAM.value;
});

/** Current warning level */
export const warningLevel = computed<"none" | "info" | "warning" | "critical">(
  () => {
    const percent = usagePercent.value;
    if (percent >= THRESHOLDS.critical) return "critical";
    if (percent >= THRESHOLDS.warning) return "warning";
    if (percent >= THRESHOLDS.info) return "info";
    return "none";
  },
);

/** List of all allocations */
export const allocationList = computed(() => {
  return Array.from(allocations.values()).sort(
    (a, b) => b.estimatedMB - a.estimatedMB,
  );
});

/** Items that can be unloaded */
export const unloadableItems = computed(() => {
  return allocationList.value.filter((a) => a.canUnload);
});

// ============================================================================
// Service Functions
// ============================================================================

/**
 * Initialize GPU detection
 */
export async function initializeGPUDetection(): Promise<void> {
  if (isInitialized.value) return;

  try {
    // Try WebGL to detect GPU
    const canvas = document.createElement("canvas");
    const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");

    if (gl) {
      const debugInfo = gl.getExtension("WEBGL_debug_renderer_info");
      const vendor = debugInfo
        ? gl.getParameter(debugInfo.UNMASKED_VENDOR_WEBGL)
        : "Unknown";
      const renderer = debugInfo
        ? gl.getParameter(debugInfo.UNMASKED_RENDERER_WEBGL)
        : "Unknown";

      // Log raw renderer string for debugging
      console.log("[Lattice] GPU Renderer string:", renderer);

      // Estimate VRAM based on GPU
      const estimatedVRAM = estimateVRAMFromRenderer(renderer);
      const tier = determineTier(estimatedVRAM);

      gpuInfo.value = {
        vendor,
        renderer,
        estimatedVRAM,
        tier,
      };

      console.log(
        `[Lattice] GPU detected: ${renderer} (~${estimatedVRAM}MB VRAM, tier: ${tier})`,
      );
    } else {
      // Fallback for no WebGL
      gpuInfo.value = {
        vendor: "Unknown",
        renderer: "Software",
        estimatedVRAM: 4000, // Conservative 4GB
        tier: "low",
      };
      logger.warn("WebGL not available, using conservative estimates");
    }

    isInitialized.value = true;
  } catch (error) {
    logger.error("GPU detection failed:", error);
    gpuInfo.value = {
      vendor: "Unknown",
      renderer: "Unknown",
      estimatedVRAM: 8000,
      tier: "medium",
    };
    isInitialized.value = true;
  }
}

/**
 * Register a memory allocation
 */
export function registerAllocation(
  id: string,
  name: string,
  category: MemoryCategory,
  estimatedMB: number,
  options?: {
    canUnload?: boolean;
    unloadFn?: () => Promise<void>;
  },
): void {
  const allocation: MemoryAllocation = {
    id,
    name,
    category,
    estimatedMB,
    timestamp: Date.now(),
    canUnload: options?.canUnload ?? false,
    unloadFn: options?.unloadFn,
  };

  allocations.set(id, allocation);
  logger.debug(
    `Registered: ${name} (${estimatedMB}MB) - Total: ${totalUsageMB.value}MB`,
  );

  // Check for warnings
  checkAndLogWarning();
}

/**
 * Unregister a memory allocation
 */
export function unregisterAllocation(id: string): void {
  const alloc = allocations.get(id);
  if (alloc) {
    allocations.delete(id);
    logger.debug(
      `Unregistered: ${alloc.name} - Total: ${totalUsageMB.value}MB`,
    );
  }
}

/**
 * Update an existing allocation's size
 */
export function updateAllocation(id: string, estimatedMB: number): void {
  const alloc = allocations.get(id);
  if (alloc) {
    alloc.estimatedMB = estimatedMB;
    checkAndLogWarning();
  }
}

/**
 * Get current memory warning
 */
export function getWarning(): MemoryWarning | null {
  const level = warningLevel.value;
  if (level === "none") return null;

  const percent = Math.round(usagePercent.value * 100);
  const suggestions: string[] = [];

  // Generate suggestions based on what's using memory
  const categories = usageByCategory.value;

  if (categories.model > 1000) {
    suggestions.push("Unload unused AI models to free GPU memory");
  }
  if (categories.texture > 500) {
    suggestions.push("Reduce image layer count or resolution");
  }
  if (categories.framebuffer > 200) {
    suggestions.push("Clear frame cache or reduce composition resolution");
  }
  if (categories.particles > 200) {
    suggestions.push("Reduce particle count or disable unused emitters");
  }
  if (categories.geometry > 500) {
    suggestions.push("Simplify point clouds or 3D models");
  }

  // Add specific unload suggestions
  const unloadable = unloadableItems.value.slice(0, 3);
  for (const item of unloadable) {
    if (item.estimatedMB > 100) {
      suggestions.push(
        `Unload "${item.name}" to free ${formatMB(item.estimatedMB)}`,
      );
    }
  }

  const messages = {
    info: `Memory usage at ${percent}% - consider cleanup for optimal performance`,
    warning: `Memory usage at ${percent}% - performance may degrade, cleanup recommended`,
    critical: `Memory usage at ${percent}% - high risk of crashes, immediate cleanup needed`,
  };

  return {
    level,
    message: messages[level],
    suggestions,
  };
}

/**
 * Check if an operation can proceed given current memory
 */
export function canAllocate(estimatedMB: number): {
  canProceed: boolean;
  warning: MemoryWarning | null;
} {
  const afterUsage = (totalUsageMB.value + estimatedMB) / availableVRAM.value;

  if (afterUsage >= THRESHOLDS.critical) {
    return {
      canProceed: false,
      warning: {
        level: "critical",
        message: `This operation requires ~${formatMB(estimatedMB)} but would exceed safe memory limits`,
        suggestions: [
          "Unload AI models before proceeding",
          "Close other GPU-intensive applications",
          "Reduce project complexity",
        ],
      },
    };
  }

  if (afterUsage >= THRESHOLDS.warning) {
    return {
      canProceed: true,
      warning: {
        level: "warning",
        message: `This operation requires ~${formatMB(estimatedMB)} - consider cleanup first`,
        suggestions: ["Unload unused models", "Clear frame cache"],
      },
    };
  }

  return { canProceed: true, warning: null };
}

/**
 * Attempt to free memory by unloading items
 */
export async function freeMemory(targetMB: number): Promise<number> {
  let freed = 0;

  // Sort by size (largest first) and unload until we hit target
  const candidates = unloadableItems.value;

  for (const item of candidates) {
    if (freed >= targetMB) break;

    if (item.unloadFn) {
      try {
        await item.unloadFn();
        freed += item.estimatedMB;
        unregisterAllocation(item.id);
        logger.info(
          `Freed ${formatMB(item.estimatedMB)} by unloading "${item.name}"`,
        );
      } catch (error) {
        logger.error(`Failed to unload "${item.name}":`, error);
      }
    }
  }

  return freed;
}

/**
 * Get a summary of current memory state
 */
export function getMemorySummary(): {
  total: number;
  available: number;
  used: number;
  percent: number;
  byCategory: Record<MemoryCategory, number>;
  gpu: GPUInfo | null;
  warning: MemoryWarning | null;
} {
  return {
    total: availableVRAM.value,
    available: availableVRAM.value - totalUsageMB.value,
    used: totalUsageMB.value,
    percent: usagePercent.value,
    byCategory: { ...usageByCategory.value },
    gpu: gpuInfo.value,
    warning: getWarning(),
  };
}

// ============================================================================
// Helper Functions
// ============================================================================

function estimateVRAMFromRenderer(renderer: string): number {
  const r = renderer.toLowerCase();

  // NVIDIA GPUs - 50 series (Blackwell, 2025)
  // Check both with and without "rtx " prefix for flexibility
  if (r.includes("5090") && (r.includes("rtx") || r.includes("geforce")))
    return 32000;
  if (r.includes("5080") && (r.includes("rtx") || r.includes("geforce")))
    return 16000;
  if (r.includes("5070") && (r.includes("rtx") || r.includes("geforce")))
    return 12000;
  if (r.includes("5060") && (r.includes("rtx") || r.includes("geforce")))
    return 8000;

  // NVIDIA GPUs - 40 series (Ada Lovelace)
  if (r.includes("4090") && (r.includes("rtx") || r.includes("geforce")))
    return 24000;
  if (r.includes("4080") && (r.includes("rtx") || r.includes("geforce")))
    return 16000;
  if (r.includes("4070") && (r.includes("rtx") || r.includes("geforce")))
    return 12000;
  if (r.includes("4060") && (r.includes("rtx") || r.includes("geforce")))
    return 8000;

  // NVIDIA GPUs - 30 series (Ampere)
  if (r.includes("3090") && (r.includes("rtx") || r.includes("geforce")))
    return 24000;
  if (r.includes("3080") && (r.includes("rtx") || r.includes("geforce")))
    return 10000;
  if (r.includes("3070") && (r.includes("rtx") || r.includes("geforce")))
    return 8000;
  if (r.includes("3060") && (r.includes("rtx") || r.includes("geforce")))
    return 12000;

  // NVIDIA GPUs - 20 series (Turing)
  if (r.includes("2080") && (r.includes("rtx") || r.includes("geforce")))
    return 8000;
  if (r.includes("2070") && (r.includes("rtx") || r.includes("geforce")))
    return 8000;
  if (r.includes("2060") && (r.includes("rtx") || r.includes("geforce")))
    return 6000;

  // NVIDIA GTX series
  if (r.includes("1080") && (r.includes("gtx") || r.includes("geforce")))
    return 8000;
  if (r.includes("1070") && (r.includes("gtx") || r.includes("geforce")))
    return 8000;
  if (r.includes("1060") && (r.includes("gtx") || r.includes("geforce")))
    return 6000;

  // AMD GPUs - RX 7000 series
  if (r.includes("7900") && r.includes("rx")) return 24000;
  if (r.includes("7800") && r.includes("rx")) return 16000;
  if (r.includes("7700") && r.includes("rx")) return 12000;

  // AMD GPUs - RX 6000 series
  if (r.includes("6900") && r.includes("rx")) return 16000;
  if (r.includes("6800") && r.includes("rx")) return 16000;
  if (r.includes("6700") && r.includes("rx")) return 12000;
  if (r.includes("6600") && r.includes("rx")) return 8000;

  // Apple Silicon (unified memory)
  if (r.includes("apple m4 max") || r.includes("m4 max")) return 64000;
  if (r.includes("apple m4 pro") || r.includes("m4 pro")) return 24000;
  if (r.includes("apple m4") || r.includes("m4")) return 16000;
  if (r.includes("apple m3 max") || r.includes("m3 max")) return 48000;
  if (r.includes("apple m3 pro") || r.includes("m3 pro")) return 18000;
  if (r.includes("apple m3")) return 8000;
  if (r.includes("apple m2 max") || r.includes("m2 max")) return 32000;
  if (r.includes("apple m2 pro") || r.includes("m2 pro")) return 16000;
  if (r.includes("apple m2")) return 8000;
  if (r.includes("apple m1")) return 8000;

  // Intel integrated
  if (r.includes("intel") && r.includes("iris")) return 4000;
  if (r.includes("intel") && r.includes("uhd")) return 2000;
  if (r.includes("intel") && r.includes("arc")) return 8000;

  // Fallback: Try to extract high-end keywords
  if (r.includes("nvidia") || r.includes("geforce")) {
    // Assume high-end if NVIDIA but unrecognized model
    return 12000;
  }
  if (r.includes("radeon") || r.includes("amd")) {
    return 8000;
  }

  // Default conservative estimate
  return 8000;
}

function determineTier(vramMB: number): "low" | "medium" | "high" | "ultra" {
  if (vramMB >= 16000) return "ultra";
  if (vramMB >= 8000) return "high";
  if (vramMB >= 4000) return "medium";
  return "low";
}

function formatMB(mb: number): string {
  if (mb >= 1000) {
    return `${(mb / 1000).toFixed(1)}GB`;
  }
  return `${Math.round(mb)}MB`;
}

function checkAndLogWarning(): void {
  const warning = getWarning();
  if (warning) {
    if (warning.level === "critical") {
      logger.error(warning.message);
    } else if (warning.level === "warning") {
      logger.warn(warning.message);
    }
  }
}

// ============================================================================
// Export reactive state for Vue components
// ============================================================================

export const memoryState = {
  totalUsageMB,
  availableVRAM,
  usagePercent,
  warningLevel,
  allocationList,
  usageByCategory,
  gpuInfo,
  isInitialized,
};
