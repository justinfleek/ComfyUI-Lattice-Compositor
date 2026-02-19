/**
 * Image Vectorization Service
 *
 * Frontend service for converting raster images to vector graphics
 * with bezier control points suitable for SplineLayer animation.
 *
 * Supports two modes:
 * 1. VTracer - Fast tracing for any image type
 * 2. StarVector - AI-powered for icons/logos (1B model)
 */

import type { ControlPoint } from "@/types/project";
import { createLogger } from "@/utils/logger";
import { isNonEmptyString } from "@/utils/typeGuards";
import { getComfyUIClient } from "./comfyui/comfyuiClient";
import {
  canAllocate,
  registerAllocation,
  unregisterAllocation,
  VRAM_ESTIMATES,
} from "./memoryBudget";

const logger = createLogger("Vectorize");

const STARVECTOR_ALLOCATION_ID = "model:starvector-1b";

// ============================================================================
// Types
// ============================================================================

export interface VectorizeStatus {
  vtracer: {
    available: boolean;
    version: string | null;
  };
  starvector: {
    available: boolean;
    downloaded: boolean;
    loaded: boolean;
    loading: boolean;
    model_path: string;
    model_size_gb: number;
  };
}

export interface VectorPath {
  id: string;
  fill: string;
  stroke: string;
  controlPoints: ControlPoint[];
  closed: boolean;
}

export interface VectorizeResult {
  status: "success" | "error";
  message?: string;
  paths: VectorPath[];
  width: number;
  height: number;
  pathCount: number;
  svg?: string;
}

export interface VTraceOptions {
  /** Curve fitting mode: 'spline' for bezier curves, 'polygon' for straight lines */
  mode?: "spline" | "polygon" | "pixel";
  /** Color mode: 'color' preserves colors, 'binary' for black/white */
  colorMode?: "color" | "binary";
  /** Layer stacking mode */
  hierarchical?: "stacked" | "cutout";
  /** Remove small artifacts (0-100, higher = more filtering) */
  filterSpeckle?: number;
  /** Color quantization precision (1-10) */
  colorPrecision?: number;
  /** Minimum color difference for separate layers (1-256) */
  layerDifference?: number;
  /** Corner detection threshold in degrees (0-180) */
  cornerThreshold?: number;
  /** Minimum path segment length */
  lengthThreshold?: number;
  /** Optimization iterations */
  maxIterations?: number;
  /** Spline angle threshold for splitting */
  spliceThreshold?: number;
  /** Output decimal precision */
  pathPrecision?: number;
}

export interface StarVectorOptions {
  /** Maximum SVG tokens to generate */
  maxLength?: number;
}

// ============================================================================
// Default Options
// ============================================================================

export const DEFAULT_VTRACE_OPTIONS: Required<VTraceOptions> = {
  mode: "spline",
  colorMode: "color",
  hierarchical: "stacked",
  filterSpeckle: 4,
  colorPrecision: 6,
  layerDifference: 16,
  cornerThreshold: 60,
  lengthThreshold: 4.0,
  maxIterations: 10,
  spliceThreshold: 45,
  pathPrecision: 3,
};

export const DEFAULT_STARVECTOR_OPTIONS: Required<StarVectorOptions> = {
  maxLength: 4000,
};

// ============================================================================
// Service Class
// ============================================================================

export class VectorizeService {
  private baseUrl: string;

  constructor(serverAddress?: string) {
    const client = getComfyUIClient(serverAddress);
    this.baseUrl = `http://${client.server}`;
  }

  /**
   * Get vectorization service status
   */
  async getStatus(): Promise<VectorizeStatus> {
    try {
      const response = await fetch(`${this.baseUrl}/lattice/vectorize/status`);

      if (!response.ok) {
        throw new Error(
          `Server returned ${response.status}: ${response.statusText}`,
        );
      }

      const result = await response.json();

      if (result.status === "success") {
        return result.data;
      }

      throw new Error(result.message || "Failed to get status");
    } catch (error) {
      logger.error("Failed to get vectorize status:", error);
      throw error;
    }
  }

  /**
   * Trace an image to vector paths using VTracer (fast, any image type)
   *
   * @param imageDataUrl - Image as data URL (data:image/...;base64,...)
   * @param options - Tracing options
   * @returns Array of vector paths with control points
   */
  async trace(
    imageDataUrl: string,
    options: VTraceOptions = {},
  ): Promise<VectorizeResult> {
    const opts = { ...DEFAULT_VTRACE_OPTIONS, ...options };

    try {
      const response = await fetch(`${this.baseUrl}/lattice/vectorize/trace`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          image: imageDataUrl,
          mode: opts.mode,
          color_mode: opts.colorMode,
          hierarchical: opts.hierarchical,
          filter_speckle: opts.filterSpeckle,
          color_precision: opts.colorPrecision,
          layer_difference: opts.layerDifference,
          corner_threshold: opts.cornerThreshold,
          length_threshold: opts.lengthThreshold,
          max_iterations: opts.maxIterations,
          splice_threshold: opts.spliceThreshold,
          path_precision: opts.pathPrecision,
        }),
      });

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      logger.info(`Traced image: ${result.pathCount} paths`);
      return result;
    } catch (error) {
      logger.error("Image tracing failed:", error);
      throw error;
    }
  }

  /**
   * Vectorize an icon/logo using StarVector AI
   * Note: Only works for simple graphics, not photos
   *
   * @param imageDataUrl - Image as data URL
   * @param options - StarVector options
   */
  async vectorizeWithAI(
    imageDataUrl: string,
    options: StarVectorOptions = {},
  ): Promise<VectorizeResult> {
    const opts = { ...DEFAULT_STARVECTOR_OPTIONS, ...options };

    // Check if we have enough memory
    const memCheck = canAllocate(VRAM_ESTIMATES["model:starvector"] || 2500);
    if (!memCheck.canProceed) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const warningMessage = (memCheck.warning != null && typeof memCheck.warning === "object" && "message" in memCheck.warning && typeof memCheck.warning.message === "string") ? memCheck.warning.message : undefined;
      throw new Error(
        warningMessage != null ? warningMessage : "Insufficient GPU memory for StarVector",
      );
    }

    try {
      const response = await fetch(`${this.baseUrl}/lattice/vectorize/ai`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          image: imageDataUrl,
          max_length: opts.maxLength,
        }),
      });

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      logger.info(`AI vectorized: ${result.pathCount} paths`);
      return result;
    } catch (error) {
      logger.error("AI vectorization failed:", error);
      throw error;
    }
  }

  /**
   * Download and load StarVector model
   */
  async loadStarVectorModel(
    onProgress?: (stage: string, message: string) => void,
  ): Promise<void> {
    // Check memory before loading
    const memCheck = canAllocate(VRAM_ESTIMATES["model:starvector"] || 2500);
    if (!memCheck.canProceed) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const warningMessage = (memCheck.warning != null && typeof memCheck.warning === "object" && "message" in memCheck.warning && typeof memCheck.warning.message === "string") ? memCheck.warning.message : undefined;
      throw new Error(warningMessage != null ? warningMessage : "Insufficient GPU memory");
    }

    try {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("downloading", "Downloading StarVector model (~2.5GB)...");
      }

      const response = await fetch(
        `${this.baseUrl}/lattice/vectorize/download-starvector`,
        {
          method: "POST",
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      // Register memory allocation
      registerAllocation(
        STARVECTOR_ALLOCATION_ID,
        "StarVector 1B Model",
        "model",
        VRAM_ESTIMATES["model:starvector"] || 2500,
        {
          canUnload: true,
          unloadFn: () => this.unloadStarVectorModel(),
        },
      );

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("complete", "StarVector model loaded");
      }
      logger.info("StarVector model loaded");
    } catch (error) {
      logger.error("Failed to load StarVector:", error);
      throw error;
    }
  }

  /**
   * Unload StarVector model to free GPU memory
   */
  async unloadStarVectorModel(): Promise<void> {
    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/vectorize/unload-starvector`,
        {
          method: "POST",
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      unregisterAllocation(STARVECTOR_ALLOCATION_ID);
      logger.info("StarVector model unloaded");
    } catch (error) {
      logger.error("Failed to unload StarVector:", error);
      throw error;
    }
  }

  /**
   * One-click vectorization with automatic mode selection
   *
   * For icons/logos (simple graphics): Uses StarVector AI
   * For photos/complex images: Uses VTracer
   *
   * @param imageDataUrl - Image to vectorize
   * @param options - Options (mode can be 'auto', 'trace', or 'ai')
   * @param onProgress - Progress callback
   */
  async vectorize(
    imageDataUrl: string,
    options: {
      mode?: "auto" | "trace" | "ai";
      traceOptions?: VTraceOptions;
      aiOptions?: StarVectorOptions;
    } = {},
    onProgress?: (stage: string, message: string) => void,
  ): Promise<VectorizeResult> {
    // Type proof: mode ∈ "auto" | "trace" | "ai" | undefined → "auto" | "trace" | "ai"
    const mode = options !== undefined && typeof options === "object" && options !== null && "mode" in options && isNonEmptyString(options.mode) && (options.mode === "auto" || options.mode === "trace" || options.mode === "ai")
      ? options.mode
      : "trace";

    if (mode === "ai") {
      // Check if StarVector is loaded
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("checking", "Checking StarVector model...");
      }
      const status = await this.getStatus();

      if (!status.starvector.loaded) {
        if (!status.starvector.downloaded) {
          if (onProgress != null && typeof onProgress === "function") {
            onProgress("downloading", "Downloading StarVector model...");
          }
        }
        await this.loadStarVectorModel(onProgress);
      }

      if (onProgress != null && typeof onProgress === "function") {
        onProgress("vectorizing", "Running AI vectorization...");
      }
      return await this.vectorizeWithAI(imageDataUrl, options.aiOptions);
    }

    // Default to VTracer (fast, works with any image)
    if (onProgress != null && typeof onProgress === "function") {
      onProgress("tracing", "Tracing image to vectors...");
    }
    return await this.trace(imageDataUrl, options.traceOptions);
  }
}

// ============================================================================
// Singleton Instance
// ============================================================================

let defaultService: VectorizeService | null = null;

export function getVectorizeService(serverAddress?: string): VectorizeService {
  if (!defaultService) {
    defaultService = new VectorizeService(serverAddress);
  }
  return defaultService;
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Convert vector paths to SplineLayer-compatible control points
 * Adds unique IDs and ensures proper handle format
 */
export function normalizeControlPoints(
  paths: VectorPath[],
  options: {
    groupByPath?: boolean; // Assign group IDs based on path
    prefix?: string; // ID prefix
  } = {},
): VectorPath[] {
  const { groupByPath = false, prefix = "vec" } = options;

  return paths.map((path, pathIdx) => {
    const groupId = groupByPath ? `${prefix}_path_${pathIdx}` : undefined;

    return {
      ...path,
      controlPoints: path.controlPoints.map((cp, cpIdx) => ({
        ...cp,
        id: cp.id || `${prefix}_${pathIdx}_${cpIdx}`,
        group: groupId,
        // Ensure handles are in correct format (absolute positions)
        handleIn: cp.handleIn ? { x: cp.handleIn.x, y: cp.handleIn.y } : null,
        handleOut: cp.handleOut
          ? { x: cp.handleOut.x, y: cp.handleOut.y }
          : null,
      })),
    };
  });
}

/**
 * Merge multiple paths into a single path
 * Useful for creating a single animated spline from traced image
 */
/**
 * Merge multiple vector paths into a single path
 * 
 * System F/Omega proof: Type guard for paths array
 * Type proof: paths: VectorPath[] → requires non-empty array for merging
 * Mathematical proof: Merging requires at least one path (array length ≥ 1)
 * 
 * @param paths - Array of vector paths to merge (must be non-empty)
 * @returns Single merged VectorPath
 * @throws Error if paths array is empty or invalid
 */
export function mergePaths(paths: VectorPath[]): VectorPath {
  // System F/Omega proof: Explicit pattern matching for array validation
  // Type proof: paths ∈ VectorPath[] → paths.length ∈ ℕ
  // Mathematical proof: Empty array (length = 0) cannot be merged
  if (typeof paths !== "object" || paths === null || !Array.isArray(paths)) {
    throw new Error(`[Vectorize] Cannot merge paths: paths parameter is not a valid array (got ${typeof paths}). This indicates a type system violation - paths must be a non-null array of VectorPath objects.`);
  }
  
  if (paths.length === 0) {
    throw new Error(`[Vectorize] Cannot merge paths: Path array is empty (length: 0). Merging requires at least one path to produce a result. Check that paths exist before calling mergePaths.`);
  }
  
  // Optimization: Single path requires no merging
  if (paths.length === 1) return paths[0];

  // Combine all control points, keeping track of original path as group
  const mergedPoints: ControlPoint[] = [];
  let pointIdx = 0;

  for (let pathIdx = 0; pathIdx < paths.length; pathIdx++) {
    const path = paths[pathIdx];
    for (const cp of path.controlPoints) {
      mergedPoints.push({
        ...cp,
        id: `merged_${pointIdx++}`,
        group: `path_${pathIdx}`,
      });
    }
  }

  return {
    id: "merged_path",
    fill: paths[0].fill,
    stroke: paths[0].stroke || "#000000",
    controlPoints: mergedPoints,
    closed: false, // Merged paths are typically not closed
  };
}

/**
 * Filter paths by minimum point count
 */
export function filterSmallPaths(
  paths: VectorPath[],
  minPoints: number = 3,
): VectorPath[] {
  return paths.filter((path) => path.controlPoints.length >= minPoints);
}

/**
 * Simplify paths by reducing control point count
 * Uses Douglas-Peucker algorithm approximation
 */
export function simplifyPath(
  controlPoints: ControlPoint[],
  tolerance: number = 2.0,
): ControlPoint[] {
  if (controlPoints.length <= 2) return controlPoints;

  // Find the point with maximum distance from the line between first and last
  const first = controlPoints[0];
  const last = controlPoints[controlPoints.length - 1];

  let maxDist = 0;
  let maxIdx = 0;

  for (let i = 1; i < controlPoints.length - 1; i++) {
    const point = controlPoints[i];
    const dist = perpendicularDistance(point, first, last);

    if (dist > maxDist) {
      maxDist = dist;
      maxIdx = i;
    }
  }

  // If max distance exceeds tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = simplifyPath(controlPoints.slice(0, maxIdx + 1), tolerance);
    const right = simplifyPath(controlPoints.slice(maxIdx), tolerance);

    // Combine results, removing duplicate middle point
    return [...left.slice(0, -1), ...right];
  }

  // All points are within tolerance, keep only endpoints
  return [first, last];
}

/**
 * Calculate perpendicular distance from point to line
 */
function perpendicularDistance(
  point: ControlPoint,
  lineStart: ControlPoint,
  lineEnd: ControlPoint,
): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;

  if (dx === 0 && dy === 0) {
    // Line is a point
    return Math.sqrt(
      (point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2,
    );
  }

  const t = Math.max(
    0,
    Math.min(
      1,
      ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) /
        (dx * dx + dy * dy),
    ),
  );

  const projX = lineStart.x + t * dx;
  const projY = lineStart.y + t * dy;

  return Math.sqrt((point.x - projX) ** 2 + (point.y - projY) ** 2);
}

/**
 * Auto-assign groups based on spatial clustering
 * Groups nearby points together for coordinated animation
 */
export function autoGroupPoints(
  controlPoints: ControlPoint[],
  options: {
    method?: "grid" | "proximity" | "quadrant";
    gridSize?: number; // For grid method
    threshold?: number; // For proximity method
    numGroups?: number; // Target number of groups
  } = {},
): ControlPoint[] {
  const {
    method = "quadrant",
    gridSize = 100,
    threshold = 50,
    numGroups = 4,
  } = options;

  if (controlPoints.length === 0) return [];

  // Calculate bounds
  let minX = Infinity,
    minY = Infinity,
    maxX = -Infinity,
    maxY = -Infinity;
  for (const cp of controlPoints) {
    minX = Math.min(minX, cp.x);
    minY = Math.min(minY, cp.y);
    maxX = Math.max(maxX, cp.x);
    maxY = Math.max(maxY, cp.y);
  }

  const width = maxX - minX || 1;
  const height = maxY - minY || 1;

  return controlPoints.map((cp) => {
    let group: string;

    switch (method) {
      case "grid": {
        const gridX = Math.floor((cp.x - minX) / gridSize);
        const gridY = Math.floor((cp.y - minY) / gridSize);
        group = `grid_${gridX}_${gridY}`;
        break;
      }

      case "quadrant": {
        const normX = (cp.x - minX) / width;
        const normY = (cp.y - minY) / height;

        if (normX < 0.5 && normY < 0.5) group = "top_left";
        else if (normX >= 0.5 && normY < 0.5) group = "top_right";
        else if (normX < 0.5 && normY >= 0.5) group = "bottom_left";
        else group = "bottom_right";
        break;
      }
      default: {
        // Simple k-means-style grouping
        const normX = (cp.x - minX) / width;
        const _normY = (cp.y - minY) / height;
        const groupIdx = Math.floor(normX * numGroups) % numGroups;
        group = `region_${groupIdx}`;
        break;
      }
    }

    return { ...cp, group };
  });
}

// Add to VRAM_ESTIMATES (extend the memory budget)
if (typeof VRAM_ESTIMATES === "object") {
  (VRAM_ESTIMATES as Record<string, number>)["model:starvector"] = 2500;
}
