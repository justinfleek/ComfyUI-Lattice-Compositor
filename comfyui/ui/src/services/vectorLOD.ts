/**
 * Vector LOD (Level of Detail) Service
 *
 * Provides level-of-detail optimization for complex vector paths.
 * Generates simplified versions for:
 * - Playback preview (faster rendering)
 * - Zoomed out views
 * - Export optimization
 */

import type { ControlPoint, SplineData } from "@/types/project";
import type { Point2D } from "@/types/shapes";
import { createLogger } from "@/utils/logger";
import { isFiniteNumber } from "@/utils/typeGuards";

const logger = createLogger("VectorLOD");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export interface LODLevel {
  /** Simplification tolerance used */
  tolerance: number;
  /** Simplified control points */
  controlPoints: ControlPoint[];
  /** Point count at this level */
  pointCount: number;
  /** Estimated rendering cost (0-1) */
  complexity?: number;
  /** Quality index (0 = highest, higher = more simplified) */
  quality?: number;
}

export interface LODConfig {
  /** Enable LOD system */
  enabled: boolean;
  /** When to use LOD */
  mode: "zoom" | "playback" | "both";
  /** Pre-generated LOD levels */
  levels: LODLevel[];
  /** Max points for preview mode */
  maxPointsForPreview: number;
  /** Base simplification tolerance */
  simplificationTolerance: number;
  /** Enable viewport culling */
  cullingEnabled: boolean;
  /** Margin for culling (pixels) */
  cullMargin: number;
}

export interface LODContext {
  /** Current zoom level (1 = 100%) */
  zoom: number;
  /** Whether playback is active */
  isPlaying: boolean;
  /** Whether user is scrubbing timeline */
  isScrubbing?: boolean;
  /** Viewport bounds */
  viewport?: { x: number; y: number; width: number; height: number };
  /** Target FPS (for adaptive LOD) */
  targetFPS?: number;
  /** Current FPS (for adaptive LOD) */
  currentFPS?: number;
}

// ═══════════════════════════════════════════════════════════════════════════
// Default Configuration
// ═══════════════════════════════════════════════════════════════════════════

export const DEFAULT_LOD_CONFIG: LODConfig = {
  enabled: true,
  mode: "both",
  levels: [],
  maxPointsForPreview: 100,
  simplificationTolerance: 2.0,
  cullingEnabled: true,
  cullMargin: 50,
};

// ═══════════════════════════════════════════════════════════════════════════
// Vector LOD Service
// ═══════════════════════════════════════════════════════════════════════════

export class VectorLODService {
  // Cache for generated LOD levels by layer ID
  private lodCache = new Map<string, LODLevel[]>();

  /**
   * Generate LOD levels for a set of control points
   *
   * @param layerId Layer ID for caching (optional - pass empty string to skip caching)
   * @param controlPoints Original high-quality points
   * @param levelCount Number of LOD levels to generate
   * @param baseTolerance Base tolerance for simplification
   * @returns Array of LOD levels from highest to lowest quality
   */
  generateLODLevels(
    layerId: string,
    controlPoints: ControlPoint[],
    levelCount: number = 4,
    baseTolerance: number = 2.0,
  ): LODLevel[] {
    // Check cache first
    if (layerId && this.lodCache.has(layerId)) {
      return this.lodCache.get(layerId)!;
    }

    const levels: LODLevel[] = [];
    const originalCount = controlPoints.length;

    // Level 0: Original quality
    levels.push({
      tolerance: 0,
      controlPoints: [...controlPoints],
      pointCount: originalCount,
      complexity: 1,
    });

    // Generate progressively simplified levels based on base tolerance
    const toleranceMultipliers = [0.5, 1, 2, 5, 10];

    for (
      let i = 0;
      i < Math.min(levelCount - 1, toleranceMultipliers.length);
      i++
    ) {
      const tolerance = baseTolerance * toleranceMultipliers[i];
      const simplified = this.simplifyPath(controlPoints, tolerance);

      // Only add if meaningfully different from previous
      const prevCount = levels[levels.length - 1].pointCount;
      if (simplified.length < prevCount * 0.9) {
        levels.push({
          tolerance,
          controlPoints: simplified,
          pointCount: simplified.length,
          complexity: simplified.length / originalCount,
        });
      }
    }

    // Cache the result
    if (layerId) {
      this.lodCache.set(layerId, levels);
    }

    logger.debug(
      "Generated LOD levels:",
      levels.map((l) => l.pointCount),
    );
    return levels;
  }

  /**
   * Clear LOD cache for a specific layer or all layers
   */
  clearCache(layerId?: string): void {
    if (layerId) {
      this.lodCache.delete(layerId);
    } else {
      this.lodCache.clear();
    }
  }

  /**
   * Select appropriate LOD level based on context
   */
  selectLODLevel(levels: LODLevel[], context: LODContext): LODLevel {
    if (levels.length === 0) {
      throw new Error("No LOD levels available");
    }

    // Always return highest quality if LOD not needed
    if (levels.length === 1) {
      return levels[0];
    }

    // Calculate desired quality (0-1)
    let targetQuality = 1;

    // Reduce quality when zoomed out
    if (context.zoom < 1) {
      targetQuality *= Math.max(0.2, context.zoom);
    }

    // Reduce quality during playback
    if (context.isPlaying) {
      targetQuality *= 0.7;
    }

    // Adaptive: reduce quality if FPS is dropping
    if (context.targetFPS && context.currentFPS) {
      const fpsRatio = context.currentFPS / context.targetFPS;
      if (fpsRatio < 0.8) {
        targetQuality *= fpsRatio;
      }
    }

    // Find level closest to target quality
    let bestLevel = levels[0];
    // Type proof: number | undefined → number
    const firstComplexity = isFiniteNumber(levels[0].complexity) && levels[0].complexity >= 0
      ? levels[0].complexity
      : 0;
    let bestDiff = Math.abs(firstComplexity - targetQuality);

    for (const level of levels) {
      // Type proof: number | undefined → number
      const levelComplexity = isFiniteNumber(level.complexity) && level.complexity >= 0
        ? level.complexity
        : 0;
      const diff = Math.abs(levelComplexity - targetQuality);
      if (diff < bestDiff) {
        bestDiff = diff;
        bestLevel = level;
      }
    }

    return bestLevel;
  }

  /**
   * Cull points outside viewport
   * Returns indices of visible points
   */
  cullOffScreenPoints(
    points: ControlPoint[],
    viewport: { x: number; y: number; width: number; height: number },
    margin: number = 50,
  ): ControlPoint[] {
    const minX = viewport.x - margin;
    const minY = viewport.y - margin;
    const maxX = viewport.x + viewport.width + margin;
    const maxY = viewport.y + viewport.height + margin;

    // Find visible segments (keep points on either side of visible ones)
    const visible = new Set<number>();

    for (let i = 0; i < points.length; i++) {
      const p = points[i];
      if (p.x >= minX && p.x <= maxX && p.y >= minY && p.y <= maxY) {
        // Point is visible, also keep neighbors for smooth curves
        visible.add(Math.max(0, i - 1));
        visible.add(i);
        visible.add(Math.min(points.length - 1, i + 1));
      }
    }

    // If nothing visible, return empty (or could return first/last)
    if (visible.size === 0) {
      return [];
    }

    // Build culled array preserving order
    const culled: ControlPoint[] = [];
    for (let i = 0; i < points.length; i++) {
      if (visible.has(i)) {
        culled.push(points[i]);
      }
    }

    return culled;
  }

  /**
   * Simplify path using Ramer-Douglas-Peucker algorithm
   */
  simplifyPath(points: ControlPoint[], tolerance: number): ControlPoint[] {
    if (points.length <= 2) return [...points];

    // Convert to simple point array for algorithm
    const simplePoints = points.map((p) => ({ x: p.x, y: p.y }));
    const simplified = this.rdpSimplify(simplePoints, tolerance);

    // Map back to control points
    const result: ControlPoint[] = [];
    let simplifiedIndex = 0;

    for (
      let i = 0;
      i < points.length && simplifiedIndex < simplified.length;
      i++
    ) {
      const p = points[i];
      const s = simplified[simplifiedIndex];

      if (Math.abs(p.x - s.x) < 0.01 && Math.abs(p.y - s.y) < 0.01) {
        result.push({ ...p });
        simplifiedIndex++;
      }
    }

    // Ensure we have at least the endpoints
    if (result.length < 2 && points.length >= 2) {
      return [points[0], points[points.length - 1]];
    }

    return result;
  }

  /**
   * Ramer-Douglas-Peucker line simplification
   */
  private rdpSimplify(points: Point2D[], tolerance: number): Point2D[] {
    if (points.length <= 2) return points;

    // Find point with max distance from line between first and last
    let maxDist = 0;
    let maxIndex = 0;
    const first = points[0];
    const last = points[points.length - 1];

    for (let i = 1; i < points.length - 1; i++) {
      const d = this.perpendicularDistance(points[i], first, last);
      if (d > maxDist) {
        maxDist = d;
        maxIndex = i;
      }
    }

    // If max distance > tolerance, recursively simplify
    if (maxDist > tolerance) {
      const left = this.rdpSimplify(points.slice(0, maxIndex + 1), tolerance);
      const right = this.rdpSimplify(points.slice(maxIndex), tolerance);
      return [...left.slice(0, -1), ...right];
    }

    // Otherwise, return just endpoints
    return [first, last];
  }

  /**
   * Calculate perpendicular distance from point to line
   */
  private perpendicularDistance(
    point: Point2D,
    lineStart: Point2D,
    lineEnd: Point2D,
  ): number {
    const dx = lineEnd.x - lineStart.x;
    const dy = lineEnd.y - lineStart.y;
    const lineLengthSq = dx * dx + dy * dy;

    if (lineLengthSq === 0) {
      return Math.sqrt(
        (point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2,
      );
    }

    const t = Math.max(
      0,
      Math.min(
        1,
        ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) /
          lineLengthSq,
      ),
    );

    const projX = lineStart.x + t * dx;
    const projY = lineStart.y + t * dy;

    return Math.sqrt((point.x - projX) ** 2 + (point.y - projY) ** 2);
  }

  /**
   * Estimate rendering complexity of a path
   */
  estimateComplexity(points: ControlPoint[]): number {
    let complexity = points.length;

    // Add weight for curves (points with handles)
    for (const p of points) {
      if (p.handleIn || p.handleOut) {
        complexity += 0.5;
      }
    }

    return complexity;
  }

  /**
   * Check if LOD should be used for a spline
   */
  shouldUseLOD(splineData: SplineData, context: LODContext): boolean {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const splineDataLod = (splineData != null && typeof splineData === "object" && "lod" in splineData && splineData.lod != null && typeof splineData.lod === "object") ? splineData.lod : undefined;
    const lodEnabled = (splineDataLod != null && typeof splineDataLod === "object" && "enabled" in splineDataLod && typeof splineDataLod.enabled === "boolean" && splineDataLod.enabled) ? true : false;
    if (!lodEnabled) return false;

    const pointCount = splineData.controlPoints.length;

    // Skip LOD for simple paths
    if (pointCount < 50) return false;

    // Use LOD during playback (splineData.lod is guaranteed by lodEnabled check above)
    const lodMode = splineData.lod?.mode;
    if (context.isPlaying && lodMode !== "zoom") return true;

    // Use LOD when zoomed out
    if (context.zoom < 0.5 && lodMode !== "playback") return true;

    return false;
  }

  /**
   * Auto-generate LOD config for a spline if point count exceeds threshold
   */
  autoGenerateLOD(
    splineData: SplineData,
    threshold: number = 200,
  ): LODConfig {
    if (splineData.controlPoints.length < threshold) {
      throw new Error(`[VectorLOD] Cannot auto-generate LOD: Control point count (${splineData.controlPoints.length}) is below threshold (${threshold}). LOD generation requires at least ${threshold} control points.`);
    }

    const levels = this.generateLODLevels("", splineData.controlPoints, 4, 2.0);

    return {
      ...DEFAULT_LOD_CONFIG,
      enabled: true,
      levels,
    };
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// Singleton Instance
// ═══════════════════════════════════════════════════════════════════════════

export const vectorLODService = new VectorLODService();

// Alias for backward compatibility
export const vectorLOD = vectorLODService;

// ═══════════════════════════════════════════════════════════════════════════
// Convenience Functions
// ═══════════════════════════════════════════════════════════════════════════

export function generateLODLevels(
  layerId: string,
  points: ControlPoint[],
  levelCount?: number,
  baseTolerance?: number,
): LODLevel[] {
  return vectorLODService.generateLODLevels(
    layerId,
    points,
    levelCount,
    baseTolerance,
  );
}

export function selectLODLevel(
  levels: LODLevel[],
  context: LODContext,
): LODLevel {
  return vectorLODService.selectLODLevel(levels, context);
}

export function simplifyPath(
  points: ControlPoint[],
  tolerance: number,
): ControlPoint[] {
  return vectorLODService.simplifyPath(points, tolerance);
}

export function cullOffScreenPoints(
  points: ControlPoint[],
  viewport: { x: number; y: number; width: number; height: number },
  margin?: number,
): ControlPoint[] {
  return vectorLODService.cullOffScreenPoints(points, viewport, margin);
}

export default vectorLODService;
