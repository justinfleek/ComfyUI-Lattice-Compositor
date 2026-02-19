/**
 * Bezier Boolean Service
 *
 * Provides bezier-aware boolean operations using Paper.js.
 * Unlike polygon-clipping which flattens curves, Paper.js maintains
 * bezier handles through boolean operations for high-quality results.
 *
 * Supported operations:
 * - Union (combine two shapes)
 * - Subtract (cut one shape from another)
 * - Intersect (area common to both shapes)
 * - Exclude (XOR - area in either but not both)
 * - Divide (split into separate pieces)
 */

import paper from "paper";
import type { BezierPath, BezierVertex, Point2D } from "@/types/shapes";
import { createLogger } from "@/utils/logger";

const logger = createLogger("BezierBoolean");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export type BooleanOperation =
  | "unite"
  | "subtract"
  | "intersect"
  | "exclude"
  | "divide";

export interface BooleanOptions {
  /** Whether to close the resulting paths (default: true for area operations) */
  closePath?: boolean;
  /** Curve tolerance for flattening during operations (default: 0.25) */
  tolerance?: number;
  /** Insert intermediate points for better curve approximation (default: true) */
  insert?: boolean;
}

export interface BooleanResult {
  /** Resulting path(s) after the boolean operation */
  paths: BezierPath[];
  /** Whether the operation succeeded */
  success: boolean;
  /** Error message if operation failed */
  error?: string;
}

// ═══════════════════════════════════════════════════════════════════════════
// Paper.js Initialization
// ═══════════════════════════════════════════════════════════════════════════

let paperInitialized = false;

/**
 * Initialize Paper.js in headless mode (no canvas)
 */
function initializePaper(): void {
  if (paperInitialized) return;

  // Paper.js needs a canvas or can run headless
  // Create a temporary offscreen canvas for headless operation
  const canvas = document.createElement("canvas");
  canvas.width = 1;
  canvas.height = 1;

  paper.setup(canvas);
  paperInitialized = true;
  logger.debug("Paper.js initialized for bezier boolean operations");
}

// ═══════════════════════════════════════════════════════════════════════════
// Conversion: Lattice Path <-> Paper.js Path
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Convert a Lattice BezierPath to a Paper.js Path
 */
function latticePathToPaperPath(path: BezierPath): paper.Path {
  initializePaper();

  const paperPath = new paper.Path();
  paperPath.closed = path.closed;

  for (let i = 0; i < path.vertices.length; i++) {
    const v = path.vertices[i];
    const prevV =
      path.vertices[(i - 1 + path.vertices.length) % path.vertices.length];

    if (i === 0) {
      // First point: just moveTo
      paperPath.moveTo(new paper.Point(v.point.x, v.point.y));
    } else {
      // Subsequent points: use bezier curves with handles
      const handleOut = prevV.outHandle;
      const handleIn = v.inHandle;

      // Check if this is a straight line (no handles)
      if (
        Math.abs(handleOut.x) < 0.001 &&
        Math.abs(handleOut.y) < 0.001 &&
        Math.abs(handleIn.x) < 0.001 &&
        Math.abs(handleIn.y) < 0.001
      ) {
        paperPath.lineTo(new paper.Point(v.point.x, v.point.y));
      } else {
        // Bezier curve
        paperPath.cubicCurveTo(
          new paper.Point(
            prevV.point.x + handleOut.x,
            prevV.point.y + handleOut.y,
          ),
          new paper.Point(v.point.x + handleIn.x, v.point.y + handleIn.y),
          new paper.Point(v.point.x, v.point.y),
        );
      }
    }
  }

  // If closed, add closing segment
  if (path.closed && path.vertices.length > 1) {
    const lastV = path.vertices[path.vertices.length - 1];
    const firstV = path.vertices[0];
    const handleOut = lastV.outHandle;
    const handleIn = firstV.inHandle;

    if (
      Math.abs(handleOut.x) < 0.001 &&
      Math.abs(handleOut.y) < 0.001 &&
      Math.abs(handleIn.x) < 0.001 &&
      Math.abs(handleIn.y) < 0.001
    ) {
      paperPath.closePath();
    } else {
      paperPath.cubicCurveTo(
        new paper.Point(
          lastV.point.x + handleOut.x,
          lastV.point.y + handleOut.y,
        ),
        new paper.Point(
          firstV.point.x + handleIn.x,
          firstV.point.y + handleIn.y,
        ),
        new paper.Point(firstV.point.x, firstV.point.y),
      );
    }
  }

  return paperPath;
}

/**
 * Convert a Paper.js Path back to a Lattice BezierPath
 */
function paperPathToLatticePath(paperPath: paper.Path): BezierPath {
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < paperPath.segments.length; i++) {
    const segment = paperPath.segments[i];
    const point = segment.point;

    // Paper.js handles are relative to the point
    const handleIn = segment.handleIn;
    const handleOut = segment.handleOut;

    vertices.push({
      point: { x: point.x, y: point.y },
      inHandle:
        handleIn.length > 0.001
          ? { x: handleIn.x, y: handleIn.y }
          : { x: 0, y: 0 },
      outHandle:
        handleOut.length > 0.001
          ? { x: handleOut.x, y: handleOut.y }
          : { x: 0, y: 0 },
    });
  }

  return {
    vertices,
    closed: paperPath.closed,
  };
}

/**
 * Convert Paper.js PathItem (could be Path or CompoundPath) to Lattice paths
 */
function paperItemToLatticePaths(item: paper.PathItem | null): BezierPath[] {
  if (!item) return [];

  if (item instanceof paper.Path) {
    return [paperPathToLatticePath(item)];
  }

  if (item instanceof paper.CompoundPath) {
    const paths: BezierPath[] = [];
    for (const child of item.children) {
      if (child instanceof paper.Path) {
        paths.push(paperPathToLatticePath(child));
      }
    }
    return paths;
  }

  return [];
}

// ═══════════════════════════════════════════════════════════════════════════
// Boolean Operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Perform a boolean operation on two paths
 */
export function booleanOperation(
  pathA: BezierPath,
  pathB: BezierPath,
  operation: BooleanOperation,
  options: BooleanOptions = {},
): BooleanResult {
  try {
    initializePaper();

    // Convert to Paper.js paths
    const paperA = latticePathToPaperPath(pathA);
    const paperB = latticePathToPaperPath(pathB);

    // Type proof: insert ∈ boolean | undefined → boolean
    const insert = typeof options.insert === "boolean" ? options.insert : false;

    let result: paper.PathItem | null = null;

    // Perform operation
    switch (operation) {
      case "unite":
        result = paperA.unite(paperB, { insert });
        break;
      case "subtract":
        result = paperA.subtract(paperB, { insert });
        break;
      case "intersect":
        result = paperA.intersect(paperB, { insert });
        break;
      case "exclude":
        result = paperA.exclude(paperB, { insert });
        break;
      case "divide":
        result = paperA.divide(paperB, { insert });
        break;
    }

    // Clean up temp paths
    paperA.remove();
    paperB.remove();

    // Convert result back to Lattice format
    const paths = paperItemToLatticePaths(result);

    if (result) {
      result.remove();
    }

    if (paths.length === 0) {
      throw new Error(`[BezierBoolean] Boolean operation "${operation}" produced no paths. Check input paths and operation type.`);
    }
    return {
      paths,
      success: true,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    logger.warn(`Boolean operation "${operation}" failed:`, error);
    throw new Error(`[BezierBoolean] Boolean operation "${operation}" failed: ${errorMessage}. Check input paths and operation parameters.`);
  }
}

/**
 * Union (combine) two paths
 */
export function unite(
  pathA: BezierPath,
  pathB: BezierPath,
  options?: BooleanOptions,
): BooleanResult {
  return booleanOperation(pathA, pathB, "unite", options);
}

/**
 * Subtract pathB from pathA
 */
export function subtract(
  pathA: BezierPath,
  pathB: BezierPath,
  options?: BooleanOptions,
): BooleanResult {
  return booleanOperation(pathA, pathB, "subtract", options);
}

/**
 * Intersect two paths (area common to both)
 */
export function intersect(
  pathA: BezierPath,
  pathB: BezierPath,
  options?: BooleanOptions,
): BooleanResult {
  return booleanOperation(pathA, pathB, "intersect", options);
}

/**
 * Exclude (XOR) two paths (area in either but not both)
 */
export function exclude(
  pathA: BezierPath,
  pathB: BezierPath,
  options?: BooleanOptions,
): BooleanResult {
  return booleanOperation(pathA, pathB, "exclude", options);
}

/**
 * Divide pathA by pathB (split into separate pieces)
 */
export function divide(
  pathA: BezierPath,
  pathB: BezierPath,
  options?: BooleanOptions,
): BooleanResult {
  return booleanOperation(pathA, pathB, "divide", options);
}

// ═══════════════════════════════════════════════════════════════════════════
// Multi-Path Operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Union multiple paths into one
 */
export function uniteAll(
  paths: BezierPath[],
  options?: BooleanOptions,
): BooleanResult {
  if (paths.length === 0) {
    return { paths: [], success: true };
  }
  if (paths.length === 1) {
    return { paths: [paths[0]], success: true };
  }

  let result = paths[0];
  for (let i = 1; i < paths.length; i++) {
    const opResult = unite(result, paths[i], options);
    if (!opResult.success || opResult.paths.length === 0) {
      return opResult;
    }
    result = opResult.paths[0];
  }

  return { paths: [result], success: true };
}

/**
 * Intersect multiple paths (area common to all)
 */
export function intersectAll(
  paths: BezierPath[],
  options?: BooleanOptions,
): BooleanResult {
  if (paths.length === 0) {
    return { paths: [], success: true };
  }
  if (paths.length === 1) {
    return { paths: [paths[0]], success: true };
  }

  let result = paths[0];
  for (let i = 1; i < paths.length; i++) {
    const opResult = intersect(result, paths[i], options);
    if (!opResult.success) {
      return opResult;
    }
    if (opResult.paths.length === 0) {
      // Intersection is empty
      return { paths: [], success: true };
    }
    result = opResult.paths[0];
  }

  return { paths: [result], success: true };
}

// ═══════════════════════════════════════════════════════════════════════════
// Utility Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Simplify a path by removing redundant points while preserving shape
 */
export function simplifyPath(
  path: BezierPath,
  tolerance: number = 2.5,
): BezierPath {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    paperPath.simplify(tolerance);
    const result = paperPathToLatticePath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn("Path simplification failed:", error);
    return path;
  }
}

/**
 * Flatten a path by converting curves to line segments
 */
export function flattenPath(
  path: BezierPath,
  tolerance: number = 0.25,
): BezierPath {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    paperPath.flatten(tolerance);
    const result = paperPathToLatticePath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn("Path flattening failed:", error);
    return path;
  }
}

/**
 * Smooth a path by adjusting handles for continuity
 */
export function smoothPath(path: BezierPath): BezierPath {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    paperPath.smooth();
    const result = paperPathToLatticePath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn("Path smoothing failed:", error);
    return path;
  }
}

/**
 * Get path area (positive for clockwise, negative for counter-clockwise)
 */
export function getPathArea(path: BezierPath): number {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    const area = paperPath.area;
    paperPath.remove();

    return area;
  } catch (error) {
    logger.warn("Failed to calculate path area:", error);
    return 0;
  }
}

/**
 * Get path length
 */
export function getPathLength(path: BezierPath): number {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    const length = paperPath.length;
    paperPath.remove();

    return length;
  } catch (error) {
    logger.warn("Failed to calculate path length:", error);
    return 0;
  }
}

/**
 * Get a point on the path at a given offset (0-1 normalized)
 */
export function getPointOnPath(
  path: BezierPath,
  offset: number,
): Point2D | null {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    const point = paperPath.getPointAt(
      paperPath.length * Math.max(0, Math.min(1, offset)),
    );
    paperPath.remove();

    if (!point) {
      throw new Error(`[BezierBoolean] Failed to get point on path at offset ${offset}`);
    }
    return { x: point.x, y: point.y };
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[BezierBoolean]")) {
      throw error;
    }
    throw new Error(`[BezierBoolean] Failed to get point on path: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Get tangent vector at a point on the path
 */
export function getTangentOnPath(
  path: BezierPath,
  offset: number,
): Point2D | null {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    const tangent = paperPath.getTangentAt(
      paperPath.length * Math.max(0, Math.min(1, offset)),
    );
    paperPath.remove();

    if (!tangent) {
      throw new Error(`[BezierBoolean] Failed to get tangent on path at offset ${offset}`);
    }
    return { x: tangent.x, y: tangent.y };
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[BezierBoolean]")) {
      throw error;
    }
    throw new Error(`[BezierBoolean] Failed to get tangent on path: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Get normal vector at a point on the path
 */
export function getNormalOnPath(
  path: BezierPath,
  offset: number,
): Point2D | null {
  try {
    initializePaper();

    const paperPath = latticePathToPaperPath(path);
    const normal = paperPath.getNormalAt(
      paperPath.length * Math.max(0, Math.min(1, offset)),
    );
    paperPath.remove();

    if (!normal) {
      throw new Error(`[BezierBoolean] Failed to get normal on path at offset ${offset}`);
    }
    return { x: normal.x, y: normal.y };
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[BezierBoolean]")) {
      throw error;
    }
    throw new Error(`[BezierBoolean] Failed to get normal on path: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Check if two paths intersect
 */
export function pathsIntersect(pathA: BezierPath, pathB: BezierPath): boolean {
  try {
    initializePaper();

    const paperA = latticePathToPaperPath(pathA);
    const paperB = latticePathToPaperPath(pathB);

    const intersections = paperA.getIntersections(paperB);
    const hasIntersections = intersections.length > 0;

    paperA.remove();
    paperB.remove();

    return hasIntersections;
  } catch (error) {
    logger.warn("Failed to check path intersections:", error);
    return false;
  }
}

/**
 * Get intersection points between two paths
 */
export function getPathIntersections(
  pathA: BezierPath,
  pathB: BezierPath,
): Point2D[] {
  try {
    initializePaper();

    const paperA = latticePathToPaperPath(pathA);
    const paperB = latticePathToPaperPath(pathB);

    const intersections = paperA.getIntersections(paperB);
    const points = intersections.map((i) => ({ x: i.point.x, y: i.point.y }));

    paperA.remove();
    paperB.remove();

    return points;
  } catch (error) {
    logger.warn("Failed to get path intersections:", error);
    return [];
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// Export Default
// ═══════════════════════════════════════════════════════════════════════════

export default {
  booleanOperation,
  unite,
  subtract,
  intersect,
  exclude,
  divide,
  uniteAll,
  intersectAll,
  simplifyPath,
  flattenPath,
  smoothPath,
  getPathArea,
  getPathLength,
  getPointOnPath,
  getTangentOnPath,
  getNormalOnPath,
  pathsIntersect,
  getPathIntersections,
};
