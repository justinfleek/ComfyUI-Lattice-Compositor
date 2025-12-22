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

import paper from 'paper';
import type { Point2D, BezierVertex, BezierPath } from '@/types/shapes';
import { createLogger } from '@/utils/logger';

const logger = createLogger('BezierBoolean');

// ============================================================================
// Types
// ============================================================================

export type BooleanOperation = 'unite' | 'subtract' | 'intersect' | 'exclude' | 'divide';

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

// ============================================================================
// Paper.js Initialization
// ============================================================================

let paperInitialized = false;

/**
 * Initialize Paper.js in headless mode (no canvas)
 */
function initializePaper(): void {
  if (paperInitialized) return;

  // Paper.js needs a canvas or can run headless
  // Create a temporary offscreen canvas for headless operation
  const canvas = document.createElement('canvas');
  canvas.width = 1;
  canvas.height = 1;

  paper.setup(canvas);
  paperInitialized = true;
  logger.debug('Paper.js initialized for bezier boolean operations');
}

// ============================================================================
// Conversion: Weyl Path <-> Paper.js Path
// ============================================================================

/**
 * Convert a Weyl BezierPath to a Paper.js Path
 */
function weylPathToPaperPath(path: BezierPath): paper.Path {
  initializePaper();

  const paperPath = new paper.Path();
  paperPath.closed = path.closed;

  for (let i = 0; i < path.vertices.length; i++) {
    const v = path.vertices[i];
    const prevV = path.vertices[(i - 1 + path.vertices.length) % path.vertices.length];

    if (i === 0) {
      // First point: just moveTo
      paperPath.moveTo(new paper.Point(v.x, v.y));
    } else {
      // Subsequent points: use bezier curves with handles
      const handleOut = prevV.handleOut || { x: 0, y: 0 };
      const handleIn = v.handleIn || { x: 0, y: 0 };

      // Check if this is a straight line (no handles)
      if (
        Math.abs(handleOut.x) < 0.001 && Math.abs(handleOut.y) < 0.001 &&
        Math.abs(handleIn.x) < 0.001 && Math.abs(handleIn.y) < 0.001
      ) {
        paperPath.lineTo(new paper.Point(v.x, v.y));
      } else {
        // Bezier curve
        paperPath.cubicCurveTo(
          new paper.Point(prevV.x + handleOut.x, prevV.y + handleOut.y),
          new paper.Point(v.x + handleIn.x, v.y + handleIn.y),
          new paper.Point(v.x, v.y)
        );
      }
    }
  }

  // If closed, add closing segment
  if (path.closed && path.vertices.length > 1) {
    const lastV = path.vertices[path.vertices.length - 1];
    const firstV = path.vertices[0];
    const handleOut = lastV.handleOut || { x: 0, y: 0 };
    const handleIn = firstV.handleIn || { x: 0, y: 0 };

    if (
      Math.abs(handleOut.x) < 0.001 && Math.abs(handleOut.y) < 0.001 &&
      Math.abs(handleIn.x) < 0.001 && Math.abs(handleIn.y) < 0.001
    ) {
      paperPath.closePath();
    } else {
      paperPath.cubicCurveTo(
        new paper.Point(lastV.x + handleOut.x, lastV.y + handleOut.y),
        new paper.Point(firstV.x + handleIn.x, firstV.y + handleIn.y),
        new paper.Point(firstV.x, firstV.y)
      );
    }
  }

  return paperPath;
}

/**
 * Convert a Paper.js Path back to a Weyl BezierPath
 */
function paperPathToWeylPath(paperPath: paper.Path): BezierPath {
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < paperPath.segments.length; i++) {
    const segment = paperPath.segments[i];
    const point = segment.point;

    // Paper.js handles are relative to the point
    const handleIn = segment.handleIn;
    const handleOut = segment.handleOut;

    vertices.push({
      x: point.x,
      y: point.y,
      handleIn: handleIn.length > 0.001 ? { x: handleIn.x, y: handleIn.y } : undefined,
      handleOut: handleOut.length > 0.001 ? { x: handleOut.x, y: handleOut.y } : undefined,
    });
  }

  return {
    vertices,
    closed: paperPath.closed,
  };
}

/**
 * Convert Paper.js PathItem (could be Path or CompoundPath) to Weyl paths
 */
function paperItemToWeylPaths(item: paper.PathItem | null): BezierPath[] {
  if (!item) return [];

  if (item instanceof paper.Path) {
    return [paperPathToWeylPath(item)];
  }

  if (item instanceof paper.CompoundPath) {
    const paths: BezierPath[] = [];
    for (const child of item.children) {
      if (child instanceof paper.Path) {
        paths.push(paperPathToWeylPath(child));
      }
    }
    return paths;
  }

  return [];
}

// ============================================================================
// Boolean Operations
// ============================================================================

/**
 * Perform a boolean operation on two paths
 */
export function booleanOperation(
  pathA: BezierPath,
  pathB: BezierPath,
  operation: BooleanOperation,
  options: BooleanOptions = {}
): BooleanResult {
  try {
    initializePaper();

    // Convert to Paper.js paths
    const paperA = weylPathToPaperPath(pathA);
    const paperB = weylPathToPaperPath(pathB);

    let result: paper.PathItem | null = null;

    // Perform operation
    switch (operation) {
      case 'unite':
        result = paperA.unite(paperB, { insert: options.insert ?? false });
        break;
      case 'subtract':
        result = paperA.subtract(paperB, { insert: options.insert ?? false });
        break;
      case 'intersect':
        result = paperA.intersect(paperB, { insert: options.insert ?? false });
        break;
      case 'exclude':
        result = paperA.exclude(paperB, { insert: options.insert ?? false });
        break;
      case 'divide':
        result = paperA.divide(paperB, { insert: options.insert ?? false });
        break;
    }

    // Clean up temp paths
    paperA.remove();
    paperB.remove();

    // Convert result back to Weyl format
    const paths = paperItemToWeylPaths(result);

    if (result) {
      result.remove();
    }

    return {
      paths,
      success: paths.length > 0,
    };
  } catch (error) {
    logger.warn(`Boolean operation "${operation}" failed:`, error);
    return {
      paths: [],
      success: false,
      error: error instanceof Error ? error.message : 'Unknown error',
    };
  }
}

/**
 * Union (combine) two paths
 */
export function unite(pathA: BezierPath, pathB: BezierPath, options?: BooleanOptions): BooleanResult {
  return booleanOperation(pathA, pathB, 'unite', options);
}

/**
 * Subtract pathB from pathA
 */
export function subtract(pathA: BezierPath, pathB: BezierPath, options?: BooleanOptions): BooleanResult {
  return booleanOperation(pathA, pathB, 'subtract', options);
}

/**
 * Intersect two paths (area common to both)
 */
export function intersect(pathA: BezierPath, pathB: BezierPath, options?: BooleanOptions): BooleanResult {
  return booleanOperation(pathA, pathB, 'intersect', options);
}

/**
 * Exclude (XOR) two paths (area in either but not both)
 */
export function exclude(pathA: BezierPath, pathB: BezierPath, options?: BooleanOptions): BooleanResult {
  return booleanOperation(pathA, pathB, 'exclude', options);
}

/**
 * Divide pathA by pathB (split into separate pieces)
 */
export function divide(pathA: BezierPath, pathB: BezierPath, options?: BooleanOptions): BooleanResult {
  return booleanOperation(pathA, pathB, 'divide', options);
}

// ============================================================================
// Multi-Path Operations
// ============================================================================

/**
 * Union multiple paths into one
 */
export function uniteAll(paths: BezierPath[], options?: BooleanOptions): BooleanResult {
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
export function intersectAll(paths: BezierPath[], options?: BooleanOptions): BooleanResult {
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

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Simplify a path by removing redundant points while preserving shape
 */
export function simplifyPath(path: BezierPath, tolerance: number = 2.5): BezierPath {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    paperPath.simplify(tolerance);
    const result = paperPathToWeylPath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn('Path simplification failed:', error);
    return path;
  }
}

/**
 * Flatten a path by converting curves to line segments
 */
export function flattenPath(path: BezierPath, tolerance: number = 0.25): BezierPath {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    paperPath.flatten(tolerance);
    const result = paperPathToWeylPath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn('Path flattening failed:', error);
    return path;
  }
}

/**
 * Smooth a path by adjusting handles for continuity
 */
export function smoothPath(path: BezierPath): BezierPath {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    paperPath.smooth();
    const result = paperPathToWeylPath(paperPath);
    paperPath.remove();

    return result;
  } catch (error) {
    logger.warn('Path smoothing failed:', error);
    return path;
  }
}

/**
 * Get path area (positive for clockwise, negative for counter-clockwise)
 */
export function getPathArea(path: BezierPath): number {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    const area = paperPath.area;
    paperPath.remove();

    return area;
  } catch (error) {
    logger.warn('Failed to calculate path area:', error);
    return 0;
  }
}

/**
 * Get path length
 */
export function getPathLength(path: BezierPath): number {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    const length = paperPath.length;
    paperPath.remove();

    return length;
  } catch (error) {
    logger.warn('Failed to calculate path length:', error);
    return 0;
  }
}

/**
 * Get a point on the path at a given offset (0-1 normalized)
 */
export function getPointOnPath(path: BezierPath, offset: number): Point2D | null {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    const point = paperPath.getPointAt(paperPath.length * Math.max(0, Math.min(1, offset)));
    paperPath.remove();

    return point ? { x: point.x, y: point.y } : null;
  } catch (error) {
    logger.warn('Failed to get point on path:', error);
    return null;
  }
}

/**
 * Get tangent vector at a point on the path
 */
export function getTangentOnPath(path: BezierPath, offset: number): Point2D | null {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    const tangent = paperPath.getTangentAt(paperPath.length * Math.max(0, Math.min(1, offset)));
    paperPath.remove();

    return tangent ? { x: tangent.x, y: tangent.y } : null;
  } catch (error) {
    logger.warn('Failed to get tangent on path:', error);
    return null;
  }
}

/**
 * Get normal vector at a point on the path
 */
export function getNormalOnPath(path: BezierPath, offset: number): Point2D | null {
  try {
    initializePaper();

    const paperPath = weylPathToPaperPath(path);
    const normal = paperPath.getNormalAt(paperPath.length * Math.max(0, Math.min(1, offset)));
    paperPath.remove();

    return normal ? { x: normal.x, y: normal.y } : null;
  } catch (error) {
    logger.warn('Failed to get normal on path:', error);
    return null;
  }
}

/**
 * Check if two paths intersect
 */
export function pathsIntersect(pathA: BezierPath, pathB: BezierPath): boolean {
  try {
    initializePaper();

    const paperA = weylPathToPaperPath(pathA);
    const paperB = weylPathToPaperPath(pathB);

    const intersections = paperA.getIntersections(paperB);
    const hasIntersections = intersections.length > 0;

    paperA.remove();
    paperB.remove();

    return hasIntersections;
  } catch (error) {
    logger.warn('Failed to check path intersections:', error);
    return false;
  }
}

/**
 * Get intersection points between two paths
 */
export function getPathIntersections(pathA: BezierPath, pathB: BezierPath): Point2D[] {
  try {
    initializePaper();

    const paperA = weylPathToPaperPath(pathA);
    const paperB = weylPathToPaperPath(pathB);

    const intersections = paperA.getIntersections(paperB);
    const points = intersections.map(i => ({ x: i.point.x, y: i.point.y }));

    paperA.remove();
    paperB.remove();

    return points;
  } catch (error) {
    logger.warn('Failed to get path intersections:', error);
    return [];
  }
}

// ============================================================================
// Export Default
// ============================================================================

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
