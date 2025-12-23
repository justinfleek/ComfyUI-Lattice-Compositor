/**
 * Shape Operations Service
 *
 * Mathematical implementations for all shape path operations.
 * Handles trim paths, merge paths, offset, pucker/bloat, wiggle, zig-zag, etc.
 *
 * Path modifier effects are in shape/pathModifiers.ts:
 * - Pucker/Bloat, Wiggle, Zig-Zag, Roughen, Wave, Twist
 */

import type {
  Point2D,
  BezierVertex,
  BezierPath,
  TrimMode,
  MergeMode,
  OffsetJoin,
  WigglePointType,
  ZigZagPointType,
} from '@/types/shapes';
import { SeededRandom } from './particleSystem';
import polygonClipping from 'polygon-clipping';
import * as bezierBoolean from './bezierBoolean';
import { createLogger } from '@/utils/logger';

// Import path modifiers
import {
  puckerBloat as _puckerBloat,
  wigglePath as _wigglePath,
  zigZagPath as _zigZagPath,
  roughenPath as _roughenPath,
  wavePath as _wavePath,
  twistPath as _twistPath,
  type WaveType as _WaveType,
} from './shape/pathModifiers';

// Re-export for backwards compatibility
export {
  puckerBloat,
  wigglePath,
  zigZagPath,
  roughenPath,
  wavePath,
  twistPath,
  type WaveType,
} from './shape/pathModifiers';

// Local aliases for internal use
const puckerBloat = _puckerBloat;
const wigglePath = _wigglePath;
const zigZagPath = _zigZagPath;
const roughenPath = _roughenPath;
const wavePath = _wavePath;
const twistPath = _twistPath;
type WaveType = _WaveType;

const logger = createLogger('ShapeOperations');

// Type alias for polygon-clipping library types
type Ring = [number, number][];
type Polygon = Ring[];
type MultiPolygon = Polygon[];

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/** Distance between two points */
export function distance(a: Point2D, b: Point2D): number {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  return Math.sqrt(dx * dx + dy * dy);
}

/** Lerp between two points */
export function lerpPoint(a: Point2D, b: Point2D, t: number): Point2D {
  return {
    x: a.x + (b.x - a.x) * t,
    y: a.y + (b.y - a.y) * t,
  };
}

/** Add two points */
export function addPoints(a: Point2D, b: Point2D): Point2D {
  return { x: a.x + b.x, y: a.y + b.y };
}

/** Subtract points (a - b) */
export function subtractPoints(a: Point2D, b: Point2D): Point2D {
  return { x: a.x - b.x, y: a.y - b.y };
}

/** Scale a point */
export function scalePoint(p: Point2D, s: number): Point2D {
  return { x: p.x * s, y: p.y * s };
}

/** Normalize a vector */
export function normalize(p: Point2D): Point2D {
  const len = Math.sqrt(p.x * p.x + p.y * p.y);
  if (len < 0.0001) return { x: 0, y: 0 };
  return { x: p.x / len, y: p.y / len };
}

/** Perpendicular vector (rotate 90 degrees) */
export function perpendicular(p: Point2D): Point2D {
  return { x: -p.y, y: p.x };
}

/** Dot product */
export function dot(a: Point2D, b: Point2D): number {
  return a.x * b.x + a.y * b.y;
}

/** Cross product (2D returns scalar) */
export function cross(a: Point2D, b: Point2D): number {
  return a.x * b.y - a.y * b.x;
}

/** Rotate point around origin */
export function rotatePoint(p: Point2D, angle: number): Point2D {
  const cos = Math.cos(angle);
  const sin = Math.sin(angle);
  return {
    x: p.x * cos - p.y * sin,
    y: p.x * sin + p.y * cos,
  };
}

/** Rotate point around center */
export function rotateAround(p: Point2D, center: Point2D, angle: number): Point2D {
  const translated = subtractPoints(p, center);
  const rotated = rotatePoint(translated, angle);
  return addPoints(rotated, center);
}

/** Clone a point */
export function clonePoint(p: Point2D): Point2D {
  return { x: p.x, y: p.y };
}

/** Clone a vertex */
export function cloneVertex(v: BezierVertex): BezierVertex {
  return {
    point: clonePoint(v.point),
    inHandle: clonePoint(v.inHandle),
    outHandle: clonePoint(v.outHandle),
  };
}

/** Clone a path */
export function clonePath(path: BezierPath): BezierPath {
  return {
    vertices: path.vertices.map(cloneVertex),
    closed: path.closed,
  };
}

// ============================================================================
// BEZIER CURVE UTILITIES
// ============================================================================

/**
 * Evaluate cubic bezier at t
 * p0 = start point, p1 = start control, p2 = end control, p3 = end point
 */
export function cubicBezierPoint(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number
): Point2D {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  const t2 = t * t;
  const t3 = t2 * t;

  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y,
  };
}

/**
 * Evaluate cubic bezier derivative at t (tangent direction)
 */
export function cubicBezierDerivative(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number
): Point2D {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const t2 = t * t;

  return {
    x: 3 * mt2 * (p1.x - p0.x) + 6 * mt * t * (p2.x - p1.x) + 3 * t2 * (p3.x - p2.x),
    y: 3 * mt2 * (p1.y - p0.y) + 6 * mt * t * (p2.y - p1.y) + 3 * t2 * (p3.y - p2.y),
  };
}

/**
 * Split a cubic bezier at t using de Casteljau's algorithm
 * Returns [leftCurve, rightCurve] as arrays of 4 points each
 */
export function splitCubicBezier(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number
): [Point2D[], Point2D[]] {
  const q0 = lerpPoint(p0, p1, t);
  const q1 = lerpPoint(p1, p2, t);
  const q2 = lerpPoint(p2, p3, t);

  const r0 = lerpPoint(q0, q1, t);
  const r1 = lerpPoint(q1, q2, t);

  const s = lerpPoint(r0, r1, t);

  return [
    [p0, q0, r0, s],
    [s, r1, q2, p3],
  ];
}

/**
 * Approximate arc length of cubic bezier using adaptive subdivision
 */
export function cubicBezierLength(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  subdivisions: number = 32
): number {
  let length = 0;
  let prev = p0;

  for (let i = 1; i <= subdivisions; i++) {
    const t = i / subdivisions;
    const curr = cubicBezierPoint(p0, p1, p2, p3, t);
    length += distance(prev, curr);
    prev = curr;
  }

  return length;
}

/**
 * Get total path length
 */
export function getPathLength(path: BezierPath): number {
  if (path.vertices.length < 2) return 0;

  let totalLength = 0;
  const numSegments = path.closed ? path.vertices.length : path.vertices.length - 1;

  for (let i = 0; i < numSegments; i++) {
    const v0 = path.vertices[i];
    const v1 = path.vertices[(i + 1) % path.vertices.length];

    const p0 = v0.point;
    const p1 = addPoints(v0.point, v0.outHandle);
    const p2 = addPoints(v1.point, v1.inHandle);
    const p3 = v1.point;

    totalLength += cubicBezierLength(p0, p1, p2, p3);
  }

  return totalLength;
}

/**
 * Get point at distance along path
 */
export function getPointAtDistance(
  path: BezierPath,
  targetDistance: number,
  totalLength?: number
): { point: Point2D; tangent: Point2D; t: number } | null {
  if (path.vertices.length < 2) return null;

  const pathLength = totalLength ?? getPathLength(path);
  if (pathLength < 0.0001) return null;

  // Clamp distance
  targetDistance = Math.max(0, Math.min(pathLength, targetDistance));

  let accumulatedLength = 0;
  const numSegments = path.closed ? path.vertices.length : path.vertices.length - 1;

  for (let i = 0; i < numSegments; i++) {
    const v0 = path.vertices[i];
    const v1 = path.vertices[(i + 1) % path.vertices.length];

    const p0 = v0.point;
    const p1 = addPoints(v0.point, v0.outHandle);
    const p2 = addPoints(v1.point, v1.inHandle);
    const p3 = v1.point;

    const segmentLength = cubicBezierLength(p0, p1, p2, p3);

    if (accumulatedLength + segmentLength >= targetDistance) {
      // Target is on this segment
      const remainingDistance = targetDistance - accumulatedLength;
      const localT = remainingDistance / segmentLength;

      const point = cubicBezierPoint(p0, p1, p2, p3, localT);
      const tangent = normalize(cubicBezierDerivative(p0, p1, p2, p3, localT));
      const globalT = (i + localT) / numSegments;

      return { point, tangent, t: globalT };
    }

    accumulatedLength += segmentLength;
  }

  // Return end point
  const lastVertex = path.vertices[path.closed ? 0 : path.vertices.length - 1];
  return {
    point: clonePoint(lastVertex.point),
    tangent: { x: 1, y: 0 },
    t: 1,
  };
}

// ============================================================================
// TRIM PATHS
// ============================================================================

/**
 * Trim a path from start% to end% with offset
 * This is the most-requested shape operator!
 */
export function trimPath(
  path: BezierPath,
  startPercent: number,
  endPercent: number,
  offsetDegrees: number = 0
): BezierPath {
  if (path.vertices.length < 2) return clonePath(path);

  const totalLength = getPathLength(path);
  if (totalLength < 0.0001) return clonePath(path);

  // Apply offset (convert degrees to path percentage)
  const offsetPercent = (offsetDegrees / 360) * 100;
  let start = ((startPercent + offsetPercent) % 100 + 100) % 100;
  let end = ((endPercent + offsetPercent) % 100 + 100) % 100;

  // Handle wrap-around for closed paths
  if (start > end && path.closed) {
    // Split into two segments: start->100 and 0->end
    const part1 = trimPathSimple(path, start, 100, totalLength);
    const part2 = trimPathSimple(path, 0, end, totalLength);
    return joinPaths(part1, part2);
  }

  // Ensure start <= end
  if (start > end) {
    [start, end] = [end, start];
  }

  return trimPathSimple(path, start, end, totalLength);
}

/**
 * Simple trim without wrap-around handling
 */
function trimPathSimple(
  path: BezierPath,
  startPercent: number,
  endPercent: number,
  totalLength: number
): BezierPath {
  const startDist = (startPercent / 100) * totalLength;
  const endDist = (endPercent / 100) * totalLength;

  if (endDist - startDist < 0.001) {
    return { vertices: [], closed: false };
  }

  const result: BezierVertex[] = [];
  let accumulatedLength = 0;
  const numSegments = path.closed ? path.vertices.length : path.vertices.length - 1;

  let inTrimRegion = false;
  let lastPoint: Point2D | null = null;

  for (let i = 0; i < numSegments; i++) {
    const v0 = path.vertices[i];
    const v1 = path.vertices[(i + 1) % path.vertices.length];

    const p0 = v0.point;
    const p1 = addPoints(v0.point, v0.outHandle);
    const p2 = addPoints(v1.point, v1.inHandle);
    const p3 = v1.point;

    const segmentLength = cubicBezierLength(p0, p1, p2, p3);
    const segmentStart = accumulatedLength;
    const segmentEnd = accumulatedLength + segmentLength;

    // Check if this segment intersects the trim region
    if (segmentEnd > startDist && segmentStart < endDist) {
      // Calculate local t values for trim boundaries
      const tStart = Math.max(0, (startDist - segmentStart) / segmentLength);
      const tEnd = Math.min(1, (endDist - segmentStart) / segmentLength);

      // Split the segment at trim boundaries
      let trimmedPoints: Point2D[];

      if (tStart > 0 && tEnd < 1) {
        // Need to split both ends
        const [, right] = splitCubicBezier(p0, p1, p2, p3, tStart);
        const newTEnd = (tEnd - tStart) / (1 - tStart);
        const [left] = splitCubicBezier(right[0], right[1], right[2], right[3], newTEnd);
        trimmedPoints = left;
      } else if (tStart > 0) {
        // Split at start only
        const [, right] = splitCubicBezier(p0, p1, p2, p3, tStart);
        trimmedPoints = right;
      } else if (tEnd < 1) {
        // Split at end only
        const [left] = splitCubicBezier(p0, p1, p2, p3, tEnd);
        trimmedPoints = left;
      } else {
        // Use whole segment
        trimmedPoints = [p0, p1, p2, p3];
      }

      // Convert to vertices
      if (!inTrimRegion || result.length === 0) {
        // Start new path segment
        result.push({
          point: trimmedPoints[0],
          inHandle: { x: 0, y: 0 },
          outHandle: subtractPoints(trimmedPoints[1], trimmedPoints[0]),
        });
        inTrimRegion = true;
      } else if (lastPoint && distance(lastPoint, trimmedPoints[0]) > 0.01) {
        // Gap in path, update last vertex's out handle
        if (result.length > 0) {
          result[result.length - 1].outHandle = subtractPoints(trimmedPoints[1], result[result.length - 1].point);
        }
      }

      // Add end vertex
      result.push({
        point: trimmedPoints[3],
        inHandle: subtractPoints(trimmedPoints[2], trimmedPoints[3]),
        outHandle: { x: 0, y: 0 },
      });

      lastPoint = trimmedPoints[3];
    }

    accumulatedLength += segmentLength;
  }

  // Update handles between consecutive vertices
  for (let i = 0; i < result.length - 1; i++) {
    // The out handle of vertex i should point toward vertex i+1
    // Already handled during construction
  }

  return { vertices: result, closed: false };
}

/**
 * Join two paths end-to-end
 */
function joinPaths(path1: BezierPath, path2: BezierPath): BezierPath {
  if (path1.vertices.length === 0) return clonePath(path2);
  if (path2.vertices.length === 0) return clonePath(path1);

  const result = clonePath(path1);
  const p2Verts = path2.vertices.map(cloneVertex);

  // If the paths meet, merge the junction vertices
  const lastP1 = result.vertices[result.vertices.length - 1];
  const firstP2 = p2Verts[0];

  if (distance(lastP1.point, firstP2.point) < 0.01) {
    // Merge the vertices
    lastP1.outHandle = firstP2.outHandle;
    result.vertices.push(...p2Verts.slice(1));
  } else {
    // Just concatenate
    result.vertices.push(...p2Verts);
  }

  return result;
}

// ============================================================================
// MERGE PATHS (Boolean Operations)
// ============================================================================

/**
 * Merge multiple paths using boolean operations
 * Uses simplified polygon clipping (for production, consider using a library like clipper-lib)
 */
export function mergePaths(paths: BezierPath[], mode: MergeMode): BezierPath[] {
  if (paths.length === 0) return [];
  if (paths.length === 1) return [clonePath(paths[0])];

  // Convert paths to polygons for boolean operations
  const polygons = paths.map(pathToPolygon);

  let result: Point2D[][] = [polygons[0]];

  for (let i = 1; i < polygons.length; i++) {
    const newPolygons: Point2D[][] = [];

    for (const existing of result) {
      switch (mode) {
        case 'add':
          newPolygons.push(...polygonUnion(existing, polygons[i]));
          break;
        case 'subtract':
        case 'minusFront':
          newPolygons.push(...polygonDifference(existing, polygons[i]));
          break;
        case 'minusBack':
          newPolygons.push(...polygonDifference(polygons[i], existing));
          break;
        case 'intersect':
          newPolygons.push(...polygonIntersection(existing, polygons[i]));
          break;
        case 'exclude':
          newPolygons.push(...polygonXor(existing, polygons[i]));
          break;
      }
    }

    result = newPolygons;
  }

  // Convert back to bezier paths
  return result.map(polygonToPath);
}

/**
 * Boolean operation type for direct use
 */
export type BooleanOperationType = 'union' | 'subtract' | 'intersect' | 'exclude';

/**
 * Perform a boolean operation on multiple BezierPaths
 * Higher-level API that handles path conversion and curve refitting
 *
 * Uses Paper.js bezier-aware booleans for best curve quality.
 * Falls back to polygon-clipping if Paper.js fails.
 *
 * @param paths - Array of BezierPaths to combine
 * @param operation - Type of boolean operation
 * @param segmentsPerCurve - Sampling resolution for fallback path flattening (default 32)
 * @returns Array of resulting BezierPaths
 */
export function booleanOperation(
  paths: BezierPath[],
  operation: BooleanOperationType,
  segmentsPerCurve: number = 32
): BezierPath[] {
  if (paths.length === 0) return [];
  if (paths.length === 1) return [clonePath(paths[0])];

  // Try Paper.js bezier-aware boolean first for better curve preservation
  const bezierResult = tryBezierBoolean(paths, operation);
  if (bezierResult) {
    logger.debug(`Bezier boolean ${operation} succeeded with ${bezierResult.length} output paths`);
    return bezierResult;
  }

  // Fallback to polygon-clipping if bezier boolean fails
  logger.debug(`Bezier boolean failed, falling back to polygon-clipping for ${operation}`);
  return fallbackPolygonBoolean(paths, operation, segmentsPerCurve);
}

/**
 * Try to perform boolean operation using Paper.js bezier-aware booleans
 * Returns null if operation fails
 */
function tryBezierBoolean(
  paths: BezierPath[],
  operation: BooleanOperationType
): BezierPath[] | null {
  try {
    // Map operation type to bezierBoolean operation
    const opMap: Record<BooleanOperationType, bezierBoolean.BooleanOperation> = {
      'union': 'unite',
      'subtract': 'subtract',
      'intersect': 'intersect',
      'exclude': 'exclude',
    };

    const bezierOp = opMap[operation];
    if (!bezierOp) return null;

    // Perform operation pairwise
    let resultPaths = [paths[0]];

    for (let i = 1; i < paths.length; i++) {
      const newResults: BezierPath[] = [];

      for (const currentPath of resultPaths) {
        const opResult = bezierBoolean.booleanOperation(currentPath, paths[i], bezierOp);
        if (!opResult.success) {
          return null; // Fallback to polygon-clipping
        }
        newResults.push(...opResult.paths);
      }

      resultPaths = newResults;
    }

    return resultPaths.length > 0 ? resultPaths : null;
  } catch (error) {
    logger.warn('Bezier boolean operation failed:', error);
    return null;
  }
}

/**
 * Fallback polygon-clipping based boolean operation
 * Used when Paper.js bezier booleans fail
 */
function fallbackPolygonBoolean(
  paths: BezierPath[],
  operation: BooleanOperationType,
  segmentsPerCurve: number
): BezierPath[] {
  // Convert all paths to polygon-clipping MultiPolygon format
  const multiPolygons: MultiPolygon[] = paths.map(path => {
    const polygon = pathToPolygon(path, segmentsPerCurve);
    return [point2DArrayToPolygon(polygon)];
  });

  let result: MultiPolygon;

  try {
    // Need at least one polygon
    if (multiPolygons.length === 0) {
      return [];
    }
    if (multiPolygons.length === 1) {
      return [clonePath(paths[0])];
    }

    switch (operation) {
      case 'union':
        // Accumulate union operations
        result = multiPolygons[0];
        for (let i = 1; i < multiPolygons.length; i++) {
          result = polygonClipping.union(result, multiPolygons[i]);
        }
        break;
      case 'subtract':
        // Subtract all subsequent paths from the first
        result = multiPolygons[0];
        for (let i = 1; i < multiPolygons.length; i++) {
          result = polygonClipping.difference(result, multiPolygons[i]);
        }
        break;
      case 'intersect':
        // Accumulate intersection operations
        result = multiPolygons[0];
        for (let i = 1; i < multiPolygons.length; i++) {
          result = polygonClipping.intersection(result, multiPolygons[i]);
        }
        break;
      case 'exclude':
        // Accumulate xor operations
        result = multiPolygons[0];
        for (let i = 1; i < multiPolygons.length; i++) {
          result = polygonClipping.xor(result, multiPolygons[i]);
        }
        break;
      default:
        return paths.map(clonePath);
    }
  } catch {
    // Fallback on error
    return paths.map(clonePath);
  }

  // Convert result back to BezierPaths with curve fitting
  const outputPaths: BezierPath[] = [];
  for (const polygon of result) {
    if (polygon.length > 0) {
      // Convert outer ring to path
      const points = ringToPoint2DArray(polygon[0]);
      if (points.length >= 3) {
        // Fit bezier curves to the polygon points for smoother result
        const bezierPath = fitBezierToPolygon(points, true);
        outputPaths.push(bezierPath);
      }
    }
  }

  return outputPaths;
}

/**
 * Fit bezier curves to a polygon for smoother paths
 * Uses Catmull-Rom to bezier conversion for smooth curves
 */
function fitBezierToPolygon(points: Point2D[], closed: boolean): BezierPath {
  if (points.length < 2) {
    return { vertices: [], closed };
  }

  // Simplify points first to reduce noise
  const simplified = simplifyPolygon(points, 0.5);

  if (simplified.length < 2) {
    return polygonToPath(points);
  }

  // For each point, calculate smooth handles using adjacent points
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < simplified.length; i++) {
    const curr = simplified[i];
    const prev = simplified[(i - 1 + simplified.length) % simplified.length];
    const next = simplified[(i + 1) % simplified.length];

    // Calculate tangent at this point (average of in and out directions)
    const toPrev = subtractPoints(prev, curr);
    const toNext = subtractPoints(next, curr);

    // Handle length is proportional to distance to neighbors
    const distPrev = distance(curr, prev);
    const distNext = distance(curr, next);
    const handleScale = 0.25; // Adjust for curve tightness

    // Smooth handles using tangent
    let inHandle: Point2D;
    let outHandle: Point2D;

    if (!closed && i === 0) {
      // First point of open path - no in handle
      inHandle = { x: 0, y: 0 };
      outHandle = scalePoint(normalize(toNext), distNext * handleScale);
    } else if (!closed && i === simplified.length - 1) {
      // Last point of open path - no out handle
      inHandle = scalePoint(normalize(toPrev), distPrev * handleScale);
      outHandle = { x: 0, y: 0 };
    } else {
      // Interior point or closed path - smooth handles
      const tangent = normalize(subtractPoints(toNext, toPrev));
      inHandle = scalePoint(tangent, -distPrev * handleScale);
      outHandle = scalePoint(tangent, distNext * handleScale);
    }

    vertices.push({
      point: clonePoint(curr),
      inHandle,
      outHandle,
    });
  }

  return { vertices, closed };
}

/**
 * Simplify polygon using Ramer-Douglas-Peucker algorithm
 */
function simplifyPolygon(points: Point2D[], tolerance: number): Point2D[] {
  if (points.length <= 2) return points;

  // Find point with maximum distance from line between first and last
  let maxDist = 0;
  let maxIndex = 0;

  const first = points[0];
  const last = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const d = perpendicularDistance(points[i], first, last);
    if (d > maxDist) {
      maxDist = d;
      maxIndex = i;
    }
  }

  // If max distance > tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = simplifyPolygon(points.slice(0, maxIndex + 1), tolerance);
    const right = simplifyPolygon(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  }

  // Otherwise, return just the endpoints
  return [first, last];
}

/**
 * Calculate perpendicular distance from point to line
 */
function perpendicularDistance(point: Point2D, lineStart: Point2D, lineEnd: Point2D): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const lineLengthSq = dx * dx + dy * dy;

  if (lineLengthSq === 0) {
    return distance(point, lineStart);
  }

  const t = Math.max(0, Math.min(1,
    ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / lineLengthSq
  ));

  const projection = {
    x: lineStart.x + t * dx,
    y: lineStart.y + t * dy,
  };

  return distance(point, projection);
}

/**
 * Convert bezier path to polygon (flattened)
 */
function pathToPolygon(path: BezierPath, segments: number = 16): Point2D[] {
  const points: Point2D[] = [];
  const numSegments = path.closed ? path.vertices.length : path.vertices.length - 1;

  for (let i = 0; i < numSegments; i++) {
    const v0 = path.vertices[i];
    const v1 = path.vertices[(i + 1) % path.vertices.length];

    const p0 = v0.point;
    const p1 = addPoints(v0.point, v0.outHandle);
    const p2 = addPoints(v1.point, v1.inHandle);
    const p3 = v1.point;

    for (let j = 0; j < segments; j++) {
      const t = j / segments;
      points.push(cubicBezierPoint(p0, p1, p2, p3, t));
    }
  }

  return points;
}

/**
 * Convert polygon back to bezier path (with straight segments)
 */
function polygonToPath(polygon: Point2D[]): BezierPath {
  const vertices: BezierVertex[] = polygon.map(p => ({
    point: clonePoint(p),
    inHandle: { x: 0, y: 0 },
    outHandle: { x: 0, y: 0 },
  }));

  return { vertices, closed: true };
}

// Simplified polygon boolean operations (placeholder implementations)
// For production, use a proper polygon clipping library

/**
 * Convert Point2D[] to polygon-clipping Ring format
 */
function point2DArrayToRing(points: Point2D[]): Ring {
  return points.map(p => [p.x, p.y] as [number, number]);
}

/**
 * Convert polygon-clipping Ring to Point2D[]
 */
function ringToPoint2DArray(ring: Ring): Point2D[] {
  return ring.map(([x, y]) => ({ x, y }));
}

/**
 * Convert Point2D[] to polygon-clipping Polygon format (single ring)
 */
function point2DArrayToPolygon(points: Point2D[]): Polygon {
  return [point2DArrayToRing(points)];
}

/**
 * Convert polygon-clipping MultiPolygon result to Point2D[][]
 */
function multiPolygonToPoint2DArrays(multiPoly: MultiPolygon): Point2D[][] {
  const result: Point2D[][] = [];
  for (const polygon of multiPoly) {
    // Take the outer ring of each polygon (index 0)
    // polygon[0] is outer ring, polygon[1+] are holes
    if (polygon.length > 0) {
      result.push(ringToPoint2DArray(polygon[0]));
    }
  }
  return result;
}

/**
 * Boolean union of two polygons using polygon-clipping
 */
function polygonUnion(a: Point2D[], b: Point2D[]): Point2D[][] {
  try {
    const polyA = point2DArrayToPolygon(a);
    const polyB = point2DArrayToPolygon(b);
    const result = polygonClipping.union([polyA], [polyB]);
    return multiPolygonToPoint2DArrays(result);
  } catch {
    // Fallback on error: return both original polygons
    return [a, b];
  }
}

/**
 * Boolean difference of two polygons (a - b) using polygon-clipping
 */
function polygonDifference(a: Point2D[], b: Point2D[]): Point2D[][] {
  try {
    const polyA = point2DArrayToPolygon(a);
    const polyB = point2DArrayToPolygon(b);
    const result = polygonClipping.difference([polyA], [polyB]);
    return multiPolygonToPoint2DArrays(result);
  } catch {
    // Fallback on error: return first polygon
    return [a];
  }
}

/**
 * Boolean intersection of two polygons using polygon-clipping
 */
function polygonIntersection(a: Point2D[], b: Point2D[]): Point2D[][] {
  try {
    const polyA = point2DArrayToPolygon(a);
    const polyB = point2DArrayToPolygon(b);
    const result = polygonClipping.intersection([polyA], [polyB]);
    return multiPolygonToPoint2DArrays(result);
  } catch {
    // Fallback on error: return empty
    return [];
  }
}

/**
 * Boolean XOR of two polygons using polygon-clipping
 */
function polygonXor(a: Point2D[], b: Point2D[]): Point2D[][] {
  try {
    const polyA = point2DArrayToPolygon(a);
    const polyB = point2DArrayToPolygon(b);
    const result = polygonClipping.xor([polyA], [polyB]);
    return multiPolygonToPoint2DArrays(result);
  } catch {
    // Fallback on error: return both original polygons
    return [a, b];
  }
}

// ============================================================================
// OFFSET PATHS
// ============================================================================

/**
 * Offset a path inward or outward
 */
export function offsetPath(
  path: BezierPath,
  amount: number,
  join: OffsetJoin = 'miter',
  miterLimit: number = 4
): BezierPath {
  if (path.vertices.length < 2 || Math.abs(amount) < 0.001) {
    return clonePath(path);
  }

  const result: BezierVertex[] = [];
  const numVertices = path.vertices.length;
  const isClosed = path.closed;

  for (let i = 0; i < numVertices; i++) {
    const curr = path.vertices[i];
    const prev = path.vertices[(i - 1 + numVertices) % numVertices];
    const next = path.vertices[(i + 1) % numVertices];

    // Get tangent directions
    let inDir: Point2D;
    let outDir: Point2D;

    if (i === 0 && !isClosed) {
      // First vertex of open path
      inDir = { x: 0, y: 0 };
      outDir = normalize(subtractPoints(
        addPoints(next.point, next.inHandle),
        addPoints(curr.point, curr.outHandle)
      ));
    } else if (i === numVertices - 1 && !isClosed) {
      // Last vertex of open path
      inDir = normalize(subtractPoints(
        addPoints(curr.point, curr.inHandle),
        addPoints(prev.point, prev.outHandle)
      ));
      outDir = { x: 0, y: 0 };
    } else {
      // Interior vertex or closed path vertex
      inDir = normalize(subtractPoints(
        curr.point,
        addPoints(prev.point, prev.outHandle)
      ));
      outDir = normalize(subtractPoints(
        addPoints(curr.point, curr.outHandle),
        curr.point
      ));
    }

    // Calculate offset direction (perpendicular to average tangent)
    let offsetDir: Point2D;

    if (Math.abs(inDir.x) < 0.001 && Math.abs(inDir.y) < 0.001) {
      offsetDir = perpendicular(outDir);
    } else if (Math.abs(outDir.x) < 0.001 && Math.abs(outDir.y) < 0.001) {
      offsetDir = perpendicular(inDir);
    } else {
      // Average the perpendiculars
      const perpIn = perpendicular(inDir);
      const perpOut = perpendicular(outDir);
      offsetDir = normalize(addPoints(perpIn, perpOut));

      // Apply miter correction for sharp corners
      const angle = Math.acos(Math.max(-1, Math.min(1, dot(inDir, outDir))));
      if (angle > 0.01) {
        const miterFactor = 1 / Math.cos(angle / 2);
        if (join === 'miter' && miterFactor <= miterLimit) {
          offsetDir = scalePoint(offsetDir, miterFactor);
        }
      }
    }

    // Calculate new position
    const newPoint = addPoints(curr.point, scalePoint(offsetDir, amount));

    // Scale handles proportionally
    const handleScale = 1; // Could adjust based on curvature

    result.push({
      point: newPoint,
      inHandle: scalePoint(curr.inHandle, handleScale),
      outHandle: scalePoint(curr.outHandle, handleScale),
    });
  }

  return { vertices: result, closed: isClosed };
}

/**
 * Create multiple offset copies
 */
export function offsetPathMultiple(
  path: BezierPath,
  baseAmount: number,
  copies: number,
  copyOffset: number,
  join: OffsetJoin = 'miter',
  miterLimit: number = 4
): BezierPath[] {
  const results: BezierPath[] = [clonePath(path)];

  for (let i = 1; i < copies; i++) {
    const amount = baseAmount + copyOffset * i;
    results.push(offsetPath(path, amount, join, miterLimit));
  }

  return results;
}

// NOTE: puckerBloat, wigglePath, zigZagPath, roughenPath, wavePath, and twistPath
// have been moved to shape/pathModifiers.ts

// ============================================================================
// ROUNDED CORNERS
// ============================================================================

/**
 * Round the corners of a path
 */
export function roundCorners(path: BezierPath, radius: number): BezierPath {
  if (path.vertices.length < 2 || radius < 0.001) {
    return clonePath(path);
  }

  const result: BezierVertex[] = [];
  const numVertices = path.vertices.length;

  for (let i = 0; i < numVertices; i++) {
    const curr = path.vertices[i];
    const prev = path.vertices[(i - 1 + numVertices) % numVertices];
    const next = path.vertices[(i + 1) % numVertices];

    // Skip if not an interior vertex (for open paths)
    if (!path.closed && (i === 0 || i === numVertices - 1)) {
      result.push(cloneVertex(curr));
      continue;
    }

    // Get directions to neighboring vertices
    const toPrev = normalize(subtractPoints(prev.point, curr.point));
    const toNext = normalize(subtractPoints(next.point, curr.point));

    // Check angle - if too shallow, skip rounding
    const dotProduct = dot(toPrev, toNext);
    if (dotProduct > 0.99) {
      result.push(cloneVertex(curr));
      continue;
    }

    // Calculate corner points
    const distPrev = distance(curr.point, prev.point);
    const distNext = distance(curr.point, next.point);
    const maxRadius = Math.min(radius, distPrev / 2, distNext / 2);

    const startPoint = addPoints(curr.point, scalePoint(toPrev, maxRadius));
    const endPoint = addPoints(curr.point, scalePoint(toNext, maxRadius));

    // Calculate control point positions for a circular arc approximation
    const kappa = 0.5522847498; // Magic number for circular bezier approximation
    const handleLength = maxRadius * kappa;

    // Add the corner as a bezier curve
    result.push({
      point: startPoint,
      inHandle: { x: 0, y: 0 },
      outHandle: scalePoint(toPrev, -handleLength),
    });

    result.push({
      point: endPoint,
      inHandle: scalePoint(toNext, -handleLength),
      outHandle: { x: 0, y: 0 },
    });
  }

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// SHAPE GENERATORS
// ============================================================================

/**
 * Generate a rectangle path
 */
export function generateRectangle(
  position: Point2D,
  size: Point2D,
  roundness: number = 0,
  direction: 1 | -1 = 1
): BezierPath {
  const hw = size.x / 2;
  const hh = size.y / 2;
  const r = Math.min(roundness, hw, hh);

  // Corner positions (clockwise from top-left)
  const corners = [
    { x: position.x - hw, y: position.y - hh }, // TL
    { x: position.x + hw, y: position.y - hh }, // TR
    { x: position.x + hw, y: position.y + hh }, // BR
    { x: position.x - hw, y: position.y + hh }, // BL
  ];

  if (direction === -1) {
    corners.reverse();
  }

  if (r < 0.01) {
    // Sharp corners
    return {
      vertices: corners.map(p => ({
        point: p,
        inHandle: { x: 0, y: 0 },
        outHandle: { x: 0, y: 0 },
      })),
      closed: true,
    };
  }

  // Rounded corners
  const kappa = 0.5522847498 * r;
  const vertices: BezierVertex[] = [];

  // Generate 8 vertices (2 per corner)
  for (let i = 0; i < 4; i++) {
    const curr = corners[i];
    const next = corners[(i + 1) % 4];

    // Direction along this edge
    const dir = normalize(subtractPoints(next, curr));
    const perp = perpendicular(dir);

    // Start of rounded corner
    vertices.push({
      point: addPoints(curr, scalePoint(dir, r)),
      inHandle: scalePoint(dir, -kappa),
      outHandle: { x: 0, y: 0 },
    });

    // End of rounded corner (start of next edge)
    vertices.push({
      point: subtractPoints(next, scalePoint(dir, r)),
      inHandle: { x: 0, y: 0 },
      outHandle: scalePoint(dir, kappa),
    });
  }

  return { vertices, closed: true };
}

/**
 * Generate an ellipse path
 */
export function generateEllipse(
  position: Point2D,
  size: Point2D,
  direction: 1 | -1 = 1
): BezierPath {
  const rx = size.x / 2;
  const ry = size.y / 2;
  const kappa = 0.5522847498;

  // 4 vertices for ellipse (using kappa for perfect circle approximation)
  let vertices: BezierVertex[] = [
    { // Top
      point: { x: position.x, y: position.y - ry },
      inHandle: { x: -rx * kappa, y: 0 },
      outHandle: { x: rx * kappa, y: 0 },
    },
    { // Right
      point: { x: position.x + rx, y: position.y },
      inHandle: { x: 0, y: -ry * kappa },
      outHandle: { x: 0, y: ry * kappa },
    },
    { // Bottom
      point: { x: position.x, y: position.y + ry },
      inHandle: { x: rx * kappa, y: 0 },
      outHandle: { x: -rx * kappa, y: 0 },
    },
    { // Left
      point: { x: position.x - rx, y: position.y },
      inHandle: { x: 0, y: ry * kappa },
      outHandle: { x: 0, y: -ry * kappa },
    },
  ];

  if (direction === -1) {
    vertices = vertices.reverse().map(v => ({
      point: v.point,
      inHandle: v.outHandle,
      outHandle: v.inHandle,
    }));
  }

  return { vertices, closed: true };
}

/**
 * Generate a polygon path
 */
export function generatePolygon(
  position: Point2D,
  points: number,
  radius: number,
  roundness: number = 0,
  rotation: number = 0,
  direction: 1 | -1 = 1
): BezierPath {
  const numPoints = Math.max(3, Math.floor(points));
  const angleStep = (Math.PI * 2) / numPoints;
  const startAngle = (rotation - 90) * (Math.PI / 180);

  const vertices: BezierVertex[] = [];

  for (let i = 0; i < numPoints; i++) {
    const idx = direction === 1 ? i : numPoints - 1 - i;
    const angle = startAngle + angleStep * idx * direction;

    const point: Point2D = {
      x: position.x + Math.cos(angle) * radius,
      y: position.y + Math.sin(angle) * radius,
    };

    // Calculate handles for roundness
    const handleLength = radius * (roundness / 100) * 0.5;
    const tangentAngle = angle + Math.PI / 2 * direction;

    vertices.push({
      point,
      inHandle: roundness > 0 ? {
        x: Math.cos(tangentAngle) * handleLength,
        y: Math.sin(tangentAngle) * handleLength,
      } : { x: 0, y: 0 },
      outHandle: roundness > 0 ? {
        x: -Math.cos(tangentAngle) * handleLength,
        y: -Math.sin(tangentAngle) * handleLength,
      } : { x: 0, y: 0 },
    });
  }

  return { vertices, closed: true };
}

/**
 * Generate a star path
 */
export function generateStar(
  position: Point2D,
  points: number,
  outerRadius: number,
  innerRadius: number,
  outerRoundness: number = 0,
  innerRoundness: number = 0,
  rotation: number = 0,
  direction: 1 | -1 = 1
): BezierPath {
  const numPoints = Math.max(3, Math.floor(points));
  const angleStep = Math.PI / numPoints;
  const startAngle = (rotation - 90) * (Math.PI / 180);

  const vertices: BezierVertex[] = [];

  for (let i = 0; i < numPoints * 2; i++) {
    const idx = direction === 1 ? i : numPoints * 2 - 1 - i;
    const angle = startAngle + angleStep * idx * direction;
    const isOuter = idx % 2 === 0;

    const radius = isOuter ? outerRadius : innerRadius;
    const roundness = isOuter ? outerRoundness : innerRoundness;

    const point: Point2D = {
      x: position.x + Math.cos(angle) * radius,
      y: position.y + Math.sin(angle) * radius,
    };

    const handleLength = radius * (roundness / 100) * 0.3;
    const tangentAngle = angle + Math.PI / 2 * direction;

    vertices.push({
      point,
      inHandle: roundness > 0 ? {
        x: Math.cos(tangentAngle) * handleLength,
        y: Math.sin(tangentAngle) * handleLength,
      } : { x: 0, y: 0 },
      outHandle: roundness > 0 ? {
        x: -Math.cos(tangentAngle) * handleLength,
        y: -Math.sin(tangentAngle) * handleLength,
      } : { x: 0, y: 0 },
    });
  }

  return { vertices, closed: true };
}

// ============================================================================
// PATH SIMPLIFICATION (Illustrator-style)
// ============================================================================

/**
 * Simplify a path using Douglas-Peucker algorithm
 */
export function simplifyPath(
  path: BezierPath,
  tolerance: number,
  straightLines: boolean = false
): BezierPath {
  if (path.vertices.length <= 2) return clonePath(path);

  // Convert to points
  const points = pathToPolygon(path, 32);

  // Apply Douglas-Peucker
  const simplified = douglasPeucker(points, tolerance);

  // Convert back to bezier
  if (straightLines) {
    return polygonToPath(simplified);
  } else {
    // Fit bezier curves to the simplified points
    return fitBezierToPoints(simplified, path.closed);
  }
}

/**
 * Douglas-Peucker line simplification
 */
function douglasPeucker(points: Point2D[], tolerance: number): Point2D[] {
  if (points.length <= 2) return [...points];

  // Find point with maximum distance from line
  let maxDist = 0;
  let maxIndex = 0;

  const start = points[0];
  const end = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDistance(points[i], start, end);
    if (dist > maxDist) {
      maxDist = dist;
      maxIndex = i;
    }
  }

  // If max distance exceeds tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = douglasPeucker(points.slice(0, maxIndex + 1), tolerance);
    const right = douglasPeucker(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  } else {
    return [start, end];
  }
}


/**
 * Fit bezier curves to a sequence of points
 */
function fitBezierToPoints(points: Point2D[], closed: boolean): BezierPath {
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < points.length; i++) {
    const prev = points[(i - 1 + points.length) % points.length];
    const curr = points[i];
    const next = points[(i + 1) % points.length];

    // Calculate smooth handles
    const toPrev = subtractPoints(prev, curr);
    const toNext = subtractPoints(next, curr);

    const handleLength = Math.min(
      distance(curr, prev) * 0.3,
      distance(curr, next) * 0.3
    );

    const avgDir = normalize(subtractPoints(toNext, toPrev));

    vertices.push({
      point: clonePoint(curr),
      inHandle: scalePoint(avgDir, -handleLength),
      outHandle: scalePoint(avgDir, handleLength),
    });
  }

  return { vertices, closed };
}

/**
 * Smooth a path by adjusting handle lengths
 */
export function smoothPath(path: BezierPath, amount: number): BezierPath {
  if (path.vertices.length < 2) return clonePath(path);

  const factor = amount / 100;

  const result: BezierVertex[] = path.vertices.map((v, i) => {
    const prev = path.vertices[(i - 1 + path.vertices.length) % path.vertices.length];
    const next = path.vertices[(i + 1) % path.vertices.length];

    // Calculate ideal smooth handles
    const toPrev = subtractPoints(prev.point, v.point);
    const toNext = subtractPoints(next.point, v.point);

    const avgDir = normalize(subtractPoints(toNext, toPrev));
    const idealHandleLength = (distance(v.point, prev.point) + distance(v.point, next.point)) / 6;

    // Blend current handles toward ideal
    const idealIn = scalePoint(avgDir, -idealHandleLength);
    const idealOut = scalePoint(avgDir, idealHandleLength);

    return {
      point: clonePoint(v.point),
      inHandle: lerpPoint(v.inHandle, idealIn, factor),
      outHandle: lerpPoint(v.outHandle, idealOut, factor),
    };
  });

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// REPEATER TRANSFORM
// ============================================================================

/**
 * Apply repeater transform to generate copies
 */
export function applyRepeater(
  paths: BezierPath[],
  copies: number,
  offset: number,
  anchorPoint: Point2D,
  position: Point2D,
  scale: Point2D,
  rotation: number,
  startOpacity: number,
  endOpacity: number
): { paths: BezierPath[]; opacities: number[] }[] {
  const results: { paths: BezierPath[]; opacities: number[] }[] = [];

  for (let i = 0; i < copies; i++) {
    const t = copies > 1 ? i / (copies - 1) : 0;

    // Calculate transform for this copy
    const copyRotation = rotation * i;
    const copyScale = {
      x: 100 + (scale.x - 100) * i,
      y: 100 + (scale.y - 100) * i,
    };
    const copyPosition = {
      x: position.x * i,
      y: position.y * i,
    };
    const copyOpacity = startOpacity + (endOpacity - startOpacity) * t;

    // Transform each path
    const transformedPaths = paths.map(path => {
      return transformPath(path, anchorPoint, copyPosition, copyScale, copyRotation);
    });

    results.push({
      paths: transformedPaths,
      opacities: paths.map(() => copyOpacity / 100),
    });
  }

  return results;
}

/**
 * Apply transform to a path
 */
export function transformPath(
  path: BezierPath,
  anchorPoint: Point2D,
  position: Point2D,
  scale: Point2D,
  rotation: number
): BezierPath {
  const rotRad = (rotation * Math.PI) / 180;
  const cos = Math.cos(rotRad);
  const sin = Math.sin(rotRad);

  const transformPoint = (p: Point2D): Point2D => {
    // Translate to anchor
    let x = p.x - anchorPoint.x;
    let y = p.y - anchorPoint.y;

    // Scale
    x *= scale.x / 100;
    y *= scale.y / 100;

    // Rotate
    const rx = x * cos - y * sin;
    const ry = x * sin + y * cos;

    // Translate back and add position offset
    return {
      x: rx + anchorPoint.x + position.x,
      y: ry + anchorPoint.y + position.y,
    };
  };

  const vertices: BezierVertex[] = path.vertices.map(v => {
    const newPoint = transformPoint(v.point);
    const absIn = addPoints(v.point, v.inHandle);
    const absOut = addPoints(v.point, v.outHandle);
    const newIn = transformPoint(absIn);
    const newOut = transformPoint(absOut);

    return {
      point: newPoint,
      inHandle: subtractPoints(newIn, newPoint),
      outHandle: subtractPoints(newOut, newPoint),
    };
  });

  return { vertices, closed: path.closed };
}

// ============================================================================
// EXPORTS
// ============================================================================

export const ShapeOperations = {
  // Utilities
  distance,
  lerpPoint,
  addPoints,
  subtractPoints,
  scalePoint,
  normalize,
  perpendicular,
  clonePath,

  // Bezier
  cubicBezierPoint,
  cubicBezierLength,
  getPathLength,
  getPointAtDistance,
  splitCubicBezier,

  // Path operators
  trimPath,
  mergePaths,
  offsetPath,
  offsetPathMultiple,
  puckerBloat,
  wigglePath,
  zigZagPath,
  roughenPath,
  wavePath,
  twistPath,
  roundCorners,
  booleanOperation,

  // Generators
  generateRectangle,
  generateEllipse,
  generatePolygon,
  generateStar,

  // Illustrator features
  simplifyPath,
  smoothPath,

  // Repeater
  applyRepeater,
  transformPath,
};

export default ShapeOperations;
