/**
 * Path Morphing Service
 *
 * Provides smooth interpolation between two bezier paths for shape morphing
 * animations. Handles point count matching, correspondence optimization,
 * and smooth vertex interpolation.
 *
 * Key features:
 * - Automatic point count matching via subdivision
 * - Optimal correspondence finding to minimize travel distance
 * - Support for open and closed paths
 * - Smooth handle interpolation
 */

import type { BezierPath, BezierVertex, Point2D } from "@/types/shapes";
import { createLogger } from "@/utils/logger";

const logger = createLogger("PathMorphing");

// ============================================================================
// TYPES
// ============================================================================

/** Configuration for path morphing preparation */
export interface MorphConfig {
  /** Strategy for matching point counts */
  pointMatchingStrategy: "subdivide-shorter" | "subdivide-both" | "resample";
  /** Method for finding optimal vertex correspondence */
  correspondenceMethod:
    | "index"
    | "nearest-rotation"
    | "nearest-distance"
    | "manual";
  /** Manual correspondence mapping (vertex indices) */
  manualMapping?: number[];
  /** Number of segments for resampling (if using 'resample' strategy) */
  resampleCount?: number;
}

/** Result of preparing two paths for morphing */
export interface PreparedMorphPaths {
  source: BezierPath;
  target: BezierPath;
  /** Applied rotation offset for correspondence */
  rotationOffset: number;
  /** Whether paths were reversed for better correspondence */
  reversed: boolean;
}

/** Default configuration */
export const DEFAULT_MORPH_CONFIG: MorphConfig = {
  pointMatchingStrategy: "subdivide-shorter",
  correspondenceMethod: "nearest-rotation",
};

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/** Clone a point */
function clonePoint(p: Point2D): Point2D {
  return { x: p.x, y: p.y };
}

/** Clone a vertex */
function cloneVertex(v: BezierVertex): BezierVertex {
  return {
    point: clonePoint(v.point),
    inHandle: clonePoint(v.inHandle),
    outHandle: clonePoint(v.outHandle),
  };
}

/** Clone a path */
function clonePath(path: BezierPath): BezierPath {
  return {
    vertices: path.vertices.map(cloneVertex),
    closed: path.closed,
  };
}

/** Calculate distance between two points */
function distance(a: Point2D, b: Point2D): number {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  return Math.sqrt(dx * dx + dy * dy);
}

/** Linear interpolation between two numbers */
function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

/** Linear interpolation between two points */
function lerpPoint(a: Point2D, b: Point2D, t: number): Point2D {
  return {
    x: lerp(a.x, b.x, t),
    y: lerp(a.y, b.y, t),
  };
}

/** Add two points */
function addPoints(a: Point2D, b: Point2D): Point2D {
  return { x: a.x + b.x, y: a.y + b.y };
}

/** Subtract two points */
function subtractPoints(a: Point2D, b: Point2D): Point2D {
  return { x: a.x - b.x, y: a.y - b.y };
}

/** Scale a point */
function scalePoint(p: Point2D, s: number): Point2D {
  return { x: p.x * s, y: p.y * s };
}

// ============================================================================
// CUBIC BEZIER OPERATIONS
// ============================================================================

/** Evaluate a cubic bezier curve at parameter t */
function cubicBezierPoint(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number,
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

/** Split a cubic bezier at parameter t using de Casteljau's algorithm */
function splitCubicBezier(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number,
): [Point2D[], Point2D[]] {
  const q0 = lerpPoint(p0, p1, t);
  const q1 = lerpPoint(p1, p2, t);
  const q2 = lerpPoint(p2, p3, t);
  const r0 = lerpPoint(q0, q1, t);
  const r1 = lerpPoint(q1, q2, t);
  const s = lerpPoint(r0, r1, t);

  return [
    [p0, q0, r0, s], // Left segment
    [s, r1, q2, p3], // Right segment
  ];
}

/** Estimate arc length of a cubic bezier segment using chord approximation */
function estimateSegmentLength(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  samples: number = 10,
): number {
  let length = 0;
  let prev = p0;

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const curr = cubicBezierPoint(p0, p1, p2, p3, t);
    length += distance(prev, curr);
    prev = curr;
  }

  return length;
}

// ============================================================================
// PATH ANALYSIS
// ============================================================================

/** Get segment control points from a path */
function getSegmentControlPoints(
  path: BezierPath,
  segmentIndex: number,
): { p0: Point2D; p1: Point2D; p2: Point2D; p3: Point2D } {
  const v0 = path.vertices[segmentIndex];
  const v1 = path.vertices[(segmentIndex + 1) % path.vertices.length];

  return {
    p0: v0.point,
    p1: addPoints(v0.point, v0.outHandle),
    p2: addPoints(v1.point, v1.inHandle),
    p3: v1.point,
  };
}

/** Calculate total arc length of a path */
function getPathLength(
  path: BezierPath,
  samplesPerSegment: number = 10,
): number {
  const numSegments = path.closed
    ? path.vertices.length
    : path.vertices.length - 1;
  let totalLength = 0;

  for (let i = 0; i < numSegments; i++) {
    const { p0, p1, p2, p3 } = getSegmentControlPoints(path, i);
    totalLength += estimateSegmentLength(p0, p1, p2, p3, samplesPerSegment);
  }

  return totalLength;
}

/** Calculate arc lengths of each segment */
function getSegmentLengths(
  path: BezierPath,
  samplesPerSegment: number = 10,
): number[] {
  const numSegments = path.closed
    ? path.vertices.length
    : path.vertices.length - 1;
  const lengths: number[] = [];

  for (let i = 0; i < numSegments; i++) {
    const { p0, p1, p2, p3 } = getSegmentControlPoints(path, i);
    lengths.push(estimateSegmentLength(p0, p1, p2, p3, samplesPerSegment));
  }

  return lengths;
}

/** Get point at a specific arc length along the path */
function getPointAtArcLength(
  path: BezierPath,
  targetLength: number,
  segmentLengths: number[],
): { point: Point2D; segmentIndex: number; t: number } {
  let accumulated = 0;

  for (let i = 0; i < segmentLengths.length; i++) {
    const segmentLength = segmentLengths[i];

    if (
      accumulated + segmentLength >= targetLength ||
      i === segmentLengths.length - 1
    ) {
      const localT =
        segmentLength > 0 ? (targetLength - accumulated) / segmentLength : 0;
      const { p0, p1, p2, p3 } = getSegmentControlPoints(path, i);
      const point = cubicBezierPoint(
        p0,
        p1,
        p2,
        p3,
        Math.max(0, Math.min(1, localT)),
      );

      return { point, segmentIndex: i, t: localT };
    }

    accumulated += segmentLength;
  }

  // Fallback: return last point
  const lastVertex = path.vertices[path.vertices.length - 1];
  return {
    point: clonePoint(lastVertex.point),
    segmentIndex: segmentLengths.length - 1,
    t: 1,
  };
}

// ============================================================================
// SUBDIVISION
// ============================================================================

/** Subdivide a path segment at a specific t value */
function subdivideSegmentAt(
  path: BezierPath,
  segmentIndex: number,
  t: number,
): BezierPath {
  const result = clonePath(path);
  const v0 = result.vertices[segmentIndex];
  const nextIdx = (segmentIndex + 1) % result.vertices.length;
  const v1 = result.vertices[nextIdx];

  const p0 = v0.point;
  const p1 = addPoints(v0.point, v0.outHandle);
  const p2 = addPoints(v1.point, v1.inHandle);
  const p3 = v1.point;

  const [left, right] = splitCubicBezier(p0, p1, p2, p3, t);

  // Update v0's out handle
  v0.outHandle = subtractPoints(left[1], left[0]);

  // Create new vertex at split point
  const newVertex: BezierVertex = {
    point: clonePoint(left[3]),
    inHandle: subtractPoints(left[2], left[3]),
    outHandle: subtractPoints(right[1], right[0]),
  };

  // Update v1's in handle
  v1.inHandle = subtractPoints(right[2], right[3]);

  // Insert new vertex
  result.vertices.splice(segmentIndex + 1, 0, newVertex);

  return result;
}

/** Subdivide a path to have a specific number of vertices */
function subdivideToVertexCount(
  path: BezierPath,
  targetCount: number,
): BezierPath {
  if (path.vertices.length >= targetCount) {
    return clonePath(path);
  }

  let current = clonePath(path);
  const segmentLengths = getSegmentLengths(current);
  const _totalLength = segmentLengths.reduce((sum, l) => sum + l, 0);

  // Add vertices evenly distributed by arc length
  while (current.vertices.length < targetCount) {
    // Find longest segment
    const currentLengths = getSegmentLengths(current);
    let maxLength = 0;
    let maxIndex = 0;

    for (let i = 0; i < currentLengths.length; i++) {
      if (currentLengths[i] > maxLength) {
        maxLength = currentLengths[i];
        maxIndex = i;
      }
    }

    // Subdivide at midpoint
    current = subdivideSegmentAt(current, maxIndex, 0.5);
  }

  return current;
}

/** Resample a path with evenly spaced vertices */
function resamplePath(path: BezierPath, vertexCount: number): BezierPath {
  if (vertexCount < 2) {
    return clonePath(path);
  }

  const segmentLengths = getSegmentLengths(path);
  const totalLength = segmentLengths.reduce((sum, l) => sum + l, 0);

  if (totalLength === 0) {
    // Degenerate path - just clone vertices
    const vertices: BezierVertex[] = [];
    for (let i = 0; i < vertexCount; i++) {
      const srcIdx = Math.floor((i * path.vertices.length) / vertexCount);
      vertices.push(cloneVertex(path.vertices[srcIdx]));
    }
    return { vertices, closed: path.closed };
  }

  const spacing = totalLength / (path.closed ? vertexCount : vertexCount - 1);
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < vertexCount; i++) {
    const targetLength = i * spacing;
    const { point } = getPointAtArcLength(path, targetLength, segmentLengths);

    // Calculate tangent for handles (simplified - use nearby points)
    const prevLength = Math.max(0, targetLength - spacing * 0.33);
    const nextLength = Math.min(totalLength, targetLength + spacing * 0.33);

    const prevPoint = getPointAtArcLength(
      path,
      prevLength,
      segmentLengths,
    ).point;
    const nextPoint = getPointAtArcLength(
      path,
      nextLength,
      segmentLengths,
    ).point;

    const tangent = {
      x: (nextPoint.x - prevPoint.x) * 0.5,
      y: (nextPoint.y - prevPoint.y) * 0.5,
    };

    const handleScale = 0.33; // Typical bezier handle scale

    vertices.push({
      point: clonePoint(point),
      inHandle: scalePoint(tangent, -handleScale),
      outHandle: scalePoint(tangent, handleScale),
    });
  }

  return { vertices, closed: path.closed };
}

// ============================================================================
// CORRESPONDENCE
// ============================================================================

/**
 * Calculate total travel distance for a given rotation offset
 * Lower is better - vertices should move less during morphing
 */
function calculateTravelDistance(
  source: BezierPath,
  target: BezierPath,
  rotationOffset: number = 0,
  reversed: boolean = false,
): number {
  const n = source.vertices.length;
  let total = 0;

  for (let i = 0; i < n; i++) {
    const srcIdx = i;
    let tgtIdx = (i + rotationOffset + n) % n;

    if (reversed) {
      tgtIdx = (n - 1 - i + rotationOffset + n) % n;
    }

    total += distance(
      source.vertices[srcIdx].point,
      target.vertices[tgtIdx].point,
    );
  }

  return total;
}

/**
 * Find optimal rotation offset to minimize travel distance
 */
function findOptimalRotation(
  source: BezierPath,
  target: BezierPath,
): { offset: number; reversed: boolean } {
  const n = source.vertices.length;
  let bestOffset = 0;
  let bestReversed = false;
  let bestDistance = Infinity;

  // Try all rotation offsets
  for (let offset = 0; offset < n; offset++) {
    // Normal direction
    const dist = calculateTravelDistance(source, target, offset, false);
    if (dist < bestDistance) {
      bestDistance = dist;
      bestOffset = offset;
      bestReversed = false;
    }

    // Reversed direction (for closed paths)
    if (source.closed && target.closed) {
      const distRev = calculateTravelDistance(source, target, offset, true);
      if (distRev < bestDistance) {
        bestDistance = distRev;
        bestOffset = offset;
        bestReversed = true;
      }
    }
  }

  return { offset: bestOffset, reversed: bestReversed };
}

/**
 * Rotate and optionally reverse a path's vertices
 */
function rotateVertices(
  path: BezierPath,
  offset: number,
  reverse: boolean = false,
): BezierPath {
  const n = path.vertices.length;
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < n; i++) {
    let srcIdx = (i + offset + n) % n;

    if (reverse) {
      srcIdx = (n - 1 - i + offset + n) % n;
    }

    const srcVertex = path.vertices[srcIdx];

    if (reverse) {
      // Swap in/out handles when reversing
      vertices.push({
        point: clonePoint(srcVertex.point),
        inHandle: clonePoint(srcVertex.outHandle),
        outHandle: clonePoint(srcVertex.inHandle),
      });
    } else {
      vertices.push(cloneVertex(srcVertex));
    }
  }

  return { vertices, closed: path.closed };
}

// ============================================================================
// MAIN API
// ============================================================================

/**
 * Prepare two paths for morphing by matching vertex counts and finding
 * optimal correspondence.
 *
 * @param source Source path (start of morph)
 * @param target Target path (end of morph)
 * @param config Configuration options
 * @returns Prepared paths ready for interpolation
 */
export function prepareMorphPaths(
  source: BezierPath,
  target: BezierPath,
  config: Partial<MorphConfig> = {},
): PreparedMorphPaths {
  const cfg: MorphConfig = { ...DEFAULT_MORPH_CONFIG, ...config };

  // Validate inputs
  if (source.vertices.length === 0 || target.vertices.length === 0) {
    logger.warn("Cannot morph empty paths");
    return {
      source: clonePath(source),
      target: clonePath(target),
      rotationOffset: 0,
      reversed: false,
    };
  }

  let preparedSource = clonePath(source);
  let preparedTarget = clonePath(target);

  // Step 1: Match vertex counts
  const sourceCount = preparedSource.vertices.length;
  const targetCount = preparedTarget.vertices.length;

  if (sourceCount !== targetCount) {
    switch (cfg.pointMatchingStrategy) {
      case "subdivide-shorter":
        if (sourceCount < targetCount) {
          preparedSource = subdivideToVertexCount(preparedSource, targetCount);
        } else {
          preparedTarget = subdivideToVertexCount(preparedTarget, sourceCount);
        }
        break;

      case "subdivide-both": {
        const maxCount = Math.max(sourceCount, targetCount);
        preparedSource = subdivideToVertexCount(preparedSource, maxCount);
        preparedTarget = subdivideToVertexCount(preparedTarget, maxCount);
        break;
      }

      case "resample": {
        const count = cfg.resampleCount ?? Math.max(sourceCount, targetCount);
        preparedSource = resamplePath(preparedSource, count);
        preparedTarget = resamplePath(preparedTarget, count);
        break;
      }
    }
  }

  // Step 2: Find optimal correspondence (for closed paths)
  let rotationOffset = 0;
  let reversed = false;

  if (preparedSource.closed && preparedTarget.closed) {
    switch (cfg.correspondenceMethod) {
      case "nearest-rotation":
      case "nearest-distance": {
        const result = findOptimalRotation(preparedSource, preparedTarget);
        rotationOffset = result.offset;
        reversed = result.reversed;
        break;
      }

      case "manual":
        // Manual mapping would be applied here if provided
        break;
      default:
        // Keep original indices
        break;
    }
  }

  // Apply rotation to target if needed
  if (rotationOffset !== 0 || reversed) {
    preparedTarget = rotateVertices(preparedTarget, rotationOffset, reversed);
  }

  return {
    source: preparedSource,
    target: preparedTarget,
    rotationOffset,
    reversed,
  };
}

/**
 * Interpolate between two prepared paths.
 *
 * IMPORTANT: Paths must have the same vertex count. Use prepareMorphPaths()
 * first if they don't.
 *
 * @param source Source path (t=0)
 * @param target Target path (t=1)
 * @param t Interpolation factor (0-1)
 * @returns Interpolated path
 */
export function morphPaths(
  source: BezierPath,
  target: BezierPath,
  t: number,
): BezierPath {
  // Clamp t to valid range
  t = Math.max(0, Math.min(1, t));

  // Handle edge cases
  if (t === 0) return clonePath(source);
  if (t === 1) return clonePath(target);

  // Validate vertex counts match
  if (source.vertices.length !== target.vertices.length) {
    logger.warn(
      "Paths have different vertex counts - use prepareMorphPaths() first",
    );
    // Fall back to direct interpolation of first path's length
    const count = Math.min(source.vertices.length, target.vertices.length);
    source = {
      vertices: source.vertices.slice(0, count),
      closed: source.closed,
    };
    target = {
      vertices: target.vertices.slice(0, count),
      closed: target.closed,
    };
  }

  // Interpolate each vertex
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < source.vertices.length; i++) {
    const srcV = source.vertices[i];
    const tgtV = target.vertices[i];

    vertices.push({
      point: lerpPoint(srcV.point, tgtV.point, t),
      inHandle: lerpPoint(srcV.inHandle, tgtV.inHandle, t),
      outHandle: lerpPoint(srcV.outHandle, tgtV.outHandle, t),
    });
  }

  // Use source's closed state (should be same as target's)
  return { vertices, closed: source.closed };
}

/**
 * Convenience function to morph between two arbitrary paths.
 * Combines preparation and interpolation.
 *
 * @param source Source path
 * @param target Target path
 * @param t Interpolation factor (0-1)
 * @param config Configuration options
 * @returns Interpolated path
 */
export function morphPathsAuto(
  source: BezierPath,
  target: BezierPath,
  t: number,
  config: Partial<MorphConfig> = {},
): BezierPath {
  const { source: prepSource, target: prepTarget } = prepareMorphPaths(
    source,
    target,
    config,
  );
  return morphPaths(prepSource, prepTarget, t);
}

/**
 * Calculate the optimal correspondence between two paths without
 * modifying them. Useful for previewing the morph.
 *
 * @param source Source path
 * @param target Target path
 * @returns Array of index pairs showing which vertices correspond
 */
export function getCorrespondence(
  source: BezierPath,
  target: BezierPath,
): Array<{ sourceIndex: number; targetIndex: number }> {
  // First prepare paths
  const {
    source: prepSource,
    target: prepTarget,
    rotationOffset,
    reversed,
  } = prepareMorphPaths(source, target);

  const n = prepSource.vertices.length;
  const correspondence: Array<{ sourceIndex: number; targetIndex: number }> =
    [];

  for (let i = 0; i < n; i++) {
    let targetIdx = i;

    // Reverse the rotation/reversal to show original indices
    if (reversed) {
      targetIdx = (n - 1 - i - rotationOffset + 2 * n) % n;
    } else {
      targetIdx = (i - rotationOffset + n) % n;
    }

    correspondence.push({
      sourceIndex: Math.min(i, source.vertices.length - 1),
      targetIndex: Math.min(targetIdx, target.vertices.length - 1),
    });
  }

  return correspondence;
}

// ============================================================================
// TYPE GUARD
// ============================================================================

/**
 * Check if a value is a BezierPath
 * Used for type-safe path morphing in interpolation
 */
export function isBezierPath(value: unknown): value is BezierPath {
  if (typeof value !== "object" || value === null) {
    return false;
  }

  const obj = value as Record<string, unknown>;

  // Must have 'vertices' array and 'closed' boolean
  if (!Array.isArray(obj.vertices) || typeof obj.closed !== "boolean") {
    return false;
  }

  // Check first vertex structure (if any vertices exist)
  if (obj.vertices.length > 0) {
    const v = obj.vertices[0] as Record<string, unknown>;
    if (typeof v !== "object" || v === null) return false;
    if (typeof (v.point as any)?.x !== "number") return false;
    if (typeof (v.point as any)?.y !== "number") return false;
  }

  return true;
}

// ============================================================================
// EXPORTS
// ============================================================================

export const PathMorphing = {
  prepareMorphPaths,
  morphPaths,
  morphPathsAuto,
  getCorrespondence,
  isBezierPath,
  // Utilities
  getPathLength,
  resamplePath,
  subdivideToVertexCount,
};

export default PathMorphing;
