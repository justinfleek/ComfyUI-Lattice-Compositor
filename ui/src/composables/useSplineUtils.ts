/**
 * Spline Utilities Composable
 *
 * Math and geometry utilities for spline/bezier curve operations.
 * Includes bezier evaluation, arc-length parameterization, and path finding.
 */

import type { ControlPoint, EvaluatedControlPoint } from "@/types/project";

// ============================================================
// BEZIER CURVE EVALUATION
// ============================================================

/**
 * Evaluate a cubic bezier curve at parameter t
 *
 * @param p0 - Start point
 * @param h0 - Control point 1 (handleOut of start)
 * @param h1 - Control point 2 (handleIn of end)
 * @param p1 - End point
 * @param t - Parameter [0, 1]
 * @returns Point on the curve
 */
export function evaluateBezier(
  p0: { x: number; y: number },
  h0: { x: number; y: number },
  h1: { x: number; y: number },
  p1: { x: number; y: number },
  t: number,
): { x: number; y: number } {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  const t2 = t * t;
  const t3 = t2 * t;

  return {
    x: mt3 * p0.x + 3 * mt2 * t * h0.x + 3 * mt * t2 * h1.x + t3 * p1.x,
    y: mt3 * p0.y + 3 * mt2 * t * h0.y + 3 * mt * t2 * h1.y + t3 * p1.y,
  };
}

/**
 * Evaluate the tangent (derivative) of a cubic bezier curve at parameter t
 *
 * @param p0 - Start point
 * @param h0 - Control point 1
 * @param h1 - Control point 2
 * @param p1 - End point
 * @param t - Parameter [0, 1]
 * @returns Tangent vector at t
 */
export function evaluateBezierTangent(
  p0: { x: number; y: number },
  h0: { x: number; y: number },
  h1: { x: number; y: number },
  p1: { x: number; y: number },
  t: number,
): { x: number; y: number } {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const t2 = t * t;

  return {
    x:
      3 * mt2 * (h0.x - p0.x) +
      6 * mt * t * (h1.x - h0.x) +
      3 * t2 * (p1.x - h1.x),
    y:
      3 * mt2 * (h0.y - p0.y) +
      6 * mt * t * (h1.y - h0.y) +
      3 * t2 * (p1.y - h1.y),
  };
}

/**
 * Calculate approximate arc length of a bezier segment using Gaussian quadrature
 *
 * @param p0 - Start point
 * @param h0 - Control point 1
 * @param h1 - Control point 2
 * @param p1 - End point
 * @param samples - Number of samples (default 10)
 * @returns Approximate arc length
 */
export function bezierArcLength(
  p0: { x: number; y: number },
  h0: { x: number; y: number },
  h1: { x: number; y: number },
  p1: { x: number; y: number },
  samples: number = 10,
): number {
  let length = 0;
  let prev = p0;

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const curr = evaluateBezier(p0, h0, h1, p1, t);
    const dx = curr.x - prev.x;
    const dy = curr.y - prev.y;
    length += Math.sqrt(dx * dx + dy * dy);
    prev = curr;
  }

  return length;
}

// ============================================================
// PATH OPERATIONS
// ============================================================

/**
 * Find the closest point on a bezier path to a given position
 *
 * @param pos - Query position
 * @param controlPoints - Array of control points forming the path
 * @param closed - Whether the path is closed
 * @param threshold - Distance threshold for hit detection (default 20)
 * @returns Closest point info or null if not within threshold
 */
export function findClosestPointOnPath(
  pos: { x: number; y: number },
  controlPoints: (ControlPoint | EvaluatedControlPoint)[],
  closed: boolean = false,
  threshold: number = 20,
): { x: number; y: number; segmentIndex: number; t: number } | null {
  if (controlPoints.length < 2) return null;

  let closest: {
    x: number;
    y: number;
    segmentIndex: number;
    t: number;
    dist: number;
  } | null = null;

  const segmentCount = closed ? controlPoints.length : controlPoints.length - 1;

  for (let i = 0; i < segmentCount; i++) {
    const p0 = controlPoints[i];
    const p1 = controlPoints[(i + 1) % controlPoints.length];

    // Get handle positions (or use point positions if no handles)
    const h0 = p0.handleOut || { x: p0.x, y: p0.y };
    const h1 = p1.handleIn || { x: p1.x, y: p1.y };

    // Sample the bezier curve at multiple points
    for (let t = 0; t <= 1; t += 0.02) {
      const pt = evaluateBezier(p0, h0, h1, p1, t);
      const dist = Math.sqrt((pos.x - pt.x) ** 2 + (pos.y - pt.y) ** 2);

      if (!closest || dist < closest.dist) {
        closest = { x: pt.x, y: pt.y, segmentIndex: i, t, dist };
      }
    }
  }

  // Only return if within threshold
  if (closest && closest.dist < threshold) {
    return {
      x: closest.x,
      y: closest.y,
      segmentIndex: closest.segmentIndex,
      t: closest.t,
    };
  }
  return null;
}

/**
 * Find control point at a given position
 *
 * @param pos - Query position
 * @param controlPoints - Array of control points
 * @param threshold - Hit detection radius (default 10)
 * @returns The point if found, null otherwise
 */
export function findPointAtPosition<
  T extends ControlPoint | EvaluatedControlPoint,
>(
  pos: { x: number; y: number },
  controlPoints: T[],
  threshold: number = 10,
): T | null {
  for (const point of controlPoints) {
    const dist = Math.sqrt((pos.x - point.x) ** 2 + (pos.y - point.y) ** 2);
    if (dist < threshold) {
      return point;
    }
  }
  return null;
}

// ============================================================
// SVG PATH GENERATION
// ============================================================

/**
 * Generate SVG path data for a spline
 *
 * @param controlPoints - Array of control points
 * @param closed - Whether the path is closed
 * @returns SVG path 'd' attribute string
 */
export function generateSplinePath(
  controlPoints: (ControlPoint | EvaluatedControlPoint)[],
  closed: boolean = false,
): string {
  if (controlPoints.length === 0) return "";
  if (controlPoints.length === 1) {
    return `M ${controlPoints[0].x},${controlPoints[0].y}`;
  }

  let d = `M ${controlPoints[0].x},${controlPoints[0].y}`;

  const segmentCount = closed ? controlPoints.length : controlPoints.length - 1;

  for (let i = 0; i < segmentCount; i++) {
    const p0 = controlPoints[i];
    const p1 = controlPoints[(i + 1) % controlPoints.length];

    const h0 = p0.handleOut || { x: p0.x, y: p0.y };
    const h1 = p1.handleIn || { x: p1.x, y: p1.y };

    d += ` C ${h0.x},${h0.y} ${h1.x},${h1.y} ${p1.x},${p1.y}`;
  }

  if (closed) {
    d += " Z";
  }

  return d;
}

/**
 * Generate a preview curve SVG path from previous point to new point
 *
 * @param prevPoint - Previous control point
 * @param newPoint - New point position
 * @param dragPos - Current drag position (defines handle direction)
 * @returns SVG path 'd' attribute string
 */
export function generateCurvePreview(
  prevPoint: ControlPoint | EvaluatedControlPoint,
  newPoint: { x: number; y: number },
  dragPos: { x: number; y: number },
): string {
  // Calculate the handle offset from the drag
  const dx = dragPos.x - newPoint.x;
  const dy = dragPos.y - newPoint.y;

  // h1 = handleOut of prevPoint (how curve LEAVES prevPoint)
  let h1x: number, h1y: number;
  if (prevPoint.handleOut) {
    h1x = prevPoint.handleOut.x;
    h1y = prevPoint.handleOut.y;
  } else {
    // Default: 1/3 of the way toward newPoint
    const dirX = newPoint.x - prevPoint.x;
    const dirY = newPoint.y - prevPoint.y;
    h1x = prevPoint.x + dirX * 0.33;
    h1y = prevPoint.y + dirY * 0.33;
  }

  // h2 = handleIn of newPoint (MIRROR of drag direction)
  const h2x = newPoint.x - dx;
  const h2y = newPoint.y - dy;

  return `M ${prevPoint.x},${prevPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${newPoint.x},${newPoint.y}`;
}

// ============================================================
// COORDINATE TRANSFORMATION
// ============================================================

export interface LayerTransformValues {
  position: { x: number; y: number };
  rotation: number;
  scale: { x: number; y: number };
  anchorPoint: { x: number; y: number };
}

/**
 * Transform a point from layer space to composition space
 *
 * @param point - Point in layer coordinates
 * @param transform - Layer transform values
 * @returns Point in composition coordinates
 */
export function transformPointToComp(
  point: { x: number; y: number },
  transform: LayerTransformValues,
): { x: number; y: number } {
  const { position, rotation, scale, anchorPoint } = transform;

  // Step 1: Subtract anchor point (move anchor to origin)
  let x = point.x - anchorPoint.x;
  let y = point.y - anchorPoint.y;

  // Step 2: Apply scale (convert from percentage)
  x *= scale.x / 100;
  y *= scale.y / 100;

  // Step 3: Apply rotation (convert degrees to radians)
  const rad = (rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  // Step 4: Add position (move to composition location)
  return {
    x: rx + position.x,
    y: ry + position.y,
  };
}

/**
 * Transform a point from composition space to layer space (inverse)
 *
 * @param point - Point in composition coordinates
 * @param transform - Layer transform values
 * @returns Point in layer coordinates
 */
export function transformPointToLayer(
  point: { x: number; y: number },
  transform: LayerTransformValues,
): { x: number; y: number } {
  const { position, rotation, scale, anchorPoint } = transform;

  // Step 1: Subtract position
  let x = point.x - position.x;
  let y = point.y - position.y;

  // Step 2: Inverse rotation (negative angle)
  const rad = (-rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  // Step 3: Inverse scale
  x = rx / (scale.x / 100);
  y = ry / (scale.y / 100);

  // Step 4: Add anchor point back
  return {
    x: x + anchorPoint.x,
    y: y + anchorPoint.y,
  };
}

// ============================================================
// PATH SMOOTHING
// ============================================================

/**
 * Smooth control point handles to create a more natural curve
 * Uses Catmull-Rom interpolation to calculate handle positions
 *
 * @param points - Array of control points
 * @param index - Index of point to smooth
 * @param tension - Tension factor (0 = straight, 1 = sharp, 0.3-0.5 = natural)
 * @returns Handle positions { handleIn, handleOut }
 */
export function calculateSmoothHandles(
  points: (ControlPoint | EvaluatedControlPoint)[],
  index: number,
  tension: number = 0.3,
): { handleIn: { x: number; y: number }; handleOut: { x: number; y: number } } {
  const point = points[index];
  const prev = points[index - 1] ?? points[points.length - 1]; // Wrap for closed paths
  const next = points[(index + 1) % points.length];

  // Direction from previous to next point
  const dx = next.x - prev.x;
  const dy = next.y - prev.y;

  // Handle length based on distance to neighbors
  const distToPrev = Math.sqrt(
    (point.x - prev.x) ** 2 + (point.y - prev.y) ** 2,
  );
  const distToNext = Math.sqrt(
    (next.x - point.x) ** 2 + (next.y - point.y) ** 2,
  );

  const handleLenIn = distToPrev * tension;
  const handleLenOut = distToNext * tension;

  // Normalize direction
  const len = Math.sqrt(dx * dx + dy * dy);
  const nx = len > 0 ? dx / len : 0;
  const ny = len > 0 ? dy / len : 0;

  return {
    handleIn: {
      x: point.x - nx * handleLenIn,
      y: point.y - ny * handleLenIn,
    },
    handleOut: {
      x: point.x + nx * handleLenOut,
      y: point.y + ny * handleLenOut,
    },
  };
}

/**
 * Simplify a path using Ramer-Douglas-Peucker algorithm
 *
 * @param points - Array of points
 * @param tolerance - Maximum distance for point removal
 * @returns Simplified array of points
 */
export function simplifyPath<T extends { x: number; y: number }>(
  points: T[],
  tolerance: number,
): T[] {
  if (points.length <= 2) return points;

  // Find the point with the maximum distance from the line between first and last
  let maxDist = 0;
  let maxIndex = 0;

  const first = points[0];
  const last = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDistance(points[i], first, last);
    if (dist > maxDist) {
      maxDist = dist;
      maxIndex = i;
    }
  }

  // If max distance is greater than tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = simplifyPath(points.slice(0, maxIndex + 1), tolerance);
    const right = simplifyPath(points.slice(maxIndex), tolerance);

    // Combine, avoiding duplicate middle point
    return [...left.slice(0, -1), ...right];
  } else {
    // All points are within tolerance, return just endpoints
    return [first, last];
  }
}

/**
 * Calculate perpendicular distance from a point to a line
 */
function perpendicularDistance(
  point: { x: number; y: number },
  lineStart: { x: number; y: number },
  lineEnd: { x: number; y: number },
): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const len = Math.sqrt(dx * dx + dy * dy);

  if (len === 0) {
    return Math.sqrt(
      (point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2,
    );
  }

  const t = Math.max(
    0,
    Math.min(
      1,
      ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) /
        (len * len),
    ),
  );

  const projX = lineStart.x + t * dx;
  const projY = lineStart.y + t * dy;

  return Math.sqrt((point.x - projX) ** 2 + (point.y - projY) ** 2);
}

// ============================================================
// COMPOSABLE EXPORT
// ============================================================

export function useSplineUtils() {
  return {
    // Bezier evaluation
    evaluateBezier,
    evaluateBezierTangent,
    bezierArcLength,

    // Path operations
    findClosestPointOnPath,
    findPointAtPosition,

    // SVG generation
    generateSplinePath,
    generateCurvePreview,

    // Coordinate transformation
    transformPointToComp,
    transformPointToLayer,

    // Path smoothing/simplification
    calculateSmoothHandles,
    simplifyPath,
  };
}
