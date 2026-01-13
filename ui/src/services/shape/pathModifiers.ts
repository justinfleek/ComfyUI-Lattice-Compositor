/**
 * Path Modifier Effects
 *
 * Functions that apply visual transformations to bezier paths:
 * - Pucker/Bloat - Move points toward/away from centroid
 * - Wiggle - Add random displacement
 * - Zig-Zag - Create zigzag pattern
 * - Roughen - Add random roughness
 * - Wave - Apply sinusoidal deformation
 * - Twist - Rotate around center
 *
 * Extracted from shapeOperations.ts for modularity.
 */

import type {
  BezierPath,
  BezierVertex,
  Point2D,
  WigglePointType,
  ZigZagPointType,
} from "@/types/shapes";
import { SeededRandom } from "../particleSystem";

// ============================================================================
// LOCAL UTILITY IMPORTS
// These functions are defined here to avoid circular dependencies
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

/** Normalize a point to unit length */
function normalize(p: Point2D): Point2D {
  const len = Math.sqrt(p.x * p.x + p.y * p.y);
  if (len < 0.0001) return { x: 0, y: 0 };
  return { x: p.x / len, y: p.y / len };
}

/** Get perpendicular vector */
function perpendicular(p: Point2D): Point2D {
  return { x: -p.y, y: p.x };
}

/** Rotate point around center */
function rotateAround(p: Point2D, center: Point2D, angle: number): Point2D {
  const cos = Math.cos(angle);
  const sin = Math.sin(angle);
  const dx = p.x - center.x;
  const dy = p.y - center.y;
  return {
    x: center.x + dx * cos - dy * sin,
    y: center.y + dx * sin + dy * cos,
  };
}

/** Evaluate cubic bezier at t */
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

/** Evaluate cubic bezier derivative at t */
function cubicBezierDerivative(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number,
): Point2D {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const t2 = t * t;

  return {
    x:
      3 * mt2 * (p1.x - p0.x) +
      6 * mt * t * (p2.x - p1.x) +
      3 * t2 * (p3.x - p2.x),
    y:
      3 * mt2 * (p1.y - p0.y) +
      6 * mt * t * (p2.y - p1.y) +
      3 * t2 * (p3.y - p2.y),
  };
}

/** Split cubic bezier at t */
function splitCubicBezier(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  t: number,
): [Point2D[], Point2D[]] {
  const p01 = { x: p0.x + (p1.x - p0.x) * t, y: p0.y + (p1.y - p0.y) * t };
  const p12 = { x: p1.x + (p2.x - p1.x) * t, y: p1.y + (p2.y - p1.y) * t };
  const p23 = { x: p2.x + (p3.x - p2.x) * t, y: p2.y + (p3.y - p2.y) * t };
  const p012 = {
    x: p01.x + (p12.x - p01.x) * t,
    y: p01.y + (p12.y - p01.y) * t,
  };
  const p123 = {
    x: p12.x + (p23.x - p12.x) * t,
    y: p12.y + (p23.y - p12.y) * t,
  };
  const p0123 = {
    x: p012.x + (p123.x - p012.x) * t,
    y: p012.y + (p123.y - p012.y) * t,
  };

  return [
    [p0, p01, p012, p0123],
    [p0123, p123, p23, p3],
  ];
}

/** Calculate length of cubic bezier segment */
function cubicBezierLength(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  samples: number = 10,
): number {
  let length = 0;
  let prevPoint = p0;

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const point = cubicBezierPoint(p0, p1, p2, p3, t);
    const dx = point.x - prevPoint.x;
    const dy = point.y - prevPoint.y;
    length += Math.sqrt(dx * dx + dy * dy);
    prevPoint = point;
  }

  return length;
}

/** Get total path length */
function getPathLength(path: BezierPath): number {
  let totalLength = 0;
  const numSegments = path.closed
    ? path.vertices.length
    : path.vertices.length - 1;

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

/** Get point and tangent at distance along path */
function getPointAtDistance(
  path: BezierPath,
  targetDistance: number,
  totalLength?: number,
): { point: Point2D; tangent: Point2D } | null {
  if (path.vertices.length < 2) return null;

  const pathLen = totalLength ?? getPathLength(path);
  if (pathLen < 0.001) return null;

  let accumulatedLength = 0;
  const numSegments = path.closed
    ? path.vertices.length
    : path.vertices.length - 1;

  for (let i = 0; i < numSegments; i++) {
    const v0 = path.vertices[i];
    const v1 = path.vertices[(i + 1) % path.vertices.length];

    const p0 = v0.point;
    const p1 = addPoints(v0.point, v0.outHandle);
    const p2 = addPoints(v1.point, v1.inHandle);
    const p3 = v1.point;

    const segmentLength = cubicBezierLength(p0, p1, p2, p3);

    if (accumulatedLength + segmentLength >= targetDistance) {
      const localT = (targetDistance - accumulatedLength) / segmentLength;
      const point = cubicBezierPoint(p0, p1, p2, p3, localT);
      const derivative = cubicBezierDerivative(p0, p1, p2, p3, localT);
      const tangent = normalize(derivative);
      return { point, tangent };
    }

    accumulatedLength += segmentLength;
  }

  // Return last point
  const lastVertex = path.vertices[path.vertices.length - 1];
  const prevVertex = path.vertices[path.vertices.length - 2];
  const derivative = subtractPoints(lastVertex.point, prevVertex.point);
  return {
    point: clonePoint(lastVertex.point),
    tangent: normalize(derivative),
  };
}

/** Get bounding box of a path */
function getPathBounds(path: BezierPath): {
  x: number;
  y: number;
  width: number;
  height: number;
} {
  let minX = Infinity,
    minY = Infinity;
  let maxX = -Infinity,
    maxY = -Infinity;

  for (const v of path.vertices) {
    minX = Math.min(minX, v.point.x);
    minY = Math.min(minY, v.point.y);
    maxX = Math.max(maxX, v.point.x);
    maxY = Math.max(maxY, v.point.y);
  }

  return {
    x: minX,
    y: minY,
    width: maxX - minX,
    height: maxY - minY,
  };
}

// ============================================================================
// PUCKER & BLOAT
// ============================================================================

/**
 * Pucker (negative) or bloat (positive) a path
 * Moves points toward/away from centroid
 */
export function puckerBloat(path: BezierPath, amount: number): BezierPath {
  if (path.vertices.length < 2 || Math.abs(amount) < 0.001) {
    return clonePath(path);
  }

  // Find centroid
  const centroid: Point2D = { x: 0, y: 0 };
  for (const v of path.vertices) {
    centroid.x += v.point.x;
    centroid.y += v.point.y;
  }
  centroid.x /= path.vertices.length;
  centroid.y /= path.vertices.length;

  // Amount is -100 to 100, convert to factor
  const factor = amount / 100;

  const result: BezierVertex[] = path.vertices.map((v) => {
    // Direction from centroid to point
    const dir = subtractPoints(v.point, centroid);
    const dist = Math.sqrt(dir.x * dir.x + dir.y * dir.y);

    if (dist < 0.001) return cloneVertex(v);

    // Move point
    const moveAmount = dist * factor;
    const newPoint = addPoints(v.point, scalePoint(normalize(dir), moveAmount));

    // Adjust handles - bloat makes them larger, pucker smaller
    const handleFactor = 1 + factor * 0.5;

    return {
      point: newPoint,
      inHandle: scalePoint(v.inHandle, handleFactor),
      outHandle: scalePoint(v.outHandle, handleFactor),
    };
  });

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// WIGGLE PATHS
// ============================================================================

/**
 * Subdivide a path to add more vertices
 */
function subdividePath(path: BezierPath, levels: number = 1): BezierPath {
  if (levels <= 0) return clonePath(path);

  let current = clonePath(path);

  for (let level = 0; level < levels; level++) {
    const result: BezierVertex[] = [];
    const numSegments = current.closed
      ? current.vertices.length
      : current.vertices.length - 1;

    for (let i = 0; i < numSegments; i++) {
      const v0 = current.vertices[i];
      const v1 = current.vertices[(i + 1) % current.vertices.length];

      const p0 = v0.point;
      const p1 = addPoints(v0.point, v0.outHandle);
      const p2 = addPoints(v1.point, v1.inHandle);
      const p3 = v1.point;

      // Split at midpoint
      const [left, right] = splitCubicBezier(p0, p1, p2, p3, 0.5);

      // Add start vertex with adjusted handles
      result.push({
        point: left[0],
        inHandle: i === 0 ? v0.inHandle : subtractPoints(left[1], left[0]),
        outHandle: subtractPoints(left[1], left[0]),
      });

      // Add midpoint vertex
      result.push({
        point: left[3],
        inHandle: subtractPoints(left[2], left[3]),
        outHandle: subtractPoints(right[1], right[0]),
      });
    }

    // Add final vertex for open paths
    if (!current.closed) {
      const lastV = current.vertices[current.vertices.length - 1];
      result.push(cloneVertex(lastV));
    }

    current = { vertices: result, closed: current.closed };
  }

  return current;
}

/**
 * Add random wiggle to a path
 */
export function wigglePath(
  path: BezierPath,
  size: number,
  detail: number,
  pointType: WigglePointType,
  correlation: number,
  temporalPhase: number,
  spatialPhase: number,
  seed: number,
): BezierPath {
  if (path.vertices.length < 2 || size < 0.001) {
    return clonePath(path);
  }

  const rng = new SeededRandom(seed);
  // Advance RNG by temporal phase
  for (let i = 0; i < Math.floor(temporalPhase * 100); i++) {
    rng.next();
  }

  const correlationFactor = correlation / 100;
  const result: BezierVertex[] = [];

  // Subdivide path for more detail
  const subdividedPath = subdividePath(path, Math.max(1, Math.floor(detail)));

  let prevOffset = { x: 0, y: 0 };

  for (let i = 0; i < subdividedPath.vertices.length; i++) {
    const v = subdividedPath.vertices[i];

    // Generate random offset
    const angle = rng.next() * Math.PI * 2 + spatialPhase;
    const magnitude = rng.next() * size;

    // Apply correlation (blend with previous offset)
    const newOffset = {
      x: Math.cos(angle) * magnitude,
      y: Math.sin(angle) * magnitude,
    };

    const offset = {
      x:
        prevOffset.x * correlationFactor +
        newOffset.x * (1 - correlationFactor),
      y:
        prevOffset.y * correlationFactor +
        newOffset.y * (1 - correlationFactor),
    };

    prevOffset = offset;

    const newVertex: BezierVertex = {
      point: addPoints(v.point, offset),
      inHandle:
        pointType === "smooth" ? clonePoint(v.inHandle) : { x: 0, y: 0 },
      outHandle:
        pointType === "smooth" ? clonePoint(v.outHandle) : { x: 0, y: 0 },
    };

    result.push(newVertex);
  }

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// ZIG ZAG
// ============================================================================

/**
 * Add zig-zag pattern to a path
 */
export function zigZagPath(
  path: BezierPath,
  size: number,
  ridgesPerSegment: number,
  pointType: ZigZagPointType,
): BezierPath {
  if (path.vertices.length < 2 || size < 0.001 || ridgesPerSegment < 1) {
    return clonePath(path);
  }

  const result: BezierVertex[] = [];
  const totalLength = getPathLength(path);
  const ridgeLength =
    totalLength /
    (ridgesPerSegment * (path.vertices.length - (path.closed ? 0 : 1)));

  let currentDistance = 0;
  let zigDirection = 1;

  while (currentDistance < totalLength) {
    const pointData = getPointAtDistance(path, currentDistance, totalLength);
    if (!pointData) break;

    // Calculate perpendicular offset
    const perp = perpendicular(pointData.tangent);
    const offset = scalePoint(perp, size * zigDirection);

    const vertex: BezierVertex = {
      point: addPoints(pointData.point, offset),
      inHandle:
        pointType === "smooth"
          ? scalePoint(pointData.tangent, -ridgeLength * 0.3)
          : { x: 0, y: 0 },
      outHandle:
        pointType === "smooth"
          ? scalePoint(pointData.tangent, ridgeLength * 0.3)
          : { x: 0, y: 0 },
    };

    result.push(vertex);

    // Move to next point
    currentDistance += ridgeLength;
    zigDirection *= -1;
  }

  // Add final point
  if (result.length > 0 && !path.closed) {
    const lastVertex = path.vertices[path.vertices.length - 1];
    result.push({
      point: clonePoint(lastVertex.point),
      inHandle: { x: 0, y: 0 },
      outHandle: { x: 0, y: 0 },
    });
  }

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// ROUGHEN PATH
// ============================================================================

/**
 * Add random roughness/distortion to a path
 * Similar to Illustrator's Roughen effect
 *
 * @param path - Input bezier path
 * @param size - Maximum displacement amount in pixels
 * @param detail - Number of points per segment (1-10)
 * @param seed - Random seed for deterministic results
 * @param relative - If true, size is relative to path bounds (percentage)
 */
export function roughenPath(
  path: BezierPath,
  size: number,
  detail: number,
  seed: number,
  relative: boolean = false,
): BezierPath {
  if (path.vertices.length < 2 || size < 0.001 || detail < 1) {
    return clonePath(path);
  }

  const rng = new SeededRandom(seed);
  const result: BezierVertex[] = [];

  // Calculate path bounds for relative mode
  let actualSize = size;
  if (relative) {
    const bounds = getPathBounds(path);
    const diagonal = Math.sqrt(
      bounds.width * bounds.width + bounds.height * bounds.height,
    );
    actualSize = (size / 100) * diagonal;
  }

  // Subdivide the path for more detail
  const subdivided = subdividePath(path, Math.max(1, Math.floor(detail)));

  for (const v of subdivided.vertices) {
    // Generate random offset for this vertex
    const angle = rng.next() * Math.PI * 2;
    const magnitude = rng.next() * actualSize;

    const offset: Point2D = {
      x: Math.cos(angle) * magnitude,
      y: Math.sin(angle) * magnitude,
    };

    // Apply offset to point
    const newPoint = addPoints(v.point, offset);

    // Optionally roughen handles too (50% of point roughness)
    const handleRoughness = actualSize * 0.5;
    const handleAngle1 = rng.next() * Math.PI * 2;
    const handleMag1 = rng.next() * handleRoughness;
    const handleAngle2 = rng.next() * Math.PI * 2;
    const handleMag2 = rng.next() * handleRoughness;

    result.push({
      point: newPoint,
      inHandle: addPoints(v.inHandle, {
        x: Math.cos(handleAngle1) * handleMag1,
        y: Math.sin(handleAngle1) * handleMag1,
      }),
      outHandle: addPoints(v.outHandle, {
        x: Math.cos(handleAngle2) * handleMag2,
        y: Math.sin(handleAngle2) * handleMag2,
      }),
    });
  }

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// WAVE PATH
// ============================================================================

export type WaveType = "sine" | "triangle" | "square";

/**
 * Apply a wave deformation along a path
 * Creates a sinusoidal/triangle/square wave pattern perpendicular to the path
 *
 * @param path - Input bezier path
 * @param amplitude - Wave height (perpendicular displacement)
 * @param frequency - Number of waves along the path length
 * @param phase - Phase offset in radians (for animation)
 * @param waveType - Type of wave: sine, triangle, or square
 */
export function wavePath(
  path: BezierPath,
  amplitude: number,
  frequency: number,
  phase: number = 0,
  waveType: WaveType = "sine",
): BezierPath {
  if (path.vertices.length < 2 || amplitude < 0.001 || frequency < 0.1) {
    return clonePath(path);
  }

  const totalLength = getPathLength(path);
  if (totalLength < 0.001) return clonePath(path);

  // Sample the path at regular intervals for wave application
  const samplesPerWave = 16; // Points per wave cycle for smooth curves
  const totalSamples = Math.max(4, Math.ceil(frequency * samplesPerWave));
  const sampleDistance = totalLength / totalSamples;

  const result: BezierVertex[] = [];

  for (let i = 0; i <= totalSamples; i++) {
    const distance = Math.min(i * sampleDistance, totalLength - 0.001);
    const pointData = getPointAtDistance(path, distance, totalLength);
    if (!pointData) continue;

    // Calculate wave position (0 to 1 along path)
    const t = distance / totalLength;
    const waveInput = t * frequency * Math.PI * 2 + phase;

    // Calculate wave value based on type
    let waveValue: number;
    switch (waveType) {
      case "triangle":
        // Triangle wave: linear ramp up and down
        waveValue = Math.abs(((waveInput / Math.PI) % 2) - 1) * 2 - 1;
        break;
      case "square":
        // Square wave: -1 or 1
        waveValue = Math.sin(waveInput) >= 0 ? 1 : -1;
        break;
      default:
        // Sine wave
        waveValue = Math.sin(waveInput);
    }

    // Calculate perpendicular offset
    const perp = perpendicular(pointData.tangent);
    const offset = scalePoint(perp, waveValue * amplitude);

    // Apply offset
    const newPoint = addPoints(pointData.point, offset);

    // Calculate smooth handles along the wave
    const handleLength = sampleDistance * 0.3;
    const inHandle = scalePoint(pointData.tangent, -handleLength);
    const outHandle = scalePoint(pointData.tangent, handleLength);

    result.push({
      point: newPoint,
      inHandle,
      outHandle,
    });
  }

  return { vertices: result, closed: path.closed };
}

// ============================================================================
// TWIST
// ============================================================================

/**
 * Twist a path around a center point
 */
export function twistPath(
  path: BezierPath,
  angle: number,
  center: Point2D,
): BezierPath {
  if (path.vertices.length < 2 || Math.abs(angle) < 0.001) {
    return clonePath(path);
  }

  // Find the bounding box to determine twist falloff
  let minY = Infinity,
    maxY = -Infinity;
  for (const v of path.vertices) {
    minY = Math.min(minY, v.point.y);
    maxY = Math.max(maxY, v.point.y);
  }

  const height = maxY - minY;
  if (height < 0.001) return clonePath(path);

  const angleRad = (angle * Math.PI) / 180;

  const result: BezierVertex[] = path.vertices.map((v) => {
    // Twist amount based on vertical position
    const yNorm = (v.point.y - minY) / height;
    const localAngle = angleRad * yNorm;

    // Rotate point around center
    const rotatedPoint = rotateAround(v.point, center, localAngle);

    // Rotate handles too
    const absInHandle = addPoints(v.point, v.inHandle);
    const absOutHandle = addPoints(v.point, v.outHandle);
    const rotatedIn = rotateAround(absInHandle, center, localAngle);
    const rotatedOut = rotateAround(absOutHandle, center, localAngle);

    return {
      point: rotatedPoint,
      inHandle: subtractPoints(rotatedIn, rotatedPoint),
      outHandle: subtractPoints(rotatedOut, rotatedPoint),
    };
  });

  return { vertices: result, closed: path.closed };
}
