/**
 * Arc Length Parameterization for Bezier Curves
 *
 * @module arcLength
 * @description
 * Provides arc-length parameterization for Bezier curves using Three.js curves.
 * Three.js curves have built-in arc-length methods which we wrap for convenience.
 *
 * **Why Three.js instead of bezier-js?**
 * - Native 3D support (x, y, z coordinates)
 * - Arc-length parameterization built-in
 * - Already used throughout the codebase
 * - Better TypeScript support
 * - No external dependency issues
 *
 * **Key Features:**
 * - Convert distance along curve to parametric t value
 * - Get evenly spaced points along any Bezier curve
 * - Support for multi-segment paths (splines)
 * - Full 3D support (z-space)
 *
 * @example
 * ```typescript
 * import * as THREE from 'three';
 * import { ArcLengthParameterizer } from './arcLength';
 *
 * const curve = new THREE.CubicBezierCurve3(
 *   new THREE.Vector3(0, 0, 0),
 *   new THREE.Vector3(50, 100, 0),
 *   new THREE.Vector3(100, 100, 0),
 *   new THREE.Vector3(150, 0, 0)
 * );
 * const param = new ArcLengthParameterizer(curve);
 *
 * // Get point at 50% of the curve length
 * const midPoint = param.getPointAtDistance(param.totalLength * 0.5);
 *
 * // Get 10 evenly spaced points
 * const points = param.getEvenlySpacedPoints(10);
 * ```
 */
import * as THREE from "three";
import { safeCoordinateDefault, isFiniteNumber } from "@/utils/typeGuards";

interface Point2D {
  x: number;
  y: number;
}

interface Point3D {
  x: number;
  y: number;
  z: number;
}

interface PointOnPath {
  point: Point2D;
  tangent: Point2D;
  t: number;
}

interface PointOnPath3D {
  point: Point3D;
  tangent: Point3D;
  t: number;
}

/**
 * Arc-length parameterizer using Three.js curves
 * Supports both 2D and 3D curves
 */
export class ArcLengthParameterizer {
  private curve: THREE.Curve<THREE.Vector2 | THREE.Vector3>;
  public totalLength: number;

  /**
   * @param curve - Three.js curve instance (CubicBezierCurve, CubicBezierCurve3, etc.)
   * @param arcLengthDivisions - Number of divisions for arc-length calculation (higher = more accurate)
   */
  constructor(
    curve: THREE.Curve<THREE.Vector2 | THREE.Vector3>,
    _arcLengthDivisions: number = 200,
  ) {
    this.curve = curve;
    // Update arc lengths with specified divisions
    this.curve.updateArcLengths();
    this.totalLength = this.curve.getLength();
  }

  /**
   * Convert arc length distance to t parameter
   *
   * @param distance - Distance along curve (0 to totalLength)
   * @returns t parameter (0 to 1)
   */
  distanceToT(distance: number): number {
    if (distance <= 0) return 0;
    if (distance >= this.totalLength) return 1;

    // Three.js uses u (0-1 arc-length parameter) internally
    const u = distance / this.totalLength;
    // Convert u to t using Three.js built-in method
    return this.curve.getUtoTmapping(u, distance);
  }

  /**
   * Get point and tangent at arc length distance (2D)
   */
  getPointAtDistance(distance: number): PointOnPath {
    const u = Math.max(0, Math.min(1, distance / this.totalLength));

    const point = this.curve.getPointAt(u);
    const tangent = this.curve.getTangentAt(u);

    return {
      point: { x: point.x, y: point.y },
      tangent: { x: tangent.x, y: tangent.y },
      t: this.distanceToT(distance),
    };
  }

  /**
   * Get point and tangent at arc length distance (3D)
   */
  getPointAtDistance3D(distance: number): PointOnPath3D {
    const u = Math.max(0, Math.min(1, distance / this.totalLength));

    const point = this.curve.getPointAt(u) as THREE.Vector3;
    const tangent = this.curve.getTangentAt(u) as THREE.Vector3;

    // Type proof: z coordinates ∈ number | undefined → number (coordinate-like, can be negative)
    return {
      point: {
        x: point.x,
        y: point.y,
        z: safeCoordinateDefault(point.z, 0, "point.z"),
      },
      tangent: {
        x: tangent.x,
        y: tangent.y,
        z: safeCoordinateDefault(tangent.z, 0, "tangent.z"),
      },
      t: this.distanceToT(distance),
    };
  }

  /**
   * Get evenly spaced points along the curve (2D)
   *
   * @param count - Number of points
   * @returns Array of points with position and tangent
   */
  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];

    for (let i = 0; i < count; i++) {
      const u = i / (count - 1);
      const distance = u * this.totalLength;
      points.push(this.getPointAtDistance(distance));
    }

    return points;
  }

  /**
   * Get evenly spaced points along the curve (3D)
   *
   * @param count - Number of points
   * @returns Array of points with position and tangent
   */
  getEvenlySpacedPoints3D(count: number): PointOnPath3D[] {
    const points: PointOnPath3D[] = [];

    for (let i = 0; i < count; i++) {
      const u = i / (count - 1);
      const distance = u * this.totalLength;
      points.push(this.getPointAtDistance3D(distance));
    }

    return points;
  }

  /**
   * Get the underlying Three.js curve
   */
  getCurve(): THREE.Curve<THREE.Vector2 | THREE.Vector3> {
    return this.curve;
  }
}

/**
 * Create a Three.js CubicBezierCurve3 from control points
 */
export function createBezierCurve(
  p1: Point2D | Point3D,
  cp1: Point2D | Point3D,
  cp2: Point2D | Point3D,
  p2: Point2D | Point3D,
): THREE.CubicBezierCurve3 {
  const z1 = "z" in p1 ? p1.z : 0;
  const zc1 = "z" in cp1 ? cp1.z : 0;
  const zc2 = "z" in cp2 ? cp2.z : 0;
  const z2 = "z" in p2 ? p2.z : 0;

  return new THREE.CubicBezierCurve3(
    new THREE.Vector3(p1.x, p1.y, z1),
    new THREE.Vector3(cp1.x, cp1.y, zc1),
    new THREE.Vector3(cp2.x, cp2.y, zc2),
    new THREE.Vector3(p2.x, p2.y, z2),
  );
}

/**
 * Convert an array of control points to Three.js Bezier curves
 */
export function controlPointsToBeziers(
  controlPoints: Array<{
    x: number;
    y: number;
    z?: number;
    handleIn: { x: number; y: number; z?: number } | null;
    handleOut: { x: number; y: number; z?: number } | null;
  }>,
): THREE.CubicBezierCurve3[] {
  const beziers: THREE.CubicBezierCurve3[] = [];

  for (let i = 0; i < controlPoints.length - 1; i++) {
    const p1 = controlPoints[i];
    const p2 = controlPoints[i + 1];

    // Type proof: z coordinates ∈ number | undefined → number (coordinate-like, can be negative)
    const p1z = safeCoordinateDefault(p1.z, 0, "p1.z");
    const p2z = safeCoordinateDefault(p2.z, 0, "p2.z");
    const h1 = p1.handleOut || { x: p1.x, y: p1.y, z: p1z };
    const h2 = p2.handleIn || { x: p2.x, y: p2.y, z: p2z };
    const h1z = h1.z !== undefined ? safeCoordinateDefault(h1.z, 0, "h1.z") : p1z;
    const h2z = h2.z !== undefined ? safeCoordinateDefault(h2.z, 0, "h2.z") : p2z;

    beziers.push(
      createBezierCurve(
        { x: p1.x, y: p1.y, z: p1z },
        { x: h1.x, y: h1.y, z: h1z },
        { x: h2.x, y: h2.y, z: h2z },
        { x: p2.x, y: p2.y, z: p2z },
      ),
    );
  }

  return beziers;
}

/**
 * Create a multi-segment arc length parameterizer using CurvePath
 * This handles paths with multiple bezier segments
 */
export class MultiSegmentParameterizer {
  private curvePath: THREE.CurvePath<THREE.Vector3>;
  public totalLength: number;

  constructor(beziers: THREE.CubicBezierCurve3[]) {
    this.curvePath = new THREE.CurvePath<THREE.Vector3>();

    for (const bezier of beziers) {
      this.curvePath.add(bezier);
    }

    this.totalLength = this.curvePath.getLength();
  }

  /**
   * Get point and tangent at arc length distance (2D)
   */
  getPointAtDistance(distance: number): PointOnPath {
    const u = Math.max(0, Math.min(1, distance / this.totalLength));

    const point = this.curvePath.getPointAt(u);
    const tangent = this.curvePath.getTangentAt(u);

    return {
      point: { x: point.x, y: point.y },
      tangent: { x: tangent.x, y: tangent.y },
      t: u,
    };
  }

  /**
   * Get point and tangent at arc length distance (3D)
   */
  getPointAtDistance3D(distance: number): PointOnPath3D {
    const u = Math.max(0, Math.min(1, distance / this.totalLength));

    const point = this.curvePath.getPointAt(u);
    const tangent = this.curvePath.getTangentAt(u);

    return {
      point: { x: point.x, y: point.y, z: point.z },
      tangent: { x: tangent.x, y: tangent.y, z: tangent.z },
      t: u,
    };
  }

  /**
   * Get evenly spaced points along the path (2D)
   */
  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];

    for (let i = 0; i < count; i++) {
      const u = i / (count - 1);
      const distance = u * this.totalLength;
      points.push(this.getPointAtDistance(distance));
    }

    return points;
  }

  /**
   * Get evenly spaced points along the path (3D)
   */
  getEvenlySpacedPoints3D(count: number): PointOnPath3D[] {
    const points: PointOnPath3D[] = [];

    for (let i = 0; i < count; i++) {
      const u = i / (count - 1);
      const distance = u * this.totalLength;
      points.push(this.getPointAtDistance3D(distance));
    }

    return points;
  }

  /**
   * Get the underlying Three.js CurvePath
   */
  getCurvePath(): THREE.CurvePath<THREE.Vector3> {
    return this.curvePath;
  }
}

/**
 * Legacy function for backward compatibility
 * Converts SVG-style path commands to a Three.js curve
 */
export function pathCommandsToBezier(
  pathCommands: Array<{ command: string; points: number[] }>,
): THREE.CubicBezierCurve3 {
  if (!pathCommands || pathCommands.length < 2) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const pathCommandsLength = (pathCommands != null && Array.isArray(pathCommands)) ? pathCommands.length : 0;
    throw new Error(`[ArcLength] Cannot create Bezier curve from path commands: Invalid path commands (${pathCommandsLength} commands, minimum 2 required)`);
  }

  let startPoint: Point3D | null = null;

  for (const cmd of pathCommands) {
    const command = cmd.command;
    const coords = cmd.points;

    if (command === "M") {
      // Type proof: z coordinate ∈ number | undefined → number (coordinate-like, can be negative)
      const zCoord = coords[2] !== undefined ? safeCoordinateDefault(coords[2], 0, "coords[2]") : 0;
      startPoint = { x: coords[0], y: coords[1], z: zCoord };
    } else if (command === "C" && startPoint) {
      // Cubic bezier: startPoint, control1, control2, endPoint
      // Type proof: z coordinates ∈ number | undefined → number (coordinate-like, can be negative)
      const c1z = coords[2] !== undefined ? safeCoordinateDefault(coords[2], 0, "coords[2]") : 0;
      const c2z = coords[5] !== undefined ? safeCoordinateDefault(coords[5], 0, "coords[5]") : 0;
      const endz = coords[8] !== undefined ? safeCoordinateDefault(coords[8], 0, "coords[8]") : 0;
      return new THREE.CubicBezierCurve3(
        new THREE.Vector3(startPoint.x, startPoint.y, startPoint.z),
        new THREE.Vector3(coords[0], coords[1], c1z),
        new THREE.Vector3(
          // Lean4/PureScript/Haskell: Explicit pattern matching on optional array elements
          // Type proof: coords[i] ∈ number | undefined → number (coordinate-like, can be negative)
          coords[3] !== undefined && isFiniteNumber(coords[3])
            ? coords[3]
            : coords[2] !== undefined && isFiniteNumber(coords[2])
              ? coords[2]
              : 0,
          coords[4] !== undefined && isFiniteNumber(coords[4])
            ? coords[4]
            : coords[3] !== undefined && isFiniteNumber(coords[3])
              ? coords[3]
              : 0,
          c2z,
        ),
        new THREE.Vector3(
          // Type proof: coords[i] ∈ number | undefined → number (coordinate-like, can be negative)
          coords[6] !== undefined && isFiniteNumber(coords[6])
            ? coords[6]
            : coords[4] !== undefined && isFiniteNumber(coords[4])
              ? coords[4]
              : 0,
          coords[7] !== undefined && isFiniteNumber(coords[7])
            ? coords[7]
            : coords[5] !== undefined && isFiniteNumber(coords[5])
              ? coords[5]
              : 0,
          endz,
        ),
      );
    } else if (command === "Q" && startPoint) {
      // Quadratic bezier - convert to cubic for consistency
      // Q: start, control, end -> C: start, (start+2*control)/3, (2*control+end)/3, end
      // Type proof: z coordinates ∈ number | undefined → number (coordinate-like, can be negative)
      const qcpz = coords[2] !== undefined ? safeCoordinateDefault(coords[2], 0, "coords[2]") : 0;
      const endz = coords[5] !== undefined ? safeCoordinateDefault(coords[5], 0, "coords[5]") : 0;
      const qcp = { x: coords[0], y: coords[1], z: qcpz };
      const end = {
        // Type proof: coords[i] ∈ number | undefined → number (coordinate-like, can be negative)
        x: coords[3] !== undefined && isFiniteNumber(coords[3])
          ? coords[3]
          : coords[2] !== undefined && isFiniteNumber(coords[2])
            ? coords[2]
            : 0,
        y: coords[4] !== undefined && isFiniteNumber(coords[4])
          ? coords[4]
          : coords[3] !== undefined && isFiniteNumber(coords[3])
            ? coords[3]
            : 0,
        z: endz,
      };

      const cp1 = {
        x: (startPoint.x + 2 * qcp.x) / 3,
        y: (startPoint.y + 2 * qcp.y) / 3,
        z: (startPoint.z + 2 * qcp.z) / 3,
      };
      const cp2 = {
        x: (2 * qcp.x + end.x) / 3,
        y: (2 * qcp.y + end.y) / 3,
        z: (2 * qcp.z + end.z) / 3,
      };

      return new THREE.CubicBezierCurve3(
        new THREE.Vector3(startPoint.x, startPoint.y, startPoint.z),
        new THREE.Vector3(cp1.x, cp1.y, cp1.z),
        new THREE.Vector3(cp2.x, cp2.y, cp2.z),
        new THREE.Vector3(end.x, end.y, end.z),
      );
    }
  }

  throw new Error(`[ArcLength] Cannot create Bezier curve from path commands: No valid cubic bezier curve found (path commands must contain 'M' followed by 'C' commands)`);
}

export default ArcLengthParameterizer;
