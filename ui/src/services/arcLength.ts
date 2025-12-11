/**
 * Arc Length Parameterization for Bezier Curves
 *
 * Bezier.js does NOT have a built-in arc-length to t conversion.
 * This class builds a lookup table for efficient distance -> parameter mapping.
 */
import * as BezierModule from 'bezier-js';
import type BezierType from 'bezier-js';
const Bezier = (BezierModule as any).default || BezierModule;
type Bezier = BezierType;

interface ArcLengthEntry {
  t: number;
  length: number;
}

interface PointOnPath {
  point: { x: number; y: number };
  tangent: { x: number; y: number };
  t: number;
}

export class ArcLengthParameterizer {
  private curve: Bezier;
  private lut: ArcLengthEntry[];
  public totalLength: number;

  /**
   * @param curve - Bezier.js curve instance
   * @param resolution - Number of samples for LUT (higher = more accurate)
   */
  constructor(curve: Bezier, resolution: number = 1000) {
    this.curve = curve;
    this.lut = [];
    this.totalLength = 0;

    this.buildLUT(resolution);
  }

  /**
   * Build the arc length lookup table
   */
  private buildLUT(resolution: number): void {
    let accumulatedLength = 0;
    let prevPoint = this.curve.get(0);

    for (let i = 0; i <= resolution; i++) {
      const t = i / resolution;
      const point = this.curve.get(t);

      if (i > 0) {
        const dx = point.x - prevPoint.x;
        const dy = point.y - prevPoint.y;
        accumulatedLength += Math.sqrt(dx * dx + dy * dy);
      }

      this.lut.push({
        t: t,
        length: accumulatedLength
      });

      prevPoint = point;
    }

    this.totalLength = accumulatedLength;
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

    // Binary search in LUT
    let low = 0;
    let high = this.lut.length - 1;

    while (low < high) {
      const mid = Math.floor((low + high) / 2);

      if (this.lut[mid].length < distance) {
        low = mid + 1;
      } else {
        high = mid;
      }
    }

    // Linear interpolation between LUT entries for precision
    const entry = this.lut[low];
    const prevEntry = this.lut[Math.max(0, low - 1)];

    if (entry.length === prevEntry.length) {
      return entry.t;
    }

    const ratio = (distance - prevEntry.length) / (entry.length - prevEntry.length);
    return prevEntry.t + ratio * (entry.t - prevEntry.t);
  }

  /**
   * Get point and tangent at arc length distance
   */
  getPointAtDistance(distance: number): PointOnPath {
    const t = this.distanceToT(distance);

    return {
      point: this.curve.get(t),
      tangent: this.curve.derivative(t),
      t: t
    };
  }

  /**
   * Get evenly spaced points along the curve
   *
   * @param count - Number of points
   * @returns Array of points with position and tangent
   */
  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];
    const spacing = this.totalLength / (count - 1);

    for (let i = 0; i < count; i++) {
      const distance = i * spacing;
      points.push(this.getPointAtDistance(distance));
    }

    return points;
  }
}

/**
 * Convert Fabric.js path commands to Bezier.js curves
 */
export function fabricPathToBezier(pathCommands: any[]): Bezier | null {
  if (!pathCommands || pathCommands.length < 2) {
    return null;
  }

  let startPoint: { x: number; y: number } | null = null;

  for (const cmd of pathCommands) {
    const [command, ...coords] = cmd;

    if (command === 'M') {
      startPoint = { x: coords[0], y: coords[1] };
    } else if (command === 'C' && startPoint) {
      // Cubic bezier: startPoint, control1, control2, endPoint
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point 1
        coords[2], coords[3],  // control point 2
        coords[4], coords[5]   // end point
      );
    } else if (command === 'Q' && startPoint) {
      // Quadratic bezier
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point
        coords[2], coords[3]   // end point
      );
    }
  }

  return null;
}

/**
 * Convert an array of control points to a series of Bezier curves
 */
export function controlPointsToBeziers(controlPoints: Array<{
  x: number;
  y: number;
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
}>): Bezier[] {
  const beziers: Bezier[] = [];

  for (let i = 0; i < controlPoints.length - 1; i++) {
    const p1 = controlPoints[i];
    const p2 = controlPoints[i + 1];

    const h1 = p1.handleOut || { x: p1.x, y: p1.y };
    const h2 = p2.handleIn || { x: p2.x, y: p2.y };

    beziers.push(new Bezier(
      p1.x, p1.y,
      h1.x, h1.y,
      h2.x, h2.y,
      p2.x, p2.y
    ));
  }

  return beziers;
}

/**
 * Create a multi-segment arc length parameterizer for paths with multiple curves
 */
export class MultiSegmentParameterizer {
  private parameterizers: ArcLengthParameterizer[];
  private segmentLengths: number[];
  public totalLength: number;

  constructor(beziers: Bezier[], resolution: number = 500) {
    this.parameterizers = beziers.map(b => new ArcLengthParameterizer(b, resolution));
    this.segmentLengths = this.parameterizers.map(p => p.totalLength);
    this.totalLength = this.segmentLengths.reduce((a, b) => a + b, 0);
  }

  getPointAtDistance(distance: number): PointOnPath {
    if (distance <= 0) {
      return this.parameterizers[0].getPointAtDistance(0);
    }
    if (distance >= this.totalLength) {
      const last = this.parameterizers[this.parameterizers.length - 1];
      return last.getPointAtDistance(last.totalLength);
    }

    // Find which segment this distance falls into
    let accumulatedLength = 0;
    for (let i = 0; i < this.parameterizers.length; i++) {
      const segmentLength = this.segmentLengths[i];
      if (accumulatedLength + segmentLength >= distance) {
        const localDistance = distance - accumulatedLength;
        return this.parameterizers[i].getPointAtDistance(localDistance);
      }
      accumulatedLength += segmentLength;
    }

    // Fallback to last point
    const last = this.parameterizers[this.parameterizers.length - 1];
    return last.getPointAtDistance(last.totalLength);
  }

  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];
    const spacing = this.totalLength / (count - 1);

    for (let i = 0; i < count; i++) {
      const distance = i * spacing;
      points.push(this.getPointAtDistance(distance));
    }

    return points;
  }
}

export default ArcLengthParameterizer;
