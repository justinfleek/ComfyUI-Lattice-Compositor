/**
 * TextOnPath Service - Arc-Length Parameterized Text Path Animation
 *
 * Professional text-on-path functionality with:
 * - Arc-length parameterization for uniform character spacing
 * - First/Last margin support
 * - Path offset animation (0-100% with keyframe control)
 * - Reverse path direction
 * - Perpendicular to path alignment
 * - Force alignment mode
 * - Multi-segment bezier path support
 */

import * as THREE from "three";
import type { ControlPoint } from "@/types/project";
import { isFiniteNumber } from "@/utils/typeGuards";

// ============================================================================
// TYPES
// ============================================================================

export interface PathPoint {
  position: THREE.Vector3;
  tangent: THREE.Vector3;
  normal: THREE.Vector3;
  t: number; // Parameter 0-1
  distance: number; // Arc length distance from start
}

export interface TextOnPathConfig {
  /** Path layer ID reference */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: pathLayerId ∈ string (empty string = no path, never null)
  pathLayerId: string;

  /** Reverse the path direction */
  reversed: boolean;

  /** Characters are perpendicular to path tangent */
  perpendicularToPath: boolean;

  /** Force alignment to path baseline */
  forceAlignment: boolean;

  /** Margin from path start (pixels) */
  firstMargin: number;

  /** Margin from path end (pixels) */
  lastMargin: number;

  /** Path offset 0-100% - shifts text along path */
  offset: number;

  /** Text alignment on path */
  align: "left" | "center" | "right";
}

export interface CharacterPlacement {
  /** Character index */
  index: number;

  /** World position */
  position: THREE.Vector3;

  /** Rotation in radians (Z rotation for 2D, full euler for 3D) */
  rotation: THREE.Euler;

  /** Scale factor */
  scale: number;

  /** Distance along path */
  pathDistance: number;

  /** Parameter t (0-1) along path */
  pathT: number;

  /** Whether character is visible (within path bounds) */
  visible: boolean;
}

// ============================================================================
// ARC LENGTH LOOKUP TABLE
// ============================================================================

interface ArcLengthEntry {
  t: number;
  distance: number;
  position: THREE.Vector3;
  tangent: THREE.Vector3;
}

class ArcLengthTable {
  private entries: ArcLengthEntry[] = [];
  public totalLength: number = 0;

  constructor(
    private curve: THREE.CurvePath<THREE.Vector3>,
    resolution: number = 500,
  ) {
    this.build(resolution);
  }

  private build(resolution: number): void {
    this.entries = [];
    let accumulatedLength = 0;
    let prevPoint = this.curve.getPointAt(0);

    for (let i = 0; i <= resolution; i++) {
      const t = i / resolution;
      const point = this.curve.getPointAt(t);
      const tangent = this.curve.getTangentAt(t);

      if (i > 0) {
        accumulatedLength += point.distanceTo(prevPoint);
      }

      this.entries.push({
        t,
        distance: accumulatedLength,
        position: point.clone(),
        tangent: tangent.clone().normalize(),
      });

      prevPoint = point;
    }

    this.totalLength = accumulatedLength;
  }

  /**
   * Convert arc length distance to parameter t
   */
  distanceToT(distance: number): number {
    if (distance <= 0) return 0;
    if (distance >= this.totalLength) return 1;

    // Binary search
    let low = 0;
    let high = this.entries.length - 1;

    while (low < high) {
      const mid = Math.floor((low + high) / 2);
      if (this.entries[mid].distance < distance) {
        low = mid + 1;
      } else {
        high = mid;
      }
    }

    // Interpolate between entries
    const entry = this.entries[low];
    const prevEntry = this.entries[Math.max(0, low - 1)];

    if (entry.distance === prevEntry.distance) {
      return entry.t;
    }

    const ratio =
      (distance - prevEntry.distance) / (entry.distance - prevEntry.distance);
    return prevEntry.t + ratio * (entry.t - prevEntry.t);
  }

  /**
   * Get point and tangent at arc length distance
   */
  getPointAtDistance(distance: number): PathPoint {
    const t = this.distanceToT(distance);
    const position = this.curve.getPointAt(t);
    const tangent = this.curve.getTangentAt(t).normalize();

    // Calculate normal (perpendicular in XY plane)
    const normal = new THREE.Vector3(-tangent.y, tangent.x, 0).normalize();

    return {
      position,
      tangent,
      normal,
      t,
      distance,
    };
  }
}

// ============================================================================
// TEXT ON PATH SERVICE
// ============================================================================

export class TextOnPathService {
  private arcLengthTable: ArcLengthTable | null = null;
  private curve: THREE.CurvePath<THREE.Vector3> | null = null;

  /**
   * Set the path from control points
   */
  setPath(controlPoints: ControlPoint[], closed: boolean = false): void {
    if (controlPoints.length < 2) {
      this.curve = null;
      this.arcLengthTable = null;
      return;
    }

    this.curve = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < controlPoints.length - 1; i++) {
      const p0 = controlPoints[i];
      const p1 = controlPoints[i + 1];

      // Type proof: z0 ∈ number | undefined → number
      const z0 = isFiniteNumber(p0.depth) ? p0.depth : 0;
      // Type proof: z1 ∈ number | undefined → number
      const z1 = isFiniteNumber(p1.depth) ? p1.depth : 0;

      // Type proof: handleOut.x ∈ number | undefined → number
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const handleOut0 = (p0 != null && typeof p0 === "object" && "handleOut" in p0 && p0.handleOut != null && typeof p0.handleOut === "object") ? p0.handleOut : undefined;
      const handleOutX0Value = (handleOut0 != null && typeof handleOut0 === "object" && "x" in handleOut0 && typeof handleOut0.x === "number") ? handleOut0.x : undefined;
      const handleOutX0 = isFiniteNumber(handleOutX0Value) ? handleOutX0Value : 0;
      // Type proof: handleOut.y ∈ number | undefined → number
      const handleOutY0Value = (handleOut0 != null && typeof handleOut0 === "object" && "y" in handleOut0 && typeof handleOut0.y === "number") ? handleOut0.y : undefined;
      const handleOutY0 = isFiniteNumber(handleOutY0Value) ? handleOutY0Value : 0;
      // Type proof: handleIn.x ∈ number | undefined → number
      const handleIn1 = (p1 != null && typeof p1 === "object" && "handleIn" in p1 && p1.handleIn != null && typeof p1.handleIn === "object") ? p1.handleIn : undefined;
      const handleInX1Value = (handleIn1 != null && typeof handleIn1 === "object" && "x" in handleIn1 && typeof handleIn1.x === "number") ? handleIn1.x : undefined;
      const handleInX1 = isFiniteNumber(handleInX1Value) ? handleInX1Value : 0;
      // Type proof: handleIn.y ∈ number | undefined → number
      const handleInY1Value = (handleIn1 != null && typeof handleIn1 === "object" && "y" in handleIn1 && typeof handleIn1.y === "number") ? handleIn1.y : undefined;
      const handleInY1 = isFiniteNumber(handleInY1Value) ? handleInY1Value : 0;

      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(p0.x + handleOutX0, -(p0.y + handleOutY0), z0),
        new THREE.Vector3(p1.x + handleInX1, -(p1.y + handleInY1), z1),
        new THREE.Vector3(p1.x, -p1.y, z1),
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (closed && controlPoints.length > 2) {
      const lastPoint = controlPoints[controlPoints.length - 1];
      const firstPoint = controlPoints[0];

      // Type proof: zLast ∈ number | undefined → number
      const zLast = isFiniteNumber(lastPoint.depth) ? lastPoint.depth : 0;
      // Type proof: zFirst ∈ number | undefined → number
      const zFirst = isFiniteNumber(firstPoint.depth) ? firstPoint.depth : 0;

      // Type proof: handleOut.x ∈ number | undefined → number
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const handleOutLast = (lastPoint != null && typeof lastPoint === "object" && "handleOut" in lastPoint && lastPoint.handleOut != null && typeof lastPoint.handleOut === "object") ? lastPoint.handleOut : undefined;
      const handleOutXLastValue = (handleOutLast != null && typeof handleOutLast === "object" && "x" in handleOutLast && typeof handleOutLast.x === "number") ? handleOutLast.x : undefined;
      const handleOutXLast = isFiniteNumber(handleOutXLastValue)
        ? handleOutXLastValue
        : 0;
      // Type proof: handleOut.y ∈ number | undefined → number
      const handleOutYLastValue = (handleOutLast != null && typeof handleOutLast === "object" && "y" in handleOutLast && typeof handleOutLast.y === "number") ? handleOutLast.y : undefined;
      const handleOutYLast = isFiniteNumber(handleOutYLastValue)
        ? handleOutYLastValue
        : 0;
      // Type proof: handleIn.x ∈ number | undefined → number
      const handleInFirst = (firstPoint != null && typeof firstPoint === "object" && "handleIn" in firstPoint && firstPoint.handleIn != null && typeof firstPoint.handleIn === "object") ? firstPoint.handleIn : undefined;
      const handleInXFirstValue = (handleInFirst != null && typeof handleInFirst === "object" && "x" in handleInFirst && typeof handleInFirst.x === "number") ? handleInFirst.x : undefined;
      const handleInXFirst = isFiniteNumber(handleInXFirstValue)
        ? handleInXFirstValue
        : 0;
      // Type proof: handleIn.y ∈ number | undefined → number
      const handleInYFirstValue = (handleInFirst != null && typeof handleInFirst === "object" && "y" in handleInFirst && typeof handleInFirst.y === "number") ? handleInFirst.y : undefined;
      const handleInYFirst = isFiniteNumber(handleInYFirstValue)
        ? handleInYFirstValue
        : 0;

      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(
          lastPoint.x + handleOutXLast,
          -(lastPoint.y + handleOutYLast),
          zLast,
        ),
        new THREE.Vector3(
          firstPoint.x + handleInXFirst,
          -(firstPoint.y + handleInYFirst),
          zFirst,
        ),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst),
      );

      this.curve.add(closingBezier);
    }

    // Build arc length table
    this.arcLengthTable = new ArcLengthTable(this.curve);
  }

  /**
   * Set path from THREE.js CurvePath directly
   */
  setCurve(curve: THREE.CurvePath<THREE.Vector3>): void {
    this.curve = curve;
    this.arcLengthTable = new ArcLengthTable(curve);
  }

  /**
   * Get total path length
   */
  getTotalLength(): number {
    // Type proof: totalLength ∈ number | undefined → number
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const arcLengthTable = this.arcLengthTable;
    const totalLength = (arcLengthTable != null && typeof arcLengthTable === "object" && "totalLength" in arcLengthTable && typeof arcLengthTable.totalLength === "number") ? arcLengthTable.totalLength : undefined;
    return isFiniteNumber(totalLength)
      ? totalLength
      : 0;
  }

  /**
   * Check if path is set
   */
  hasPath(): boolean {
    return this.curve !== null && this.arcLengthTable !== null;
  }

  /**
   * Calculate character placements along the path
   *
   * @param characterWidths - Array of character widths in pixels
   * @param config - Text on path configuration
   * @param tracking - Letter spacing in 1/1000 em
   * @param fontSize - Font size for tracking calculation
   * @returns Array of character placements
   */
  calculatePlacements(
    characterWidths: number[],
    config: TextOnPathConfig,
    tracking: number = 0,
    fontSize: number = 72,
  ): CharacterPlacement[] {
    if (!this.arcLengthTable || characterWidths.length === 0) {
      return [];
    }

    const totalLength = this.arcLengthTable.totalLength;
    const placements: CharacterPlacement[] = [];

    // Calculate total text width
    const trackingPx = (tracking / 1000) * fontSize;
    let totalTextWidth = 0;
    for (let i = 0; i < characterWidths.length; i++) {
      totalTextWidth += characterWidths[i];
      if (i < characterWidths.length - 1) {
        totalTextWidth += trackingPx;
      }
    }

    // Calculate available path length (accounting for margins)
    const availableLength =
      totalLength - config.firstMargin - config.lastMargin;

    // Calculate starting position based on alignment
    let startDistance: number;
    switch (config.align) {
      case "center":
        startDistance =
          config.firstMargin + (availableLength - totalTextWidth) / 2;
        break;
      case "right":
        startDistance = config.firstMargin + availableLength - totalTextWidth;
        break;
      default: // 'left'
        startDistance = config.firstMargin;
    }

    // Apply path offset (0-100% of available length)
    const offsetDistance = (config.offset / 100) * availableLength;
    startDistance += offsetDistance;

    // Handle reversed path
    if (config.reversed) {
      startDistance = totalLength - startDistance - totalTextWidth;
    }

    // Place each character
    let currentDistance = startDistance;

    for (let i = 0; i < characterWidths.length; i++) {
      const charWidth = characterWidths[i];

      // Get center position of character
      const charCenterDistance = currentDistance + charWidth / 2;

      // Check visibility (within path bounds with wrapping)
      let actualDistance = charCenterDistance;
      let visible = true;

      if (actualDistance < 0 || actualDistance > totalLength) {
        // For closed paths, wrap around; for open paths, hide
        if (config.forceAlignment) {
          actualDistance =
            ((actualDistance % totalLength) + totalLength) % totalLength;
        } else {
          visible =
            actualDistance >= -charWidth &&
            actualDistance <= totalLength + charWidth;
          actualDistance = Math.max(0, Math.min(totalLength, actualDistance));
        }
      }

      // Get path point
      const pathPoint = this.arcLengthTable.getPointAtDistance(actualDistance);

      // Calculate rotation
      let rotation: THREE.Euler;
      if (config.perpendicularToPath) {
        // Perpendicular to tangent (baseline along path)
        const angle = Math.atan2(pathPoint.tangent.y, pathPoint.tangent.x);
        rotation = new THREE.Euler(
          0,
          0,
          config.reversed ? angle + Math.PI : angle,
        );
      } else {
        // Upright characters (no rotation)
        rotation = new THREE.Euler(0, 0, 0);
      }

      placements.push({
        index: i,
        position: pathPoint.position.clone(),
        rotation,
        scale: 1,
        pathDistance: actualDistance,
        pathT: pathPoint.t,
        visible,
      });

      // Move to next character position
      currentDistance += charWidth + trackingPx;
    }

    return placements;
  }

  /**
   * Get a point on the path at a specific percentage
   * Useful for positioning anchors or debugging
   */
  getPointAtPercent(percent: number): PathPoint {
    if (!this.arcLengthTable) {
      throw new Error(`[TextOnPath] Cannot get point at ${percent}%: Arc length table not initialized. Call initialize() first.`);
    }

    const distance = (percent / 100) * this.arcLengthTable.totalLength;
    return this.arcLengthTable.getPointAtDistance(distance);
  }

  /**
   * Get evenly spaced points along the path
   * Useful for path visualization
   */
  getEvenlySpacedPoints(count: number): PathPoint[] {
    if (!this.arcLengthTable || count < 2) return [];

    const points: PathPoint[] = [];
    const spacing = this.arcLengthTable.totalLength / (count - 1);

    for (let i = 0; i < count; i++) {
      const distance = i * spacing;
      points.push(this.arcLengthTable.getPointAtDistance(distance));
    }

    return points;
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.curve = null;
    this.arcLengthTable = null;
  }
}

// ============================================================================
// FACTORY FUNCTION
// ============================================================================

/**
 * Create a TextOnPath service instance
 */
export function createTextOnPathService(): TextOnPathService {
  return new TextOnPathService();
}

/**
 * Create default path options config
 */
export function createDefaultPathConfig(): TextOnPathConfig {
  return {
    pathLayerId: "",
    reversed: false,
    perpendicularToPath: true,
    forceAlignment: false,
    firstMargin: 0,
    lastMargin: 0,
    offset: 0,
    align: "left",
  };
}

export default TextOnPathService;
