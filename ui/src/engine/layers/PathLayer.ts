/**
 * PathLayer - Motion Path Layer (Invisible Guide)
 *
 * A path layer for motion guides that other layers can reference:
 * - Text-on-path: TextLayer references PathLayer for text positioning
 * - Camera paths: CameraLayer can follow a PathLayer trajectory
 * - Particle emitters: Particles can emit along a PathLayer
 *
 * Unlike SplineLayer (which renders visible shapes with stroke/fill),
 * PathLayer only shows a dashed guide line in the editor and is
 * invisible at render time.
 *
 * DETERMINISM:
 * - All interpolation uses pure functions from interpolation.ts
 * - Same frame + same project = identical path geometry
 */

import * as THREE from "three";
import { Line2 } from "three/examples/jsm/lines/Line2.js";
import { LineGeometry } from "three/examples/jsm/lines/LineGeometry.js";
import { LineMaterial } from "three/examples/jsm/lines/LineMaterial.js";
import { interpolateProperty } from "@/services/interpolation";
import type {
  AnimatableControlPoint,
  ControlPoint,
  EvaluatedControlPoint,
  Layer,
  PathLayerData,
} from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export class PathLayer extends BaseLayer {
  /** The dashed guide line mesh */
  private guideLine: Line2 | null = null;

  /** Canvas resolution for LineMaterial */
  private resolution: THREE.Vector2 = new THREE.Vector2(1920, 1080);

  /** Path data */
  private pathData: PathLayerData;

  /** Cached curve for path calculations */
  private curve: THREE.CurvePath<THREE.Vector3> | null = null;

  /** Animated control points (if path is animated) */
  private animatedPoints: AnimatableControlPoint[] | null = null;

  /** Last evaluated frame for cache invalidation */
  private lastEvaluatedFrame: number = -1;

  /** Cached evaluated points for the current frame */
  private cachedEvaluatedPoints: EvaluatedControlPoint[] | null = null;

  /** Hash of last evaluated points for change detection */
  private lastPointsHash: string = "";

  constructor(layerData: Layer) {
    super(layerData);

    // Extract path data
    this.pathData = this.extractPathData(layerData);

    // Check for animated control points
    if (this.pathData.animated && this.pathData.animatedControlPoints) {
      this.animatedPoints = this.pathData.animatedControlPoints;
    }

    // Build the path geometry
    this.buildPath();

    // Apply initial blend mode (though paths are typically not blended)
    this.initializeBlendMode();
  }

  /**
   * Extract path layer data from layer object
   */
  private extractPathData(layerData: Layer): PathLayerData {
    const data = layerData.data as PathLayerData | null;

    return {
      controlPoints: data?.controlPoints ?? [],
      closed: data?.closed ?? false,
      pathData: data?.pathData ?? "",
      showGuide: data?.showGuide ?? true,
      guideColor: data?.guideColor ?? "#00FFFF",
      guideDashPattern: data?.guideDashPattern ?? [10, 5],
      animatedControlPoints: data?.animatedControlPoints,
      animated: data?.animated,
    };
  }

  /**
   * Build the Three.js path from control points
   */
  private buildPath(): void {
    // Clear existing guide line
    this.clearGuideLine();

    const points = this.pathData.controlPoints;
    if (points.length < 2) return;

    // Build curve path from control points
    this.curve = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < points.length - 1; i++) {
      const p0 = points[i];
      const p1 = points[i + 1];

      // Use depth for Z position (if available)
      const z0 = p0.depth ?? 0;
      const z1 = p1.depth ?? 0;

      // Create bezier curve segment
      // Handles are stored as ABSOLUTE positions
      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(
          p0.handleOut?.x ?? p0.x,
          -(p0.handleOut?.y ?? p0.y),
          z0,
        ),
        new THREE.Vector3(
          p1.handleIn?.x ?? p1.x,
          -(p1.handleIn?.y ?? p1.y),
          z1,
        ),
        new THREE.Vector3(p1.x, -p1.y, z1),
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.pathData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      const zLast = lastPoint.depth ?? 0;
      const zFirst = firstPoint.depth ?? 0;

      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(
          lastPoint.handleOut?.x ?? lastPoint.x,
          -(lastPoint.handleOut?.y ?? lastPoint.y),
          zLast,
        ),
        new THREE.Vector3(
          firstPoint.handleIn?.x ?? firstPoint.x,
          -(firstPoint.handleIn?.y ?? firstPoint.y),
          zFirst,
        ),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst),
      );

      this.curve.add(closingBezier);
    }

    // Create dashed guide line if guide is visible
    if (this.pathData.showGuide) {
      this.createGuideLine();
    }
  }

  /**
   * Create the dashed guide line visualization
   */
  private createGuideLine(): void {
    if (!this.curve) return;

    // Get points along the curve
    const points = this.pathData.controlPoints;
    const curvePoints = this.curve.getPoints(points.length * 20);

    // Convert to flat position array for LineGeometry
    const positions: number[] = [];
    for (const pt of curvePoints) {
      positions.push(pt.x, pt.y, pt.z);
    }

    const lineGeometry = new LineGeometry();
    lineGeometry.setPositions(positions);

    // Parse guide color
    const color = new THREE.Color(this.pathData.guideColor);

    // Create dashed line material
    const lineMaterial = new LineMaterial({
      color: color.getHex(),
      linewidth: 2,
      transparent: true,
      opacity: 0.7,
      resolution: this.resolution,
      worldUnits: false,
      dashed: true,
      dashSize: this.pathData.guideDashPattern[0],
      gapSize: this.pathData.guideDashPattern[1],
    });

    this.guideLine = new Line2(lineGeometry, lineMaterial);
    this.guideLine.computeLineDistances();
    this.guideLine.name = `path_guide_${this.id}`;

    // Guide lines should be visible in editor but not in final render
    // The render pass can filter these out by checking userData.isGuide
    this.guideLine.userData.isGuide = true;
    this.guideLine.userData.layerId = this.id;

    this.group.add(this.guideLine);
  }

  /**
   * Clear existing guide line
   */
  private clearGuideLine(): void {
    if (this.guideLine) {
      this.group.remove(this.guideLine);
      this.guideLine.geometry.dispose();
      (this.guideLine.material as THREE.Material).dispose();
      this.guideLine = null;
    }
    this.curve = null;
  }

  // ============================================================================
  // PATH UTILITIES (Used by TextLayer, CameraLayer, ParticleLayer)
  // ============================================================================

  /**
   * Get a point on the path at parameter t (0-1)
   */
  getPointAt(t: number): THREE.Vector3 | null {
    if (!this.curve) return null;
    // Validate t (NaN bypasses Math.max/min clamp)
    const validT = Number.isFinite(t) ? Math.max(0, Math.min(1, t)) : 0;
    return this.curve.getPointAt(validT);
  }

  /**
   * Get the tangent at parameter t (0-1)
   */
  getTangentAt(t: number): THREE.Vector3 | null {
    if (!this.curve) return null;
    // Validate t (NaN bypasses Math.max/min clamp)
    const validT = Number.isFinite(t) ? Math.max(0, Math.min(1, t)) : 0;
    return this.curve.getTangentAt(validT);
  }

  /**
   * Get the total length of the path
   */
  getLength(): number {
    if (!this.curve) return 0;
    return this.curve.getLength();
  }

  /**
   * Get point and rotation for placing objects along path
   */
  getTransformAt(
    t: number,
  ): { position: THREE.Vector3; rotation: number } | null {
    const point = this.getPointAt(t);
    const tangent = this.getTangentAt(t);

    if (!point || !tangent) return null;

    // Calculate rotation from tangent
    const rotation = Math.atan2(tangent.y, tangent.x) * (180 / Math.PI);

    return { position: point, rotation };
  }

  /**
   * Get the underlying curve for advanced operations
   */
  getCurve(): THREE.CurvePath<THREE.Vector3> | null {
    return this.curve;
  }

  /**
   * Check if the path is closed
   */
  isClosed(): boolean {
    return this.pathData.closed;
  }

  // ============================================================================
  // EVALUATED CONTROL POINTS API
  // ============================================================================

  /**
   * Check if this path has animated control points
   */
  isAnimated(): boolean {
    return this.animatedPoints !== null && this.animatedPoints.length > 0;
  }

  /**
   * Get evaluated control points at a specific frame
   * PUBLIC API for TextLayer, CameraLayer, and other consumers
   *
   * DETERMINISM: Same frame = same output (pure function)
   */
  getEvaluatedControlPoints(frame: number): EvaluatedControlPoint[] {
    // Use cached result if same frame
    if (frame === this.lastEvaluatedFrame && this.cachedEvaluatedPoints) {
      return this.cachedEvaluatedPoints;
    }

    let points: EvaluatedControlPoint[];

    if (this.animatedPoints && this.animatedPoints.length > 0) {
      // Animated path - interpolate each control point
      points = this.animatedPoints.map((acp) =>
        this.evaluateControlPointAtFrame(acp, frame),
      );
    } else {
      // Static path - convert ControlPoint to EvaluatedControlPoint
      points = this.pathData.controlPoints.map((cp) => ({
        id: cp.id,
        x: cp.x,
        y: cp.y,
        depth: cp.depth ?? 0,
        handleIn: cp.handleIn,
        handleOut: cp.handleOut,
        type: cp.type,
        group: cp.group,
      }));
    }

    // Cache the result
    this.lastEvaluatedFrame = frame;
    this.cachedEvaluatedPoints = points;

    return points;
  }

  /**
   * Evaluate a single animated control point at a specific frame
   */
  private evaluateControlPointAtFrame(
    acp: AnimatableControlPoint,
    frame: number,
  ): EvaluatedControlPoint {
    // Use composition fps for correct animation timing (not hardcoded 30fps)
    const fps = this.compositionFps;
    const layerId = this.id;

    return {
      id: acp.id,
      x: interpolateProperty(acp.x, frame, fps, layerId),
      y: interpolateProperty(acp.y, frame, fps, layerId),
      depth: acp.depth
        ? interpolateProperty(acp.depth, frame, fps, layerId)
        : 0,
      handleIn: acp.handleIn
        ? {
            x: interpolateProperty(acp.handleIn.x, frame, fps, layerId),
            y: interpolateProperty(acp.handleIn.y, frame, fps, layerId),
          }
        : null,
      handleOut: acp.handleOut
        ? {
            x: interpolateProperty(acp.handleOut.x, frame, fps, layerId),
            y: interpolateProperty(acp.handleOut.y, frame, fps, layerId),
          }
        : null,
      type: acp.type,
      group: acp.group,
    };
  }

  /**
   * Compute a hash of control point positions for change detection
   */
  private computePointsHash(points: EvaluatedControlPoint[]): string {
    return points
      .map((p) => `${p.x.toFixed(2)},${p.y.toFixed(2)},${p.depth.toFixed(2)}`)
      .join("|");
  }

  // ============================================================================
  // PROPERTY SETTERS
  // ============================================================================

  /**
   * Set guide visibility
   */
  setShowGuide(show: boolean): void {
    if (this.pathData.showGuide === show) return;

    this.pathData.showGuide = show;

    if (show && !this.guideLine && this.curve) {
      this.createGuideLine();
    } else if (!show && this.guideLine) {
      this.group.remove(this.guideLine);
      this.guideLine.geometry.dispose();
      (this.guideLine.material as THREE.Material).dispose();
      this.guideLine = null;
    }
  }

  /**
   * Set guide color
   */
  setGuideColor(color: string): void {
    this.pathData.guideColor = color;
    if (this.guideLine) {
      (this.guideLine.material as LineMaterial).color.set(color);
    }
  }

  /**
   * Set guide dash pattern [dash, gap]
   */
  setGuideDashPattern(pattern: [number, number]): void {
    this.pathData.guideDashPattern = pattern;
    if (this.guideLine) {
      const mat = this.guideLine.material as LineMaterial;
      mat.dashSize = pattern[0];
      mat.gapSize = pattern[1];
      mat.needsUpdate = true;
      this.guideLine.computeLineDistances();
    }
  }

  /**
   * Set resolution for line material (call when canvas resizes)
   */
  setResolution(width: number, height: number): void {
    // Validate dimensions (NaN would corrupt LineMaterial resolution)
    const validWidth = Number.isFinite(width) && width > 0 ? width : 1920;
    const validHeight = Number.isFinite(height) && height > 0 ? height : 1080;
    this.resolution.set(validWidth, validHeight);
    if (this.guideLine) {
      (this.guideLine.material as LineMaterial).resolution.set(
        validWidth,
        validHeight,
      );
    }
  }

  /**
   * Update control points (static)
   */
  setControlPoints(points: ControlPoint[]): void {
    this.pathData.controlPoints = points;
    this.animatedPoints = null;
    this.pathData.animated = false;
    this.lastEvaluatedFrame = -1;
    this.cachedEvaluatedPoints = null;
    this.buildPath();
  }

  /**
   * Set animated control points
   */
  setAnimatedControlPoints(points: AnimatableControlPoint[]): void {
    this.animatedPoints = points;
    this.pathData.animatedControlPoints = points;
    this.pathData.animated = true;
    this.lastEvaluatedFrame = -1;
    this.cachedEvaluatedPoints = null;
    this.lastPointsHash = "";
  }

  /**
   * Set closed state
   */
  setClosed(closed: boolean): void {
    if (this.pathData.closed === closed) return;
    this.pathData.closed = closed;
    this.buildPath();
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Skip if not animated
    if (!this.isAnimated()) return;

    // Evaluate control points at this frame
    const evaluatedPoints = this.getEvaluatedControlPoints(frame);
    const pointsHash = this.computePointsHash(evaluatedPoints);

    // Only rebuild if points have changed
    if (pointsHash !== this.lastPointsHash) {
      this.buildPathFromEvaluatedPoints(evaluatedPoints);
      this.lastPointsHash = pointsHash;
    }
  }

  /**
   * Build path geometry from evaluated control points
   */
  private buildPathFromEvaluatedPoints(points: EvaluatedControlPoint[]): void {
    this.clearGuideLine();

    if (points.length < 2) return;

    // Build curve path from evaluated points
    this.curve = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < points.length - 1; i++) {
      const p0 = points[i];
      const p1 = points[i + 1];

      const z0 = p0.depth;
      const z1 = p1.depth;

      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(
          p0.handleOut?.x ?? p0.x,
          -(p0.handleOut?.y ?? p0.y),
          z0,
        ),
        new THREE.Vector3(
          p1.handleIn?.x ?? p1.x,
          -(p1.handleIn?.y ?? p1.y),
          z1,
        ),
        new THREE.Vector3(p1.x, -p1.y, z1),
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.pathData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, lastPoint.depth),
        new THREE.Vector3(
          lastPoint.handleOut?.x ?? lastPoint.x,
          -(lastPoint.handleOut?.y ?? lastPoint.y),
          lastPoint.depth,
        ),
        new THREE.Vector3(
          firstPoint.handleIn?.x ?? firstPoint.x,
          -(firstPoint.handleIn?.y ?? firstPoint.y),
          firstPoint.depth,
        ),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, firstPoint.depth),
      );

      this.curve.add(closingBezier);
    }

    // Create guide line if visible
    if (this.pathData.showGuide) {
      this.createGuideLine();
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply evaluated control points if present
    if (props.controlPoints !== undefined) {
      const points = props.controlPoints as EvaluatedControlPoint[];
      const pointsHash = this.computePointsHash(points);
      if (pointsHash !== this.lastPointsHash) {
        this.buildPathFromEvaluatedPoints(points);
        this.lastPointsHash = pointsHash;
      }
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<PathLayerData> | undefined;

    if (data) {
      let needsRebuild = false;

      // Handle animated control points
      if (data.animatedControlPoints !== undefined) {
        this.setAnimatedControlPoints(data.animatedControlPoints);
      } else if (data.controlPoints !== undefined) {
        this.pathData.controlPoints = data.controlPoints;
        if (!data.animated) {
          this.animatedPoints = null;
          this.pathData.animated = false;
        }
        needsRebuild = true;
      }

      if (data.closed !== undefined && data.closed !== this.pathData.closed) {
        this.pathData.closed = data.closed;
        needsRebuild = true;
      }

      if (data.showGuide !== undefined) {
        this.setShowGuide(data.showGuide);
      }

      if (data.guideColor !== undefined) {
        this.setGuideColor(data.guideColor);
      }

      if (data.guideDashPattern !== undefined) {
        this.setGuideDashPattern(data.guideDashPattern);
      }

      if (needsRebuild) {
        this.buildPath();
      }
    }
  }

  protected onDispose(): void {
    this.clearGuideLine();
  }
}
