/**
 * SplineLayer - 3D Spline/Path Layer
 *
 * Renders bezier splines in 3D space. Used for:
 * - Shape paths
 * - Motion paths
 * - Text-on-path
 * - Mask paths
 *
 * ANIMATED SPLINES (Phase 1):
 * - Control point x/y can be AnimatableProperty<number>
 * - onEvaluateFrame() interpolates control points per frame
 * - Curve is rebuilt when control points change
 * - TextLayer can query getEvaluatedControlPoints(frame) for text-on-path
 *
 * DETERMINISM:
 * - All interpolation uses pure functions from interpolation.ts
 * - Same frame + same project = identical curve geometry
 */

import * as THREE from 'three';
import type {
  Layer,
  SplineData,
  ControlPoint,
  AnimatableControlPoint,
  EvaluatedControlPoint,
} from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { interpolateProperty } from '@/services/interpolation';

export class SplineLayer extends BaseLayer {
  /** The line mesh for the spline */
  private lineMesh: THREE.Line | null = null;

  /** The fill mesh (if closed path with fill) */
  private fillMesh: THREE.Mesh | null = null;

  /** Spline data */
  private splineData: SplineData;

  /** Cached curve for path calculations */
  private curve: THREE.CurvePath<THREE.Vector3> | null = null;

  /** Animated control points (if spline is animated) */
  private animatedPoints: AnimatableControlPoint[] | null = null;

  /** Last evaluated frame for cache invalidation */
  private lastEvaluatedFrame: number = -1;

  /** Cached evaluated points for the current frame */
  private cachedEvaluatedPoints: EvaluatedControlPoint[] | null = null;

  /** Hash of last evaluated points for change detection */
  private lastPointsHash: string = '';

  constructor(layerData: Layer) {
    super(layerData);

    // Extract spline data
    this.splineData = this.extractSplineData(layerData);

    // Check for animated control points
    if (this.splineData.animated && this.splineData.animatedControlPoints) {
      this.animatedPoints = this.splineData.animatedControlPoints;
    }

    // Build the spline geometry
    this.buildSpline();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Extract spline data from layer
   */
  private extractSplineData(layerData: Layer): SplineData {
    const data = layerData.data as SplineData | null;

    return {
      controlPoints: data?.controlPoints ?? [],
      closed: data?.closed ?? false,
      stroke: data?.stroke ?? '#00ff00',
      strokeWidth: data?.strokeWidth ?? 2,
      fill: data?.fill ?? '',
      pathData: data?.pathData ?? '',
    };
  }

  /**
   * Build the Three.js spline from control points
   */
  private buildSpline(): void {
    // Clear existing meshes
    this.clearMeshes();

    const points = this.splineData.controlPoints;
    if (points.length < 2) return;

    // Build curve path from control points
    this.curve = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < points.length - 1; i++) {
      const p0 = points[i];
      const p1 = points[i + 1];

      // Use depth for Z position (depth map sampled value)
      const z0 = p0.depth ?? 0;
      const z1 = p1.depth ?? 0;

      // Create bezier curve segment
      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(
          p0.x + (p0.handleOut?.x ?? 0),
          -(p0.y + (p0.handleOut?.y ?? 0)),
          z0
        ),
        new THREE.Vector3(
          p1.x + (p1.handleIn?.x ?? 0),
          -(p1.y + (p1.handleIn?.y ?? 0)),
          z1
        ),
        new THREE.Vector3(p1.x, -p1.y, z1)
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.splineData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      const zLast = lastPoint.depth ?? 0;
      const zFirst = firstPoint.depth ?? 0;

      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(
          lastPoint.x + (lastPoint.handleOut?.x ?? 0),
          -(lastPoint.y + (lastPoint.handleOut?.y ?? 0)),
          zLast
        ),
        new THREE.Vector3(
          firstPoint.x + (firstPoint.handleIn?.x ?? 0),
          -(firstPoint.y + (firstPoint.handleIn?.y ?? 0)),
          zFirst
        ),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst)
      );

      this.curve.add(closingBezier);
    }

    // Create line geometry
    const curvePoints = this.curve.getPoints(points.length * 20);
    const lineGeometry = new THREE.BufferGeometry().setFromPoints(curvePoints);

    const lineMaterial = new THREE.LineBasicMaterial({
      color: this.splineData.stroke,
      linewidth: this.splineData.strokeWidth,
      transparent: true,
    });

    this.lineMesh = new THREE.Line(lineGeometry, lineMaterial);
    this.lineMesh.name = `spline_line_${this.id}`;
    this.group.add(this.lineMesh);

    // Create fill if specified and path is closed
    if (this.splineData.fill && this.splineData.closed) {
      this.createFill(curvePoints);
    }
  }

  /**
   * Create fill mesh for closed paths
   */
  private createFill(curvePoints: THREE.Vector3[]): void {
    if (curvePoints.length < 3) return;

    // Create shape from points (project to XY plane)
    const shape = new THREE.Shape();
    shape.moveTo(curvePoints[0].x, curvePoints[0].y);

    for (let i = 1; i < curvePoints.length; i++) {
      shape.lineTo(curvePoints[i].x, curvePoints[i].y);
    }

    shape.closePath();

    const fillGeometry = new THREE.ShapeGeometry(shape);
    const fillMaterial = new THREE.MeshBasicMaterial({
      color: this.splineData.fill,
      transparent: true,
      side: THREE.DoubleSide,
      depthWrite: false,
    });

    this.fillMesh = new THREE.Mesh(fillGeometry, fillMaterial);
    this.fillMesh.name = `spline_fill_${this.id}`;
    this.fillMesh.position.z = -0.1; // Slightly behind stroke
    this.group.add(this.fillMesh);
  }

  /**
   * Clear existing meshes
   */
  private clearMeshes(): void {
    if (this.lineMesh) {
      this.group.remove(this.lineMesh);
      this.lineMesh.geometry.dispose();
      (this.lineMesh.material as THREE.Material).dispose();
      this.lineMesh = null;
    }

    if (this.fillMesh) {
      this.group.remove(this.fillMesh);
      this.fillMesh.geometry.dispose();
      (this.fillMesh.material as THREE.Material).dispose();
      this.fillMesh = null;
    }

    this.curve = null;
  }

  // ============================================================================
  // PATH UTILITIES
  // ============================================================================

  /**
   * Get a point on the path at parameter t (0-1)
   */
  getPointAt(t: number): THREE.Vector3 | null {
    if (!this.curve) return null;
    return this.curve.getPointAt(Math.max(0, Math.min(1, t)));
  }

  /**
   * Get the tangent at parameter t (0-1)
   */
  getTangentAt(t: number): THREE.Vector3 | null {
    if (!this.curve) return null;
    return this.curve.getTangentAt(Math.max(0, Math.min(1, t)));
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
  getTransformAt(t: number): { position: THREE.Vector3; rotation: number } | null {
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

  // ============================================================================
  // PROPERTY SETTERS
  // ============================================================================

  /**
   * Set stroke color
   */
  setStroke(color: string): void {
    this.splineData.stroke = color;
    if (this.lineMesh) {
      (this.lineMesh.material as THREE.LineBasicMaterial).color.set(color);
    }
  }

  /**
   * Set stroke width
   */
  setStrokeWidth(width: number): void {
    this.splineData.strokeWidth = width;
    if (this.lineMesh) {
      (this.lineMesh.material as THREE.LineBasicMaterial).linewidth = width;
    }
  }

  /**
   * Set fill color
   */
  setFill(color: string): void {
    this.splineData.fill = color;
    if (this.fillMesh) {
      (this.fillMesh.material as THREE.MeshBasicMaterial).color.set(color);
    } else if (color && this.splineData.closed && this.curve) {
      // Create fill if it doesn't exist
      const curvePoints = this.curve.getPoints(this.splineData.controlPoints.length * 20);
      this.createFill(curvePoints);
    }
  }

  /**
   * Update control points (static)
   */
  setControlPoints(points: ControlPoint[]): void {
    this.splineData.controlPoints = points;
    // Clear animated points when setting static points
    this.animatedPoints = null;
    this.splineData.animated = false;
    this.buildSpline();
  }

  /**
   * Set animated control points
   * Enables animation mode for this spline
   */
  setAnimatedControlPoints(points: AnimatableControlPoint[]): void {
    this.animatedPoints = points;
    this.splineData.animatedControlPoints = points;
    this.splineData.animated = true;
    // Clear cache to force re-evaluation
    this.lastEvaluatedFrame = -1;
    this.cachedEvaluatedPoints = null;
    this.lastPointsHash = '';
  }

  /**
   * Enable animation on this spline by converting static control points
   * to AnimatableControlPoint format
   */
  enableAnimation(): AnimatableControlPoint[] {
    if (this.animatedPoints) {
      return this.animatedPoints;
    }

    // Import the conversion function dynamically to avoid circular deps
    const { controlPointToAnimatable } = require('@/types/project');

    // Convert static points to animated
    const animatedPoints = this.splineData.controlPoints.map(
      (cp: ControlPoint) => controlPointToAnimatable(cp)
    );

    this.setAnimatedControlPoints(animatedPoints);
    return animatedPoints;
  }

  /**
   * Disable animation and convert back to static control points
   */
  disableAnimation(): void {
    if (!this.animatedPoints) return;

    const { animatableToControlPoint } = require('@/types/project');

    // Convert animated points back to static using current values
    this.splineData.controlPoints = this.animatedPoints.map(
      (acp: AnimatableControlPoint) => animatableToControlPoint(acp)
    );

    this.animatedPoints = null;
    this.splineData.animatedControlPoints = undefined;
    this.splineData.animated = false;
    this.lastEvaluatedFrame = -1;
    this.cachedEvaluatedPoints = null;
    this.lastPointsHash = '';

    this.buildSpline();
  }

  /**
   * Set closed state
   */
  setClosed(closed: boolean): void {
    if (this.splineData.closed === closed) return;
    this.splineData.closed = closed;
    this.buildSpline();
  }

  /**
   * Check if the spline path is closed
   */
  isClosed(): boolean {
    return this.splineData.closed;
  }

  // ============================================================================
  // ANIMATED SPLINE EVALUATION
  // ============================================================================

  /**
   * Check if this spline has animated control points
   */
  isAnimated(): boolean {
    return this.animatedPoints !== null && this.animatedPoints.length > 0;
  }

  /**
   * Evaluate a single animated control point at a specific frame
   * PURE FUNCTION - uses interpolateProperty from interpolation.ts
   */
  private evaluateControlPointAtFrame(
    acp: AnimatableControlPoint,
    frame: number
  ): EvaluatedControlPoint {
    return {
      id: acp.id,
      x: interpolateProperty(acp.x, frame),
      y: interpolateProperty(acp.y, frame),
      depth: acp.depth ? interpolateProperty(acp.depth, frame) : 0,
      handleIn: acp.handleIn ? {
        x: interpolateProperty(acp.handleIn.x, frame),
        y: interpolateProperty(acp.handleIn.y, frame),
      } : null,
      handleOut: acp.handleOut ? {
        x: interpolateProperty(acp.handleOut.x, frame),
        y: interpolateProperty(acp.handleOut.y, frame),
      } : null,
      type: acp.type,
    };
  }

  /**
   * Get evaluated control points at a specific frame
   * PUBLIC API for TextLayer and other consumers
   *
   * For static splines, returns the static control points converted to EvaluatedControlPoint
   * For animated splines, interpolates all control points at the given frame
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
      // Animated spline - interpolate each control point
      points = this.animatedPoints.map(acp =>
        this.evaluateControlPointAtFrame(acp, frame)
      );
    } else {
      // Static spline - convert ControlPoint to EvaluatedControlPoint
      points = this.splineData.controlPoints.map(cp => ({
        id: cp.id,
        x: cp.x,
        y: cp.y,
        depth: cp.depth ?? 0,
        handleIn: cp.handleIn,
        handleOut: cp.handleOut,
        type: cp.type,
      }));
    }

    // Cache the result
    this.lastEvaluatedFrame = frame;
    this.cachedEvaluatedPoints = points;

    return points;
  }

  /**
   * Compute a hash of control point positions for change detection
   * Used to avoid rebuilding geometry when positions haven't changed
   */
  private computePointsHash(points: EvaluatedControlPoint[]): string {
    // Simple hash using position values (sufficient for change detection)
    return points.map(p =>
      `${p.x.toFixed(2)},${p.y.toFixed(2)},${p.depth.toFixed(2)}`
    ).join('|');
  }

  /**
   * Build spline geometry from evaluated control points
   * Called when control points change during animation
   */
  private buildSplineFromEvaluatedPoints(points: EvaluatedControlPoint[]): void {
    // Clear existing meshes
    this.clearMeshes();

    if (points.length < 2) return;

    // Build curve path from evaluated points
    this.curve = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < points.length - 1; i++) {
      const p0 = points[i];
      const p1 = points[i + 1];

      // Use depth for Z position
      const z0 = p0.depth;
      const z1 = p1.depth;

      // Create bezier curve segment
      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(
          p0.x + (p0.handleOut?.x ?? 0),
          -(p0.y + (p0.handleOut?.y ?? 0)),
          z0
        ),
        new THREE.Vector3(
          p1.x + (p1.handleIn?.x ?? 0),
          -(p1.y + (p1.handleIn?.y ?? 0)),
          z1
        ),
        new THREE.Vector3(p1.x, -p1.y, z1)
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.splineData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      const zLast = lastPoint.depth;
      const zFirst = firstPoint.depth;

      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(
          lastPoint.x + (lastPoint.handleOut?.x ?? 0),
          -(lastPoint.y + (lastPoint.handleOut?.y ?? 0)),
          zLast
        ),
        new THREE.Vector3(
          firstPoint.x + (firstPoint.handleIn?.x ?? 0),
          -(firstPoint.y + (firstPoint.handleIn?.y ?? 0)),
          zFirst
        ),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst)
      );

      this.curve.add(closingBezier);
    }

    // Create line geometry
    const curvePoints = this.curve.getPoints(points.length * 20);
    const lineGeometry = new THREE.BufferGeometry().setFromPoints(curvePoints);

    const lineMaterial = new THREE.LineBasicMaterial({
      color: this.splineData.stroke,
      linewidth: this.splineData.strokeWidth,
      transparent: true,
    });

    this.lineMesh = new THREE.Line(lineGeometry, lineMaterial);
    this.lineMesh.name = `spline_line_${this.id}`;
    this.group.add(this.lineMesh);

    // Create fill if specified and path is closed
    if (this.splineData.fill && this.splineData.closed) {
      this.createFill(curvePoints);
    }
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Skip if not animated - static splines don't change
    if (!this.isAnimated()) {
      return;
    }

    // Evaluate control points at this frame
    const evaluatedPoints = this.getEvaluatedControlPoints(frame);

    // Compute hash to detect changes
    const pointsHash = this.computePointsHash(evaluatedPoints);

    // Only rebuild if points have actually changed
    if (pointsHash !== this.lastPointsHash) {
      this.buildSplineFromEvaluatedPoints(evaluatedPoints);
      this.lastPointsHash = pointsHash;
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as SplineData | undefined;

    if (data) {
      let needsRebuild = false;

      // Handle animated control points
      if (data.animatedControlPoints !== undefined) {
        this.setAnimatedControlPoints(data.animatedControlPoints);
        needsRebuild = false; // setAnimatedControlPoints handles rebuild
      } else if (data.controlPoints !== undefined) {
        this.splineData.controlPoints = data.controlPoints;
        // Clear animated if static points are being set
        if (!data.animated) {
          this.animatedPoints = null;
          this.splineData.animated = false;
        }
        needsRebuild = true;
      }

      // Handle animated flag toggle
      if (data.animated !== undefined) {
        if (data.animated && !this.animatedPoints) {
          this.enableAnimation();
          needsRebuild = false;
        } else if (!data.animated && this.animatedPoints) {
          this.disableAnimation();
          needsRebuild = false;
        }
      }

      if (data.closed !== undefined && data.closed !== this.splineData.closed) {
        this.splineData.closed = data.closed;
        needsRebuild = true;
      }

      if (data.stroke !== undefined) {
        this.setStroke(data.stroke);
      }

      if (data.strokeWidth !== undefined) {
        this.setStrokeWidth(data.strokeWidth);
      }

      if (data.fill !== undefined) {
        this.setFill(data.fill);
      }

      if (needsRebuild) {
        this.buildSpline();
      }
    }
  }

  protected onDispose(): void {
    this.clearMeshes();
  }
}
