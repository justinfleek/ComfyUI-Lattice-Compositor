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

import * as THREE from "three";
import { Line2 } from "three/examples/jsm/lines/Line2.js";
import { LineGeometry } from "three/examples/jsm/lines/LineGeometry.js";
import { LineMaterial } from "three/examples/jsm/lines/LineMaterial.js";
import { isFiniteNumber, isNonEmptyString } from "@/utils/typeGuards";
import { interpolateProperty } from "@/services/interpolation";
import { meshWarpDeformation } from "@/services/meshWarpDeformation";
import {
  createSplineControlPointPath,
  isSplineControlPointPath,
} from "@/services/propertyDriver";
import {
  offsetPath,
  roughenPath,
  trimPath,
  type WaveType,
  wavePath,
  wigglePath,
  zigZagPath,
} from "@/services/shapeOperations";
import {
  type LODContext,
  type LODLevel,
  vectorLOD,
} from "@/services/vectorLOD";
import type { WarpPin, WarpPinType } from "@/types/meshWarp";
import type {
  AnimatableControlPoint,
  AnimatableProperty,
  ControlPoint,
  EvaluatedControlPoint,
  Layer,
  SplineData,
  SplinePathEffectInstance,
} from "@/types/project";
import type { BezierPath, BezierVertex, Point2D } from "@/types/shapes";
import { BaseLayer } from "./BaseLayer";

// Backwards compatibility type aliases
type PuppetPin = WarpPin;

export class SplineLayer extends BaseLayer {
  /** The line mesh for the spline (using Line2 for proper width support) */
  private lineMesh: Line2 | null = null;

  /** The fill mesh (if closed path with fill) */
  private fillMesh: THREE.Mesh | null = null;

  /** Canvas resolution for LineMaterial (needed for proper width rendering) */
  private resolution: THREE.Vector2 = new THREE.Vector2(1920, 1080);

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
  private lastPointsHash: string = "";

  /** Trim start property (static or animated) */
  private trimStartProp?: number | AnimatableProperty<number>;

  /** Trim end property (static or animated) */
  private trimEndProp?: number | AnimatableProperty<number>;

  /** Trim offset property (static or animated) */
  private trimOffsetProp?: number | AnimatableProperty<number>;

  /** Path effects to apply */
  private pathEffects?: SplinePathEffectInstance[];

  /** LOD levels for this spline */
  private lodLevels: LODLevel[] = [];

  /** Whether LOD is enabled for this spline */
  private lodEnabled: boolean = false;

  /** Current LOD context (updated during playback) */
  private lodContext: LODContext = {
    zoom: 1,
    isPlaying: false,
    isScrubbing: false,
    targetFPS: 60,
    currentFPS: 60,
    viewport: { x: 0, y: 0, width: 1920, height: 1080 },
  };

  /** Whether warp (mesh warp) deformation is enabled for this spline */
  private warpEnabled: boolean = false;

  /** Warp pins for this spline (stored on layer, mesh managed by service) */
  private warpPins: WarpPin[] = [];
  /** @deprecated Use warpPins instead */
  private get puppetPins(): WarpPin[] {
    return this.warpPins;
  }
  private set puppetPins(val: WarpPin[]) {
    this.warpPins = val;
  }

  constructor(layerData: Layer) {
    super(layerData);

    // Extract spline data
    this.splineData = this.extractSplineData(layerData);

    // Check for animated control points
    if (this.splineData.animated && this.splineData.animatedControlPoints) {
      this.animatedPoints = this.splineData.animatedControlPoints;
    }

    // Extract trim properties
    const data = layerData.data as SplineData | null;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    this.trimStartProp = (data != null && typeof data === "object" && "trimStart" in data && typeof data.trimStart === "number") ? data.trimStart : undefined;
    this.trimEndProp = (data != null && typeof data === "object" && "trimEnd" in data && typeof data.trimEnd === "number") ? data.trimEnd : undefined;
    this.trimOffsetProp = (data != null && typeof data === "object" && "trimOffset" in data && typeof data.trimOffset === "number") ? data.trimOffset : undefined;
    this.pathEffects = (data != null && typeof data === "object" && "pathEffects" in data && Array.isArray(data.pathEffects)) ? data.pathEffects : undefined;

    // Initialize LOD if enabled and path is complex enough
    this.initializeLOD(data);

    // Initialize mesh warp deformation if pins are present
    this.initializeWarp(data);

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

    // Type proofs: all properties with explicit checks
    const controlPoints = data !== null && typeof data === "object" && "controlPoints" in data && Array.isArray(data.controlPoints)
      ? data.controlPoints
      : [];
    const closed = data !== null && typeof data === "object" && "closed" in data && typeof data.closed === "boolean"
      ? data.closed
      : false;
    const stroke = data !== null && typeof data === "object" && "stroke" in data && isNonEmptyString(data.stroke)
      ? data.stroke
      : "#00ff00";
    const strokeWidth = data !== null && typeof data === "object" && "strokeWidth" in data && isFiniteNumber(data.strokeWidth) && data.strokeWidth > 0
      ? data.strokeWidth
      : 2;
    const fill = data !== null && typeof data === "object" && "fill" in data && typeof data.fill === "string"
      ? data.fill
      : "";
    const pathData = data !== null && typeof data === "object" && "pathData" in data && typeof data.pathData === "string"
      ? data.pathData
      : "";

    return {
      controlPoints,
      closed,
      stroke,
      strokeWidth,
      fill,
      pathData,
    };
  }

  /**
   * Initialize LOD levels for complex paths
   */
  private initializeLOD(data: SplineData | null): void {
    if (!data) return;

    // Check if LOD settings exist in the data
    const lodSettings = data.lod;
    const points = data.controlPoints;

    // Auto-enable LOD for complex paths (>100 points)
    const shouldAutoEnable = points.length > 100;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const lodEnabled = (lodSettings != null && typeof lodSettings === "object" && "enabled" in lodSettings && typeof lodSettings.enabled === "boolean" && lodSettings.enabled) ? true : false;
    if (lodEnabled || shouldAutoEnable) {
      this.lodEnabled = true;

      // Use pre-generated levels if available, otherwise generate them
      const lodLevels = (lodSettings != null && typeof lodSettings === "object" && "levels" in lodSettings && Array.isArray(lodSettings.levels) && lodSettings.levels.length > 0) ? lodSettings.levels : undefined;
      if (lodLevels != null) {
        this.lodLevels = lodLevels.map((level) => ({
          tolerance: level.tolerance,
          controlPoints: level.controlPoints,
          pointCount: level.controlPoints.length,
          quality: 0, // Will be set by index
        }));
        // Set quality based on index
        this.lodLevels.forEach((level, i) => {
          level.quality = i;
        });
      } else {
        // Generate LOD levels on-the-fly
        // Type proof: simplificationTolerance ∈ number | undefined → number
        const tolerance = lodSettings !== undefined && typeof lodSettings === "object" && lodSettings !== null && "simplificationTolerance" in lodSettings && isFiniteNumber(lodSettings.simplificationTolerance) && lodSettings.simplificationTolerance >= 0
          ? lodSettings.simplificationTolerance
          : 2.0;
        this.lodLevels = vectorLOD.generateLODLevels(
          this.layerData.id,
          points,
          4, // 4 levels
          tolerance,
        );
      }
    }
  }

  /**
   * Update LOD context (call this when playback state changes)
   */
  public updateLODContext(context: Partial<LODContext>): void {
    this.lodContext = { ...this.lodContext, ...context };
  }

  /**
   * Initialize mesh warp deformation from layer data
   */
  private initializeWarp(data: SplineData | null): void {
    // Support both new 'warpPins' and deprecated 'puppetPins' property names
    // Type proof: pins ∈ WarpPin[] | undefined
    const warpPins = data !== null && typeof data === "object" && "warpPins" in data && Array.isArray(data.warpPins)
      ? data.warpPins
      : undefined;
    const puppetPins = data !== null && typeof data === "object" && "puppetPins" in data && Array.isArray(data.puppetPins)
      ? data.puppetPins
      : undefined;
    const pins = warpPins !== undefined ? warpPins : puppetPins;
    if (!data || !pins || pins.length === 0) {
      return;
    }

    this.warpPins = pins;
    this.warpEnabled = true;

    // Build the warp mesh using the deformation service
    meshWarpDeformation.buildMesh(this.layerData.id, data.controlPoints, pins);
  }

  /**
   * Enable mesh warp deformation mode
   * Creates a deformation mesh from current control points
   */
  public enableWarpMode(): void {
    if (this.warpEnabled) return;

    this.warpEnabled = true;

    // Build initial mesh with current pins
    meshWarpDeformation.buildMesh(
      this.layerData.id,
      this.splineData.controlPoints,
      this.warpPins,
    );

    this.lastPointsHash = ""; // Force rebuild
  }

  /** @deprecated Use enableWarpMode instead */
  public enablePuppetMode(): void {
    return this.enableWarpMode();
  }

  /**
   * Disable mesh warp deformation mode
   */
  public disableWarpMode(): void {
    if (!this.warpEnabled) return;

    this.warpEnabled = false;
    this.warpPins = [];
    meshWarpDeformation.clearMesh(this.layerData.id);

    this.lastPointsHash = ""; // Force rebuild
  }

  /** @deprecated Use disableWarpMode instead */
  public disablePuppetMode(): void {
    return this.disableWarpMode();
  }

  /**
   * Check if mesh warp deformation is enabled
   */
  public isWarpEnabled(): boolean {
    return this.warpEnabled;
  }

  /** @deprecated Use isWarpEnabled instead */
  public isPuppetEnabled(): boolean {
    return this.isWarpEnabled();
  }

  /**
   * Add a warp pin at the specified position
   * @param x - X position of the pin
   * @param y - Y position of the pin
   * @param type - Pin type (position, rotation, or starch)
   * @returns The created pin
   */
  public addWarpPin(
    x: number,
    y: number,
    type: WarpPinType = "position",
  ): WarpPin {
    // Import the helper function to create default pins
    const { createDefaultWarpPin } = require("@/types/meshWarp");
    const id = `pin_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;

    const pin = createDefaultWarpPin(id, x, y, type);
    this.warpPins.push(pin);

    // Enable warp mode if not already enabled
    if (!this.warpEnabled) {
      this.enableWarpMode();
    }

    // Add pin to the deformation mesh
    meshWarpDeformation.addPin(this.layerData.id, pin);

    this.lastPointsHash = ""; // Force rebuild
    return pin;
  }

  /** @deprecated Use addWarpPin instead */
  public addPuppetPin(
    x: number,
    y: number,
    type: "position" | "rotation" | "starch" = "position",
  ): WarpPin {
    return this.addWarpPin(x, y, type);
  }

  /**
   * Remove a warp pin by ID
   * @param pinId - The ID of the pin to remove
   */
  public removeWarpPin(pinId: string): void {
    const index = this.warpPins.findIndex((p) => p.id === pinId);
    if (index === -1) return;

    this.warpPins.splice(index, 1);
    meshWarpDeformation.removePin(this.layerData.id, pinId);

    // Disable warp mode if no pins remain
    if (this.warpPins.length === 0) {
      this.disableWarpMode();
    }

    this.lastPointsHash = ""; // Force rebuild
  }

  /** @deprecated Use removeWarpPin instead */
  public removePuppetPin(pinId: string): void {
    return this.removeWarpPin(pinId);
  }

  /**
   * Get all warp pins
   */
  public getWarpPins(): WarpPin[] {
    return this.warpPins;
  }

  /** @deprecated Use getWarpPins instead */
  public getPuppetPins(): WarpPin[] {
    return this.getWarpPins();
  }

  /**
   * Update a warp pin's position
   * @param pinId - The ID of the pin to update
   * @param x - New X position
   * @param y - New Y position
   */
  public updateWarpPinPosition(pinId: string, x: number, y: number): void {
    const pin = this.warpPins.find((p) => p.id === pinId);
    if (!pin) return;

    // Validate coordinates (NaN would corrupt warp mesh calculations)
    const validX = Number.isFinite(x) ? x : 0;
    const validY = Number.isFinite(y) ? y : 0;

    pin.position.value = { x: validX, y: validY };
    meshWarpDeformation.updatePinPosition(
      this.layerData.id,
      pinId,
      validX,
      validY,
    );

    this.lastPointsHash = ""; // Force rebuild
  }

  /** @deprecated Use updateWarpPinPosition instead */
  public updatePuppetPinPosition(pinId: string, x: number, y: number): void {
    return this.updateWarpPinPosition(pinId, x, y);
  }

  /**
   * Set warp pins (replacing all existing pins)
   * @param pins - Array of warp pins
   */
  public setWarpPins(pins: WarpPin[]): void {
    this.warpPins = pins;

    if (pins.length > 0) {
      if (!this.warpEnabled) {
        this.enableWarpMode();
      }
      meshWarpDeformation.updateMeshPins(this.layerData.id, pins);
    } else {
      this.disableWarpMode();
    }

    this.lastPointsHash = ""; // Force rebuild
  }

  /** @deprecated Use setWarpPins instead */
  public setPuppetPins(pins: WarpPin[]): void {
    return this.setWarpPins(pins);
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
      // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const z0Value = p0.depth;
      const z0 = isFiniteNumber(z0Value) ? z0Value : 0;
      const z1Value = p1.depth;
      const z1 = isFiniteNumber(z1Value) ? z1Value : 0;

      // Create bezier curve segment
      // Handles are stored as ABSOLUTE positions, not relative offsets
      // Type proof: handleOut.x ∈ number | undefined → number
      const handleOutX0Build = p0.handleOut !== null && typeof p0.handleOut === "object" && "x" in p0.handleOut && isFiniteNumber(p0.handleOut.x)
        ? p0.handleOut.x
        : p0.x;
      const handleOutY0Build = p0.handleOut !== null && typeof p0.handleOut === "object" && "y" in p0.handleOut && isFiniteNumber(p0.handleOut.y)
        ? p0.handleOut.y
        : p0.y;
      // Type proof: handleIn.x ∈ number | undefined → number
      const handleInX1Build = p1.handleIn !== null && typeof p1.handleIn === "object" && "x" in p1.handleIn && isFiniteNumber(p1.handleIn.x)
        ? p1.handleIn.x
        : p1.x;
      const handleInY1Build = p1.handleIn !== null && typeof p1.handleIn === "object" && "y" in p1.handleIn && isFiniteNumber(p1.handleIn.y)
        ? p1.handleIn.y
        : p1.y;
      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(handleOutX0Build, -handleOutY0Build, z0),
        new THREE.Vector3(handleInX1Build, -handleInY1Build, z1),
        new THREE.Vector3(p1.x, -p1.y, z1),
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.splineData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zLastValue = lastPoint.depth;
      const zLast = isFiniteNumber(zLastValue) ? zLastValue : 0;
      const zFirstValue = firstPoint.depth;
      const zFirst = isFiniteNumber(zFirstValue) ? zFirstValue : 0;

      // Closing bezier also uses absolute handle positions
      // Type proof: handleOut.x ∈ number | undefined → number
      const lastHandleOutX = lastPoint.handleOut !== null && typeof lastPoint.handleOut === "object" && "x" in lastPoint.handleOut && isFiniteNumber(lastPoint.handleOut.x)
        ? lastPoint.handleOut.x
        : lastPoint.x;
      const lastHandleOutY = lastPoint.handleOut !== null && typeof lastPoint.handleOut === "object" && "y" in lastPoint.handleOut && isFiniteNumber(lastPoint.handleOut.y)
        ? lastPoint.handleOut.y
        : lastPoint.y;
      // Type proof: handleIn.x ∈ number | undefined → number
      const firstHandleInX = firstPoint.handleIn !== null && typeof firstPoint.handleIn === "object" && "x" in firstPoint.handleIn && isFiniteNumber(firstPoint.handleIn.x)
        ? firstPoint.handleIn.x
        : firstPoint.x;
      const firstHandleInY = firstPoint.handleIn !== null && typeof firstPoint.handleIn === "object" && "y" in firstPoint.handleIn && isFiniteNumber(firstPoint.handleIn.y)
        ? firstPoint.handleIn.y
        : firstPoint.y;
      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(lastHandleOutX, -lastHandleOutY, zLast),
        new THREE.Vector3(firstHandleInX, -firstHandleInY, zFirst),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst),
      );

      this.curve.add(closingBezier);
    }

    // Create line geometry using Line2 for proper width support
    const curvePoints = this.curve.getPoints(points.length * 20);

    // Convert THREE.Vector3[] to flat position array for LineGeometry
    const positions: number[] = [];
    for (const pt of curvePoints) {
      positions.push(pt.x, pt.y, pt.z);
    }

    const lineGeometry = new LineGeometry();
    lineGeometry.setPositions(positions);

    // Parse stroke color
    const color = new THREE.Color(this.splineData.stroke);

    const lineMaterial = new LineMaterial({
      color: color.getHex(),
      linewidth: this.splineData.strokeWidth,
      transparent: true,
      resolution: this.resolution,
      // Use world units so linewidth is in pixels
      worldUnits: false,
    });

    this.lineMesh = new Line2(lineGeometry, lineMaterial);
    this.lineMesh.computeLineDistances();
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
   * 
   * System F/Omega proof: Explicit validation of curve initialization
   * Type proof: t ∈ number → THREE.Vector3 (non-nullable)
   * Mathematical proof: Curve must be initialized to calculate point at parameter t
   * Geometric proof: Point calculation requires valid curve geometry
   */
  getPointAt(t: number): THREE.Vector3 {
    // System F/Omega proof: Explicit validation of curve existence
    // Type proof: curve ∈ THREE.Curve<THREE.Vector3> | null
    // Mathematical proof: Curve must be initialized before calculating points
    if (!this.curve) {
      throw new Error(
        `[SplineLayer] Cannot get point at parameter: Curve not initialized. ` +
        `Layer ID: ${this.id}, parameter t: ${t}. ` +
        `Spline layer must have a valid curve before calculating points. ` +
        `Wrap in try/catch if "curve not ready" is an expected state.`
      );
    }
    // Validate t (NaN bypasses Math.max/min clamp)
    const validT = Number.isFinite(t) ? Math.max(0, Math.min(1, t)) : 0;
    return this.curve.getPointAt(validT);
  }

  /**
   * Get the tangent at parameter t (0-1)
   * 
   * System F/Omega proof: Explicit validation of curve initialization
   * Type proof: t ∈ number → THREE.Vector3 (non-nullable)
   * Mathematical proof: Curve must be initialized to calculate tangent at parameter t
   * Geometric proof: Tangent calculation requires valid curve geometry
   */
  getTangentAt(t: number): THREE.Vector3 {
    // System F/Omega proof: Explicit validation of curve existence
    // Type proof: curve ∈ THREE.Curve<THREE.Vector3> | null
    // Mathematical proof: Curve must be initialized before calculating tangents
    if (!this.curve) {
      throw new Error(
        `[SplineLayer] Cannot get tangent at parameter: Curve not initialized. ` +
        `Layer ID: ${this.id}, parameter t: ${t}. ` +
        `Spline layer must have a valid curve before calculating tangents. ` +
        `Wrap in try/catch if "curve not ready" is an expected state.`
      );
    }
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
   * 
   * System F/Omega proof: Explicit validation of point and tangent calculation
   * Type proof: t ∈ number → { position: THREE.Vector3; rotation: number } (non-nullable)
   * Mathematical proof: Point and tangent must be calculated successfully to determine transform
   * Geometric proof: Transform calculation requires valid point and tangent vectors
   */
  getTransformAt(
    t: number,
  ): { position: THREE.Vector3; rotation: number } {
    // System F/Omega pattern: getPointAt and getTangentAt now throw explicit errors
    const point = this.getPointAt(t);
    const tangent = this.getTangentAt(t);

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
      (this.lineMesh.material as LineMaterial).color.set(color);
    }
  }

  /**
   * Set stroke width
   */
  setStrokeWidth(width: number): void {
    // Validate width (NaN/0 would corrupt LineMaterial rendering)
    const validWidth = Number.isFinite(width) && width > 0 ? width : 2;
    this.splineData.strokeWidth = validWidth;
    if (this.lineMesh) {
      (this.lineMesh.material as LineMaterial).linewidth = validWidth;
      (this.lineMesh.material as LineMaterial).needsUpdate = true;
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
      const curvePoints = this.curve.getPoints(
        this.splineData.controlPoints.length * 20,
      );
      this.createFill(curvePoints);
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
    if (this.lineMesh) {
      (this.lineMesh.material as LineMaterial).resolution.set(
        validWidth,
        validHeight,
      );
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
    this.lastPointsHash = "";
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
    const { controlPointToAnimatable } = require("@/types/project");

    // Convert static points to animated
    const animatedPoints = this.splineData.controlPoints.map(
      (cp: ControlPoint) => controlPointToAnimatable(cp),
    );

    this.setAnimatedControlPoints(animatedPoints);
    return animatedPoints;
  }

  /**
   * Disable animation and convert back to static control points
   */
  disableAnimation(): void {
    if (!this.animatedPoints) return;

    const { animatableToControlPoint } = require("@/types/project");

    // Convert animated points back to static using current values
    this.splineData.controlPoints = this.animatedPoints.map(
      (acp: AnimatableControlPoint) => animatableToControlPoint(acp),
    );

    this.animatedPoints = null;
    this.splineData.animatedControlPoints = undefined;
    this.splineData.animated = false;
    this.lastEvaluatedFrame = -1;
    this.cachedEvaluatedPoints = null;
    this.lastPointsHash = "";

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
  // TRIM PATH SETTERS/GETTERS
  // ============================================================================

  /**
   * Set trim start (static value)
   * @param value - Trim start percentage (0-100)
   */
  setTrimStart(value: number): void {
    this.trimStartProp = value;
    this.lastPointsHash = ""; // Force rebuild
  }

  /**
   * Set trim end (static value)
   * @param value - Trim end percentage (0-100)
   */
  setTrimEnd(value: number): void {
    this.trimEndProp = value;
    this.lastPointsHash = ""; // Force rebuild
  }

  /**
   * Set trim offset (static value)
   * @param value - Trim offset in degrees
   */
  setTrimOffset(value: number): void {
    this.trimOffsetProp = value;
    this.lastPointsHash = ""; // Force rebuild
  }

  /**
   * Set animated trim start property
   * @param prop - AnimatableProperty for trim start
   */
  setAnimatedTrimStart(prop: AnimatableProperty<number>): void {
    this.trimStartProp = prop;
    this.lastPointsHash = "";
  }

  /**
   * Set animated trim end property
   * @param prop - AnimatableProperty for trim end
   */
  setAnimatedTrimEnd(prop: AnimatableProperty<number>): void {
    this.trimEndProp = prop;
    this.lastPointsHash = "";
  }

  /**
   * Set animated trim offset property
   * @param prop - AnimatableProperty for trim offset
   */
  setAnimatedTrimOffset(prop: AnimatableProperty<number>): void {
    this.trimOffsetProp = prop;
    this.lastPointsHash = "";
  }

  /**
   * Get current trim values at a specific frame
   * Useful for UI display and debugging
   */
  getTrimValues(frame: number): { start: number; end: number; offset: number } {
    return {
      start: this.evaluateStaticOrAnimated(this.trimStartProp, frame, 0),
      end: this.evaluateStaticOrAnimated(this.trimEndProp, frame, 100),
      offset: this.evaluateStaticOrAnimated(this.trimOffsetProp, frame, 0),
    };
  }

  /**
   * Check if trim path is enabled (has non-default values or animated)
   */
  hasTrimPath(): boolean {
    // Check if any trim property is set (not undefined)
    return (
      this.trimStartProp !== undefined ||
      this.trimEndProp !== undefined ||
      this.trimOffsetProp !== undefined
    );
  }

  /**
   * Set path effects
   * @param effects - Array of path effects to apply
   */
  setPathEffects(effects: SplinePathEffectInstance[]): void {
    this.pathEffects = effects;
    this.lastPointsHash = ""; // Force rebuild
  }

  /**
   * Get current path effects
   */
  getPathEffects(): SplinePathEffectInstance[] | undefined {
    return this.pathEffects;
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
   * Uses interpolateProperty from interpolation.ts
   * Driven values override interpolated values
   */
  private evaluateControlPointAtFrame(
    acp: AnimatableControlPoint,
    frame: number,
    index: number,
  ): EvaluatedControlPoint {
    // Use composition fps for correct animation timing (not hardcoded 30fps)
    const fps = this.compositionFps;
    const layerId = this.id;

    // Get interpolated values first
    const interpolatedX = interpolateProperty(acp.x, frame, fps, layerId);
    const interpolatedY = interpolateProperty(acp.y, frame, fps, layerId);
    const interpolatedDepth = acp.depth
      ? interpolateProperty(acp.depth, frame, fps, layerId)
      : 0;

    // Apply driven value overrides
    return {
      id: acp.id,
      x: this.getDrivenControlPointValue(index, "x", interpolatedX),
      y: this.getDrivenControlPointValue(index, "y", interpolatedY),
      depth: this.getDrivenControlPointValue(index, "depth", interpolatedDepth),
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
   * Get evaluated control points at a specific frame
   * PUBLIC API for TextLayer and other consumers
   *
   * For static splines, returns the static control points converted to EvaluatedControlPoint
   * For animated splines, interpolates all control points at the given frame
   * Driven values (from PropertyDriverSystem) override interpolated values
   *
   * DETERMINISM: Same frame + same drivers = same output (pure function)
   */
  getEvaluatedControlPoints(frame: number): EvaluatedControlPoint[] {
    // Use cached result if same frame AND no driven values have changed
    // Note: We don't cache when driven values are present to ensure reactivity
    const hasDrivenValues = this.hasSplineDrivers();
    if (
      frame === this.lastEvaluatedFrame &&
      this.cachedEvaluatedPoints &&
      !hasDrivenValues
    ) {
      return this.cachedEvaluatedPoints;
    }

    let points: EvaluatedControlPoint[];

    if (this.animatedPoints && this.animatedPoints.length > 0) {
      // Animated spline - interpolate each control point
      points = this.animatedPoints.map((acp, index) =>
        this.evaluateControlPointAtFrame(acp, frame, index),
      );
    } else {
      // Static spline - convert ControlPoint to EvaluatedControlPoint
      points = this.splineData.controlPoints.map((cp, index) => ({
        id: cp.id,
        x: this.getDrivenControlPointValue(index, "x", cp.x),
        y: this.getDrivenControlPointValue(index, "y", cp.y),
        // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
        depth: this.getDrivenControlPointValue(index, "depth", (() => {
          const depthValue = cp.depth;
          return isFiniteNumber(depthValue) ? depthValue : 0;
        })()),
        handleIn: cp.handleIn,
        handleOut: cp.handleOut,
        type: cp.type,
        group: cp.group,
      }));
    }

    // Cache the result (only if no driven values)
    this.lastEvaluatedFrame = frame;
    if (!hasDrivenValues) {
      this.cachedEvaluatedPoints = points;
    }

    return points;
  }

  /**
   * Check if any spline control point drivers are active
   */
  private hasSplineDrivers(): boolean {
    // Check if any driven values match spline control point pattern
    for (const key of this.drivenValues.keys()) {
      if (isSplineControlPointPath(key)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Get a driven control point value, falling back to base value
   */
  private getDrivenControlPointValue(
    index: number,
    property: "x" | "y" | "depth",
    baseValue: number,
  ): number {
    const path = createSplineControlPointPath(index, property);
    return this.getDrivenOrBase(path, baseValue);
  }

  /**
   * Compute a hash of control point positions for change detection
   * Used to avoid rebuilding geometry when positions haven't changed
   */
  private computePointsHash(points: EvaluatedControlPoint[]): string {
    // Simple hash using position values (sufficient for change detection)
    return points
      .map((p) => `${p.x.toFixed(2)},${p.y.toFixed(2)},${p.depth.toFixed(2)}`)
      .join("|");
  }

  // ============================================================================
  // TRIM PATH & PATH EFFECTS HELPERS
  // ============================================================================

  /**
   * Evaluate a property that can be either a static value or AnimatableProperty
   * @param prop - Static value or AnimatableProperty
   * @param frame - Current frame number
   * @param defaultValue - Value to use if prop is undefined
   */
  private evaluateStaticOrAnimated(
    prop: number | AnimatableProperty<number> | undefined,
    frame: number,
    defaultValue: number,
  ): number {
    if (prop === undefined) {
      return defaultValue;
    }
    if (typeof prop === "number") {
      return prop;
    }
    // It's an AnimatableProperty - use composition fps for correct timing
    return interpolateProperty(prop, frame, this.compositionFps, this.id);
  }

  /**
   * Check if trim is active (differs from default values)
   */
  private isTrimActive(
    trimStart: number,
    trimEnd: number,
    trimOffset: number,
  ): boolean {
    // Default values that result in showing the full path
    return trimStart !== 0 || trimEnd !== 100 || trimOffset !== 0;
  }

  /**
   * Check if any path effects are enabled
   */
  private hasActivePathEffects(): boolean {
    // Type proof: pathEffects ∈ SplinePathEffectInstance[] | undefined → boolean
    if (this.pathEffects === undefined || !Array.isArray(this.pathEffects)) {
      return false;
    }
    return this.pathEffects.some((e) => e.enabled === true);
  }

  /**
   * Convert EvaluatedControlPoint[] to BezierPath format for shapeOperations
   * Note: EvaluatedControlPoint handles are ABSOLUTE, BezierVertex handles are RELATIVE
   */
  private evaluatedPointsToBezierPath(
    points: EvaluatedControlPoint[],
  ): BezierPath {
    const vertices: BezierVertex[] = points.map((p) => {
      // Convert absolute handles to relative handles
      const inHandle: Point2D = p.handleIn
        ? { x: p.handleIn.x - p.x, y: p.handleIn.y - p.y }
        : { x: 0, y: 0 };
      const outHandle: Point2D = p.handleOut
        ? { x: p.handleOut.x - p.x, y: p.handleOut.y - p.y }
        : { x: 0, y: 0 };

      return {
        point: { x: p.x, y: p.y },
        inHandle,
        outHandle,
      };
    });

    return {
      vertices,
      closed: this.splineData.closed,
    };
  }

  /**
   * Convert BezierPath back to EvaluatedControlPoint[] format
   * Note: Depth information is lost during trim - we interpolate from original points
   */
  private bezierPathToEvaluatedPoints(
    bezierPath: BezierPath,
    originalPoints: EvaluatedControlPoint[],
  ): EvaluatedControlPoint[] {
    // If the trimmed path has different vertex count, we need to handle depth
    // For now, use depth=0 for new vertices (trim typically creates new interpolated points)
    return bezierPath.vertices.map((v, i) => {
      // Try to find closest original point for depth value
      const originalDepth =
        i < originalPoints.length ? originalPoints[i].depth : 0;

      // Convert relative handles back to absolute
      const handleIn =
        v.inHandle.x !== 0 || v.inHandle.y !== 0
          ? { x: v.point.x + v.inHandle.x, y: v.point.y + v.inHandle.y }
          : null;
      const handleOut =
        v.outHandle.x !== 0 || v.outHandle.y !== 0
          ? { x: v.point.x + v.outHandle.x, y: v.point.y + v.outHandle.y }
          : null;

      return {
        id: `trimmed_${i}`,
        x: v.point.x,
        y: v.point.y,
        depth: originalDepth,
        handleIn,
        handleOut,
        type: "smooth" as const,
      };
    });
  }

  /**
   * Apply path effects in order (before trim)
   * @param bezierPath - The input path
   * @param frame - Current frame for animated effect properties
   */
  private applyPathEffects(bezierPath: BezierPath, frame: number): BezierPath {
    if (!this.pathEffects || this.pathEffects.length === 0) {
      return bezierPath;
    }

    // Use composition fps for correct animation timing
    const fps = this.compositionFps;
    const layerId = this.id;

    // Sort effects by order
    const sortedEffects = [...this.pathEffects]
      .filter((e) => e.enabled)
      .sort((a, b) => a.order - b.order);

    let result = bezierPath;

    for (const effect of sortedEffects) {
      switch (effect.type) {
        case "offsetPath": {
          const offsetEffect =
            effect as import("@/types/project").OffsetPathEffect;
          const amount = interpolateProperty(
            offsetEffect.amount,
            frame,
            fps,
            layerId,
          );
          const miterLimit = interpolateProperty(
            offsetEffect.miterLimit,
            frame,
            fps,
            layerId,
          );
          result = offsetPath(
            result,
            amount,
            offsetEffect.lineJoin,
            miterLimit,
          );
          break;
        }
        case "wiggle": {
          const wiggleEffect =
            effect as import("@/types/project").WigglePathEffect;
          const size = interpolateProperty(
            wiggleEffect.size,
            frame,
            fps,
            layerId,
          );
          const detail = interpolateProperty(
            wiggleEffect.detail,
            frame,
            fps,
            layerId,
          );
          const temporalPhase = interpolateProperty(
            wiggleEffect.temporalPhase,
            frame,
            fps,
            layerId,
          );
          const spatialPhase = interpolateProperty(
            wiggleEffect.spatialPhase,
            frame,
            fps,
            layerId,
          );
          const correlation = interpolateProperty(
            wiggleEffect.correlation,
            frame,
            fps,
            layerId,
          );
          result = wigglePath(
            result,
            size,
            detail,
            "smooth", // WigglePathEffect pointType mapping
            correlation,
            temporalPhase,
            spatialPhase,
            wiggleEffect.seed,
          );
          break;
        }
        case "zigzag": {
          const zigzagEffect = effect as import("@/types/project").ZigZagEffect;
          const size = interpolateProperty(
            zigzagEffect.size,
            frame,
            fps,
            layerId,
          );
          const ridges = interpolateProperty(
            zigzagEffect.ridgesPerSegment,
            frame,
            fps,
            layerId,
          );
          result = zigZagPath(result, size, ridges, zigzagEffect.pointType);
          break;
        }
        case "roughen": {
          const roughenEffect =
            effect as import("@/types/project").RoughenEffect;
          const size = interpolateProperty(
            roughenEffect.size,
            frame,
            fps,
            layerId,
          );
          const detail = interpolateProperty(
            roughenEffect.detail,
            frame,
            fps,
            layerId,
          );
          result = roughenPath(result, size, detail, roughenEffect.seed);
          break;
        }
        case "wave": {
          const waveEffect = effect as import("@/types/project").WaveEffect;
          const amplitude = interpolateProperty(
            waveEffect.amplitude,
            frame,
            fps,
            layerId,
          );
          const frequency = interpolateProperty(
            waveEffect.frequency,
            frame,
            fps,
            layerId,
          );
          const phase = interpolateProperty(
            waveEffect.phase,
            frame,
            fps,
            layerId,
          );
          result = wavePath(
            result,
            amplitude,
            frequency,
            phase,
            waveEffect.waveType as WaveType,
          );
          break;
        }
      }
    }

    return result;
  }

  /**
   * Build spline geometry from evaluated control points
   * Called when control points change during animation
   */
  private buildSplineFromEvaluatedPoints(
    points: EvaluatedControlPoint[],
  ): void {
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
      // Handles are stored as ABSOLUTE positions, not relative offsets
      // Type proof: handleOut.x ∈ number | undefined → number
      const handleOutX0EvalPoints = p0.handleOut !== null && typeof p0.handleOut === "object" && "x" in p0.handleOut && isFiniteNumber(p0.handleOut.x)
        ? p0.handleOut.x
        : p0.x;
      const handleOutY0EvalPoints = p0.handleOut !== null && typeof p0.handleOut === "object" && "y" in p0.handleOut && isFiniteNumber(p0.handleOut.y)
        ? p0.handleOut.y
        : p0.y;
      // Type proof: handleIn.x ∈ number | undefined → number
      const handleInX1EvalPoints = p1.handleIn !== null && typeof p1.handleIn === "object" && "x" in p1.handleIn && isFiniteNumber(p1.handleIn.x)
        ? p1.handleIn.x
        : p1.x;
      const handleInY1EvalPoints = p1.handleIn !== null && typeof p1.handleIn === "object" && "y" in p1.handleIn && isFiniteNumber(p1.handleIn.y)
        ? p1.handleIn.y
        : p1.y;
      const bezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(p0.x, -p0.y, z0),
        new THREE.Vector3(handleOutX0EvalPoints, -handleOutY0EvalPoints, z0),
        new THREE.Vector3(handleInX1EvalPoints, -handleInY1EvalPoints, z1),
        new THREE.Vector3(p1.x, -p1.y, z1),
      );

      this.curve.add(bezier);
    }

    // Close path if needed
    if (this.splineData.closed && points.length > 2) {
      const lastPoint = points[points.length - 1];
      const firstPoint = points[0];

      const zLast = lastPoint.depth;
      const zFirst = firstPoint.depth;

      // Closing bezier also uses absolute handle positions
      // Type proof: handleOut.x ∈ number | undefined → number
      const lastHandleOutXEvalPoints = lastPoint.handleOut !== null && typeof lastPoint.handleOut === "object" && "x" in lastPoint.handleOut && isFiniteNumber(lastPoint.handleOut.x)
        ? lastPoint.handleOut.x
        : lastPoint.x;
      const lastHandleOutYEvalPoints = lastPoint.handleOut !== null && typeof lastPoint.handleOut === "object" && "y" in lastPoint.handleOut && isFiniteNumber(lastPoint.handleOut.y)
        ? lastPoint.handleOut.y
        : lastPoint.y;
      // Type proof: handleIn.x ∈ number | undefined → number
      const firstHandleInXEvalPoints = firstPoint.handleIn !== null && typeof firstPoint.handleIn === "object" && "x" in firstPoint.handleIn && isFiniteNumber(firstPoint.handleIn.x)
        ? firstPoint.handleIn.x
        : firstPoint.x;
      const firstHandleInYEvalPoints = firstPoint.handleIn !== null && typeof firstPoint.handleIn === "object" && "y" in firstPoint.handleIn && isFiniteNumber(firstPoint.handleIn.y)
        ? firstPoint.handleIn.y
        : firstPoint.y;
      const closingBezier = new THREE.CubicBezierCurve3(
        new THREE.Vector3(lastPoint.x, -lastPoint.y, zLast),
        new THREE.Vector3(lastHandleOutXEvalPoints, -lastHandleOutYEvalPoints, zLast),
        new THREE.Vector3(firstHandleInXEvalPoints, -firstHandleInYEvalPoints, zFirst),
        new THREE.Vector3(firstPoint.x, -firstPoint.y, zFirst),
      );

      this.curve.add(closingBezier);
    }

    // Create line geometry using Line2 for proper width support
    const curvePoints = this.curve.getPoints(points.length * 20);

    // Convert THREE.Vector3[] to flat position array for LineGeometry
    const positions: number[] = [];
    for (const pt of curvePoints) {
      positions.push(pt.x, pt.y, pt.z);
    }

    const lineGeometry = new LineGeometry();
    lineGeometry.setPositions(positions);

    // Parse stroke color
    const color = new THREE.Color(this.splineData.stroke);

    const lineMaterial = new LineMaterial({
      color: color.getHex(),
      linewidth: this.splineData.strokeWidth,
      transparent: true,
      resolution: this.resolution,
      worldUnits: false,
    });

    this.lineMesh = new Line2(lineGeometry, lineMaterial);
    this.lineMesh.computeLineDistances();
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
    // Evaluate trim properties (these may be animated even if control points aren't)
    const trimStart = this.evaluateStaticOrAnimated(
      this.trimStartProp,
      frame,
      0,
    );
    const trimEnd = this.evaluateStaticOrAnimated(this.trimEndProp, frame, 100);
    const trimOffset = this.evaluateStaticOrAnimated(
      this.trimOffsetProp,
      frame,
      0,
    );

    const needsTrim = this.isTrimActive(trimStart, trimEnd, trimOffset);
    const hasEffects = this.hasActivePathEffects();
    const useLOD = this.shouldUseLOD();
    const hasWarp = this.warpEnabled && this.warpPins.length > 0;

    // Skip if not animated and no trim/effects/LOD/warp needed
    if (
      !this.isAnimated() &&
      !needsTrim &&
      !hasEffects &&
      !useLOD &&
      !hasWarp
    ) {
      return;
    }

    // Evaluate control points at this frame
    const evaluatedPoints = this.getEvaluatedControlPoints(frame);

    // Compute hash including trim values, LOD state, and warp for change detection
    const lodHash = useLOD
      ? `|lod:${this.lodContext.isPlaying},${this.lodContext.zoom.toFixed(2)}`
      : "";
    const trimHash =
      needsTrim || hasEffects
        ? `|trim:${trimStart.toFixed(2)},${trimEnd.toFixed(2)},${trimOffset.toFixed(2)}|fx:${frame}`
        : "";
    const warpHash = hasWarp ? `|warp:${frame}` : "";
    const pointsHash =
      this.computePointsHash(evaluatedPoints) + trimHash + lodHash + warpHash;

    // Only rebuild if points or trim have actually changed
    if (pointsHash !== this.lastPointsHash) {
      let finalPoints = evaluatedPoints;

      // Apply mesh warp deformation first (deforms the base shape)
      if (hasWarp) {
        // Convert EvaluatedControlPoint[] to ControlPoint[] for the deformation service
        const controlPoints: ControlPoint[] = evaluatedPoints.map((ep) => ({
          id: ep.id,
          x: ep.x,
          y: ep.y,
          depth: ep.depth,
          handleIn: ep.handleIn,
          handleOut: ep.handleOut,
          type: ep.type,
          group: ep.group,
        }));

        // Get deformed control points from mesh warp service
        const deformedPoints = meshWarpDeformation.getDeformedControlPoints(
          this.layerData.id,
          frame,
          controlPoints,
        );

        // Convert back to EvaluatedControlPoint format
        finalPoints = deformedPoints.map((cp) => ({
          id: cp.id,
          x: cp.x,
          y: cp.y,
          // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
          depth: (() => {
            const depthValue = cp.depth;
            return isFiniteNumber(depthValue) ? depthValue : 0;
          })(),
          handleIn: cp.handleIn,
          handleOut: cp.handleOut,
          type: cp.type,
          group: cp.group,
        }));
      }

      // Apply path effects and/or trim if needed
      if (needsTrim || hasEffects) {
        // Convert to BezierPath format for processing
        let bezierPath = this.evaluatedPointsToBezierPath(finalPoints);

        // Apply path effects first (they modify the path shape)
        if (hasEffects) {
          bezierPath = this.applyPathEffects(bezierPath, frame);
        }

        // Then apply trim (reveals/hides portions of the modified path)
        if (needsTrim) {
          bezierPath = trimPath(bezierPath, trimStart, trimEnd, trimOffset);
        }

        // Convert back to EvaluatedControlPoint format
        finalPoints = this.bezierPathToEvaluatedPoints(
          bezierPath,
          evaluatedPoints,
        );
      }

      // Apply LOD simplification during playback/scrubbing
      if (useLOD && finalPoints.length > 50) {
        const lodLevel = vectorLOD.selectLODLevel(
          this.lodLevels,
          this.lodContext,
        );
        if (lodLevel && lodLevel.pointCount < finalPoints.length) {
          // Use simplified points from LOD level
          // Map LOD points to evaluated format with all required fields
          finalPoints = lodLevel.controlPoints.map((cp, _i) => {
            // Type proof: handleIn ∈ { x: number; y: number } | null | undefined → { x: number; y: number }
            const handleIn = cp.handleIn !== null && cp.handleIn !== undefined && typeof cp.handleIn === "object" && "x" in cp.handleIn && "y" in cp.handleIn && isFiniteNumber(cp.handleIn.x) && isFiniteNumber(cp.handleIn.y)
              ? cp.handleIn
              : { x: cp.x, y: cp.y };
            // Type proof: handleOut ∈ { x: number; y: number } | null | undefined → { x: number; y: number }
            const handleOut = cp.handleOut !== null && cp.handleOut !== undefined && typeof cp.handleOut === "object" && "x" in cp.handleOut && "y" in cp.handleOut && isFiniteNumber(cp.handleOut.x) && isFiniteNumber(cp.handleOut.y)
              ? cp.handleOut
              : { x: cp.x, y: cp.y };
            return {
              id: cp.id,
              x: cp.x,
              y: cp.y,
              handleIn,
              handleOut,
            // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
          depth: (() => {
            const depthValue = cp.depth;
            return isFiniteNumber(depthValue) ? depthValue : 0;
          })(),
            type: cp.type,
            group: cp.group,
            };
          });
        }
      }

      this.buildSplineFromEvaluatedPoints(finalPoints);
      this.lastPointsHash = pointsHash;
    }
  }

  /**
   * Check if LOD should be used based on current context
   */
  private shouldUseLOD(): boolean {
    if (!this.lodEnabled || this.lodLevels.length === 0) {
      return false;
    }

    // Use LOD during playback or scrubbing
    if (this.lodContext.isPlaying || this.lodContext.isScrubbing) {
      return true;
    }

    // Use LOD when zoomed out significantly
    if (this.lodContext.zoom < 0.5) {
      return true;
    }

    // Use LOD if frame rate is suffering
    // Type proof: currentFPS ∈ number | undefined → number
    const currentFPS = isFiniteNumber(this.lodContext.currentFPS) && this.lodContext.currentFPS > 0
      ? this.lodContext.currentFPS
      : 60;
    // Type proof: targetFPS ∈ number | undefined → number
    const targetFPS = isFiniteNumber(this.lodContext.targetFPS) && this.lodContext.targetFPS > 0
      ? this.lodContext.targetFPS
      : 60;
    if (currentFPS < targetFPS * 0.8) {
      return true;
    }

    return false;
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply evaluated control points if present
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy type assertions
    // Type guard: Check if controlPoints is an array of EvaluatedControlPoint
    const controlPointsRaw = props.controlPoints;
    if (controlPointsRaw != null && Array.isArray(controlPointsRaw) && controlPointsRaw.length > 0) {
      // Type guard: Verify first element has EvaluatedControlPoint shape
      const firstPoint = controlPointsRaw[0];
      if (
        firstPoint != null &&
        typeof firstPoint === "object" &&
        "id" in firstPoint &&
        "x" in firstPoint &&
        "y" in firstPoint &&
        "depth" in firstPoint &&
        "handleIn" in firstPoint &&
        "handleOut" in firstPoint &&
        "type" in firstPoint &&
        typeof firstPoint.id === "string" &&
        typeof firstPoint.x === "number" &&
        typeof firstPoint.y === "number" &&
        typeof firstPoint.depth === "number"
      ) {
        // Type proof: controlPointsRaw is EvaluatedControlPoint[]
        let points = controlPointsRaw as EvaluatedControlPoint[];

        // Apply audio-reactive modifiers to control point positions
        points = this.applySplineAudioModifiers(points);

        const pointsHash = this.computePointsHash(points);
        if (pointsHash !== this.lastPointsHash) {
          this.buildSplineFromEvaluatedPoints(points);
          this.lastPointsHash = pointsHash;
        }
      }
    } else {
      // Check if audio modifiers need to be applied to current control points
      // even when control points weren't explicitly set this frame
      if (this.hasSplineAudioModifiers()) {
        const currentPoints = this.getEvaluatedControlPoints(state.frame);
        const modifiedPoints = this.applySplineAudioModifiers(currentPoints);
        const pointsHash = `${this.computePointsHash(modifiedPoints)}|audio`;
        if (pointsHash !== this.lastPointsHash) {
          this.buildSplineFromEvaluatedPoints(modifiedPoints);
          this.lastPointsHash = pointsHash;
        }
      }
    }

    // Apply stroke properties
    if (props.strokeWidth !== undefined) {
      this.setStrokeWidth(props.strokeWidth as number);
    }

    if (props.strokeColor !== undefined) {
      this.setStroke(props.strokeColor as string);
    }
  }

  /**
   * Check if any spline control point audio modifiers are active.
   */
  private hasSplineAudioModifiers(): boolean {
    const audioMod = this.currentAudioModifiers;
    for (const key in audioMod) {
      if (key.startsWith("splineControlPoint_")) {
        const value = (audioMod as Record<string, number | undefined>)[key];
        if (value !== undefined && value !== 0) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Apply audio-reactive modifiers to spline control points.
   * Modifiers are additive to base control point values.
   * @param points - Input control points
   * @returns Modified control points with audio modifiers applied
   */
  private applySplineAudioModifiers(
    points: EvaluatedControlPoint[],
  ): EvaluatedControlPoint[] {
    const audioMod = this.currentAudioModifiers;

    // Quick check if any spline modifiers exist
    if (!this.hasSplineAudioModifiers()) {
      return points;
    }

    // Apply modifiers to each control point
    // Type-safe access using AudioReactiveModifiers index signature
    return points.map((point, index) => {
      // Get audio modifiers for this control point index
      // AudioReactiveModifiers has index signature: [key: `splineControlPoint_${number}_${"x" | "y" | "depth"}`]: number | undefined
      const xKey = `splineControlPoint_${index}_x` as const;
      const yKey = `splineControlPoint_${index}_y` as const;
      const depthKey = `splineControlPoint_${index}_depth` as const;
      
      const xMod = audioMod[xKey];
      const yMod = audioMod[yKey];
      const depthMod = audioMod[depthKey];

      // If no modifiers for this point, return unchanged
      if (!xMod && !yMod && !depthMod) {
        return point;
      }

      // Apply additive modifiers
      // Type proof: xMod ∈ number | undefined → number
      const xModValue = isFiniteNumber(xMod) ? xMod : 0;
      const yModValue = isFiniteNumber(yMod) ? yMod : 0;
      const depthModValue = isFiniteNumber(depthMod) ? depthMod : 0;
      return {
        ...point,
        x: point.x + xModValue,
        y: point.y + yModValue,
        depth: point.depth + depthModValue,
      };
    });
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

      // Handle trim path updates
      if (data.trimStart !== undefined) {
        this.trimStartProp = data.trimStart;
        this.lastPointsHash = ""; // Force rebuild on next frame
      }
      if (data.trimEnd !== undefined) {
        this.trimEndProp = data.trimEnd;
        this.lastPointsHash = "";
      }
      if (data.trimOffset !== undefined) {
        this.trimOffsetProp = data.trimOffset;
        this.lastPointsHash = "";
      }

      // Handle path effects updates
      if (data.pathEffects !== undefined) {
        this.pathEffects = data.pathEffects;
        this.lastPointsHash = ""; // Force rebuild on next frame
      }

      // Handle warp pin updates (support both warpPins and deprecated puppetPins)
      // Type proof: warpPins ∈ WarpPin[] | undefined
      const warpPinsData = data.warpPins !== undefined && Array.isArray(data.warpPins)
        ? data.warpPins
        : data.puppetPins !== undefined && Array.isArray(data.puppetPins)
          ? data.puppetPins
          : undefined;
      if (warpPinsData !== undefined) {
        this.setWarpPins(warpPinsData);
      }

      if (needsRebuild) {
        this.buildSpline();
      }
    }
  }

  protected onDispose(): void {
    this.clearMeshes();

    // Clean up mesh warp deformation mesh
    if (this.warpEnabled) {
      meshWarpDeformation.clearMesh(this.layerData.id);
    }
  }
}
