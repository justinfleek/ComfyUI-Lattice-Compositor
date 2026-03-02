/**
 * VACE Control Video Export Service
 *
 * Generates control videos for VACE (Video Animation Control Engine) and
 * similar motion-controllable video generation systems.
 *
 * Features:
 * - Shapes following spline paths
 * - Speed based on path length / duration (arc-length parameterization)
 * - White shapes on black background output
 * - Multiple shape types (circle, square, triangle, custom)
 * - Easing functions for motion timing
 * - Multi-object support
 *
 * Output: Canvas frames or WebM video with white shapes on #000000
 */

import { isFiniteNumber, safeCoordinateDefault } from "@/utils/typeGuards";
import type { ControlPoint } from "@/types/spline";
import { createBezierCurve } from "../arcLength";

// Extended type with optional z coordinate for 3D curves
type SplineControlPoint = ControlPoint & {
  z?: number;
  handleIn?: { x: number; y: number; z?: number } | null;
  handleOut?: { x: number; y: number; z?: number } | null;
};

import * as THREE from "three";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type PathFollowerShape =
  | "circle"
  | "square"
  | "triangle"
  | "diamond"
  | "arrow"
  | "custom";
export type PathFollowerEasing =
  | "linear"
  | "ease-in"
  | "ease-out"
  | "ease-in-out"
  | "ease-in-cubic"
  | "ease-out-cubic";

export interface PathFollowerConfig {
  /** Unique identifier */
  id: string;

  /** Path definition (control points) */
  controlPoints: SplineControlPoint[];

  /** Whether path is closed loop */
  closed: boolean;

  /** Shape to render */
  shape: PathFollowerShape;

  /** Shape size in pixels [width, height] */
  size: [number, number];

  /** Fill color (typically white for VACE) */
  fillColor: string;

  /** Optional stroke */
  strokeColor?: string;
  strokeWidth?: number;

  /** Animation timing */
  startFrame: number;
  duration: number; // frames - speed = pathLength / duration

  /** Easing function */
  easing: PathFollowerEasing;

  /** Whether shape rotates to follow path tangent */
  alignToPath: boolean;

  /** Additional rotation offset (degrees) */
  rotationOffset: number;

  /** Loop mode */
  loop: boolean;
  loopMode?: "restart" | "pingpong";

  /** Scale animation (optional) */
  scaleStart?: number;
  scaleEnd?: number;

  /** Opacity animation (optional) */
  opacityStart?: number;
  opacityEnd?: number;
}

export interface VACEExportConfig {
  /** Canvas dimensions */
  width: number;
  height: number;

  /** Frame range */
  startFrame: number;
  endFrame: number;
  frameRate: number;

  /** Background color (default black) */
  backgroundColor: string;

  /** All path followers */
  pathFollowers: PathFollowerConfig[];

  /** Output format */
  outputFormat: "canvas" | "webm" | "frames";

  /** Quality settings */
  antiAlias: boolean;
}

export interface PathFollowerState {
  position: { x: number; y: number };
  rotation: number; // radians
  scale: number;
  opacity: number;
  progress: number; // 0-1 along path
  visible: boolean;
}

export interface VACEFrame {
  frameNumber: number;
  canvas: HTMLCanvasElement;
  states: Map<string, PathFollowerState>;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // easing // functions
// ════════════════════════════════════════════════════════════════════════════

const EASING_FUNCTIONS: Record<PathFollowerEasing, (t: number) => number> = {
  linear: (t) => t,
  "ease-in": (t) => t * t,
  "ease-out": (t) => t * (2 - t),
  "ease-in-out": (t) => (t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t),
  "ease-in-cubic": (t) => t * t * t,
  "ease-out-cubic": (t) => --t * t * t + 1,
};

// ════════════════════════════════════════════════════════════════════════════
//                                                 // path // follower // class
// ════════════════════════════════════════════════════════════════════════════

export class PathFollower {
  private config: PathFollowerConfig;
  private curvePath: THREE.CurvePath<THREE.Vector3> | null = null;
  private pathLength: number = 0;

  constructor(config: PathFollowerConfig) {
    this.config = config;
    this.buildPath();
  }

  private buildPath(): void {
    const { controlPoints, closed } = this.config;

    if (controlPoints.length < 2) {
      this.curvePath = null;
      this.pathLength = 0;
      return;
    }

    // Convert control points to THREE.js curves
    const curvePath = new THREE.CurvePath<THREE.Vector3>();

    for (let i = 0; i < controlPoints.length - 1; i++) {
      const p0 = controlPoints[i];
      const p1 = controlPoints[i + 1];

      // Type proof: All z coordinates are unbounded (can be 0, negative, any ℝ)
      const p0z = safeCoordinateDefault(p0.z, 0, "p0.z");
      const p1z = safeCoordinateDefault(p1.z, 0, "p1.z");
      
      // Type proof: Handle offsets are unbounded (can be negative for backwards)
      const p0HandleOutX = p0.handleOut 
        ? safeCoordinateDefault(p0.handleOut.x, 0, "p0.handleOut.x")
        : 0;
      const p0HandleOutY = p0.handleOut
        ? safeCoordinateDefault(p0.handleOut.y, 0, "p0.handleOut.y")
        : 0;
      const p0HandleOutZ = p0.handleOut
        ? safeCoordinateDefault(p0.handleOut.z, 0, "p0.handleOut.z")
        : 0;
      
      const p1HandleInX = p1.handleIn
        ? safeCoordinateDefault(p1.handleIn.x, 0, "p1.handleIn.x")
        : 0;
      const p1HandleInY = p1.handleIn
        ? safeCoordinateDefault(p1.handleIn.y, 0, "p1.handleIn.y")
        : 0;
      const p1HandleInZ = p1.handleIn
        ? safeCoordinateDefault(p1.handleIn.z, 0, "p1.handleIn.z")
        : 0;

      // Create cubic bezier curve from control points
      const curve = createBezierCurve(
        { x: p0.x, y: p0.y, z: p0z },
        {
          x: p0.x + p0HandleOutX,
          y: p0.y + p0HandleOutY,
          z: p0z + p0HandleOutZ,
        },
        {
          x: p1.x + p1HandleInX,
          y: p1.y + p1HandleInY,
          z: p1z + p1HandleInZ,
        },
        { x: p1.x, y: p1.y, z: p1z },
      );

      curvePath.add(curve);
    }

    // Close path if needed
    if (closed && controlPoints.length > 2) {
      const last = controlPoints[controlPoints.length - 1];
      const first = controlPoints[0];

      // Type proof: All z coordinates are unbounded (can be 0, negative, any ℝ)
      const lastZ = safeCoordinateDefault(last.z, 0, "last.z");
      const firstZ = safeCoordinateDefault(first.z, 0, "first.z");

      // Type proof: Handle offsets are unbounded (can be negative for backwards)
      const lastHandleOutX = last.handleOut
        ? safeCoordinateDefault(last.handleOut.x, 0, "last.handleOut.x")
        : 0;
      const lastHandleOutY = last.handleOut
        ? safeCoordinateDefault(last.handleOut.y, 0, "last.handleOut.y")
        : 0;
      const lastHandleOutZ = last.handleOut
        ? safeCoordinateDefault(last.handleOut.z, 0, "last.handleOut.z")
        : 0;

      const firstHandleInX = first.handleIn
        ? safeCoordinateDefault(first.handleIn.x, 0, "first.handleIn.x")
        : 0;
      const firstHandleInY = first.handleIn
        ? safeCoordinateDefault(first.handleIn.y, 0, "first.handleIn.y")
        : 0;
      const firstHandleInZ = first.handleIn
        ? safeCoordinateDefault(first.handleIn.z, 0, "first.handleIn.z")
        : 0;

      const closingCurve = createBezierCurve(
        { x: last.x, y: last.y, z: lastZ },
        {
          x: last.x + lastHandleOutX,
          y: last.y + lastHandleOutY,
          z: lastZ + lastHandleOutZ,
        },
        {
          x: first.x + firstHandleInX,
          y: first.y + firstHandleInY,
          z: firstZ + firstHandleInZ,
        },
        { x: first.x, y: first.y, z: firstZ },
      );

      curvePath.add(closingCurve);
    }

    this.curvePath = curvePath;
    this.pathLength = curvePath.getLength();
  }

  /**
   * Calculate state at a given frame
   * Speed is implicitly determined by: pathLength / duration
   */
  getStateAtFrame(frame: number): PathFollowerState {
    const {
      startFrame,
      duration,
      easing,
      loop,
      loopMode,
      alignToPath,
      rotationOffset,
    } = this.config;
    const {
      scaleStart = 1,
      scaleEnd = 1,
      opacityStart = 1,
      opacityEnd = 1,
    } = this.config;

    // Default state (not visible)
    const defaultState: PathFollowerState = {
      position: { x: 0, y: 0 },
      rotation: 0,
      scale: 1,
      opacity: 0,
      progress: 0,
      visible: false,
    };

    if (!this.curvePath || this.pathLength === 0) {
      return defaultState;
    }

    // Guard against division by zero
    if (duration <= 0) {
      return defaultState;
    }

    // Calculate local frame within animation
    let localFrame = frame - startFrame;

    // Before animation starts
    if (localFrame < 0) {
      return defaultState;
    }

    // After animation ends (handle looping)
    if (localFrame >= duration) {
      if (loop) {
        if (loopMode === "pingpong") {
          const cycles = Math.floor(localFrame / duration);
          localFrame = localFrame % duration;
          if (cycles % 2 === 1) {
            localFrame = duration - localFrame;
          }
        } else {
          localFrame = localFrame % duration;
        }
      } else {
        // Animation complete, stay at end
        localFrame = duration;
      }
    }

    // Calculate progress (0-1)
    const rawProgress = Math.min(1, localFrame / duration);
    const easingFn = EASING_FUNCTIONS[easing] || EASING_FUNCTIONS.linear;
    const progress = easingFn(rawProgress);

    // Get position and tangent from arc-length parameterized path
    //                                                                     // three
    const point = this.curvePath.getPointAt(progress);
    const tangent = this.curvePath.getTangentAt(progress);

    // Calculate rotation
    let rotation = 0;
    if (alignToPath && tangent) {
      rotation = Math.atan2(tangent.y, tangent.x);
    }
    rotation += (rotationOffset * Math.PI) / 180;

    // Interpolate scale and opacity
    const scale = scaleStart + (scaleEnd - scaleStart) * progress;
    const opacity = opacityStart + (opacityEnd - opacityStart) * progress;

    return {
      position: { x: point.x, y: point.y },
      rotation,
      scale,
      opacity,
      progress,
      visible: opacity > 0,
    };
  }

  getConfig(): PathFollowerConfig {
    return this.config;
  }

  getPathLength(): number {
    return this.pathLength;
  }

  /**
   * Calculate speed in pixels per frame
   */
  getSpeed(): number {
    return this.pathLength / this.config.duration;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // shape // rendering
// ════════════════════════════════════════════════════════════════════════════

function renderShape(
  ctx: CanvasRenderingContext2D,
  state: PathFollowerState,
  config: PathFollowerConfig,
): void {
  if (!state.visible || state.opacity <= 0) return;

  const { shape, size, fillColor, strokeColor, strokeWidth } = config;
  const [width, height] = size;
  const scaledWidth = width * state.scale;
  const scaledHeight = height * state.scale;

  ctx.save();
  ctx.translate(state.position.x, state.position.y);
  ctx.rotate(state.rotation);
  // Opacity is stored as 0-100 in the system, canvas globalAlpha is 0-1
  ctx.globalAlpha = state.opacity / 100;

  ctx.fillStyle = fillColor;
  if (strokeColor && strokeWidth) {
    ctx.strokeStyle = strokeColor;
    ctx.lineWidth = strokeWidth;
  }

  ctx.beginPath();

  switch (shape) {
    case "circle":
      ctx.ellipse(0, 0, scaledWidth / 2, scaledHeight / 2, 0, 0, Math.PI * 2);
      break;

    case "square":
      ctx.rect(-scaledWidth / 2, -scaledHeight / 2, scaledWidth, scaledHeight);
      break;

    case "triangle":
      ctx.moveTo(0, -scaledHeight / 2);
      ctx.lineTo(scaledWidth / 2, scaledHeight / 2);
      ctx.lineTo(-scaledWidth / 2, scaledHeight / 2);
      ctx.closePath();
      break;

    case "diamond":
      ctx.moveTo(0, -scaledHeight / 2);
      ctx.lineTo(scaledWidth / 2, 0);
      ctx.lineTo(0, scaledHeight / 2);
      ctx.lineTo(-scaledWidth / 2, 0);
      ctx.closePath();
      break;

    case "arrow": {
      // Arrow pointing right (rotated by path tangent)
      const arrowHead = scaledWidth * 0.4;
      const _arrowTail = scaledWidth * 0.6;
      const arrowWidth = scaledHeight * 0.3;
      const arrowHeadWidth = scaledHeight * 0.5;

      ctx.moveTo(scaledWidth / 2, 0); // Tip
      ctx.lineTo(scaledWidth / 2 - arrowHead, -arrowHeadWidth);
      ctx.lineTo(scaledWidth / 2 - arrowHead, -arrowWidth);
      ctx.lineTo(-scaledWidth / 2, -arrowWidth);
      ctx.lineTo(-scaledWidth / 2, arrowWidth);
      ctx.lineTo(scaledWidth / 2 - arrowHead, arrowWidth);
      ctx.lineTo(scaledWidth / 2 - arrowHead, arrowHeadWidth);
      ctx.closePath();
      break;
    }

    default:
      // Default to circle
      ctx.ellipse(0, 0, scaledWidth / 2, scaledHeight / 2, 0, 0, Math.PI * 2);
  }

  ctx.fill();
  if (strokeColor && strokeWidth) {
    ctx.stroke();
  }

  ctx.restore();
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // vace // export // renderer
// ════════════════════════════════════════════════════════════════════════════

export class VACEControlExporter {
  private config: VACEExportConfig;
  private pathFollowers: PathFollower[] = [];

  constructor(config: VACEExportConfig) {
    this.config = config;
    this.initializeFollowers();
  }

  private initializeFollowers(): void {
    this.pathFollowers = this.config.pathFollowers.map(
      (followerConfig) => new PathFollower(followerConfig),
    );
  }

  /**
   * Render a single frame
   */
  renderFrame(frameNumber: number): VACEFrame {
    const { width, height, backgroundColor, antiAlias } = this.config;

    // Create canvas
    const canvas = document.createElement("canvas");
    canvas.width = width;
    canvas.height = height;
    const ctx = canvas.getContext("2d", { alpha: false })!;

    // Configure anti-aliasing
    ctx.imageSmoothingEnabled = antiAlias;
    ctx.imageSmoothingQuality = "high";

    // Fill background (typically black for VACE)
    ctx.fillStyle = backgroundColor;
    ctx.fillRect(0, 0, width, height);

    // Collect all states
    const states = new Map<string, PathFollowerState>();

    // Render each path follower
    for (const follower of this.pathFollowers) {
      const config = follower.getConfig();
      const state = follower.getStateAtFrame(frameNumber);
      states.set(config.id, state);
      renderShape(ctx, state, config);
    }

    return {
      frameNumber,
      canvas,
      states,
    };
  }

  /**
   * Render all frames
   */
  *renderAllFrames(): Generator<VACEFrame> {
    const { startFrame, endFrame } = this.config;

    for (let frame = startFrame; frame <= endFrame; frame++) {
      yield this.renderFrame(frame);
    }
  }

  /**
   * Get frame count
   */
  getFrameCount(): number {
    return this.config.endFrame - this.config.startFrame + 1;
  }

  /**
   * Get path statistics for each follower
   */
  getPathStats(): Array<{
    id: string;
    length: number;
    speed: number;
    duration: number;
  }> {
    return this.pathFollowers.map((follower) => {
      const config = follower.getConfig();
      return {
        id: config.id,
        length: follower.getPathLength(),
        speed: follower.getSpeed(),
        duration: config.duration,
      };
    });
  }

  /**
   * Export to ImageData array (for video encoding)
   */
  exportToImageDataArray(): ImageData[] {
    const frames: ImageData[] = [];
    const { width, height } = this.config;

    for (const frame of this.renderAllFrames()) {
      const ctx = frame.canvas.getContext("2d")!;
      frames.push(ctx.getImageData(0, 0, width, height));
    }

    return frames;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                  // convenience // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a simple path follower from spline control points
 * Speed is automatically calculated from path length and duration
 */
export function createPathFollower(
  id: string,
  controlPoints: SplineControlPoint[],
  options: Partial<PathFollowerConfig> = {},
): PathFollowerConfig {
  // Type proof: closed ∈ boolean | undefined → boolean
  const closed =
    typeof options.closed === "boolean" ? options.closed : false;

  // Type proof: shape ∈ PathFollowerShape | undefined → PathFollowerShape
  const validShapes: PathFollowerShape[] = [
    "circle",
    "square",
    "triangle",
    "diamond",
    "arrow",
    "custom",
  ];
  const shape =
    typeof options.shape === "string" &&
    validShapes.includes(options.shape as PathFollowerShape)
      ? (options.shape as PathFollowerShape)
      : "circle";

  // Type proof: size ∈ [number, number] | undefined → [number, number]
  const size =
    Array.isArray(options.size) &&
    options.size.length === 2 &&
    isFiniteNumber(options.size[0]) &&
    isFiniteNumber(options.size[1]) &&
    options.size[0] > 0 &&
    options.size[1] > 0
      ? [
          Math.max(1, Math.min(10000, options.size[0])),
          Math.max(1, Math.min(10000, options.size[1])),
        ] as [number, number]
      : [20, 20] as [number, number];

  // Type proof: fillColor ∈ string | undefined → string
  const fillColor =
    typeof options.fillColor === "string" && options.fillColor.length > 0
      ? options.fillColor
      : "#FFFFFF";

  // Type proof: startFrame ∈ number | undefined → number
  const startFrame = isFiniteNumber(options.startFrame)
    ? Math.max(0, Math.floor(options.startFrame))
    : 0;

  // Type proof: duration ∈ number | undefined → number
  const duration = isFiniteNumber(options.duration)
    ? Math.max(1, Math.floor(options.duration))
    : 60;

  // Type proof: easing ∈ PathFollowerEasing | undefined → PathFollowerEasing
  const validEasings: PathFollowerEasing[] = [
    "linear",
    "ease-in",
    "ease-out",
    "ease-in-out",
    "ease-in-cubic",
    "ease-out-cubic",
  ];
  const easing =
    typeof options.easing === "string" &&
    validEasings.includes(options.easing as PathFollowerEasing)
      ? (options.easing as PathFollowerEasing)
      : "ease-in-out";

  // Type proof: alignToPath ∈ boolean | undefined → boolean
  const alignToPath =
    typeof options.alignToPath === "boolean" ? options.alignToPath : true;

  // Type proof: rotationOffset ∈ number | undefined → number
  const rotationOffset = isFiniteNumber(options.rotationOffset)
    ? options.rotationOffset
    : 0;

  // Type proof: loop ∈ boolean | undefined → boolean
  const loop = typeof options.loop === "boolean" ? options.loop : false;

  // Type proof: loopMode ∈ "restart" | "pingpong" | undefined → "restart" | "pingpong"
  const validLoopModes: ("restart" | "pingpong")[] = ["restart", "pingpong"];
  const loopMode =
    typeof options.loopMode === "string" &&
    validLoopModes.includes(options.loopMode)
      ? options.loopMode
      : "restart";

  // Type proof: scaleStart ∈ number | undefined → number
  const scaleStart = isFiniteNumber(options.scaleStart)
    ? Math.max(0, Math.min(10, options.scaleStart))
    : 1;

  // Type proof: scaleEnd ∈ number | undefined → number
  const scaleEnd = isFiniteNumber(options.scaleEnd)
    ? Math.max(0, Math.min(10, options.scaleEnd))
    : 1;

  // Type proof: opacityStart ∈ number | undefined → number
  const opacityStart = isFiniteNumber(options.opacityStart)
    ? Math.max(0, Math.min(1, options.opacityStart))
    : 1;

  // Type proof: opacityEnd ∈ number | undefined → number
  const opacityEnd = isFiniteNumber(options.opacityEnd)
    ? Math.max(0, Math.min(1, options.opacityEnd))
    : 1;

  return {
    id,
    controlPoints,
    closed,
    shape,
    size,
    fillColor,
    strokeColor: options.strokeColor,
    strokeWidth: options.strokeWidth,
    startFrame,
    duration,
    easing,
    alignToPath,
    rotationOffset,
    loop,
    loopMode,
    scaleStart,
    scaleEnd,
    opacityStart,
    opacityEnd,
  };
}

/**
 * Create VACE export config with defaults
 */
export function createVACEExportConfig(
  pathFollowers: PathFollowerConfig[],
  options: Partial<VACEExportConfig> = {},
): VACEExportConfig {
  // Type proof: width ∈ number | undefined → number
  const width = isFiniteNumber(options.width)
    ? Math.max(1, Math.min(8192, Math.floor(options.width)))
    : 512;

  // Type proof: height ∈ number | undefined → number
  const height = isFiniteNumber(options.height)
    ? Math.max(1, Math.min(8192, Math.floor(options.height)))
    : 512;

  // Type proof: startFrame ∈ number | undefined → number
  const startFrame = isFiniteNumber(options.startFrame)
    ? Math.max(0, Math.floor(options.startFrame))
    : 0;

  // Type proof: endFrame ∈ number | undefined → number
  const endFrame = isFiniteNumber(options.endFrame)
    ? Math.max(startFrame, Math.floor(options.endFrame))
    : 80;

  // Type proof: frameRate ∈ number | undefined → number
  const frameRate = isFiniteNumber(options.frameRate)
    ? Math.max(1, Math.min(120, options.frameRate))
    : 16;

  // Type proof: backgroundColor ∈ string | undefined → string
  const backgroundColor =
    typeof options.backgroundColor === "string" &&
    options.backgroundColor.length > 0
      ? options.backgroundColor
      : "#000000";

  // Type proof: outputFormat ∈ "canvas" | "webm" | "frames" | undefined → "canvas" | "webm" | "frames"
  const validFormats: ("canvas" | "webm" | "frames")[] = [
    "canvas",
    "webm",
    "frames",
  ];
  const outputFormat =
    typeof options.outputFormat === "string" &&
    validFormats.includes(options.outputFormat)
      ? options.outputFormat
      : "canvas";

  // Type proof: antiAlias ∈ boolean | undefined → boolean
  const antiAlias =
    typeof options.antiAlias === "boolean" ? options.antiAlias : true;

  return {
    width,
    height,
    startFrame,
    endFrame,
    frameRate,
    backgroundColor,
    pathFollowers,
    outputFormat,
    antiAlias,
  };
}

/**
 * Calculate duration needed for a specific speed (pixels per frame)
 */
export function calculateDurationForSpeed(
  pathLength: number,
  pixelsPerFrame: number,
): number {
  return Math.ceil(pathLength / pixelsPerFrame);
}

/**
 * Calculate speed given path length and duration
 */
export function calculateSpeed(
  pathLength: number,
  durationFrames: number,
): number {
  return pathLength / durationFrames;
}

/**
 * Convert SplineLayer data to PathFollowerConfig
 */
export function splineLayerToPathFollower(
  layerId: string,
  controlPoints: SplineControlPoint[],
  closed: boolean,
  totalFrames: number,
  options: Partial<PathFollowerConfig> = {},
): PathFollowerConfig {
  return createPathFollower(layerId, controlPoints, {
    closed,
    duration: totalFrames,
    ...options,
  });
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  PathFollower,
  VACEControlExporter,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
};
