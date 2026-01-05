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

import type { ControlPoint } from "@/types/spline";
import { createBezierCurve } from "../arcLength";

// Extended type with optional z coordinate for 3D curves
type SplineControlPoint = ControlPoint & {
  z?: number;
  handleIn?: { x: number; y: number; z?: number } | null;
  handleOut?: { x: number; y: number; z?: number } | null;
};

import * as THREE from "three";

// ============================================================================
// TYPES
// ============================================================================

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

// ============================================================================
// EASING FUNCTIONS
// ============================================================================

const EASING_FUNCTIONS: Record<PathFollowerEasing, (t: number) => number> = {
  linear: (t) => t,
  "ease-in": (t) => t * t,
  "ease-out": (t) => t * (2 - t),
  "ease-in-out": (t) => (t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t),
  "ease-in-cubic": (t) => t * t * t,
  "ease-out-cubic": (t) => --t * t * t + 1,
};

// ============================================================================
// PATH FOLLOWER CLASS
// ============================================================================

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

      // Create cubic bezier curve from control points
      const curve = createBezierCurve(
        { x: p0.x, y: p0.y, z: p0.z || 0 },
        {
          x: p0.x + (p0.handleOut?.x || 0),
          y: p0.y + (p0.handleOut?.y || 0),
          z: (p0.z || 0) + (p0.handleOut?.z || 0),
        },
        {
          x: p1.x + (p1.handleIn?.x || 0),
          y: p1.y + (p1.handleIn?.y || 0),
          z: (p1.z || 0) + (p1.handleIn?.z || 0),
        },
        { x: p1.x, y: p1.y, z: p1.z || 0 },
      );

      curvePath.add(curve);
    }

    // Close path if needed
    if (closed && controlPoints.length > 2) {
      const last = controlPoints[controlPoints.length - 1];
      const first = controlPoints[0];

      const closingCurve = createBezierCurve(
        { x: last.x, y: last.y, z: last.z || 0 },
        {
          x: last.x + (last.handleOut?.x || 0),
          y: last.y + (last.handleOut?.y || 0),
          z: (last.z || 0) + (last.handleOut?.z || 0),
        },
        {
          x: first.x + (first.handleIn?.x || 0),
          y: first.y + (first.handleIn?.y || 0),
          z: (first.z || 0) + (first.handleIn?.z || 0),
        },
        { x: first.x, y: first.y, z: first.z || 0 },
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
    // THREE.js CurvePath.getPointAt uses arc-length parameterization
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

// ============================================================================
// SHAPE RENDERING
// ============================================================================

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
  ctx.globalAlpha = state.opacity;

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

// ============================================================================
// VACE EXPORT RENDERER
// ============================================================================

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

// ============================================================================
// CONVENIENCE FUNCTIONS
// ============================================================================

/**
 * Create a simple path follower from spline control points
 * Speed is automatically calculated from path length and duration
 */
export function createPathFollower(
  id: string,
  controlPoints: SplineControlPoint[],
  options: Partial<PathFollowerConfig> = {},
): PathFollowerConfig {
  return {
    id,
    controlPoints,
    closed: options.closed ?? false,
    shape: options.shape ?? "circle",
    size: options.size ?? [20, 20],
    fillColor: options.fillColor ?? "#FFFFFF",
    strokeColor: options.strokeColor,
    strokeWidth: options.strokeWidth,
    startFrame: options.startFrame ?? 0,
    duration: options.duration ?? 60,
    easing: options.easing ?? "ease-in-out",
    alignToPath: options.alignToPath ?? true,
    rotationOffset: options.rotationOffset ?? 0,
    loop: options.loop ?? false,
    loopMode: options.loopMode ?? "restart",
    scaleStart: options.scaleStart ?? 1,
    scaleEnd: options.scaleEnd ?? 1,
    opacityStart: options.opacityStart ?? 1,
    opacityEnd: options.opacityEnd ?? 1,
  };
}

/**
 * Create VACE export config with defaults
 */
export function createVACEExportConfig(
  pathFollowers: PathFollowerConfig[],
  options: Partial<VACEExportConfig> = {},
): VACEExportConfig {
  return {
    width: options.width ?? 512,
    height: options.height ?? 512,
    startFrame: options.startFrame ?? 0,
    endFrame: options.endFrame ?? 80,
    frameRate: options.frameRate ?? 16,
    backgroundColor: options.backgroundColor ?? "#000000",
    pathFollowers,
    outputFormat: options.outputFormat ?? "canvas",
    antiAlias: options.antiAlias ?? true,
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

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  PathFollower,
  VACEControlExporter,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
};
