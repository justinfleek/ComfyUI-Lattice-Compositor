// ============================================================
// SPLINE TYPES - Bezier paths, control points, path effects
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import type { AnimatableProperty } from "./animation";
import { createAnimatableProperty } from "./animation";

// ============================================================
// CONTROL POINTS
// ============================================================

/**
 * Static control point - for non-animated splines (legacy/default)
 */
export interface ControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number; // Sampled from depth map
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: "corner" | "smooth" | "symmetric";
  group?: string; // Group ID for grouped animations (e.g., "head", "arm_left")
}

/**
 * Animated control point - for keyframe-animated splines
 * x and y are AnimatableProperty<number> enabling per-frame interpolation
 */
export interface AnimatableControlPoint {
  id: string;
  x: AnimatableProperty<number>;
  y: AnimatableProperty<number>;
  depth?: AnimatableProperty<number>; // Can also be animated in Phase 2
  handleIn: AnimatableHandle | null; // Handles can be animated too
  handleOut: AnimatableHandle | null;
  type: "corner" | "smooth" | "symmetric";
  group?: string; // Group ID for grouped animations
}

/**
 * Animated bezier handle - for advanced handle animation
 */
export interface AnimatableHandle {
  x: AnimatableProperty<number>;
  y: AnimatableProperty<number>;
}

/**
 * Evaluated control point at a specific frame
 * Result of interpolating an AnimatableControlPoint
 */
export interface EvaluatedControlPoint {
  id: string;
  x: number;
  y: number;
  depth: number;
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: "corner" | "smooth" | "symmetric";
  group?: string; // Group ID for grouped animations
}

// ============================================================
// SPLINE DATA
// ============================================================

/** Gradient stop for stroke gradients */
export interface SplineGradientStop {
  position: number; // 0-1
  color: { r: number; g: number; b: number; a: number }; // RGBA color
}

/** Gradient definition for stroke gradients */
export interface SplineStrokeGradient {
  type: "linear" | "radial";
  stops: SplineGradientStop[];
  followPath?: boolean; // Gradient follows the stroke path (for linear gradients)
  spread?: number; // Gradient spread along path (0-100%, default 100)
  offsetKeyframes?: Array<{ frame: number; value: number }>; // Animated gradient offset along path
}

export interface SplineData {
  pathData: string; // SVG path commands (M, C, Q, L, Z)
  controlPoints: ControlPoint[];
  closed: boolean;

  // Stroke properties
  strokeType?: "solid" | "gradient"; // Stroke type (default: "solid" when stroke is set)
  stroke: string; // Stroke color hex (used when strokeType is "solid" or undefined)
  strokeGradient?: SplineStrokeGradient; // Gradient definition (used when strokeType is "gradient")
  strokeWidth: number; // Stroke width in pixels
  strokeOpacity?: number; // Stroke opacity 0-100 (default 100)
  lineCap?: "butt" | "round" | "square"; // Line cap style (CODE IS TRUTH - was strokeLineCap)
  lineJoin?: "miter" | "round" | "bevel"; // Line join style (CODE IS TRUTH - was strokeLineJoin)
  strokeMiterLimit?: number; // Miter limit (default 4)

  // Animated Dash properties (CODE IS TRUTH - was strokeDashArray/strokeDashOffset)
  dashArray?: number[] | AnimatableProperty<number[]>; // Dash pattern [dash, gap, ...]
  dashOffset?: number | AnimatableProperty<number>; // Animated dash offset

  // Fill properties
  fill?: string; // Fill color hex (empty = no fill) - made optional per CODE IS TRUTH
  fillOpacity?: number; // Fill opacity 0-100 (default 100)

  // Animated Trim Paths (for draw-on effects)
  trimStart?: number | AnimatableProperty<number>; // Trim start 0-100%
  trimEnd?: number | AnimatableProperty<number>; // Trim end 0-100%
  trimOffset?: number | AnimatableProperty<number>; // Trim offset in degrees

  // Path Effects (applied in order before trim)
  // Uses SplinePathEffectInstance union for proper type narrowing on effect.type
  pathEffects?: SplinePathEffectInstance[];

  // Animated spline support (Phase 1)
  animatedControlPoints?: AnimatableControlPoint[];
  animated?: boolean; // True if using animatedControlPoints

  // Level of Detail (for complex vectors)
  lod?: SplineLODSettings;

  // Mesh Warp deformation pins (primary property)
  warpPins?: import("./meshWarp").WarpPin[];

  /** @deprecated Use warpPins instead */
  puppetPins?: import("./meshWarp").WarpPin[];

  /** Audio-reactive animation configuration */
  audioReactive?: {
    enabled: boolean;
    sourceLayerId: string; // ID of audio layer to react to
    property: string; // Property to animate (e.g., 'scale', 'opacity')
    multiplier: number; // Amplitude multiplier
    smoothing: number; // Frames of smoothing
  };
}

// ============================================================
// PATH LAYER DATA
// Motion path for text-on-path, camera paths, particle emitters
// Unlike SplineData, has NO visual stroke/fill properties
// ============================================================

export interface PathLayerData {
  /** SVG path commands (M, C, Q, L, Z) */
  pathData: string;

  /** Control points defining the path */
  controlPoints: ControlPoint[];

  /** Whether the path is closed */
  closed: boolean;

  /** Show dashed guide line in editor (default: true) */
  showGuide: boolean;

  /** Guide line color (default: '#00FFFF' cyan) */
  guideColor: string;

  /** Guide line dash pattern [dash, gap] */
  guideDashPattern: [number, number];

  /** Animated control points for path morphing */
  animatedControlPoints?: AnimatableControlPoint[];

  /** True if using animatedControlPoints */
  animated?: boolean;
}

// ============================================================
// PATH EFFECTS
// ============================================================

/**
 * Path effect base interface
 */
export interface SplinePathEffect {
  id: string;
  type: SplinePathEffectType;
  enabled: boolean;
  order: number; // Execution order (lower = first)
}

export type SplinePathEffectType =
  | "offsetPath"
  | "roughen"
  | "wiggle"
  | "zigzag"
  | "wave";

/**
 * Offset Path Effect - grow/shrink paths
 */
export interface OffsetPathEffect extends SplinePathEffect {
  type: "offsetPath";
  amount: AnimatableProperty<number>; // Positive = expand, negative = contract
  lineJoin: "miter" | "round" | "bevel";
  miterLimit: AnimatableProperty<number>;
}

/**
 * Roughen Effect - organic hand-drawn look
 */
export interface RoughenEffect extends SplinePathEffect {
  type: "roughen";
  size: AnimatableProperty<number>; // Roughness magnitude
  detail: AnimatableProperty<number>; // Points per segment
  seed: number; // Deterministic randomness
}

/**
 * Wiggle Path Effect - animated jitter
 */
export interface WigglePathEffect extends SplinePathEffect {
  type: "wiggle";
  size: AnimatableProperty<number>;
  detail: AnimatableProperty<number>;
  temporalPhase: AnimatableProperty<number>; // Animated offset for motion
  spatialPhase: AnimatableProperty<number>;
  correlation: AnimatableProperty<number>; // 0-100%
  seed: number;
}

/**
 * ZigZag Effect - decorative zigzag pattern
 */
export interface ZigZagEffect extends SplinePathEffect {
  type: "zigzag";
  size: AnimatableProperty<number>;
  ridgesPerSegment: AnimatableProperty<number>;
  pointType: "corner" | "smooth";
}

/**
 * Wave Effect - sine/triangle/square wave distortion
 */
export interface WaveEffect extends SplinePathEffect {
  type: "wave";
  amplitude: AnimatableProperty<number>;
  frequency: AnimatableProperty<number>;
  phase: AnimatableProperty<number>; // Animated phase for wave motion
  waveType: "sine" | "triangle" | "square";
}

/**
 * Union type for all path effects
 */
export type SplinePathEffectInstance =
  | OffsetPathEffect
  | RoughenEffect
  | WigglePathEffect
  | ZigZagEffect
  | WaveEffect;

// ============================================================
// LEVEL OF DETAIL
// ============================================================

/**
 * Level of Detail settings for complex vectors
 */
export interface SplineLODSettings {
  enabled: boolean;
  mode: "zoom" | "playback" | "both";
  levels: LODLevel[];
  maxPointsForPreview: number;
  simplificationTolerance: number;
  cullingEnabled: boolean;
  cullMargin: number;
}

/**
 * Single LOD level with pre-simplified points
 */
export interface LODLevel {
  tolerance: number;
  controlPoints: ControlPoint[];
  pointCount: number;
  /** Quality index (0 = highest, higher = more simplified) */
  quality?: number;
  /** Complexity metric for this level */
  complexity?: number;
}

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Convert a static ControlPoint to an AnimatableControlPoint
 * Used for migration and enabling animation on existing splines
 */
export function controlPointToAnimatable(
  cp: ControlPoint,
): AnimatableControlPoint {
  return {
    id: cp.id,
    x: createAnimatableProperty("x", cp.x, "number"),
    y: createAnimatableProperty("y", cp.y, "number"),
    depth:
      cp.depth !== undefined
        ? createAnimatableProperty("depth", cp.depth, "number")
        : undefined,
    handleIn: cp.handleIn
      ? {
          x: createAnimatableProperty("handleIn.x", cp.handleIn.x, "number"),
          y: createAnimatableProperty("handleIn.y", cp.handleIn.y, "number"),
        }
      : null,
    handleOut: cp.handleOut
      ? {
          x: createAnimatableProperty("handleOut.x", cp.handleOut.x, "number"),
          y: createAnimatableProperty("handleOut.y", cp.handleOut.y, "number"),
        }
      : null,
    type: cp.type,
    group: cp.group,
  };
}

/**
 * Convert an AnimatableControlPoint back to a static ControlPoint
 * Uses current/default values (not frame-evaluated)
 */
export function animatableToControlPoint(
  acp: AnimatableControlPoint,
): ControlPoint {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const acpDepth = (acp != null && typeof acp === "object" && "depth" in acp && acp.depth != null && typeof acp.depth === "object") ? acp.depth : undefined;
  const depthValue = (acpDepth != null && typeof acpDepth === "object" && "value" in acpDepth && typeof acpDepth.value === "number") ? acpDepth.value : undefined;
  return {
    id: acp.id,
    x: acp.x.value,
    y: acp.y.value,
    depth: depthValue,
    handleIn: acp.handleIn
      ? {
          x: acp.handleIn.x.value,
          y: acp.handleIn.y.value,
        }
      : null,
    handleOut: acp.handleOut
      ? {
          x: acp.handleOut.x.value,
          y: acp.handleOut.y.value,
        }
      : null,
    type: acp.type,
    group: acp.group,
  };
}

/**
 * Create default spline data
 */
export function createDefaultSplineData(): SplineData {
  return {
    pathData: "",
    controlPoints: [],
    closed: false,
    stroke: "#ffffff",
    strokeWidth: 2,
    fill: "",
  };
}

/**
 * Create default path layer data
 */
export function createDefaultPathLayerData(): PathLayerData {
  return {
    pathData: "",
    controlPoints: [],
    closed: false,
    showGuide: true,
    guideColor: "#00FFFF",
    guideDashPattern: [5, 5],
  };
}
