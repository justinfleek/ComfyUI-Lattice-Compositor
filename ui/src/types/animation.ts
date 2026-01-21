// ============================================================
// ANIMATION TYPES - Keyframes, Properties, Interpolation
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

/**
 * Animatable property with optional keyframes and expressions
 */
export interface AnimatableProperty<T> {
  id: string;
  name: string;
  type: "number" | "position" | "color" | "enum" | "vector3";
  value: T; // Default/current value
  animated: boolean;
  keyframes: Keyframe<T>[];
  group?: string; // Property group for timeline organization (e.g., "Transform", "Text", "More Options")

  // Expression system - applies post-interpolation modifications
  expression?: PropertyExpression;
}

/**
 * Expression attached to a property
 * Evaluated after keyframe interpolation to add dynamic behavior
 */
export interface PropertyExpression {
  /** Whether the expression is active */
  enabled: boolean;
  /** Expression type: 'preset' for named expressions, 'custom' for user scripts */
  type: "preset" | "custom";
  /** Expression name (for presets: 'jitter', 'repeatAfter', 'inertia', etc.) */
  name: string;
  /** Expression parameters */
  params: Record<string, number | string | boolean>;
}

/**
 * Keyframe with bezier handles for smooth interpolation
 */
export interface Keyframe<T> {
  id: string;
  frame: number; // 0-80
  value: T;
  interpolation: InterpolationType;
  inHandle: BezierHandle;
  outHandle: BezierHandle;
  controlMode: ControlMode; // How handles behave when dragged
  // Spatial tangents for position keyframes (motion path curves)
  spatialInTangent?: { x: number; y: number; z: number };
  spatialOutTangent?: { x: number; y: number; z: number };
}

/**
 * Bezier handle for keyframe curves
 */
export interface BezierHandle {
  frame: number; // Frame offset from keyframe (negative for inHandle, positive for outHandle)
  value: number; // Value offset from keyframe (can be positive or negative)
  enabled: boolean; // Whether this handle is active (for graph editor)
}

// Control mode for bezier handles (industry standard)
export type ControlMode = "symmetric" | "smooth" | "corner";

// Base interpolation types
export type BaseInterpolationType = "linear" | "bezier" | "hold";

// All easing function names
export type EasingType =
  | "easeInSine"
  | "easeOutSine"
  | "easeInOutSine"
  | "easeInQuad"
  | "easeOutQuad"
  | "easeInOutQuad"
  | "easeInCubic"
  | "easeOutCubic"
  | "easeInOutCubic"
  | "easeInQuart"
  | "easeOutQuart"
  | "easeInOutQuart"
  | "easeInQuint"
  | "easeOutQuint"
  | "easeInOutQuint"
  | "easeInExpo"
  | "easeOutExpo"
  | "easeInOutExpo"
  | "easeInCirc"
  | "easeOutCirc"
  | "easeInOutCirc"
  | "easeInBack"
  | "easeOutBack"
  | "easeInOutBack"
  | "easeInElastic"
  | "easeOutElastic"
  | "easeInOutElastic"
  | "easeInBounce"
  | "easeOutBounce"
  | "easeInOutBounce";

// Combined interpolation type (base types + easing functions)
export type InterpolationType = BaseInterpolationType | EasingType;

// ============================================================
// PROPERTY VALUE TYPES
// ============================================================

/**
 * All possible values that can be stored in keyframes.
 * Used for type-safe clipboard operations and generic property handling.
 */
export type PropertyValue =
  | number // Opacity, rotation, scalar values
  | string // Enum values, hex colors
  | boolean // Boolean flags (e.g., _requiresSimulation)
  | { x: number; y: number } // Vec2 (2D position/scale)
  | { x: number; y: number; z?: number } // Position/Scale (optional z)
  | { x: number; y: number; z: number } // Vec3 (orientation, 3D vectors)
  | { r: number; g: number; b: number; a: number }; // RGBA color

/**
 * Clipboard keyframe entry with property path context
 */
export interface ClipboardKeyframe {
  layerId: string;
  propertyPath: string;
  keyframes: Keyframe<PropertyValue>[];
}

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Create a new animatable property with default values
 */
export function createAnimatableProperty<T>(
  name: string,
  value: T,
  type: "number" | "position" | "color" | "enum" | "vector3" = "number",
  group?: string,
): AnimatableProperty<T> {
  return {
    id: `prop_${name}_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
    group,
  };
}

/**
 * Create a default keyframe
 * 
 * BEZIER HANDLE DEFAULTS:
 * - inHandle: { frame: -5, value: 0, enabled: true }
 * - outHandle: { frame: 5, value: 0, enabled: true }
 * 
 * The ±5 frame offset creates a gentle ease curve by default.
 * At 30fps: 5 frames = ~0.167 seconds of influence
 * At 16fps: 5 frames = ~0.313 seconds of influence
 * 
 * A value of 0 means flat tangent (no acceleration at the keyframe).
 * 
 * These defaults were chosen to provide reasonable ease-in/ease-out
 * behavior without requiring manual handle adjustment for most animations.
 * 
 * @throws Error if frame is NaN or Infinity (prevents silent interpolation failures)
 */
export function createKeyframe<T>(
  frame: number,
  value: T,
  interpolation: InterpolationType = "linear",
): Keyframe<T> {
  // Validate frame to prevent silent interpolation failures
  // NaN/Infinity frames cause incorrect animation output without any error
  if (!Number.isFinite(frame)) {
    throw new Error(
      `Invalid keyframe frame: ${frame}. Frame must be a finite number.`,
    );
  }

  return {
    id: `kf_${frame}_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
    frame,
    value,
    interpolation,
    // Bezier handles: ±5 frame offset, flat slope (value: 0)
    // Creates gentle ease-in/ease-out by default
    inHandle: { frame: -5, value: 0, enabled: true },
    outHandle: { frame: 5, value: 0, enabled: true },
    controlMode: "smooth",
  };
}
