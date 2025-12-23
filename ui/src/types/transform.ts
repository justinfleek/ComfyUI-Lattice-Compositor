// ============================================================
// TRANSFORM TYPES - Layer transforms and motion blur
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import type { AnimatableProperty } from './animation';
import { createAnimatableProperty } from './animation';

// ============================================================
// VECTOR TYPES
// ============================================================

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

export interface Vec2 {
  x: number;
  y: number;
}

// ============================================================
// LAYER TRANSFORM
// ============================================================

export interface LayerTransform {
  // Position can be {x,y} or {x,y,z} depending on threeD flag
  position: AnimatableProperty<{ x: number; y: number; z?: number }>;

  // Origin point for rotation/scale (new name, replaces anchorPoint)
  origin: AnimatableProperty<{ x: number; y: number; z?: number }>;

  /** @deprecated Use 'origin' instead. Kept for backwards compatibility. */
  anchorPoint?: AnimatableProperty<{ x: number; y: number; z?: number }>;

  scale: AnimatableProperty<{ x: number; y: number; z?: number }>;

  // 2D Rotation
  rotation: AnimatableProperty<number>;

  // 3D Rotations (Only active if threeD is true)
  orientation?: AnimatableProperty<{ x: number; y: number; z: number }>;
  rotationX?: AnimatableProperty<number>;
  rotationY?: AnimatableProperty<number>;
  rotationZ?: AnimatableProperty<number>;
}

// ============================================================
// MOTION BLUR SETTINGS
// ============================================================

export type MotionBlurType =
  | 'standard'     // Standard shutter-based blur
  | 'pixel'        // Pixel motion blur (analyzes frame differences)
  | 'directional'  // Directional blur (fixed direction)
  | 'radial'       // Radial blur (spin/zoom from center)
  | 'vector'       // Vector-based (uses velocity data)
  | 'adaptive';    // Auto-selects based on motion

export interface LayerMotionBlurSettings {
  /** Blur type */
  type: MotionBlurType;
  /** Shutter angle in degrees (0-720, 180 = standard film) */
  shutterAngle: number;
  /** Shutter phase offset (-180 to 180) */
  shutterPhase: number;
  /** Samples per frame (2-64, higher = smoother but slower) */
  samplesPerFrame: number;
  /** For directional blur: angle in degrees */
  direction?: number;
  /** For directional blur: blur length in pixels */
  blurLength?: number;
  /** For radial blur: 'spin' or 'zoom' */
  radialMode?: 'spin' | 'zoom';
  /** For radial blur: center point (0-1 normalized) */
  radialCenterX?: number;
  radialCenterY?: number;
  /** For radial blur: amount (0-100) */
  radialAmount?: number;
}

// ============================================================
// 3D MATERIAL OPTIONS (Industry Standard)
// ============================================================

export interface LayerMaterialOptions {
  /** Whether this layer casts shadows */
  castsShadows: 'off' | 'on' | 'only';
  /** Light transmission percentage (0-100) */
  lightTransmission: number;
  /** Whether this layer accepts shadows from other layers */
  acceptsShadows: boolean;
  /** Whether this layer is affected by lights */
  acceptsLights: boolean;
  /** Ambient light response (0-100%) */
  ambient: number;
  /** Diffuse light response (0-100%) */
  diffuse: number;
  /** Specular highlight intensity (0-100%) */
  specularIntensity: number;
  /** Specular highlight shininess (0-100%) */
  specularShininess: number;
  /** Metallic appearance (0-100%) */
  metal: number;
}

// ============================================================
// AUTO-ORIENT AND PATH FOLLOWING
// ============================================================

/**
 * Auto-Orient Mode - How a layer orients itself in 3D space
 */
export type AutoOrientMode = 'off' | 'toCamera' | 'alongPath' | 'toPointOfInterest';

/**
 * Follow Path Constraint - Position a layer along a path/spline layer
 */
export interface FollowPathConstraint {
  /** Enable/disable the constraint */
  enabled: boolean;

  /** ID of the path or spline layer to follow */
  pathLayerId: string;

  /** Progress along the path (0 = start, 1 = end) - ANIMATABLE */
  progress: AnimatableProperty<number>;

  /** Perpendicular offset from the path (pixels) - positive = right of tangent */
  offset: AnimatableProperty<number>;

  /** Offset distance along the path (0-1 normalized) */
  tangentOffset: number;

  /** Auto-orient layer rotation to path tangent */
  autoOrient: boolean;

  /** Additional rotation offset when auto-orienting (degrees) */
  rotationOffset: AnimatableProperty<number>;

  /** Banking/tilt on curves (like a car on a racetrack) */
  banking: AnimatableProperty<number>;

  /** Loop behavior when progress goes beyond 0-1 */
  loopMode: 'clamp' | 'loop' | 'pingpong';
}

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Create default layer transform
 */
export function createDefaultTransform(): LayerTransform {
  const originProp = createAnimatableProperty('origin', { x: 0, y: 0, z: 0 }, 'vector3');
  return {
    position: createAnimatableProperty('position', { x: 0, y: 0, z: 0 }, 'vector3'),
    origin: originProp,
    // @deprecated alias for backwards compatibility
    anchorPoint: originProp,
    scale: createAnimatableProperty('scale', { x: 100, y: 100, z: 100 }, 'vector3'),
    rotation: createAnimatableProperty('rotation', 0, 'number'),
    // 3D rotation properties (always present for consistent structure)
    orientation: createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3'),
    rotationX: createAnimatableProperty('rotationX', 0, 'number'),
    rotationY: createAnimatableProperty('rotationY', 0, 'number'),
    rotationZ: createAnimatableProperty('rotationZ', 0, 'number')
  };
}

/**
 * Normalize a layer transform to use the new 'origin' property.
 * Handles migration from 'anchorPoint' to 'origin'.
 */
export function normalizeLayerTransform(transform: LayerTransform): LayerTransform {
  // If origin is missing but anchorPoint exists, use anchorPoint as origin
  if (!transform.origin && transform.anchorPoint) {
    transform.origin = transform.anchorPoint;
  }
  // Ensure both exist for backwards compatibility
  if (transform.origin && !transform.anchorPoint) {
    transform.anchorPoint = transform.origin;
  }
  return transform;
}

/**
 * Create default Follow Path constraint
 */
export function createFollowPathConstraint(pathLayerId: string): FollowPathConstraint {
  return {
    enabled: true,
    pathLayerId,
    progress: createAnimatableProperty('Progress', 0, 'number'),
    offset: createAnimatableProperty('Offset', 0, 'number'),
    tangentOffset: 0,
    autoOrient: true,
    rotationOffset: createAnimatableProperty('Rotation Offset', 0, 'number'),
    banking: createAnimatableProperty('Banking', 0, 'number'),
    loopMode: 'clamp',
  };
}
