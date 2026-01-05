// ============================================================
// TRANSFORM TYPES - Layer transforms and motion blur
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import type { AnimatableProperty } from "./animation";
import { createAnimatableProperty } from "./animation";

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

  // Separate dimension properties (when separateDimensions.position is true)
  positionX?: AnimatableProperty<number>;
  positionY?: AnimatableProperty<number>;
  positionZ?: AnimatableProperty<number>;

  // Origin point for rotation/scale (new name, replaces anchorPoint)
  origin: AnimatableProperty<{ x: number; y: number; z?: number }>;

  /** @deprecated Use 'origin' instead. Kept for backwards compatibility. */
  anchorPoint?: AnimatableProperty<{ x: number; y: number; z?: number }>;

  scale: AnimatableProperty<{ x: number; y: number; z?: number }>;

  // Separate scale properties (when separateDimensions.scale is true)
  scaleX?: AnimatableProperty<number>;
  scaleY?: AnimatableProperty<number>;
  scaleZ?: AnimatableProperty<number>;

  // 2D Rotation
  rotation: AnimatableProperty<number>;

  // 3D Rotations (Only active if threeD is true)
  orientation?: AnimatableProperty<{ x: number; y: number; z: number }>;
  rotationX?: AnimatableProperty<number>;
  rotationY?: AnimatableProperty<number>;
  rotationZ?: AnimatableProperty<number>;

  // Separate dimensions flags - when true, use individual X/Y/Z properties
  separateDimensions?: {
    position: boolean;
    scale: boolean;
  };
}

// ============================================================
// MOTION BLUR SETTINGS
// ============================================================

export type MotionBlurType =
  | "standard" // Standard shutter-based blur
  | "pixel" // Pixel motion blur (analyzes frame differences)
  | "directional" // Directional blur (fixed direction)
  | "radial" // Radial blur (spin/zoom from center)
  | "vector" // Vector-based (uses velocity data)
  | "adaptive"; // Auto-selects based on motion

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
  radialMode?: "spin" | "zoom";
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
  castsShadows: "off" | "on" | "only";
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
export type AutoOrientMode =
  | "off"
  | "toCamera"
  | "alongPath"
  | "toPointOfInterest";

/**
 * Follow Path Constraint - Position a layer along a path/spline layer
 */
export interface FollowPathConstraint {
  /** Enable/disable the constraint */
  enabled: boolean;

  /** ID of the path or spline layer to follow (empty string if no target) */
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
  loopMode: "clamp" | "loop" | "pingpong";
}

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Create default layer transform
 */
export function createDefaultTransform(): LayerTransform {
  const originProp = createAnimatableProperty(
    "origin",
    { x: 0, y: 0, z: 0 },
    "vector3",
  );
  return {
    position: createAnimatableProperty(
      "position",
      { x: 0, y: 0, z: 0 },
      "vector3",
    ),
    origin: originProp,
    // @deprecated alias for backwards compatibility
    anchorPoint: originProp,
    scale: createAnimatableProperty(
      "scale",
      { x: 100, y: 100, z: 100 },
      "vector3",
    ),
    rotation: createAnimatableProperty("rotation", 0, "number"),
    // 3D rotation properties (always present for consistent structure)
    orientation: createAnimatableProperty(
      "orientation",
      { x: 0, y: 0, z: 0 },
      "vector3",
    ),
    rotationX: createAnimatableProperty("rotationX", 0, "number"),
    rotationY: createAnimatableProperty("rotationY", 0, "number"),
    rotationZ: createAnimatableProperty("rotationZ", 0, "number"),
  };
}

/**
 * Normalize a layer transform to use the new 'origin' property.
 * Handles migration from 'anchorPoint' to 'origin'.
 */
export function normalizeLayerTransform(
  transform: LayerTransform,
): LayerTransform {
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
export function createFollowPathConstraint(
  pathLayerId: string,
): FollowPathConstraint {
  return {
    enabled: true,
    pathLayerId,
    progress: createAnimatableProperty("Progress", 0, "number"),
    offset: createAnimatableProperty("Offset", 0, "number"),
    tangentOffset: 0,
    autoOrient: true,
    rotationOffset: createAnimatableProperty("Rotation Offset", 0, "number"),
    banking: createAnimatableProperty("Banking", 0, "number"),
    loopMode: "clamp",
  };
}

// ============================================================
// SEPARATE DIMENSIONS
// ============================================================

/**
 * Separate position into individual X, Y, Z properties.
 * Copies keyframes from the combined position property to separate dimension properties.
 */
export function separatePositionDimensions(transform: LayerTransform): void {
  const pos = transform.position;
  const currentValue = pos.value;

  // Create separate X, Y, Z properties
  transform.positionX = createAnimatableProperty(
    "Position X",
    currentValue.x,
    "number",
  );
  transform.positionY = createAnimatableProperty(
    "Position Y",
    currentValue.y,
    "number",
  );
  transform.positionZ = createAnimatableProperty(
    "Position Z",
    currentValue.z ?? 0,
    "number",
  );

  // Copy keyframes to separate properties
  if (pos.animated && pos.keyframes.length > 0) {
    transform.positionX.animated = true;
    transform.positionY.animated = true;
    transform.positionZ.animated = true;

    pos.keyframes.forEach((kf) => {
      const val = kf.value;

      // X keyframe
      transform.positionX?.keyframes.push({
        ...kf,
        id: `${kf.id}_x`,
        value: val.x,
      });

      // Y keyframe
      transform.positionY?.keyframes.push({
        ...kf,
        id: `${kf.id}_y`,
        value: val.y,
      });

      // Z keyframe
      transform.positionZ?.keyframes.push({
        ...kf,
        id: `${kf.id}_z`,
        value: val.z ?? 0,
      });
    });
  }

  // Set flag
  if (!transform.separateDimensions) {
    transform.separateDimensions = { position: false, scale: false };
  }
  transform.separateDimensions.position = true;
}

/**
 * Link position dimensions back into a combined property.
 * Merges keyframes from X, Y, Z into the combined position property.
 */
export function linkPositionDimensions(transform: LayerTransform): void {
  if (!transform.positionX || !transform.positionY) return;

  const posX = transform.positionX;
  const posY = transform.positionY;
  const posZ = transform.positionZ;

  // Update current value
  transform.position.value = {
    x: posX.value,
    y: posY.value,
    z: posZ?.value ?? 0,
  };

  // Merge keyframes - collect all unique frames
  const allFrames = new Set<number>();
  posX.keyframes.forEach((kf) => allFrames.add(kf.frame));
  posY.keyframes.forEach((kf) => allFrames.add(kf.frame));
  posZ?.keyframes.forEach((kf) => allFrames.add(kf.frame));

  // Clear existing keyframes
  transform.position.keyframes = [];
  transform.position.animated = allFrames.size > 0;

  // Create combined keyframes at each frame
  const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

  sortedFrames.forEach((frame) => {
    const xKf = posX.keyframes.find((k) => k.frame === frame);
    const yKf = posY.keyframes.find((k) => k.frame === frame);
    const zKf = posZ?.keyframes.find((k) => k.frame === frame);

    // Get values (interpolate if keyframe doesn't exist at this frame)
    const xVal =
      xKf?.value ?? getInterpolatedValue(posX.keyframes, frame) ?? posX.value;
    const yVal =
      yKf?.value ?? getInterpolatedValue(posY.keyframes, frame) ?? posY.value;
    const zVal =
      zKf?.value ??
      getInterpolatedValue(posZ?.keyframes ?? [], frame) ??
      posZ?.value ??
      0;

    // Use the first available keyframe as template for handles/interpolation
    const templateKf = xKf || yKf || zKf;

    transform.position.keyframes.push({
      id: `kf_pos_${frame}_${Date.now()}`,
      frame,
      value: { x: xVal, y: yVal, z: zVal },
      interpolation: templateKf?.interpolation ?? "linear",
      inHandle: templateKf?.inHandle ?? { frame: -5, value: 0, enabled: false },
      outHandle: templateKf?.outHandle ?? {
        frame: 5,
        value: 0,
        enabled: false,
      },
      controlMode: templateKf?.controlMode ?? "smooth",
    });
  });

  // Clear separate properties
  delete transform.positionX;
  delete transform.positionY;
  delete transform.positionZ;

  // Update flag
  if (transform.separateDimensions) {
    transform.separateDimensions.position = false;
  }
}

/**
 * Separate scale into individual X, Y, Z properties.
 */
export function separateScaleDimensions(transform: LayerTransform): void {
  const scale = transform.scale;
  const currentValue = scale.value;

  transform.scaleX = createAnimatableProperty(
    "Scale X",
    currentValue.x,
    "number",
  );
  transform.scaleY = createAnimatableProperty(
    "Scale Y",
    currentValue.y,
    "number",
  );
  transform.scaleZ = createAnimatableProperty(
    "Scale Z",
    currentValue.z ?? 100,
    "number",
  );

  if (scale.animated && scale.keyframes.length > 0) {
    transform.scaleX.animated = true;
    transform.scaleY.animated = true;
    transform.scaleZ.animated = true;

    scale.keyframes.forEach((kf) => {
      const val = kf.value;

      transform.scaleX?.keyframes.push({
        ...kf,
        id: `${kf.id}_x`,
        value: val.x,
      });

      transform.scaleY?.keyframes.push({
        ...kf,
        id: `${kf.id}_y`,
        value: val.y,
      });

      transform.scaleZ?.keyframes.push({
        ...kf,
        id: `${kf.id}_z`,
        value: val.z ?? 100,
      });
    });
  }

  if (!transform.separateDimensions) {
    transform.separateDimensions = { position: false, scale: false };
  }
  transform.separateDimensions.scale = true;
}

/**
 * Link scale dimensions back into a combined property.
 */
export function linkScaleDimensions(transform: LayerTransform): void {
  if (!transform.scaleX || !transform.scaleY) return;

  const scaleX = transform.scaleX;
  const scaleY = transform.scaleY;
  const scaleZ = transform.scaleZ;

  transform.scale.value = {
    x: scaleX.value,
    y: scaleY.value,
    z: scaleZ?.value ?? 100,
  };

  const allFrames = new Set<number>();
  scaleX.keyframes.forEach((kf) => allFrames.add(kf.frame));
  scaleY.keyframes.forEach((kf) => allFrames.add(kf.frame));
  scaleZ?.keyframes.forEach((kf) => allFrames.add(kf.frame));

  transform.scale.keyframes = [];
  transform.scale.animated = allFrames.size > 0;

  const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

  sortedFrames.forEach((frame) => {
    const xKf = scaleX.keyframes.find((k) => k.frame === frame);
    const yKf = scaleY.keyframes.find((k) => k.frame === frame);
    const zKf = scaleZ?.keyframes.find((k) => k.frame === frame);

    const xVal =
      xKf?.value ??
      getInterpolatedValue(scaleX.keyframes, frame) ??
      scaleX.value;
    const yVal =
      yKf?.value ??
      getInterpolatedValue(scaleY.keyframes, frame) ??
      scaleY.value;
    const zVal =
      zKf?.value ??
      getInterpolatedValue(scaleZ?.keyframes ?? [], frame) ??
      scaleZ?.value ??
      100;

    const templateKf = xKf || yKf || zKf;

    transform.scale.keyframes.push({
      id: `kf_scale_${frame}_${Date.now()}`,
      frame,
      value: { x: xVal, y: yVal, z: zVal },
      interpolation: templateKf?.interpolation ?? "linear",
      inHandle: templateKf?.inHandle ?? { frame: -5, value: 0, enabled: false },
      outHandle: templateKf?.outHandle ?? {
        frame: 5,
        value: 0,
        enabled: false,
      },
      controlMode: templateKf?.controlMode ?? "smooth",
    });
  });

  delete transform.scaleX;
  delete transform.scaleY;
  delete transform.scaleZ;

  if (transform.separateDimensions) {
    transform.separateDimensions.scale = false;
  }
}

/**
 * Helper: Get interpolated value at a frame from keyframes array
 */
function getInterpolatedValue(
  keyframes: Array<{ frame: number; value: number }>,
  frame: number,
): number | undefined {
  if (keyframes.length === 0) return undefined;
  if (keyframes.length === 1) return keyframes[0].value;

  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Before first keyframe
  if (frame <= sorted[0].frame) return sorted[0].value;

  // After last keyframe
  if (frame >= sorted[sorted.length - 1].frame)
    return sorted[sorted.length - 1].value;

  // Find surrounding keyframes
  for (let i = 0; i < sorted.length - 1; i++) {
    if (sorted[i].frame <= frame && sorted[i + 1].frame > frame) {
      const t =
        (frame - sorted[i].frame) / (sorted[i + 1].frame - sorted[i].frame);
      return sorted[i].value + (sorted[i + 1].value - sorted[i].value) * t;
    }
  }

  return undefined;
}
