// ============================================================
// TRANSFORM TYPES - Layer transforms and motion blur
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import { isFiniteNumber } from "@/utils/typeGuards";
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
  // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
  const zValue = currentValue.z;
  const z = isFiniteNumber(zValue) ? zValue : 0;
  transform.positionZ = createAnimatableProperty(
    "Position Z",
    z,
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (transform.positionX != null && typeof transform.positionX === "object" && "keyframes" in transform.positionX && Array.isArray(transform.positionX.keyframes)) {
        transform.positionX.keyframes.push({
          ...kf,
          id: `${kf.id}_x`,
          value: val.x,
        });
      }

      // Y keyframe
      if (transform.positionY != null && typeof transform.positionY === "object" && "keyframes" in transform.positionY && Array.isArray(transform.positionY.keyframes)) {
        transform.positionY.keyframes.push({
          ...kf,
          id: `${kf.id}_y`,
          value: val.y,
        });
      }

      // Z keyframe
      if (transform.positionZ != null && typeof transform.positionZ === "object" && "keyframes" in transform.positionZ && Array.isArray(transform.positionZ.keyframes)) {
        transform.positionZ.keyframes.push({
          ...kf,
          id: `${kf.id}_z`,
          // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
          value: (() => {
            const zValue = val.z;
            return isFiniteNumber(zValue) ? zValue : 0;
          })(),
        });
      }
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
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    z: (() => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const zValue = (posZ != null && typeof posZ === "object" && "value" in posZ && typeof posZ.value === "number") ? posZ.value : undefined;
      return isFiniteNumber(zValue) ? zValue : 0;
    })(),
  };

  // Merge keyframes - collect all unique frames
  const allFrames = new Set<number>();
  posX.keyframes.forEach((kf) => allFrames.add(kf.frame));
  posY.keyframes.forEach((kf) => allFrames.add(kf.frame));
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (posZ != null && typeof posZ === "object" && "keyframes" in posZ && Array.isArray(posZ.keyframes)) {
    posZ.keyframes.forEach((kf) => allFrames.add(kf.frame));
  }

  // Clear existing keyframes
  transform.position.keyframes = [];
  transform.position.animated = allFrames.size > 0;

  // Create combined keyframes at each frame
  const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

  sortedFrames.forEach((frame) => {
    const xKf = posX.keyframes.find((k) => k.frame === frame);
    const yKf = posY.keyframes.find((k) => k.frame === frame);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const zKf = (posZ != null && typeof posZ === "object" && "keyframes" in posZ && Array.isArray(posZ.keyframes) && typeof posZ.keyframes.find === "function") ? posZ.keyframes.find((k) => k.frame === frame) : undefined;

    // Get values (interpolate if keyframe doesn't exist at this frame)
    // System F/Omega proof: Validate keyframes exist before calling utility
    // Type proof: keyframes.length ∈ number → number | undefined
    // Mathematical proof: At least one keyframe required for interpolation
    const xInterpolated = posX.keyframes.length > 0 
      ? getInterpolatedValue(posX.keyframes, frame)
      : undefined;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: xKf.value ∈ number | undefined → number (fallback chain: xInterpolated → posX.value)
    const xKfValue = (xKf !== null && typeof xKf === "object" && "value" in xKf && typeof xKf.value === "number" && Number.isFinite(xKf.value)) ? xKf.value : undefined;
    const xVal = (xKfValue !== undefined) ? xKfValue : ((xInterpolated !== undefined && typeof xInterpolated === "number" && Number.isFinite(xInterpolated)) ? xInterpolated : posX.value);
    
    const yInterpolated = posY.keyframes.length > 0
      ? getInterpolatedValue(posY.keyframes, frame)
      : undefined;
    // Pattern match: yKf.value ∈ number | undefined → number (fallback chain: yInterpolated → posY.value)
    const yKfValue = (yKf !== null && typeof yKf === "object" && "value" in yKf && typeof yKf.value === "number" && Number.isFinite(yKf.value)) ? yKf.value : undefined;
    const yVal = (yKfValue !== undefined) ? yKfValue : ((yInterpolated !== undefined && typeof yInterpolated === "number" && Number.isFinite(yInterpolated)) ? yInterpolated : posY.value);
    
    // Pattern match: posZ.keyframes ∈ Keyframe[] | undefined → Keyframe[] (default [])
    const posZData = (posZ !== null && typeof posZ === "object" && "keyframes" in posZ && Array.isArray(posZ.keyframes)) ? posZ.keyframes : undefined;
    const zKeyframes = (posZData !== undefined) ? posZData : [];
    const zInterpolated = zKeyframes.length > 0
      ? getInterpolatedValue(zKeyframes, frame)
      : undefined;
    // Pattern match: zKf.value ∈ number | undefined → number (fallback chain: zInterpolated → posZ.value → 0)
    const zKfValue = (zKf !== null && typeof zKf === "object" && "value" in zKf && typeof zKf.value === "number" && Number.isFinite(zKf.value)) ? zKf.value : undefined;
    const zInterpolatedValue = (zInterpolated !== undefined && typeof zInterpolated === "number" && Number.isFinite(zInterpolated)) ? zInterpolated : undefined;
    const posZValue = (posZ !== null && typeof posZ === "object" && "value" in posZ && typeof posZ.value === "number" && Number.isFinite(posZ.value)) ? posZ.value : undefined;
    const zVal = (zKfValue !== undefined) ? zKfValue : ((zInterpolatedValue !== undefined) ? zInterpolatedValue : ((posZValue !== undefined) ? posZValue : 0));

    // Use the first available keyframe as template for handles/interpolation
    const templateKf = xKf || yKf || zKf;

    transform.position.keyframes.push({
      id: `kf_pos_${frame}_${Date.now()}`,
      frame,
      value: { x: xVal, y: yVal, z: zVal },
      // Pattern match: templateKf.interpolation ∈ string | undefined → string (default "linear")
      interpolation: (templateKf !== null && typeof templateKf === "object" && "interpolation" in templateKf && typeof templateKf.interpolation === "string") ? templateKf.interpolation : "linear",
      // Pattern match: templateKf.inHandle ∈ Handle | undefined → Handle (default)
      inHandle: (templateKf !== null && typeof templateKf === "object" && "inHandle" in templateKf && typeof templateKf.inHandle === "object" && templateKf.inHandle !== null) ? templateKf.inHandle : { frame: -5, value: 0, enabled: false },
      // Pattern match: templateKf.outHandle ∈ Handle | undefined → Handle (default)
      outHandle: (templateKf !== null && typeof templateKf === "object" && "outHandle" in templateKf && typeof templateKf.outHandle === "object" && templateKf.outHandle !== null) ? templateKf.outHandle : {
        frame: 5,
        value: 0,
        enabled: false,
      },
      // Pattern match: templateKf.controlMode ∈ string | undefined → string (default "smooth")
      controlMode: (templateKf !== null && typeof templateKf === "object" && "controlMode" in templateKf && typeof templateKf.controlMode === "string") ? templateKf.controlMode : "smooth",
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
    (() => {
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zValue = currentValue.z;
      return isFiniteNumber(zValue) ? zValue : 100;
    })(),
    "number",
  );

  if (scale.animated && scale.keyframes.length > 0) {
    transform.scaleX.animated = true;
    transform.scaleY.animated = true;
    transform.scaleZ.animated = true;

    scale.keyframes.forEach((kf) => {
      const val = kf.value;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (transform.scaleX != null && typeof transform.scaleX === "object" && "keyframes" in transform.scaleX && Array.isArray(transform.scaleX.keyframes)) {
        transform.scaleX.keyframes.push({
          ...kf,
          id: `${kf.id}_x`,
          value: val.x,
        });
      }

      if (transform.scaleY != null && typeof transform.scaleY === "object" && "keyframes" in transform.scaleY && Array.isArray(transform.scaleY.keyframes)) {
        transform.scaleY.keyframes.push({
          ...kf,
          id: `${kf.id}_y`,
          value: val.y,
        });
      }

      if (transform.scaleZ != null && typeof transform.scaleZ === "object" && "keyframes" in transform.scaleZ && Array.isArray(transform.scaleZ.keyframes)) {
        transform.scaleZ.keyframes.push({
          ...kf,
          id: `${kf.id}_z`,
          // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
          value: (() => {
            const zValue = val.z;
            return isFiniteNumber(zValue) ? zValue : 100;
          })(),
        });
      }
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
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    z: (() => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Pattern match: scaleZ.value ∈ number | undefined → number | undefined
      const zValue = (scaleZ !== null && typeof scaleZ === "object" && "value" in scaleZ && typeof scaleZ.value === "number" && Number.isFinite(scaleZ.value)) ? scaleZ.value : undefined;
      return isFiniteNumber(zValue) ? zValue : 100;
    })(),
  };

  const allFrames = new Set<number>();
  scaleX.keyframes.forEach((kf) => allFrames.add(kf.frame));
  scaleY.keyframes.forEach((kf) => allFrames.add(kf.frame));
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (scaleZ != null && typeof scaleZ === "object" && "keyframes" in scaleZ && Array.isArray(scaleZ.keyframes)) {
    scaleZ.keyframes.forEach((kf) => allFrames.add(kf.frame));
  }

  transform.scale.keyframes = [];
  transform.scale.animated = allFrames.size > 0;

  const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

  sortedFrames.forEach((frame) => {
    const xKf = scaleX.keyframes.find((k) => k.frame === frame);
    const yKf = scaleY.keyframes.find((k) => k.frame === frame);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const zKf = (scaleZ != null && typeof scaleZ === "object" && "keyframes" in scaleZ && Array.isArray(scaleZ.keyframes) && typeof scaleZ.keyframes.find === "function") ? scaleZ.keyframes.find((k) => k.frame === frame) : undefined;

    // System F/Omega proof: Validate keyframes exist before calling utility
    // Type proof: keyframes.length ∈ number → number | undefined
    // Mathematical proof: At least one keyframe required for interpolation
    const xInterpolated = scaleX.keyframes.length > 0
      ? getInterpolatedValue(scaleX.keyframes, frame)
      : undefined;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: xKf.value ∈ number | undefined → number (fallback chain: xInterpolated → scaleX.value)
    const xKfValue = (xKf !== null && typeof xKf === "object" && "value" in xKf && typeof xKf.value === "number" && Number.isFinite(xKf.value)) ? xKf.value : undefined;
    const xVal = (xKfValue !== undefined) ? xKfValue : ((xInterpolated !== undefined && typeof xInterpolated === "number" && Number.isFinite(xInterpolated)) ? xInterpolated : scaleX.value);
    
    const yInterpolated = scaleY.keyframes.length > 0
      ? getInterpolatedValue(scaleY.keyframes, frame)
      : undefined;
    // Pattern match: yKf.value ∈ number | undefined → number (fallback chain: yInterpolated → scaleY.value)
    const yKfValue = (yKf !== null && typeof yKf === "object" && "value" in yKf && typeof yKf.value === "number" && Number.isFinite(yKf.value)) ? yKf.value : undefined;
    const yVal = (yKfValue !== undefined) ? yKfValue : ((yInterpolated !== undefined && typeof yInterpolated === "number" && Number.isFinite(yInterpolated)) ? yInterpolated : scaleY.value);
    
    // Type proof: zVal ∈ ℝ ∪ {undefined} → z ∈ ℝ
    // Pattern match: zKf.value ∈ number | undefined → number | undefined
    const zKfValue = (zKf !== null && typeof zKf === "object" && "value" in zKf && typeof zKf.value === "number" && Number.isFinite(zKf.value)) ? zKf.value : undefined;
    // Pattern match: scaleZ.keyframes ∈ Keyframe[] | undefined → Keyframe[] (default [])
    const scaleZData = (scaleZ !== null && typeof scaleZ === "object" && "keyframes" in scaleZ && Array.isArray(scaleZ.keyframes)) ? scaleZ.keyframes : undefined;
    const zKeyframes = (scaleZData !== undefined) ? scaleZData : [];
    const zInterpolated = zKeyframes.length > 0
      ? getInterpolatedValue(zKeyframes, frame)
      : undefined;
    // Pattern match: scaleZ.value ∈ number | undefined → number | undefined
    const zScaleZValue = (scaleZ !== null && typeof scaleZ === "object" && "value" in scaleZ && typeof scaleZ.value === "number" && Number.isFinite(scaleZ.value)) ? scaleZ.value : undefined;
    const zVal = isFiniteNumber(zKfValue)
      ? zKfValue
      : (isFiniteNumber(zInterpolated)
          ? zInterpolated
          : (isFiniteNumber(zScaleZValue) ? zScaleZValue : 100));

    const templateKf = xKf || yKf || zKf;

    transform.scale.keyframes.push({
      id: `kf_scale_${frame}_${Date.now()}`,
      frame,
      value: { x: xVal, y: yVal, z: zVal },
      // Pattern match: templateKf.interpolation ∈ string | undefined → string (default "linear")
      interpolation: (templateKf !== null && typeof templateKf === "object" && "interpolation" in templateKf && typeof templateKf.interpolation === "string") ? templateKf.interpolation : "linear",
      // Pattern match: templateKf.inHandle ∈ Handle | undefined → Handle (default)
      inHandle: (templateKf !== null && typeof templateKf === "object" && "inHandle" in templateKf && typeof templateKf.inHandle === "object" && templateKf.inHandle !== null) ? templateKf.inHandle : { frame: -5, value: 0, enabled: false },
      // Pattern match: templateKf.outHandle ∈ Handle | undefined → Handle (default)
      outHandle: (templateKf !== null && typeof templateKf === "object" && "outHandle" in templateKf && typeof templateKf.outHandle === "object" && templateKf.outHandle !== null) ? templateKf.outHandle : {
        frame: 5,
        value: 0,
        enabled: false,
      },
      // Pattern match: templateKf.controlMode ∈ string | undefined → string (default "smooth")
      controlMode: (templateKf !== null && typeof templateKf === "object" && "controlMode" in templateKf && typeof templateKf.controlMode === "string") ? templateKf.controlMode : "smooth",
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
 * 
 * System F/Omega proof: Explicit validation of keyframes array and frame position
 * Type proof: keyframes ∈ Array<{ frame: number; value: number }>, frame ∈ number → number (non-nullable)
 * Mathematical proof: Keyframes array must be non-empty and frame must be within valid range
 */
function getInterpolatedValue(
  keyframes: Array<{ frame: number; value: number }>,
  frame: number,
): number {
  // System F/Omega proof: Explicit validation of keyframes array
  // Type proof: keyframes.length ∈ number
  // Mathematical proof: At least one keyframe required for interpolation
  if (keyframes.length === 0) {
    throw new Error(
      `[Transform] Cannot interpolate value: Keyframes array is empty. ` +
      `Frame: ${frame}, keyframes length: 0. ` +
      `At least one keyframe is required for interpolation. ` +
      `Wrap in try/catch if "no keyframes" is an expected state.`
    );
  }
  
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

  // System F/Omega proof: Explicit validation of frame position
  // Type proof: frame ∈ number, sorted keyframes ∈ Array<{ frame: number; value: number }>
  // Mathematical proof: Frame must be within valid range (handled above) or between keyframes
  // This should never be reached due to logic above, but included for completeness
  throw new Error(
    `[Transform] Cannot interpolate value: Frame position invalid. ` +
    `Frame: ${frame}, keyframes: ${sorted.map(k => k.frame).join(", ")}, ` +
    `range: [${sorted[0].frame}, ${sorted[sorted.length - 1].frame}]. ` +
    `Frame must be within keyframe range or between adjacent keyframes. ` +
    `Wrap in try/catch if "invalid frame" is an expected state.`
  );
}
