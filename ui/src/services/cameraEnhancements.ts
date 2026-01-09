/**
 * Camera Enhancement Service
 *
 * Advanced camera features:
 * - Camera shake (handheld simulation)
 * - Rack focus (smooth focus transition)
 * - Depth-aware autofocus
 * - Motion blur estimation
 */

import { createNoise2D, createNoise3D } from "simplex-noise";
import type { Camera3D, CameraKeyframe } from "@/types/camera";

// ============================================================================
// TYPES
// ============================================================================

export interface CameraShakeConfig {
  /** Shake intensity (0-1) */
  intensity: number;
  /** Frequency multiplier (higher = more jittery) */
  frequency: number;
  /** Enable rotation shake */
  rotationEnabled: boolean;
  /** Rotation intensity multiplier */
  rotationScale: number;
  /** Seed for deterministic shake */
  seed: number;
  /** Shake decay (reduces over time, 0=constant, 1=full decay) */
  decay: number;
  /** Shake type */
  type: "handheld" | "impact" | "earthquake" | "subtle" | "custom";
}

export interface RackFocusConfig {
  /** Starting focus distance */
  startDistance: number;
  /** Ending focus distance */
  endDistance: number;
  /** Duration in frames */
  duration: number;
  /** Starting frame */
  startFrame: number;
  /** Easing type */
  easing: "linear" | "ease-in" | "ease-out" | "ease-in-out" | "snap";
  /** Hold duration at start (frames) */
  holdStart: number;
  /** Hold duration at end (frames) */
  holdEnd: number;
}

export interface AutoFocusConfig {
  /** Auto-focus mode */
  mode: "center" | "point" | "face" | "nearest" | "farthest";
  /** Focus point (for 'point' mode, normalized 0-1) */
  focusPoint: { x: number; y: number };
  /** Smoothing factor (0=instant, 1=very smooth) */
  smoothing: number;
  /** Minimum focus distance change to trigger update */
  threshold: number;
  /** Sample radius for focus calculation */
  sampleRadius: number;
}

export interface MotionBlurEstimate {
  /** Velocity magnitude */
  velocity: number;
  /** Recommended motion blur amount (0-1) */
  blurAmount: number;
  /** Motion direction in degrees */
  direction: number;
}

// ============================================================================
// CAMERA SHAKE PRESETS
// ============================================================================

export const SHAKE_PRESETS: Record<
  CameraShakeConfig["type"],
  Partial<CameraShakeConfig>
> = {
  handheld: {
    intensity: 0.3,
    frequency: 1.0,
    rotationEnabled: true,
    rotationScale: 0.5,
    decay: 0,
  },
  impact: {
    intensity: 0.8,
    frequency: 3.0,
    rotationEnabled: true,
    rotationScale: 1.0,
    decay: 0.9,
  },
  earthquake: {
    intensity: 0.6,
    frequency: 2.0,
    rotationEnabled: true,
    rotationScale: 0.3,
    decay: 0.5,
  },
  subtle: {
    intensity: 0.1,
    frequency: 0.5,
    rotationEnabled: false,
    rotationScale: 0,
    decay: 0,
  },
  custom: {},
};

// ============================================================================
// DEFAULT VALUES
// ============================================================================

export const DEFAULT_SHAKE_CONFIG: CameraShakeConfig = {
  intensity: 0.3,
  frequency: 1.0,
  rotationEnabled: true,
  rotationScale: 0.5,
  seed: 12345,
  decay: 0,
  type: "handheld",
};

export const DEFAULT_RACK_FOCUS: RackFocusConfig = {
  startDistance: 1000,
  endDistance: 2000,
  duration: 30,
  startFrame: 0,
  easing: "ease-in-out",
  holdStart: 0,
  holdEnd: 0,
};

export const DEFAULT_AUTOFOCUS: AutoFocusConfig = {
  mode: "center",
  focusPoint: { x: 0.5, y: 0.5 },
  smoothing: 0.8,
  threshold: 10,
  sampleRadius: 0.1,
};

// ============================================================================
// CAMERA SHAKE
// ============================================================================

/**
 * Mulberry32 PRNG - a fast, seeded 32-bit random number generator
 * Used to provide proper seeding for simplex-noise
 */
function createMulberry32(seed: number): () => number {
  let state = seed >>> 0; // Ensure unsigned 32-bit
  return function() {
    state = (state + 0x6D2B79F5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/**
 * Camera shake generator with deterministic noise
 */
export class CameraShake {
  private noise2D: ReturnType<typeof createNoise2D>;
  private config: CameraShakeConfig;
  private startFrame: number;
  private duration: number;

  // Maximum shake duration to prevent infinite loops (10 hours at 30fps)
  private static readonly MAX_DURATION = 1_080_000;

  constructor(
    config: Partial<CameraShakeConfig> = {},
    startFrame: number = 0,
    duration: number = CameraShake.MAX_DURATION,
  ) {
    this.config = {
      ...DEFAULT_SHAKE_CONFIG,
      ...SHAKE_PRESETS[config.type || "handheld"],
      ...config,
    };
    this.startFrame = startFrame;
    // Clamp duration to prevent Infinity which can cause issues in calculations
    this.duration = Math.min(duration, CameraShake.MAX_DURATION);

    // Initialize simplex noise with seeded PRNG for deterministic results.
    // The noise library requires a function that returns different values per call.
    const prng = createMulberry32(this.config.seed);
    this.noise2D = createNoise2D(prng);
    this.noise3D = createNoise3D(prng);
  }

  /**
   * Get shake offset for a specific frame
   */
  getOffset(frame: number): {
    position: { x: number; y: number; z: number };
    rotation: { x: number; y: number; z: number };
  } {
    const relativeFrame = frame - this.startFrame;

    // Check if within duration
    if (relativeFrame < 0 || relativeFrame > this.duration) {
      return {
        position: { x: 0, y: 0, z: 0 },
        rotation: { x: 0, y: 0, z: 0 },
      };
    }

    const { intensity, frequency, rotationEnabled, rotationScale, decay } =
      this.config;

    // Calculate decay factor
    const decayFactor =
      decay > 0 ? 1 - (relativeFrame / this.duration) * decay : 1;

    const time = relativeFrame * frequency * 0.1;
    const scale = intensity * decayFactor * 10; // 10 pixels base scale

    // Multi-frequency noise for natural motion
    const posX =
      (this.noise2D(time, 0) * 0.5 +
        this.noise2D(time * 2.3, 100) * 0.3 +
        this.noise2D(time * 5.7, 200) * 0.2) *
      scale;

    const posY =
      (this.noise2D(time, 1000) * 0.5 +
        this.noise2D(time * 2.1, 1100) * 0.3 +
        this.noise2D(time * 4.9, 1200) * 0.2) *
      scale;

    const posZ =
      (this.noise2D(time, 2000) * 0.3 + this.noise2D(time * 1.7, 2100) * 0.2) *
      scale *
      0.5;

    // Rotation shake
    let rotation = { x: 0, y: 0, z: 0 };
    if (rotationEnabled) {
      const rotScale = rotationScale * decayFactor * 2; // 2 degrees base
      rotation = {
        x: this.noise2D(time, 3000) * rotScale,
        y: this.noise2D(time, 4000) * rotScale,
        z: this.noise2D(time, 5000) * rotScale * 0.5, // Less roll
      };
    }

    return {
      position: { x: posX, y: posY, z: posZ },
      rotation,
    };
  }

  /**
   * Apply shake to camera
   */
  applyToCamera(camera: Camera3D, frame: number): Camera3D {
    const offset = this.getOffset(frame);

    return {
      ...camera,
      position: {
        x: camera.position.x + offset.position.x,
        y: camera.position.y + offset.position.y,
        z: camera.position.z + offset.position.z,
      },
      xRotation: camera.xRotation + offset.rotation.x,
      yRotation: camera.yRotation + offset.rotation.y,
      zRotation: camera.zRotation + offset.rotation.z,
    };
  }

  /**
   * Generate keyframes with shake applied
   */
  generateKeyframes(
    baseKeyframes: CameraKeyframe[],
    interval: number = 1,
  ): CameraKeyframe[] {
    const result: CameraKeyframe[] = [];
    const frames = new Set<number>();

    // Collect all frames from base keyframes
    for (const kf of baseKeyframes) {
      frames.add(kf.frame);
    }

    // Add intermediate frames
    const minFrame = Math.min(...frames);
    const maxFrame = Math.max(...frames);
    for (let f = minFrame; f <= maxFrame; f += interval) {
      frames.add(f);
    }

    // Generate shaken keyframes
    const sortedFrames = Array.from(frames).sort((a, b) => a - b);

    for (const frame of sortedFrames) {
      // Find base values (interpolate if needed)
      const base = this.interpolateBaseKeyframe(baseKeyframes, frame);
      const offset = this.getOffset(frame);

      const keyframe: CameraKeyframe = {
        frame,
        temporalInterpolation: "linear",
      };

      if (base.position) {
        keyframe.position = {
          x: base.position.x + offset.position.x,
          y: base.position.y + offset.position.y,
          z: base.position.z + offset.position.z,
        };
      }

      if (base.xRotation !== undefined) {
        keyframe.xRotation = base.xRotation + offset.rotation.x;
      }
      if (base.yRotation !== undefined) {
        keyframe.yRotation = base.yRotation + offset.rotation.y;
      }
      if (base.zRotation !== undefined) {
        keyframe.zRotation = base.zRotation + offset.rotation.z;
      }

      result.push(keyframe);
    }

    return result;
  }

  private interpolateBaseKeyframe(
    keyframes: CameraKeyframe[],
    frame: number,
  ): Partial<CameraKeyframe> {
    if (keyframes.length === 0) return {};
    if (keyframes.length === 1) return keyframes[0];

    // Find surrounding keyframes
    let before: CameraKeyframe | null = null;
    let after: CameraKeyframe | null = null;

    for (const kf of keyframes) {
      if (kf.frame <= frame) {
        if (!before || kf.frame > before.frame) before = kf;
      }
      if (kf.frame >= frame) {
        if (!after || kf.frame < after.frame) after = kf;
      }
    }

    if (!before) return after || {};
    if (!after) return before;
    if (before.frame === after.frame) return before;

    // Interpolate
    const t = (frame - before.frame) / (after.frame - before.frame);

    return {
      frame,
      position:
        before.position && after.position
          ? {
              x: before.position.x + (after.position.x - before.position.x) * t,
              y: before.position.y + (after.position.y - before.position.y) * t,
              z: before.position.z + (after.position.z - before.position.z) * t,
            }
          : before.position || after.position,
      xRotation:
        before.xRotation !== undefined && after.xRotation !== undefined
          ? before.xRotation + (after.xRotation - before.xRotation) * t
          : (before.xRotation ?? after.xRotation),
      yRotation:
        before.yRotation !== undefined && after.yRotation !== undefined
          ? before.yRotation + (after.yRotation - before.yRotation) * t
          : (before.yRotation ?? after.yRotation),
      zRotation:
        before.zRotation !== undefined && after.zRotation !== undefined
          ? before.zRotation + (after.zRotation - before.zRotation) * t
          : (before.zRotation ?? after.zRotation),
    };
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<CameraShakeConfig>): void {
    this.config = { ...this.config, ...config };
  }
}

// ============================================================================
// RACK FOCUS
// ============================================================================

/**
 * Calculate focus distance for rack focus at a specific frame
 */
export function getRackFocusDistance(
  config: RackFocusConfig,
  frame: number,
): number {
  const {
    startDistance,
    endDistance,
    duration,
    startFrame,
    easing,
    holdStart,
    holdEnd,
  } = config;

  const endFrame = startFrame + holdStart + duration + holdEnd;

  // Before start
  if (frame < startFrame) {
    return startDistance;
  }

  // Hold at start
  if (frame < startFrame + holdStart) {
    return startDistance;
  }

  // After end
  if (frame >= endFrame) {
    return endDistance;
  }

  // Hold at end
  if (frame >= startFrame + holdStart + duration) {
    return endDistance;
  }

  // Transition
  const transitionFrame = frame - startFrame - holdStart;
  const t = transitionFrame / duration;
  const easedT = applyRackEasing(t, easing);

  return startDistance + (endDistance - startDistance) * easedT;
}

function applyRackEasing(t: number, easing: RackFocusConfig["easing"]): number {
  switch (easing) {
    case "linear":
      return t;
    case "ease-in":
      return t * t * t;
    case "ease-out":
      return 1 - (1 - t) ** 3;
    case "ease-in-out":
      return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
    case "snap":
      // Quick transition at 80% mark
      return t < 0.8 ? t * 0.1 : 0.1 + (t - 0.8) * 4.5;
    default:
      return t;
  }
}

/**
 * Generate focus keyframes for rack focus
 */
export function generateRackFocusKeyframes(
  config: RackFocusConfig,
  interval: number = 2,
): CameraKeyframe[] {
  const keyframes: CameraKeyframe[] = [];
  const { startFrame, duration, holdStart, holdEnd } = config;

  const totalDuration = holdStart + duration + holdEnd;
  const endFrame = startFrame + totalDuration;

  // Generate keyframes
  for (let frame = startFrame; frame <= endFrame; frame += interval) {
    keyframes.push({
      frame,
      focusDistance: getRackFocusDistance(config, frame),
      temporalInterpolation: "linear",
    });
  }

  // Ensure end keyframe exists
  if (keyframes[keyframes.length - 1].frame !== endFrame) {
    keyframes.push({
      frame: endFrame,
      focusDistance: getRackFocusDistance(config, endFrame),
      temporalInterpolation: "linear",
    });
  }

  return keyframes;
}

// ============================================================================
// DEPTH-AWARE AUTOFOCUS
// ============================================================================

/**
 * Calculate focus distance from depth map
 */
export function calculateAutoFocusDistance(
  depthMap: ImageData | null,
  config: AutoFocusConfig,
  previousDistance: number,
): number {
  if (!depthMap) return previousDistance;

  const { mode, focusPoint, smoothing, threshold, sampleRadius } = config;
  const { width, height, data } = depthMap;

  let targetDistance: number;

  switch (mode) {
    case "center":
      targetDistance = sampleDepthAt(
        data,
        width,
        height,
        0.5,
        0.5,
        sampleRadius,
      );
      break;

    case "point":
      targetDistance = sampleDepthAt(
        data,
        width,
        height,
        focusPoint.x,
        focusPoint.y,
        sampleRadius,
      );
      break;

    case "nearest":
      targetDistance = findExtreme(data, width, height, "min");
      break;

    case "farthest":
      targetDistance = findExtreme(data, width, height, "max");
      break;

    case "face":
      // Face detection would require ML - fallback to center for now
      targetDistance = sampleDepthAt(
        data,
        width,
        height,
        0.5,
        0.4,
        sampleRadius * 2,
      );
      break;

    default:
      targetDistance = previousDistance;
  }

  // Apply threshold
  if (Math.abs(targetDistance - previousDistance) < threshold) {
    return previousDistance;
  }

  // Apply smoothing
  return (
    previousDistance + (targetDistance - previousDistance) * (1 - smoothing)
  );
}

function sampleDepthAt(
  data: Uint8ClampedArray,
  width: number,
  height: number,
  normalizedX: number,
  normalizedY: number,
  radius: number,
): number {
  const centerX = Math.floor(normalizedX * width);
  const centerY = Math.floor(normalizedY * height);
  const radiusPixels = Math.floor(radius * Math.min(width, height));

  let sum = 0;
  let count = 0;

  for (let dy = -radiusPixels; dy <= radiusPixels; dy++) {
    for (let dx = -radiusPixels; dx <= radiusPixels; dx++) {
      const x = centerX + dx;
      const y = centerY + dy;

      if (x >= 0 && x < width && y >= 0 && y < height) {
        // Circular sampling
        if (dx * dx + dy * dy <= radiusPixels * radiusPixels) {
          const idx = (y * width + x) * 4;
          // Assume grayscale depth (R channel)
          sum += data[idx];
          count++;
        }
      }
    }
  }

  if (count === 0) return 1000;

  // Convert depth value (0-255) to distance (100-5000 pixels)
  const normalizedDepth = sum / count / 255;
  return 100 + normalizedDepth * 4900;
}

function findExtreme(
  data: Uint8ClampedArray,
  width: number,
  height: number,
  type: "min" | "max",
): number {
  let extreme = type === "min" ? 255 : 0;

  // Sample every 10th pixel for performance
  for (let y = 0; y < height; y += 10) {
    for (let x = 0; x < width; x += 10) {
      const idx = (y * width + x) * 4;
      const depth = data[idx];

      if (type === "min") {
        extreme = Math.min(extreme, depth);
      } else {
        extreme = Math.max(extreme, depth);
      }
    }
  }

  // Convert to distance
  const normalizedDepth = extreme / 255;
  return 100 + normalizedDepth * 4900;
}

// ============================================================================
// MOTION BLUR ESTIMATION
// ============================================================================

/**
 * Estimate motion blur from camera velocity
 */
export function estimateMotionBlur(
  currentCamera: Camera3D,
  previousCamera: Camera3D | null,
  shutterAngle: number = 180, // degrees, 180 = half frame
): MotionBlurEstimate {
  if (!previousCamera) {
    return { velocity: 0, blurAmount: 0, direction: 0 };
  }

  // Calculate position delta
  const dx = currentCamera.position.x - previousCamera.position.x;
  const dy = currentCamera.position.y - previousCamera.position.y;
  const dz = currentCamera.position.z - previousCamera.position.z;

  const velocity = Math.sqrt(dx * dx + dy * dy + dz * dz);

  // Shutter angle affects blur amount (180° = half frame exposure)
  const shutterFactor = shutterAngle / 360;

  // Map velocity to blur amount (0-1)
  // Empirical: ~100 pixels/frame = full blur
  const blurAmount = Math.min(1, (velocity / 100) * shutterFactor);

  // Calculate dominant direction in screen space (XY)
  const direction = Math.atan2(dy, dx) * (180 / Math.PI);

  return { velocity, blurAmount, direction };
}

/**
 * Generate motion blur keyframes based on camera movement
 */
export function generateMotionBlurKeyframes(
  cameraKeyframes: CameraKeyframe[],
  shutterAngle: number = 180,
): Array<{ frame: number; blurAmount: number }> {
  const result: Array<{ frame: number; blurAmount: number }> = [];

  for (let i = 0; i < cameraKeyframes.length; i++) {
    const current = cameraKeyframes[i];
    const previous = i > 0 ? cameraKeyframes[i - 1] : null;

    let velocity = 0;
    if (previous && current.position && previous.position) {
      const dx = current.position.x - previous.position.x;
      const dy = current.position.y - previous.position.y;
      const dz = current.position.z - previous.position.z;
      velocity = Math.sqrt(dx * dx + dy * dy + dz * dz);
    }

    const shutterFactor = shutterAngle / 360;
    const blurAmount = Math.min(1, (velocity / 100) * shutterFactor);

    result.push({ frame: current.frame, blurAmount });
  }

  return result;
}

// ============================================================================
// FACTORY FUNCTIONS
// ============================================================================

/**
 * Create camera shake from preset
 */
export function createCameraShake(
  type: CameraShakeConfig["type"],
  overrides?: Partial<CameraShakeConfig>,
  startFrame?: number,
  duration?: number,
): CameraShake {
  return new CameraShake({ type, ...overrides }, startFrame, duration);
}

/**
 * Create rack focus configuration
 */
export function createRackFocus(
  startDistance: number,
  endDistance: number,
  duration: number,
  options?: Partial<RackFocusConfig>,
): RackFocusConfig {
  return {
    ...DEFAULT_RACK_FOCUS,
    startDistance,
    endDistance,
    duration,
    ...options,
  };
}

/**
 * Create autofocus configuration
 */
export function createAutoFocus(
  mode: AutoFocusConfig["mode"],
  options?: Partial<AutoFocusConfig>,
): AutoFocusConfig {
  return {
    ...DEFAULT_AUTOFOCUS,
    mode,
    ...options,
  };
}
