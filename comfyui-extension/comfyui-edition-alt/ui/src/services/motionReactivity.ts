/**
 * Motion-Based Reactivity Service
 *
 * Provides motion-based reactive values for layers based on their position
 * changes over time. Inspired by RyanOnTheInside's Flex features.
 *
 * Features:
 * - Velocity tracking (speed and direction)
 * - Acceleration tracking
 * - Proximity to other layers or points
 * - Motion direction
 *
 * All values are deterministic and frame-based for scrub-safe playback.
 *
 * @module services/motionReactivity
 */

import type { Layer } from "@/types/project";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ════════════════════════════════════════════════════════════════════════════

export interface MotionState {
  position: { x: number; y: number; z: number };
  velocity: { x: number; y: number; z: number };
  acceleration: { x: number; y: number; z: number };
  speed: number; // Magnitude of velocity
  accelerationMag: number; // Magnitude of acceleration
  direction: number; // Angle in radians (2D, XY plane)
  verticalDirection: number; // Vertical angle (XZ plane)
}

export interface MotionReactivityConfig {
  id: string;
  enabled: boolean;
  sourceLayerId: string;

  // What motion feature to use
  feature: MotionFeature;

  // Target property to modulate
  targetLayerId: string;
  targetPropertyPath: string;

  // Value mapping
  sensitivity: number; // Multiplier
  smoothing: number; // Temporal smoothing (0-1)
  min: number; // Output minimum
  max: number; // Output maximum
  curve: "linear" | "exponential" | "logarithmic" | "step";

  // Feature-specific options
  options?: {
    // For direction: reference angle
    referenceAngle?: number;
    // For proximity: target point or layer
    targetPoint?: { x: number; y: number; z: number };
    targetLayerId?: string;
    maxDistance?: number;
  };
}

export type MotionFeature =
  | "speed" // Speed (velocity magnitude)
  | "acceleration" // Acceleration magnitude
  | "velocityX" // X component of velocity
  | "velocityY" // Y component of velocity
  | "velocityZ" // Z component of velocity
  | "direction" // 2D direction angle (normalized 0-1)
  | "verticalDirection" // Vertical direction angle (normalized 0-1)
  | "isMoving" // Binary: 1 if moving, 0 if stationary
  | "isAccelerating" // Binary: 1 if accelerating, 0 if decelerating
  | "directionChange"; // Rate of direction change (turning)

// ════════════════════════════════════════════════════════════════════════════
// Motion State Computation
// ════════════════════════════════════════════════════════════════════════════

// Cache for motion states (layer ID -> frame -> state)
const motionStateCache = new Map<string, Map<number, MotionState>>();
const MAX_CACHE_FRAMES = 1000;

/**
 * Compute motion state for a layer at a specific frame
 *
 * Uses finite differences:
 * velocity = (position[frame] - position[frame-1]) * fps
 * acceleration = (velocity[frame] - velocity[frame-1]) * fps
 */
export function computeMotionState(
  layer: Layer,
  frame: number,
  fps: number,
  getPositionAtFrame: (
    layer: Layer,
    frame: number,
  ) => { x: number; y: number; z: number },
): MotionState {
  // Check cache first
  let layerCache = motionStateCache.get(layer.id);
  if (!layerCache) {
    layerCache = new Map();
    motionStateCache.set(layer.id, layerCache);
  }

  if (layerCache.has(frame)) {
    return layerCache.get(frame)!;
  }

  // Get positions at current and previous frames
  const pos = getPositionAtFrame(layer, frame);
  const prevPos = frame > 0 ? getPositionAtFrame(layer, frame - 1) : pos;
  const prevPrevPos =
    frame > 1 ? getPositionAtFrame(layer, frame - 2) : prevPos;

  // Compute velocity (units per second)
  const dt = 1 / fps;
  const velocity = {
    x: (pos.x - prevPos.x) / dt,
    y: (pos.y - prevPos.y) / dt,
    z: (pos.z - prevPos.z) / dt,
  };

  // Compute previous velocity for acceleration
  const prevVelocity = {
    x: (prevPos.x - prevPrevPos.x) / dt,
    y: (prevPos.y - prevPrevPos.y) / dt,
    z: (prevPos.z - prevPrevPos.z) / dt,
  };

  // Compute acceleration (units per second squared)
  const acceleration = {
    x: (velocity.x - prevVelocity.x) / dt,
    y: (velocity.y - prevVelocity.y) / dt,
    z: (velocity.z - prevVelocity.z) / dt,
  };

  // Compute magnitudes
  const speed = Math.sqrt(velocity.x ** 2 + velocity.y ** 2 + velocity.z ** 2);
  const accelerationMag = Math.sqrt(
    acceleration.x ** 2 + acceleration.y ** 2 + acceleration.z ** 2,
  );

  // Compute directions
  const direction = Math.atan2(velocity.y, velocity.x);
  const horizontalSpeed = Math.sqrt(velocity.x ** 2 + velocity.y ** 2);
  const verticalDirection = Math.atan2(velocity.z, horizontalSpeed);

  const state: MotionState = {
    position: pos,
    velocity,
    acceleration,
    speed,
    accelerationMag,
    direction,
    verticalDirection,
  };

  // Cache the result
  layerCache.set(frame, state);

  // Limit cache size
  if (layerCache.size > MAX_CACHE_FRAMES) {
    const oldestFrame = Math.min(...layerCache.keys());
    layerCache.delete(oldestFrame);
  }

  return state;
}

/**
 * Get motion feature value for a layer at a frame
 */
export function getMotionFeatureValue(
  layer: Layer,
  frame: number,
  fps: number,
  feature: MotionFeature,
  getPositionAtFrame: (
    layer: Layer,
    frame: number,
  ) => { x: number; y: number; z: number },
  _options?: MotionReactivityConfig["options"],
): number {
  const state = computeMotionState(layer, frame, fps, getPositionAtFrame);

  switch (feature) {
    case "speed":
      return state.speed;

    case "acceleration":
      return state.accelerationMag;

    case "velocityX":
      return state.velocity.x;

    case "velocityY":
      return state.velocity.y;

    case "velocityZ":
      return state.velocity.z;

    case "direction":
      // Normalize to 0-1 range (0 = right, 0.25 = up, 0.5 = left, 0.75 = down)
      return (state.direction + Math.PI) / (2 * Math.PI);

    case "verticalDirection":
      // Normalize to 0-1 range
      return (state.verticalDirection + Math.PI / 2) / Math.PI;

    case "isMoving":
      // Binary: 1 if speed > threshold, 0 otherwise
      return state.speed > 0.1 ? 1 : 0;

    case "isAccelerating": {
      // Binary: 1 if acceleration is positive in direction of motion
      const dotProduct =
        state.velocity.x * state.acceleration.x +
        state.velocity.y * state.acceleration.y +
        state.velocity.z * state.acceleration.z;
      return dotProduct > 0 ? 1 : 0;
    }

    case "directionChange": {
      // Compare direction with previous frame
      if (frame === 0) return 0;
      const prevState = computeMotionState(
        layer,
        frame - 1,
        fps,
        getPositionAtFrame,
      );
      let directionDiff = state.direction - prevState.direction;
      // Wrap around
      if (directionDiff > Math.PI) directionDiff -= 2 * Math.PI;
      if (directionDiff < -Math.PI) directionDiff += 2 * Math.PI;
      return Math.abs(directionDiff) / Math.PI; // Normalize to 0-1
    }

    default:
      return 0;
  }
}

// ════════════════════════════════════════════════════════════════════════════
// Proximity Reactivity
// ════════════════════════════════════════════════════════════════════════════

/**
 * Calculate proximity between two points or layers
 */
export function calculateProximity(
  sourcePos: { x: number; y: number; z: number },
  targetPos: { x: number; y: number; z: number },
  maxDistance: number = 1000,
): number {
  const dx = targetPos.x - sourcePos.x;
  const dy = targetPos.y - sourcePos.y;
  const dz = targetPos.z - sourcePos.z;
  const distance = Math.sqrt(dx * dx + dy * dy + dz * dz);

  // Normalize to 0-1 (1 = at target, 0 = at or beyond max distance)
  return Math.max(0, 1 - distance / maxDistance);
}

/**
 * Calculate proximity-based reactivity value
 */
export function getProximityValue(
  layer: Layer,
  frame: number,
  targetPoint: { x: number; y: number; z: number },
  maxDistance: number,
  getPositionAtFrame: (
    layer: Layer,
    frame: number,
  ) => { x: number; y: number; z: number },
): number {
  const sourcePos = getPositionAtFrame(layer, frame);
  return calculateProximity(sourcePos, targetPoint, maxDistance);
}

// ════════════════════════════════════════════════════════════════════════════
// Motion Reactivity Mapping
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply response curve to a value
 */
export function applyMotionCurve(
  value: number,
  curve: MotionReactivityConfig["curve"],
): number {
  switch (curve) {
    case "linear":
      return value;
    case "exponential":
      return value * value;
    case "logarithmic":
      return Math.log(1 + value * (Math.E - 1));
    case "step":
      return value > 0.5 ? 1 : 0;
    default:
      return value;
  }
}

/**
 * Get mapped motion value for a reactivity config
 */
export function getMappedMotionValue(
  config: MotionReactivityConfig,
  layer: Layer,
  frame: number,
  fps: number,
  getPositionAtFrame: (
    layer: Layer,
    frame: number,
  ) => { x: number; y: number; z: number },
  previousValue?: number,
): number {
  if (!config.enabled) return config.min;

  // Get raw feature value
  let rawValue = getMotionFeatureValue(
    layer,
    frame,
    fps,
    config.feature,
    getPositionAtFrame,
    config.options,
  );

  // Apply sensitivity
  rawValue *= config.sensitivity;

  // Clamp to 0-1 for curve application
  const clampedValue = Math.max(0, Math.min(1, rawValue));

  // Apply curve
  const curvedValue = applyMotionCurve(clampedValue, config.curve);

  // Map to output range
  let outputValue = config.min + curvedValue * (config.max - config.min);

  // Apply smoothing if previous value available
  if (previousValue !== undefined && config.smoothing > 0) {
    outputValue =
      previousValue * config.smoothing + outputValue * (1 - config.smoothing);
  }

  return outputValue;
}

// ════════════════════════════════════════════════════════════════════════════
// Cache Management
// ════════════════════════════════════════════════════════════════════════════

/**
 * Clear motion state cache for a layer
 */
export function clearMotionCache(layerId?: string): void {
  if (layerId) {
    motionStateCache.delete(layerId);
  } else {
    motionStateCache.clear();
  }
}

/**
 * Get cache statistics
 */
export function getMotionCacheStats(): { layers: number; totalFrames: number } {
  let totalFrames = 0;
  for (const cache of motionStateCache.values()) {
    totalFrames += cache.size;
  }
  return {
    layers: motionStateCache.size,
    totalFrames,
  };
}

// ════════════════════════════════════════════════════════════════════════════
// Exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  computeMotionState,
  getMotionFeatureValue,
  calculateProximity,
  getProximityValue,
  applyMotionCurve,
  getMappedMotionValue,
  clearMotionCache,
  getMotionCacheStats,
};
