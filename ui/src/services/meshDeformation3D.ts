/**
 * 3D Mesh Deformation Service
 *
 * Extends mesh deformation capabilities to 3D models with:
 * - Velocity-based squash/stretch (animation principle)
 * - 3D pin deformation for posing
 * - Bounce/settle effects
 *
 * Works with ModelLayer for 3D file input (GLTF, FBX, OBJ, etc.)
 */

import type * as THREE from "three";
import type { AnimatableProperty, Vec3 } from "@/types/project";
import { createLogger } from "@/utils/logger";
import { interpolateProperty } from "./interpolation";

const logger = createLogger("MeshDeformation3D");

// ============================================================================
// TYPES
// ============================================================================

export interface SquashStretchConfig {
  /** Enable auto squash/stretch based on velocity */
  enabled: boolean;
  /** Maximum stretch factor (1.0 = no stretch, 2.0 = double length) */
  maxStretch: number;
  /** Maximum squash factor (1.0 = no squash, 0.5 = half height) */
  maxSquash: number;
  /** Velocity threshold below which no effect applies */
  velocityThreshold: number;
  /** How quickly the effect responds (0-1, higher = faster) */
  responsiveness: number;
  /** Preserve volume during deformation */
  preserveVolume: boolean;
}

export interface BounceConfig {
  /** Enable bounce settle effect */
  enabled: boolean;
  /** Elasticity (0-1, how much energy is retained per bounce) */
  elasticity: number;
  /** Gravity strength (pixels/sec^2) */
  gravity: number;
  /** Ground plane Y position */
  groundY: number;
  /** Number of bounces before settling */
  maxBounces: number;
}

export interface Deformation3DPin {
  id: string;
  name: string;
  /** Pin position in 3D space */
  position: AnimatableProperty<Vec3>;
  /** Influence radius */
  radius: number;
  /** Weight falloff (1 = linear, 2 = quadratic, etc.) */
  falloff: number;
  /** Pin stiffness (0 = fully deformable, 1 = rigid) */
  stiffness: number;
  /** Rest position (initial placement) */
  restPosition: Vec3;
}

export interface Deformation3DResult {
  /** Deformed position */
  position: Vec3;
  /** Scale to apply for squash/stretch */
  scale: Vec3;
  /** Rotation adjustment */
  rotation: Vec3;
}

// ============================================================================
// DEFAULT CONFIGS
// ============================================================================

export const DEFAULT_SQUASH_STRETCH: SquashStretchConfig = {
  enabled: true,
  maxStretch: 1.5,
  maxSquash: 0.7,
  velocityThreshold: 10,
  responsiveness: 0.5,
  preserveVolume: true,
};

export const DEFAULT_BOUNCE: BounceConfig = {
  enabled: true,
  elasticity: 0.7,
  gravity: 980, // Earth gravity in px/s^2 (scaled for compositor)
  groundY: 0,
  maxBounces: 5,
};

// ============================================================================
// SQUASH/STRETCH CALCULATION
// ============================================================================

/**
 * Calculate squash/stretch scale based on velocity vector
 *
 * Animation principle: Objects stretch in direction of motion,
 * and squash perpendicular to it. Volume is preserved.
 */
export function calculateSquashStretch(
  velocity: Vec3,
  config: SquashStretchConfig = DEFAULT_SQUASH_STRETCH,
): Vec3 {
  if (!config.enabled) {
    return { x: 1, y: 1, z: 1 };
  }

  // Calculate velocity magnitude
  const speed = Math.sqrt(
    velocity.x * velocity.x + velocity.y * velocity.y + velocity.z * velocity.z,
  );

  // Below threshold, no deformation
  if (speed < config.velocityThreshold) {
    return { x: 1, y: 1, z: 1 };
  }

  // Normalize velocity to get direction
  const dir = {
    x: velocity.x / speed,
    y: velocity.y / speed,
    z: velocity.z / speed,
  };

  // Calculate stretch factor based on speed
  // Using exponential approach to maxStretch
  const normalizedSpeed = Math.min(speed / 500, 1); // Normalize to 0-1
  const stretchFactor =
    1 + (config.maxStretch - 1) * normalizedSpeed * config.responsiveness;

  // Calculate squash factor (perpendicular)
  // If preserveVolume, squash = 1/sqrt(stretch) to maintain volume
  const squashFactor = config.preserveVolume
    ? 1 / Math.sqrt(stretchFactor)
    : 1 - (1 - config.maxSquash) * normalizedSpeed * config.responsiveness;

  // Clamp factors
  const clampedStretch = Math.min(stretchFactor, config.maxStretch);
  const clampedSquash = Math.max(squashFactor, config.maxSquash);

  // Calculate scale in each axis based on velocity direction
  // Stretch along velocity, squash perpendicular
  const absX = Math.abs(dir.x);
  const absY = Math.abs(dir.y);
  const absZ = Math.abs(dir.z);

  // Determine dominant axis
  if (absY > absX && absY > absZ) {
    // Vertical motion - stretch Y, squash X and Z
    return {
      x: clampedSquash,
      y: clampedStretch,
      z: clampedSquash,
    };
  } else if (absX > absZ) {
    // Horizontal X motion
    return {
      x: clampedStretch,
      y: clampedSquash,
      z: clampedSquash,
    };
  } else {
    // Z motion
    return {
      x: clampedSquash,
      y: clampedSquash,
      z: clampedStretch,
    };
  }
}

/**
 * Calculate velocity from position keyframes at a given frame
 */
export function calculateVelocityAtFrame(
  position: AnimatableProperty<Vec3>,
  frame: number,
  fps: number = 30,
): Vec3 {
  const dt = 1 / fps;

  // Get positions at adjacent frames
  const posCurrent = interpolateProperty(position, frame);
  const posPrev = interpolateProperty(position, Math.max(0, frame - 1));

  // Calculate velocity (position delta / time delta)
  return {
    x: (posCurrent.x - posPrev.x) / dt,
    y: (posCurrent.y - posPrev.y) / dt,
    z: (posCurrent.z - posPrev.z) / dt,
  };
}

// ============================================================================
// BOUNCE PHYSICS
// ============================================================================

/**
 * Calculate bounce position at a given time after impact
 *
 * @param impactTime - Frame when object hits ground
 * @param initialVelocityY - Downward velocity at impact (negative)
 * @param currentFrame - Current frame to evaluate
 * @param config - Bounce configuration
 * @returns Y offset from ground plane
 */
export function calculateBounceOffset(
  impactFrame: number,
  initialVelocityY: number,
  currentFrame: number,
  fps: number,
  config: BounceConfig = DEFAULT_BOUNCE,
): number {
  if (!config.enabled || currentFrame < impactFrame) {
    return 0;
  }

  const t = (currentFrame - impactFrame) / fps; // Time since impact in seconds
  let velocity = Math.abs(initialVelocityY); // Convert to positive (bounce up)
  let bounceStartTime = 0;
  let bounceCount = 0;

  // Find which bounce we're in
  while (bounceCount < config.maxBounces) {
    // Time to reach apex of this bounce
    const timeToApex = velocity / config.gravity;
    // Total time for this bounce (up and down)
    const bounceDuration = timeToApex * 2;

    if (t - bounceStartTime < bounceDuration) {
      // We're in this bounce
      const localT = t - bounceStartTime;

      // Parabolic motion: h = v*t - 0.5*g*t^2
      const height = velocity * localT - 0.5 * config.gravity * localT * localT;
      return Math.max(0, height);
    }

    // Move to next bounce
    bounceStartTime += bounceDuration;
    velocity *= config.elasticity;
    bounceCount++;

    // If velocity too low, stop bouncing
    if (velocity < 10) {
      return 0;
    }
  }

  return 0;
}

/**
 * Calculate squash at bounce impact point
 */
export function calculateImpactSquash(
  impactFrame: number,
  currentFrame: number,
  _fps: number,
  config: SquashStretchConfig = DEFAULT_SQUASH_STRETCH,
): Vec3 {
  const framesSinceImpact = currentFrame - impactFrame;

  if (framesSinceImpact < 0 || framesSinceImpact > 5) {
    return { x: 1, y: 1, z: 1 };
  }

  // Quick squash and recover
  // Peak squash at frame 1, recover by frame 5
  const squashProgress = framesSinceImpact / 5;
  const squashAmount =
    Math.sin(squashProgress * Math.PI) * (1 - config.maxSquash);

  return {
    x: 1 + squashAmount * 0.5, // Expand horizontally
    y: 1 - squashAmount, // Compress vertically
    z: 1 + squashAmount * 0.5, // Expand depth
  };
}

// ============================================================================
// 3D PIN DEFORMATION
// ============================================================================

/**
 * Create a default 3D deformation pin
 */
export function createDefault3DPin(
  id: string,
  position: Vec3,
): Deformation3DPin {
  return {
    id,
    name: `Pin ${id.slice(-4)}`,
    position: {
      id: `${id}_pos`,
      name: "Position",
      type: "position",
      value: { ...position },
      animated: false,
      keyframes: [],
    },
    radius: 100,
    falloff: 2,
    stiffness: 0,
    restPosition: { ...position },
  };
}

/**
 * Calculate weight for a vertex based on distance to pin
 */
export function calculate3DPinWeight(
  vertexPosition: Vec3,
  pin: Deformation3DPin,
  pinPosition: Vec3,
): number {
  const dx = vertexPosition.x - pinPosition.x;
  const dy = vertexPosition.y - pinPosition.y;
  const dz = vertexPosition.z - pinPosition.z;
  const distance = Math.sqrt(dx * dx + dy * dy + dz * dz);

  if (distance > pin.radius * 3) {
    return 0; // Too far, no influence
  }

  if (distance < 0.001) {
    return 1; // At pin position
  }

  // Inverse distance weighting with radius falloff
  const normalizedDist = distance / pin.radius;
  const weight = (1 / (1 + normalizedDist)) ** pin.falloff;

  // Apply stiffness (reduces deformation)
  return weight * (1 - pin.stiffness);
}

/**
 * Deform a 3D position based on multiple pins
 */
export function deform3DPosition(
  originalPosition: Vec3,
  pins: Deformation3DPin[],
  frame: number,
): Vec3 {
  if (pins.length === 0) {
    return { ...originalPosition };
  }

  let totalWeight = 0;
  let deformedX = 0;
  let deformedY = 0;
  let deformedZ = 0;

  for (const pin of pins) {
    // Get pin's current animated position
    const pinPos = interpolateProperty(pin.position, frame);

    // Calculate displacement from rest position
    const deltaX = pinPos.x - pin.restPosition.x;
    const deltaY = pinPos.y - pin.restPosition.y;
    const deltaZ = pinPos.z - pin.restPosition.z;

    // Calculate weight for this vertex relative to pin's rest position
    const weight = calculate3DPinWeight(
      originalPosition,
      pin,
      pin.restPosition,
    );

    if (weight > 0) {
      // Apply weighted displacement
      deformedX += (originalPosition.x + deltaX) * weight;
      deformedY += (originalPosition.y + deltaY) * weight;
      deformedZ += (originalPosition.z + deltaZ) * weight;
      totalWeight += weight;
    }
  }

  if (totalWeight > 0) {
    return {
      x: deformedX / totalWeight,
      y: deformedY / totalWeight,
      z: deformedZ / totalWeight,
    };
  }

  return { ...originalPosition };
}

// ============================================================================
// THREE.JS INTEGRATION
// ============================================================================

/**
 * Apply squash/stretch to a Three.js object
 */
export function applySquashStretchToObject(
  object: THREE.Object3D,
  scale: Vec3,
): void {
  object.scale.set(scale.x, scale.y, scale.z);
}

/**
 * Deform a Three.js BufferGeometry using pins
 */
export function deformGeometryWithPins(
  geometry: THREE.BufferGeometry,
  originalPositions: Float32Array,
  pins: Deformation3DPin[],
  frame: number,
): void {
  const positions = geometry.attributes.position;
  const vertexCount = positions.count;

  for (let i = 0; i < vertexCount; i++) {
    const original: Vec3 = {
      x: originalPositions[i * 3],
      y: originalPositions[i * 3 + 1],
      z: originalPositions[i * 3 + 2],
    };

    const deformed = deform3DPosition(original, pins, frame);

    positions.setXYZ(i, deformed.x, deformed.y, deformed.z);
  }

  positions.needsUpdate = true;
  geometry.computeVertexNormals();
}

// ============================================================================
// SERVICE CLASS
// ============================================================================

export class MeshDeformation3DService {
  private pinsByLayer = new Map<string, Deformation3DPin[]>();
  private originalGeometries = new Map<string, Float32Array>();
  private squashStretchConfigs = new Map<string, SquashStretchConfig>();
  private bounceConfigs = new Map<string, BounceConfig>();

  /**
   * Initialize deformation for a layer
   */
  initializeLayer(
    layerId: string,
    geometry?: THREE.BufferGeometry,
    squashStretch?: Partial<SquashStretchConfig>,
    bounce?: Partial<BounceConfig>,
  ): void {
    this.pinsByLayer.set(layerId, []);

    if (geometry) {
      // Store original vertex positions
      const positions = geometry.attributes.position.array as Float32Array;
      this.originalGeometries.set(layerId, new Float32Array(positions));
    }

    this.squashStretchConfigs.set(layerId, {
      ...DEFAULT_SQUASH_STRETCH,
      ...squashStretch,
    });

    this.bounceConfigs.set(layerId, {
      ...DEFAULT_BOUNCE,
      ...bounce,
    });

    logger.debug(`Initialized 3D deformation for layer ${layerId}`);
  }

  /**
   * Add a pin to a layer
   */
  addPin(layerId: string, position: Vec3): Deformation3DPin {
    const pins = this.pinsByLayer.get(layerId) ?? [];
    const id = `pin_${layerId}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
    const pin = createDefault3DPin(id, position);
    pins.push(pin);
    this.pinsByLayer.set(layerId, pins);
    return pin;
  }

  /**
   * Get pins for a layer
   */
  getPins(layerId: string): Deformation3DPin[] {
    return this.pinsByLayer.get(layerId) ?? [];
  }

  /**
   * Evaluate deformation at a frame
   */
  evaluate(
    layerId: string,
    frame: number,
    position: AnimatableProperty<Vec3>,
    fps: number = 30,
  ): Deformation3DResult {
    const squashConfig =
      this.squashStretchConfigs.get(layerId) ?? DEFAULT_SQUASH_STRETCH;

    // Calculate velocity for squash/stretch
    const velocity = calculateVelocityAtFrame(position, frame, fps);
    const scale = calculateSquashStretch(velocity, squashConfig);

    // Get evaluated position
    const pos = interpolateProperty(position, frame);

    return {
      position: pos,
      scale,
      rotation: { x: 0, y: 0, z: 0 },
    };
  }

  /**
   * Clear a layer's deformation data
   */
  clearLayer(layerId: string): void {
    this.pinsByLayer.delete(layerId);
    this.originalGeometries.delete(layerId);
    this.squashStretchConfigs.delete(layerId);
    this.bounceConfigs.delete(layerId);
  }

  /**
   * Clear all data
   */
  clearAll(): void {
    this.pinsByLayer.clear();
    this.originalGeometries.clear();
    this.squashStretchConfigs.clear();
    this.bounceConfigs.clear();
  }
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const meshDeformation3D = new MeshDeformation3DService();
export default meshDeformation3D;
