/**
 * Camera Trajectory System - Uni3C-style Camera Motion Presets
 *
 * Provides predefined camera movement trajectories that can be applied
 * to Camera3D objects. Based on Uni3C camera control parameters.
 *
 * Supports:
 * - Spherical coordinate system (distance, theta/azimuth, phi/elevation)
 * - Trajectory presets (orbit, swing, dolly, pan, etc.)
 * - Keyframe generation from trajectories
 * - Audio-reactive camera motion
 */

import type { Camera3D, CameraKeyframe } from "@/types/camera";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/** Spherical camera coordinates (Uni3C style) */
export interface SphericalCoords {
  /** Distance from center (0.25-2.5, default 1.0) */
  d_r: number;
  /** Elevation angle in degrees (-90 to 30, where 0 is horizon) */
  d_theta: number;
  /** Azimuth angle in degrees (-360 to 360, horizontal rotation) */
  d_phi: number;
  /** X offset (-0.5 to 0.5) */
  x_offset: number;
  /** Y offset (-0.5 to 0.5) */
  y_offset: number;
  /** Z offset (-0.5 to 0.5) */
  z_offset: number;
  /** Focal length multiplier (0.25-2.5) */
  focalMultiplier: number;
}

/** Trajectory preset types */
export type TrajectoryType =
  | "custom"
  | "orbit"
  | "orbit_reverse"
  | "swing1"
  | "swing2"
  | "dolly_in"
  | "dolly_out"
  | "pan_left"
  | "pan_right"
  | "tilt_up"
  | "tilt_down"
  | "zoom_in"
  | "zoom_out"
  | "circle"
  | "figure8"
  | "spiral_in"
  | "spiral_out"
  | "crane_up"
  | "crane_down"
  | "truck_left"
  | "truck_right"
  | "arc_left"
  | "arc_right";

/** Trajectory configuration */
export interface TrajectoryConfig {
  type: TrajectoryType;
  /** Base distance from target (pixels) */
  baseDistance: number;
  /** Center point to orbit/look at */
  center: { x: number; y: number; z: number };
  /** Duration in frames */
  duration: number;
  /** Starting phase (0-1) */
  startPhase: number;
  /** Number of loops (for orbit, circle, etc.) */
  loops: number;
  /** Amplitude/strength multiplier */
  amplitude: number;
  /** Easing type */
  easing: "linear" | "ease-in" | "ease-out" | "ease-in-out" | "bounce";
  /** Enable for audio-reactive motion */
  audioReactive: boolean;
  /** Audio feature to react to */
  audioFeature?: string;
  /** Audio sensitivity */
  audioSensitivity?: number;
}

/** Keyframe output for trajectory */
export interface TrajectoryKeyframes {
  position: CameraKeyframe[];
  pointOfInterest: CameraKeyframe[];
  zoom?: CameraKeyframe[];
}

// ════════════════════════════════════════════════════════════════════════════
//                                                         // default // values
// ════════════════════════════════════════════════════════════════════════════

export const DEFAULT_SPHERICAL: SphericalCoords = {
  d_r: 1.0,
  d_theta: 0,
  d_phi: 0,
  x_offset: 0,
  y_offset: 0,
  z_offset: 0,
  focalMultiplier: 1.0,
};

export const DEFAULT_TRAJECTORY: TrajectoryConfig = {
  type: "custom",
  baseDistance: 1500,
  center: { x: 960, y: 540, z: 0 },
  duration: 150, // 5 seconds at 30fps
  startPhase: 0,
  loops: 1,
  amplitude: 1.0,
  easing: "ease-in-out",
  audioReactive: false,
};

// ════════════════════════════════════════════════════════════════════════════
//                                                     // trajectory // presets
// ════════════════════════════════════════════════════════════════════════════

export const TRAJECTORY_PRESETS: Record<
  TrajectoryType,
  Partial<TrajectoryConfig>
> = {
  custom: {},

  orbit: {
    loops: 1,
    amplitude: 1.0,
    easing: "linear",
  },

  orbit_reverse: {
    loops: 1,
    amplitude: -1.0, // Negative for reverse
    easing: "linear",
  },

  swing1: {
    amplitude: 0.25, // Smaller arc
    easing: "ease-in-out",
  },

  swing2: {
    amplitude: 0.5, // Larger arc
    easing: "ease-in-out",
  },

  dolly_in: {
    amplitude: 0.5, // Move 50% closer
    easing: "ease-out",
  },

  dolly_out: {
    amplitude: -0.5, // Move 50% away
    easing: "ease-in",
  },

  pan_left: {
    amplitude: 30, // 30 degree pan
    easing: "ease-in-out",
  },

  pan_right: {
    amplitude: -30,
    easing: "ease-in-out",
  },

  tilt_up: {
    amplitude: 20, // 20 degree tilt
    easing: "ease-in-out",
  },

  tilt_down: {
    amplitude: -20,
    easing: "ease-in-out",
  },

  zoom_in: {
    amplitude: 0.5, // 50% zoom increase
    easing: "ease-out",
  },

  zoom_out: {
    amplitude: -0.3, // 30% zoom decrease
    easing: "ease-in",
  },

  circle: {
    loops: 1,
    amplitude: 1.0,
    easing: "linear",
  },

  figure8: {
    loops: 1,
    amplitude: 1.0,
    easing: "linear",
  },

  spiral_in: {
    loops: 2,
    amplitude: 0.6,
    easing: "ease-out",
  },

  spiral_out: {
    loops: 2,
    amplitude: 0.6,
    easing: "ease-in",
  },

  crane_up: {
    amplitude: 500, // Pixels to move up
    easing: "ease-in-out",
  },

  crane_down: {
    amplitude: -500,
    easing: "ease-in-out",
  },

  truck_left: {
    amplitude: 300, // Pixels to move left
    easing: "ease-in-out",
  },

  truck_right: {
    amplitude: -300,
    easing: "ease-in-out",
  },

  arc_left: {
    amplitude: 0.25, // Quarter circle left
    easing: "ease-in-out",
  },

  arc_right: {
    amplitude: -0.25,
    easing: "ease-in-out",
  },
};

// ════════════════════════════════════════════════════════════════════════════
//                                                      // utility // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert spherical coordinates to Cartesian position
 */
export function sphericalToCartesian(
  spherical: SphericalCoords,
  center: { x: number; y: number; z: number },
  baseDistance: number,
): { x: number; y: number; z: number } {
  const r = baseDistance * spherical.d_r;
  const theta = spherical.d_theta * (Math.PI / 180); // Elevation
  const phi = spherical.d_phi * (Math.PI / 180); // Azimuth

  // Spherical to Cartesian (Y-up coordinate system)
  const x = r * Math.cos(theta) * Math.sin(phi);
  const y = r * Math.sin(theta);
  const z = r * Math.cos(theta) * Math.cos(phi);

  return {
    x: center.x + x + spherical.x_offset * baseDistance,
    y: center.y + y + spherical.y_offset * baseDistance,
    z: center.z - z + spherical.z_offset * baseDistance, // Negative Z = camera behind
  };
}

/**
 * Convert Cartesian position to spherical coordinates
 */
export function cartesianToSpherical(
  position: { x: number; y: number; z: number },
  center: { x: number; y: number; z: number },
  baseDistance: number,
): SphericalCoords {
  const dx = position.x - center.x;
  const dy = position.y - center.y;
  const dz = center.z - position.z; // Flip Z

  const r = Math.sqrt(dx * dx + dy * dy + dz * dz);
  const theta = Math.asin(dy / r) * (180 / Math.PI);
  const phi = Math.atan2(dx, dz) * (180 / Math.PI);

  return {
    d_r: r / baseDistance,
    d_theta: theta,
    d_phi: phi,
    x_offset: 0,
    y_offset: 0,
    z_offset: 0,
    focalMultiplier: 1.0,
  };
}

/**
 * Apply easing function
 */
function applyEasing(t: number, easing: TrajectoryConfig["easing"]): number {
  switch (easing) {
    case "linear":
      return t;
    case "ease-in":
      return t * t;
    case "ease-out":
      return 1 - (1 - t) * (1 - t);
    case "ease-in-out":
      return t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2;
    case "bounce": {
      if (t < 0.5) {
        return 8 * t * t * t * t;
      }
      const f = t - 1;
      return 1 - 8 * f * f * f * f;
    }
    default:
      return t;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                  // trajectory // generation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Generate camera position at a specific time along trajectory
 */
export function getTrajectoryPosition(
  config: TrajectoryConfig,
  t: number, // Normalized time 0-1
): {
  position: { x: number; y: number; z: number };
  target: { x: number; y: number; z: number };
} {
  const easedT = applyEasing(t, config.easing);
  const { center, baseDistance, amplitude, loops, startPhase, type } = config;

  let position = { x: center.x, y: center.y, z: center.z - baseDistance };
  let target = { ...center };

  switch (type) {
    case "orbit":
    case "orbit_reverse": {
      const angle =
        (startPhase + easedT * loops) * 2 * Math.PI * Math.sign(amplitude);
      position = {
        x: center.x + Math.sin(angle) * baseDistance,
        y: center.y,
        z: center.z - Math.cos(angle) * baseDistance,
      };
      break;
    }

    case "swing1":
    case "swing2": {
      const maxAngle = Math.abs(amplitude) * Math.PI;
      const angle = Math.sin(easedT * Math.PI) * maxAngle;
      position = {
        x: center.x + Math.sin(angle) * baseDistance,
        y: center.y,
        z: center.z - Math.cos(angle) * baseDistance,
      };
      break;
    }

    case "dolly_in": {
      const distance = baseDistance * (1 - easedT * Math.abs(amplitude));
      position = {
        x: center.x,
        y: center.y,
        z: center.z - distance,
      };
      break;
    }

    case "dolly_out": {
      const distance = baseDistance * (1 + easedT * Math.abs(amplitude));
      position = {
        x: center.x,
        y: center.y,
        z: center.z - distance,
      };
      break;
    }

    case "pan_left":
    case "pan_right": {
      const panAngle = easedT * amplitude * (Math.PI / 180);
      target = {
        x: center.x + Math.sin(panAngle) * baseDistance,
        y: center.y,
        z: center.z + Math.cos(panAngle) * baseDistance - baseDistance,
      };
      break;
    }

    case "tilt_up":
    case "tilt_down": {
      const tiltAngle = easedT * amplitude * (Math.PI / 180);
      target = {
        x: center.x,
        y: center.y + Math.sin(tiltAngle) * baseDistance,
        z: center.z,
      };
      break;
    }

    case "circle": {
      const angle = (startPhase + easedT * loops) * 2 * Math.PI;
      const radius = baseDistance * 0.3 * Math.abs(amplitude);
      position = {
        x: center.x + Math.sin(angle) * radius,
        y: center.y + Math.cos(angle) * radius * 0.5, // Elliptical
        z: center.z - baseDistance + Math.cos(angle) * radius * 0.3,
      };
      break;
    }

    case "figure8": {
      const angle = (startPhase + easedT * loops) * 2 * Math.PI;
      const radius = baseDistance * 0.3 * Math.abs(amplitude);
      position = {
        x: center.x + Math.sin(angle) * radius,
        y: center.y + Math.sin(angle * 2) * radius * 0.3,
        z: center.z - baseDistance,
      };
      break;
    }

    case "spiral_in": {
      const angle = (startPhase + easedT * loops) * 2 * Math.PI;
      const radius = baseDistance * (1 - easedT * Math.abs(amplitude));
      position = {
        x: center.x + Math.sin(angle) * radius * 0.3,
        y: center.y,
        z: center.z - radius,
      };
      break;
    }

    case "spiral_out": {
      const angle = (startPhase + easedT * loops) * 2 * Math.PI;
      const radius = baseDistance * (1 + easedT * Math.abs(amplitude));
      position = {
        x: center.x + Math.sin(angle) * radius * 0.3,
        y: center.y,
        z: center.z - radius,
      };
      break;
    }

    case "crane_up":
    case "crane_down": {
      position = {
        x: center.x,
        y: center.y + easedT * amplitude,
        z: center.z - baseDistance,
      };
      target = {
        x: center.x,
        y: center.y + easedT * amplitude * 0.5, // Target moves less
        z: center.z,
      };
      break;
    }

    case "truck_left":
    case "truck_right": {
      position = {
        x: center.x + easedT * amplitude,
        y: center.y,
        z: center.z - baseDistance,
      };
      target = {
        x: center.x + easedT * amplitude,
        y: center.y,
        z: center.z,
      };
      break;
    }

    case "arc_left":
    case "arc_right": {
      const arcAngle = easedT * amplitude * 2 * Math.PI;
      position = {
        x: center.x + Math.sin(arcAngle) * baseDistance,
        y: center.y,
        z: center.z - Math.cos(arcAngle) * baseDistance,
      };
      break;
    }

    default:
      // Custom - return current position
      break;
  }

  return { position, target };
}

/**
 * Generate keyframes for a camera trajectory
 */
export function generateTrajectoryKeyframes(
  config: TrajectoryConfig,
  startFrame: number = 0,
  keyframeInterval: number = 5, // One keyframe every N frames
): TrajectoryKeyframes {
  const positionKeyframes: CameraKeyframe[] = [];
  const poiKeyframes: CameraKeyframe[] = [];
  const zoomKeyframes: CameraKeyframe[] = [];

  const numKeyframes = Math.ceil(config.duration / keyframeInterval) + 1;

  for (let i = 0; i < numKeyframes; i++) {
    const frame = startFrame + Math.min(i * keyframeInterval, config.duration);
    const t = Math.min(i * keyframeInterval, config.duration) / config.duration;

    const { position, target } = getTrajectoryPosition(config, t);

    positionKeyframes.push({
      frame,
      position,
      spatialInterpolation: "bezier",
      temporalInterpolation: "linear",
    });

    poiKeyframes.push({
      frame,
      pointOfInterest: target,
      spatialInterpolation: "bezier",
      temporalInterpolation: "linear",
    });

    // Add zoom keyframes for zoom trajectories
    if (config.type === "zoom_in" || config.type === "zoom_out") {
      const easedT = applyEasing(t, config.easing);
      const zoomMultiplier =
        config.type === "zoom_in"
          ? 1 + easedT * Math.abs(config.amplitude)
          : 1 - easedT * Math.abs(config.amplitude);

      zoomKeyframes.push({
        frame,
        zoom: 1778 * zoomMultiplier, // Base 50mm zoom
        temporalInterpolation: "linear",
      });
    }
  }

  return {
    position: positionKeyframes,
    pointOfInterest: poiKeyframes,
    zoom: zoomKeyframes.length > 0 ? zoomKeyframes : undefined,
  };
}

/**
 * Apply trajectory to a Camera3D object (modifies in place)
 */
export function applyCameraTrajectory(
  camera: Camera3D,
  config: TrajectoryConfig,
  t: number, // Normalized time 0-1
): void {
  const { position, target } = getTrajectoryPosition(config, t);

  camera.position = position;

  if (camera.type === "two-node") {
    camera.pointOfInterest = target;
  }

  // Apply zoom for zoom trajectories
  if (config.type === "zoom_in" || config.type === "zoom_out") {
    const easedT = applyEasing(t, config.easing);
    const zoomMultiplier =
      config.type === "zoom_in"
        ? 1 + easedT * Math.abs(config.amplitude)
        : 1 - easedT * Math.abs(config.amplitude);
    camera.zoom *= zoomMultiplier;
  }
}

/**
 * Create trajectory config from preset
 */
export function createTrajectoryFromPreset(
  preset: TrajectoryType,
  overrides?: Partial<TrajectoryConfig>,
): TrajectoryConfig {
  return {
    ...DEFAULT_TRAJECTORY,
    ...TRAJECTORY_PRESETS[preset],
    type: preset,
    ...overrides,
  };
}

/**
 * Get human-readable description of trajectory
 */
export function getTrajectoryDescription(type: TrajectoryType): string {
  const descriptions: Record<TrajectoryType, string> = {
    custom: "Custom trajectory with manual keyframes",
    orbit: "360° horizontal orbit around target",
    orbit_reverse: "360° reverse orbit around target",
    swing1: "Gentle pendulum swing (45°)",
    swing2: "Wide pendulum swing (90°)",
    dolly_in: "Move camera toward target",
    dolly_out: "Move camera away from target",
    pan_left: "Rotate camera left while stationary",
    pan_right: "Rotate camera right while stationary",
    tilt_up: "Tilt camera up while stationary",
    tilt_down: "Tilt camera down while stationary",
    zoom_in: "Zoom lens in (narrower FOV)",
    zoom_out: "Zoom lens out (wider FOV)",
    circle: "Elliptical circling motion",
    figure8: "Figure-8 weaving pattern",
    spiral_in: "Spiral toward target",
    spiral_out: "Spiral away from target",
    crane_up: "Vertical lift (crane shot up)",
    crane_down: "Vertical descent (crane shot down)",
    truck_left: "Horizontal slide left",
    truck_right: "Horizontal slide right",
    arc_left: "Curved arc movement left",
    arc_right: "Curved arc movement right",
  };

  return descriptions[type] || "Unknown trajectory";
}

/**
 * Get category for trajectory type (for UI grouping)
 */
export function getTrajectoryCategory(type: TrajectoryType): string {
  const categories: Record<TrajectoryType, string> = {
    custom: "Custom",
    orbit: "Orbital",
    orbit_reverse: "Orbital",
    swing1: "Orbital",
    swing2: "Orbital",
    circle: "Orbital",
    figure8: "Orbital",
    arc_left: "Orbital",
    arc_right: "Orbital",
    dolly_in: "Dolly",
    dolly_out: "Dolly",
    spiral_in: "Dolly",
    spiral_out: "Dolly",
    pan_left: "Pan/Tilt",
    pan_right: "Pan/Tilt",
    tilt_up: "Pan/Tilt",
    tilt_down: "Pan/Tilt",
    crane_up: "Crane",
    crane_down: "Crane",
    truck_left: "Truck",
    truck_right: "Truck",
    zoom_in: "Zoom",
    zoom_out: "Zoom",
  };

  return categories[type] || "Other";
}

/**
 * Get all trajectory types grouped by category
 */
export function getTrajectoryTypesByCategory(): Record<
  string,
  TrajectoryType[]
> {
  const types = Object.keys(TRAJECTORY_PRESETS) as TrajectoryType[];
  const grouped: Record<string, TrajectoryType[]> = {};

  for (const type of types) {
    const category = getTrajectoryCategory(type);
    if (!grouped[category]) {
      grouped[category] = [];
    }
    grouped[category].push(type);
  }

  return grouped;
}
