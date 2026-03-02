/**
 * Mesh Warp Types
 *
 * Types for mesh deformation using control pins.
 * Supports position, rotation, and stiffness pin types.
 *
 * This provides vector skinning-style deformation for spline layers,
 * allowing organic animation by manipulating control pins.
 */

import type { AnimatableProperty } from "./project";

// ============================================================================
// PIN TYPES
// ============================================================================

/** Type of warp pin */
export type WarpPinType =
  | "position" // Deform pin: Move mesh vertices by animating position
  | "rotation" // Rotation pin: Rotate around fixed point (legacy, use 'bend' for new code)
  | "starch" // Stiffness pin: Define rigid areas that resist deformation
  | "overlap" // Overlap pin: Control depth/z-order during deformation
  | "bend" // Bend pin: Rotation + scale at joints (position is fixed reference)
  | "advanced"; // Advanced pin: Full transform control (position + rotation + scale)

/**
 * A control pin for mesh warp deformation
 *
 * Pin type determines which properties are actively used:
 * - position: Animates position only (standard deform pin)
 * - rotation: Animates rotation only (legacy, prefer 'bend')
 * - starch: No animation, uses stiffness to define rigid areas
 * - overlap: No position animation, uses inFront for depth control
 * - bend: Animates rotation + scale at fixed position (joint pin)
 * - advanced: Animates position + rotation + scale (full transform)
 */
export interface WarpPin {
  /** Unique identifier */
  id: string;
  /** Display name */
  name: string;
  /** Pin type determines deformation behavior */
  type: WarpPinType;
  /** Pin position (animatable for position/advanced types) */
  position: AnimatableProperty<{ x: number; y: number }>;
  /** Influence radius in pixels (also used as extent for overlap pins) */
  radius: number;
  /** Stiffness/rigidity of the pin area (0-1, used by starch type) */
  stiffness: number;
  /** Rotation at this pin in degrees (animatable for rotation/bend/advanced types) */
  rotation: AnimatableProperty<number>;
  /** Scale factor at this pin (animatable for bend/advanced types) */
  scale: AnimatableProperty<number>;
  /** Pin depth/priority (higher = processed first) */
  depth: number;
  /** Is this pin selected in the UI */
  selected?: boolean;
  /**
   * Overlap depth value (animatable, used by overlap type)
   * Positive = in front of other mesh areas, Negative = behind
   * Range: -100 to +100
   */
  inFront?: AnimatableProperty<number>;
}

/**
 * Initial/rest state of a pin (before animation)
 * Used for calculating animation deltas
 */
export interface WarpPinRestState {
  pinId: string;
  position: { x: number; y: number };
  rotation: number;
  scale: number;
  /** Rest state for overlap depth (for overlap pins) */
  inFront?: number;
}

// ============================================================================
// MESH TYPES
// ============================================================================

/**
 * A triangulated mesh for warp deformation
 */
export interface WarpMesh {
  /** Layer this mesh belongs to */
  layerId: string;
  /** Control pins for deformation */
  pins: WarpPin[];
  /** Triangle indices (triplets of vertex indices) */
  triangulation: number[];
  /** Pin influence weights per vertex (pinCount weights per vertex) */
  weights: Float32Array;
  /** Original (undeformed) vertex positions */
  originalVertices: Float32Array;
  /** Rest state of pins (for calculating deltas) */
  pinRestStates: WarpPinRestState[];
  /** Number of vertices in the mesh */
  vertexCount: number;
  /** Whether mesh needs rebuild */
  dirty: boolean;
}

/**
 * Result of deforming a mesh
 */
export interface WarpDeformationResult {
  /** Deformed vertex positions */
  vertices: Float32Array;
  /** Deformed control point positions (for path reconstruction) */
  controlPoints: Array<{
    x: number;
    y: number;
    inHandle: { x: number; y: number };
    outHandle: { x: number; y: number };
  }>;
}

// ============================================================================
// WEIGHT CALCULATION
// ============================================================================

/** Method for calculating pin influence weights */
export type WarpWeightMethod =
  | "inverse-distance" // Standard 1/d^n falloff
  | "heat-diffusion" // Heat equation simulation
  | "radial-basis" // RBF interpolation
  | "bounded"; // Bounded biharmonic weights

/**
 * Options for weight calculation
 */
export interface WarpWeightOptions {
  /** Weight calculation method */
  method: WarpWeightMethod;
  /** Falloff power for inverse-distance (typically 2) */
  falloffPower: number;
  /** Whether to normalize weights to sum to 1 */
  normalize: boolean;
  /** Minimum weight threshold (weights below this are set to 0) */
  minWeight: number;
}

// ============================================================================
// DEFAULTS
// ============================================================================

/** Default weight calculation options */
export const DEFAULT_WARP_WEIGHT_OPTIONS: WarpWeightOptions = {
  method: "inverse-distance",
  falloffPower: 2,
  normalize: true,
  minWeight: 0.001,
};

/** Create a default warp pin */
export function createDefaultWarpPin(
  id: string,
  x: number,
  y: number,
  type: WarpPinType = "position",
): WarpPin {
  const pin: WarpPin = {
    id,
    name: getPinDefaultName(type, id),
    type,
    position: {
      id: `pin_pos_${id}`,
      name: "Position",
      type: "position",
      value: { x, y },
      animated: false,
      keyframes: [],
    },
    radius: 50,
    stiffness: type === "starch" ? 1.0 : 0.0,
    rotation: {
      id: `pin_rot_${id}`,
      name: "Rotation",
      type: "number",
      value: 0,
      animated: false,
      keyframes: [],
    },
    scale: {
      id: `pin_scale_${id}`,
      name: "Scale",
      type: "number",
      value: 1,
      animated: false,
      keyframes: [],
    },
    depth: 0,
    selected: false,
  };

  // Add inFront property for overlap pins
  if (type === "overlap") {
    pin.inFront = {
      id: `pin_infront_${id}`,
      name: "In Front",
      type: "number",
      value: 0,
      animated: false,
      keyframes: [],
    };
  }

  return pin;
}

/** Get default name based on pin type */
function getPinDefaultName(type: WarpPinType, id: string): string {
  const suffix = id.slice(-4);
  switch (type) {
    case "position":
      return `Deform ${suffix}`;
    case "starch":
      return `Stiffness ${suffix}`;
    case "overlap":
      return `Overlap ${suffix}`;
    case "bend":
      return `Bend ${suffix}`;
    case "advanced":
      return `Advanced ${suffix}`;
    default:
      return `Pin ${suffix}`;
  }
}

/** Create an empty warp mesh */
export function createEmptyWarpMesh(layerId: string): WarpMesh {
  return {
    layerId,
    pins: [],
    triangulation: [],
    weights: new Float32Array(0),
    originalVertices: new Float32Array(0),
    pinRestStates: [],
    vertexCount: 0,
    dirty: true,
  };
}

// ============================================================================
// BACKWARDS COMPATIBILITY ALIASES
// ============================================================================

/** @deprecated Use WarpPinType instead */
export type PinType = WarpPinType;

/** @deprecated Use WarpPin instead */
export type PuppetPin = WarpPin;

/** @deprecated Use WarpPinRestState instead */
export type PinRestState = WarpPinRestState;

/** @deprecated Use WarpMesh instead */
export type PuppetMesh = WarpMesh;

/** @deprecated Use WarpDeformationResult instead */
export type DeformationResult = WarpDeformationResult;

/** @deprecated Use WarpWeightMethod instead */
export type WeightMethod = WarpWeightMethod;

/** @deprecated Use WarpWeightOptions instead */
export type WeightOptions = WarpWeightOptions;

/** @deprecated Use DEFAULT_WARP_WEIGHT_OPTIONS instead */
export const DEFAULT_WEIGHT_OPTIONS = DEFAULT_WARP_WEIGHT_OPTIONS;

/** @deprecated Use createDefaultWarpPin instead */
export const createDefaultPuppetPin = createDefaultWarpPin;

/** @deprecated Use createEmptyWarpMesh instead */
export const createEmptyPuppetMesh = createEmptyWarpMesh;
