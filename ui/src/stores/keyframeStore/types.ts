/**
 * Keyframe Store Types
 *
 * Interface definitions for keyframe store operations.
 */

import type {
  AnimatableProperty,
  ClipboardKeyframe,
  Layer,
} from "@/types/project";

// ============================================================================
// STORE ACCESS INTERFACES
// ============================================================================

/**
 * Base interface for keyframe store operations.
 * Provides access to project state and layer data.
 */
export interface KeyframeStoreAccess {
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  getActiveComp(): {
    currentFrame: number;
    layers: Layer[];
    settings: { fps: number; frameCount: number; duration: number; width: number; height: number };
  } | null;
  getActiveCompLayers(): Layer[];
  getLayerById(id: string): Layer | null;
  pushHistory(): void;
  /** Get FPS from active composition */
  readonly fps: number;
}

/**
 * Extended interface for roving keyframe operations.
 * Same as base but explicitly requires getLayerById.
 */
export interface RovingKeyframeStoreAccess extends KeyframeStoreAccess {
  getLayerById(id: string): Layer | null;
}

/**
 * Extended interface for clipboard operations.
 * Adds clipboard state and current frame access.
 */
export interface ClipboardKeyframeStoreAccess extends KeyframeStoreAccess {
  clipboard: {
    keyframes: ClipboardKeyframe[];
  };
  currentFrame: number;
}

/**
 * Extended interface for velocity operations.
 * Adds FPS access for velocity calculations.
 */
export interface VelocityStoreAccess extends KeyframeStoreAccess {
  fps: number;
}

/**
 * Extended interface for expression baking.
 * Adds frame count and property evaluation capability.
 */
export interface BakeExpressionStoreAccess extends KeyframeStoreAccess {
  fps: number;
  frameCount: number;
  currentFrame: number;
  /** Returns array for position/scale (x,y components), number for scalars, null if not found */
  evaluatePropertyAtFrame(
    layerId: string,
    propertyPath: string,
    frame: number,
  ): number[] | number | null;
}

// ============================================================================
// OPERATION PARAMETERS
// ============================================================================

/**
 * Velocity settings for keyframe handles.
 */
export interface VelocitySettings {
  /** Incoming velocity in units per second */
  incomingVelocity: number;
  /** Outgoing velocity in units per second */
  outgoingVelocity: number;
  /** Incoming influence as percentage (0-100) */
  incomingInfluence: number;
  /** Outgoing influence as percentage (0-100) */
  outgoingInfluence: number;
}

/**
 * Keyframe selection for bulk operations.
 */
export interface KeyframeSelection {
  layerId: string;
  propertyPath: string;
  keyframeId: string;
}

// ============================================================================
// STORE STATE
// ============================================================================

/**
 * Keyframe store state.
 * Maintains clipboard state for keyframe copy/paste.
 */
export interface KeyframeState {
  clipboard: {
    keyframes: ClipboardKeyframe[];
  };
}
