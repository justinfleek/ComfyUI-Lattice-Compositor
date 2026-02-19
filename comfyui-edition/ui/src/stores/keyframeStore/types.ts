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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                             // store // access // interfaces
// ════════════════════════════════════════════════════════════════════════════

/**
 * Base interface for keyframe store operations.
 * Provides access to project state and layer data.
 * 
 * @deprecated This interface is no longer used. All keyframeStore methods now use domain stores directly.
 * Will be removed in a future cleanup pass.
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
 * 
 * @deprecated This interface is no longer used. All keyframeStore methods now use domain stores directly.
 * Will be removed in a future cleanup pass.
 */
export interface RovingKeyframeStoreAccess extends KeyframeStoreAccess {
  getLayerById(id: string): Layer | null;
}

/**
 * Extended interface for clipboard operations.
 * Adds clipboard state and current frame access.
 * 
 * @deprecated This interface is no longer used. All keyframeStore methods now use domain stores directly.
 * Will be removed in a future cleanup pass.
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
 * 
 * @deprecated This interface is no longer used. All keyframeStore methods now use domain stores directly.
 * Will be removed in a future cleanup pass.
 */
export interface VelocityStoreAccess extends KeyframeStoreAccess {
  fps: number;
}

/**
 * Extended interface for expression baking.
 * Adds frame count and property evaluation capability.
 * 
 * @deprecated This interface is no longer used. All keyframeStore methods now use domain stores directly.
 * Will be removed in a future cleanup pass.
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

// ════════════════════════════════════════════════════════════════════════════
//                                                   // operation // parameters
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                                            // store // state
// ════════════════════════════════════════════════════════════════════════════

/**
 * Keyframe store state.
 * Maintains clipboard state for keyframe copy/paste.
 */
export interface KeyframeState {
  clipboard: {
    keyframes: ClipboardKeyframe[];
  };
}
