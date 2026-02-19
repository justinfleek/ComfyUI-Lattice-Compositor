/**
 * Animation Store Types
 *
 * Type definitions for animation/playback operations.
 */

import type { Composition, Layer, LatticeProject } from "@/types/project";
import type { SnapConfig } from "@/services/timelineSnap";
import type { FrameState } from "@/engine/MotionEngine";

/**
 * Interface for accessing compositor store from animation actions.
 * Uses dependency injection to avoid circular imports.
 *
 * Extends the minimal interface needed for keyframe navigation,
 * which requires access to layer data for keyframe queries.
 */
export interface AnimationStoreAccess {
  /** Whether playback is currently active */
  isPlaying: boolean;
  /** Get the currently active composition */
  getActiveComp(): Composition | null;
  /** Get current frame from active composition */
  readonly currentFrame: number;
  /** Get frame count from active composition */
  readonly frameCount: number;
  /** Get FPS from active composition */
  readonly fps: number;
  /** Get all layers in active composition (for keyframe navigation) */
  getActiveCompLayers(): Layer[];
  /** Get layer by ID (for keyframe navigation) */
  getLayerById(id: string): Layer | null;
  /** Project metadata (for keyframe store access) */
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  /** Push history state (for keyframe store access) */
  pushHistory(): void;
}

/**
 * Extended access for frame evaluation operations.
 * Requires full project and camera state.
 */
export interface FrameEvaluationAccess extends AnimationStoreAccess {
  /** Full project data (for MotionEngine.evaluate) */
  project: LatticeProject;
  /** Active camera ID (for frame evaluation) */
  activeCameraId: string | null;
}

/**
 * Extended access for timeline snapping operations.
 * Requires layer access and audio store data.
 */
export interface SnapPointAccess extends AnimationStoreAccess {
  /** Get layers array (for snap point calculation) */
  readonly layers: Layer[];
}

/**
 * State for animation store
 */
export interface AnimationState {
  /** Loop playback when reaching end */
  loopPlayback: boolean;
  /** Work area start frame (null = use 0) */
  workAreaStart: number | null;
  /** Work area end frame (null = use frameCount - 1) */
  workAreaEnd: number | null;
  /** Timeline zoom level (1.0 = 100%) */
  timelineZoom: number;
  /** Timeline snap configuration */
  snapConfig: SnapConfig;
}
