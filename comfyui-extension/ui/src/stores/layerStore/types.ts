/**
 * Layer Store Types
 *
 * Type definitions for layer store operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type { LayerDataUnion, AssetReference, ClipboardKeyframe, Layer } from "@/types/project";
import type { Camera3D } from "@/types/camera";

// ============================================================================
// LAYER SOURCE REPLACEMENT
// ============================================================================

/**
 * Layer source replacement data for asset/composition swapping
 */
export interface LayerSourceReplacement {
  type: "asset" | "composition" | string;
  name: string;
  path?: string;
  id?: string;
  assetId?: string;
  data?: string;
}

// ============================================================================
// LAYER CREATION OPTIONS
// ============================================================================

/**
 * Options for creating a new layer
 */
export interface CreateLayerOptions {
  name?: string;
  position?: { x: number; y: number };
  size?: { width: number; height: number };
  data?: Partial<LayerDataUnion>;
  parentId?: string;
  insertIndex?: number;
}

/**
 * Options for deleting a layer
 */
export interface DeleteLayerOptions {
  skipHistory?: boolean;
  deleteChildren?: boolean;
  onRemoveFromSelection?: (id: string) => void;
}

/**
 * Options for duplicating a layer
 */
export interface DuplicateLayerOptions {
  newName?: string;
  offsetPosition?: boolean;
  includeChildren?: boolean;
}

// ============================================================================
// BATCH OPERATION OPTIONS
// ============================================================================

/**
 * Options for sequencing layers
 */
export interface SequenceLayersOptions {
  /** Gap between layers in frames (positive = gap, negative = overlap) */
  gapFrames?: number;
  /** Starting frame for the sequence */
  startFrame?: number;
  /** Whether to maintain layer order or reverse */
  reverse?: boolean;
}

/**
 * Options for exponential scale animation
 */
export interface ExponentialScaleOptions {
  /** Starting scale percentage */
  startScale?: number;
  /** Ending scale percentage */
  endScale?: number;
  /** Starting frame */
  startFrame?: number;
  /** Ending frame */
  endFrame?: number;
  /** Number of keyframes to create (more = smoother) */
  keyframeCount?: number;
  /** Whether to apply to X, Y, or both */
  axis?: "both" | "x" | "y";
}

// ============================================================================
// TIME MANIPULATION OPTIONS
// ============================================================================

/**
 * Options for time stretch operation
 */
export interface TimeStretchOptions {
  stretchFactor: number; // 100% = normal, 200% = half speed, 50% = double speed
  holdInPlace: "in-point" | "current-frame" | "out-point";
  reverse: boolean;
  newStartFrame: number;
  newEndFrame: number;
  speed: number; // Computed speed value (100 / stretchFactor)
}

// ============================================================================
// STATE INTERFACE
// ============================================================================

/**
 * Layer store state
 */
export interface LayerState {
  /**
   * Clipboard for layer copy/paste operations
   * NOTE: Layers are stored in project.compositions[x].layers
   * This store provides methods to access/modify them
   */
  clipboard: {
    layers: Layer[];
    keyframes: ClipboardKeyframe[];
  };
}

// ============================================================================
// COMPOSITOR STORE INTERFACE (for type safety)
// ============================================================================

/**
 * Minimal interface for compositor store access
 * This defines what layer actions need from the compositor store
 */
export interface CompositorStoreAccess {
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  getActiveComp(): {
    settings: {
      width: number;
      height: number;
      fps: number;
      frameCount: number;
    };
    currentFrame?: number;
    layers: Layer[];
  } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
  // For time operations
  currentFrame?: number;
  fps?: number;
  // Layer CRUD methods (for cross-module operations)
  createLayer?(type: Layer["type"], name?: string): Layer;
  deleteLayer?(layerId: string): void;
  // Camera store access (for camera layer creation)
  cameras?: Map<string, Camera3D>;
  activeCameraId?: string | null;
  selectLayer?(layerId: string): void;
  // Video store access (for video layer creation)
  assets?: Record<string, AssetReference>;
}
