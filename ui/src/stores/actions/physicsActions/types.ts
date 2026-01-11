/**
 * Physics Actions - Types
 *
 * Store interface and baking types for physics actions.
 */

import type { Keyframe, Layer } from "@/types/project";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface PhysicsStore {
  // State
  activeCompositionId: string;
  currentFrame: number;

  // Methods the store must provide
  project: {
    compositions: Record<
      string,
      {
        layers: Layer[];
        settings: {
          width: number;
          height: number;
          frameCount: number;
          fps: number;
        };
      }
    >;
  };

  // Layer access
  getLayerById(id: string): Layer | null;
  updateLayerData(layerId: string, data: Record<string, unknown>): void;
  // Signature must match compositorStore.addKeyframe
  addKeyframe<T>(
    layerId: string,
    propertyName: string,
    value: T,
    atFrame?: number,
  ): Keyframe<T> | null;
}

// ============================================================================
// BAKING TYPES
// ============================================================================

/** Internal keyframe structure for baking */
export interface BakedKeyframe<T> {
  frame: number;
  value: T;
  interpolation: "linear" | "bezier";
}

/** Options for baking physics to keyframes */
export interface BakeOptions {
  startFrame?: number;
  endFrame?: number;
  sampleInterval?: number;
  simplify?: boolean;
}

/** Result of baking physics to keyframes */
export interface BakeResult {
  layerId: string;
  positionKeyframes: BakedKeyframe<{ x: number; y: number; z: number }>[];
  rotationKeyframes: BakedKeyframe<number>[];
}
