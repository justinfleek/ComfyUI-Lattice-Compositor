/**
 * Video Actions - Types
 *
 * Store interface and result types for video import operations.
 */

import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import type {
  AssetReference,
  Composition,
  Layer,
} from "@/types/project";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface VideoStore {
  project: {
    assets: Record<string, AssetReference>;
    composition: {
      width: number;
      height: number;
      frameCount: number;
      duration: number;
      fps: number;
    };
    compositions: Record<string, Composition>;
    meta: { modified: string };
  };
  activeCompositionId: string;
  selectedLayerIds: string[];

  // Methods the actions need to call
  getActiveComp(): Composition | null;
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer["type"], name?: string): Layer;
  pushHistory(): void;
  selectAllLayers?(): void;
  nestSelectedLayers?(name: string): Composition | null;
  timeStretchLayer?(
    layerId: string,
    options: {
      stretchFactor: number;
      holdInPlace: "in-point" | "current-frame" | "out-point";
      reverse: boolean;
      newStartFrame: number;
      newEndFrame: number;
      speed: number;
    },
  ): void;
}

// ============================================================================
// VIDEO IMPORT RESULT TYPES
// ============================================================================

export interface VideoImportSuccess {
  status: "success";
  layer: Layer;
  metadata: VideoMetadata;
}

export interface VideoImportFpsMismatch {
  status: "fps_mismatch";
  importedFps: number;
  compositionFps: number;
  fileName: string;
  videoDuration: number;
  /** Stored metadata and URL for deferred layer creation */
  pendingImport: {
    videoUrl: string;
    metadata: VideoMetadata;
    assetId: string;
  };
}

export interface VideoImportFpsUnknown {
  status: "fps_unknown";
  fileName: string;
  videoDuration: number;
  /** Stored metadata and URL for deferred layer creation */
  pendingImport: {
    videoUrl: string;
    metadata: VideoMetadata;
    assetId: string;
  };
}

export interface VideoImportError {
  status: "error";
  error: string;
}

export type VideoImportResult =
  | VideoImportSuccess
  | VideoImportFpsMismatch
  | VideoImportFpsUnknown
  | VideoImportError;
