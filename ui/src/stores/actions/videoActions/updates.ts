/**
 * Video Actions - Updates
 *
 * Video data updates, metadata handling, and composition resize.
 */

import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import type { VideoData } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import type { VideoStore } from "./types";

// ============================================================================
// VIDEO LAYER DATA UPDATES
// ============================================================================

/**
 * Update video layer data
 */
export function updateVideoLayerData(
  store: VideoStore,
  layerId: string,
  updates: Partial<VideoData>,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "video") return;

  const data = layer.data as VideoData;
  Object.assign(data, updates);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Handle video metadata loaded callback from engine
 * Called by LayerManager when a video finishes loading
 */
export function onVideoMetadataLoaded(
  store: VideoStore,
  layerId: string,
  metadata: VideoMetadata,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "video") return;

  const videoData = layer.data as VideoData;
  if (!videoData.assetId) return;

  // Update asset with accurate metadata
  const asset = store.project.assets[videoData.assetId];
  if (asset) {
    asset.width = metadata.width;
    asset.height = metadata.height;
    asset.duration = metadata.duration;
    asset.frameCount = metadata.frameCount;
    asset.fps = metadata.fps ?? undefined;
    asset.hasAudio = metadata.hasAudio;
  }

  storeLogger.debug("Video metadata loaded:", { layerId, metadata });
}

// ============================================================================
// COMPOSITION RESIZE
// ============================================================================

/**
 * Resize composition settings
 * Used for manual resize or when importing video
 */
export function resizeComposition(
  store: VideoStore,
  width: number,
  height: number,
  frameCount?: number,
): void {
  const comp = store.getActiveComp();
  if (!comp) return;

  const oldFrameCount = comp.settings.frameCount;

  comp.settings.width = width;
  comp.settings.height = height;

  // Keep legacy alias in sync
  store.project.composition.width = width;
  store.project.composition.height = height;

  if (frameCount !== undefined) {
    comp.settings.frameCount = frameCount;
    comp.settings.duration = frameCount / comp.settings.fps;

    // Keep legacy alias in sync
    store.project.composition.frameCount = frameCount;
    store.project.composition.duration =
      frameCount / store.project.composition.fps;

    // Extend layer outPoints if frameCount increased
    // Only extend layers that were at the old max frame
    if (frameCount > oldFrameCount) {
      for (const layer of comp.layers) {
        // If layer ended at the old composition end, extend it to new end
        if (layer.outPoint === oldFrameCount - 1) {
          layer.outPoint = frameCount - 1;
        }
      }
    }
  }

  // Update current frame if it's now out of bounds
  if (comp.currentFrame >= comp.settings.frameCount) {
    comp.currentFrame = comp.settings.frameCount - 1;
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug("Composition resized:", {
    width,
    height,
    frameCount: comp.settings.frameCount,
  });
}
