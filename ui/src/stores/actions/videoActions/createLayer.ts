/**
 * Video Actions - Layer Creation
 *
 * Create video layers from files and assets.
 */

import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import {
  calculateCompositionFromVideo,
  extractVideoMetadata,
} from "@/engine/layers/VideoLayer";
import type { AssetReference, Layer, VideoData } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import type { VideoStore, VideoImportResult } from "./types";

// ============================================================================
// VIDEO LAYER CREATION
// ============================================================================

/**
 * Create a video layer from a file
 * Returns fps_mismatch status if comp has layers and fps differs
 */
export async function createVideoLayer(
  store: VideoStore,
  file: File,
  autoResizeComposition: boolean = true,
): Promise<VideoImportResult> {
  // First extract metadata to determine dimensions and duration
  let videoUrl: string;
  try {
    videoUrl = URL.createObjectURL(file);
  } catch {
    return { status: "error", error: "Failed to create URL for video file" };
  }

  let metadata: VideoMetadata;
  try {
    metadata = await extractVideoMetadata(videoUrl);
  } catch (error) {
    URL.revokeObjectURL(videoUrl);
    return {
      status: "error",
      error: `Failed to load video metadata: ${(error as Error).message}`,
    };
  }

  // Create asset reference (stored regardless of fps decision)
  const assetId = `video_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const asset: AssetReference = {
    id: assetId,
    type: "video",
    source: "file",
    width: metadata.width,
    height: metadata.height,
    data: videoUrl,
    // Video-specific metadata
    duration: metadata.duration,
    frameCount: metadata.frameCount,
    fps: metadata.fps ?? undefined,
    hasAudio: metadata.hasAudio,
  };

  store.project.assets[assetId] = asset;

  // Check if fps could not be detected - user must specify
  if (metadata.fps === null) {
    storeLogger.debug("FPS unknown - user must specify:", {
      fileName: file.name,
      duration: metadata.duration,
    });

    return {
      status: "fps_unknown",
      fileName: file.name,
      videoDuration: metadata.duration,
      pendingImport: {
        videoUrl,
        metadata,
        assetId,
      },
    };
  }

  // Check for fps mismatch scenario (only if fps is known)
  const compHasLayers = store.getActiveCompLayers().length > 0;
  const fpsMismatch =
    Math.abs(metadata.fps - store.project.composition.fps) > 0.5; // Allow small tolerance

  if (autoResizeComposition && compHasLayers && fpsMismatch) {
    // Return fps_mismatch for dialog handling
    storeLogger.debug("FPS mismatch detected:", {
      videoFps: metadata.fps,
      compositionFps: store.project.composition.fps,
      fileName: file.name,
    });

    return {
      status: "fps_mismatch",
      importedFps: metadata.fps,
      compositionFps: store.project.composition.fps,
      fileName: file.name,
      videoDuration: metadata.duration,
      pendingImport: {
        videoUrl,
        metadata,
        assetId,
      },
    };
  }

  // Auto-resize composition if requested (empty comp or matching fps)
  if (autoResizeComposition) {
    const compSettings = calculateCompositionFromVideo(metadata);
    const comp = store.getActiveComp();

    storeLogger.debug("Auto-resizing composition for video:", {
      originalWidth: store.project.composition.width,
      originalHeight: store.project.composition.height,
      originalFrameCount: store.project.composition.frameCount,
      originalFps: store.project.composition.fps,
      newWidth: compSettings.width,
      newHeight: compSettings.height,
      newFrameCount: compSettings.frameCount,
      newFps: compSettings.fps,
      videoDuration: metadata.duration,
    });

    // Update composition settings including fps
    store.project.composition.width = compSettings.width;
    store.project.composition.height = compSettings.height;
    store.project.composition.frameCount = compSettings.frameCount;
    store.project.composition.fps = compSettings.fps;
    store.project.composition.duration =
      compSettings.frameCount / compSettings.fps;

    // Also update the actual composition object
    if (comp) {
      comp.settings.width = compSettings.width;
      comp.settings.height = compSettings.height;
      comp.settings.frameCount = compSettings.frameCount;
      comp.settings.fps = compSettings.fps;
      comp.settings.duration = compSettings.frameCount / compSettings.fps;
    }
  }

  // Create the layer
  const layer = createVideoLayerFromAsset(store, assetId, metadata, file.name);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug("Created video layer:", {
    layerId: layer.id,
    assetId,
    dimensions: `${metadata.width}x${metadata.height}`,
    duration: `${metadata.duration.toFixed(2)}s`,
    frameCount: metadata.frameCount,
    fps: metadata.fps,
    hasAudio: metadata.hasAudio,
  });

  return { status: "success", layer, metadata };
}

/**
 * Create video layer from existing asset (used after fps decision)
 */
export function createVideoLayerFromAsset(
  store: VideoStore,
  assetId: string,
  metadata: VideoMetadata,
  fileName: string,
  timeStretch: number = 100,
): Layer {
  // Create the layer
  const layer = store.createLayer("video", fileName.replace(/\.[^.]+$/, ""));

  // Set video data
  const videoData: VideoData = {
    assetId,
    loop: false,
    pingPong: false,
    startTime: 0,
    endTime: undefined,
    speed: 1,
    // Speed map (new naming)
    speedMapEnabled: false,
    speedMap: undefined,
    // Backwards compatibility
    timeRemapEnabled: false,
    timeRemap: undefined,
    frameBlending: "none",
    audioEnabled: metadata.hasAudio,
    audioLevel: 100,
    posterFrame: 0,
  };

  layer.data = videoData;

  // Apply time stretch if not 100%
  if (timeStretch !== 100) {
    layer.timeStretch = timeStretch;
  }

  // Set layer duration based on video at composition fps
  const videoFrameCount = Math.ceil(
    metadata.duration * store.project.composition.fps,
  );
  layer.outPoint = Math.min(
    videoFrameCount - 1,
    store.project.composition.frameCount - 1,
  );
  layer.endFrame = layer.outPoint;

  return layer;
}
