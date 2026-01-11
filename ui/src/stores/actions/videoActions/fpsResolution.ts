/**
 * Video Actions - FPS Resolution
 *
 * Handle FPS mismatch and unknown FPS scenarios during video import.
 */

import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import { calculateCompositionFromVideo } from "@/engine/layers/VideoLayer";
import type { Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { createVideoLayerFromAsset } from "./createLayer";
import type {
  VideoStore,
  VideoImportFpsMismatch,
  VideoImportFpsUnknown,
  VideoImportResult,
} from "./types";

// ============================================================================
// FPS MISMATCH RESOLUTION
// ============================================================================

/**
 * Complete video import with "Match" choice:
 * - Precomp all existing layers at original fps
 * - Change composition to video's fps
 * - Add video layer
 */
export async function completeVideoImportWithMatch(
  store: VideoStore,
  pendingImport: VideoImportFpsMismatch["pendingImport"],
  fileName: string,
): Promise<Layer | null> {
  const { metadata, assetId } = pendingImport;
  const originalFps = store.project.composition.fps;
  const comp = store.getActiveComp();

  if (!comp) return null;

  // Step 1: Select all existing layers and precomp them
  const existingLayers = store.getActiveCompLayers();
  if (
    existingLayers.length > 0 &&
    store.selectAllLayers &&
    store.nestSelectedLayers
  ) {
    // Store current selection
    const previousSelection = [...store.selectedLayerIds];

    // Select all layers
    store.selectAllLayers();

    // Precomp them with original fps name
    const precompName = `Original ${originalFps}fps Layers`;
    const nestedComp = store.nestSelectedLayers(precompName);

    if (nestedComp) {
      storeLogger.debug("Precomposed existing layers:", {
        precompName,
        layerCount: existingLayers.length,
        originalFps,
      });
    }

    // Restore selection (will be empty now since layers moved)
    store.selectedLayerIds = previousSelection.filter((id) =>
      store.getActiveCompLayers().some((l) => l.id === id),
    );
  }

  // Step 2: Change composition fps to match video
  const compSettings = calculateCompositionFromVideo(metadata);

  store.project.composition.fps = compSettings.fps;
  store.project.composition.frameCount = compSettings.frameCount;
  store.project.composition.width = compSettings.width;
  store.project.composition.height = compSettings.height;
  store.project.composition.duration =
    compSettings.frameCount / compSettings.fps;

  if (comp) {
    comp.settings.fps = compSettings.fps;
    comp.settings.frameCount = compSettings.frameCount;
    comp.settings.width = compSettings.width;
    comp.settings.height = compSettings.height;
    comp.settings.duration = compSettings.frameCount / compSettings.fps;
  }

  storeLogger.debug("Changed composition fps:", {
    from: originalFps,
    to: compSettings.fps,
  });

  // Step 3: Create video layer
  const layer = createVideoLayerFromAsset(store, assetId, metadata, fileName);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return layer;
}

/**
 * Complete video import with "Conform" choice:
 * - Keep composition fps as-is
 * - Add video layer with time stretch to match fps
 */
export function completeVideoImportWithConform(
  store: VideoStore,
  pendingImport: VideoImportFpsMismatch["pendingImport"],
  fileName: string,
  compositionFps: number,
): Layer {
  const { metadata, assetId } = pendingImport;

  // This function is only called from fps_mismatch path where fps is guaranteed non-null
  const videoFps = metadata.fps!;

  // Validate fps values to prevent division by zero
  const safeCompFps =
    Number.isFinite(compositionFps) && compositionFps > 0 ? compositionFps : 16;
  const safeVideoFps =
    Number.isFinite(videoFps) && videoFps > 0 ? videoFps : safeCompFps;

  // Calculate time stretch factor
  // If video is 30fps and comp is 16fps: video should play slower
  // stretchFactor = compFps / videoFps * 100 = 16/30 * 100 = 53.3%
  // But timeStretch is inverted: 100% = normal, 200% = half speed
  // So: timeStretch = videoFps / compFps * 100 = 30/16 * 100 = 187.5%
  const timeStretch = (safeVideoFps / safeCompFps) * 100;

  storeLogger.debug("Conforming video to composition fps:", {
    videoFps: metadata.fps,
    compositionFps,
    timeStretch: `${timeStretch.toFixed(1)}%`,
  });

  // Create video layer with time stretch
  const layer = createVideoLayerFromAsset(
    store,
    assetId,
    metadata,
    fileName,
    timeStretch,
  );

  // Adjust layer duration for stretched video (use safe fps values)
  const stretchedDuration = metadata.duration * (safeVideoFps / safeCompFps);
  const frameCount = Math.ceil(stretchedDuration * safeCompFps);
  layer.outPoint = Math.min(
    frameCount - 1,
    store.project.composition.frameCount - 1,
  );
  layer.endFrame = layer.outPoint;

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return layer;
}

/**
 * Cancel pending video import (cleanup)
 */
export function cancelVideoImport(
  store: VideoStore,
  pendingImport:
    | VideoImportFpsMismatch["pendingImport"]
    | VideoImportFpsUnknown["pendingImport"],
): void {
  // Remove the asset that was pre-created
  delete store.project.assets[pendingImport.assetId];

  // Revoke the object URL
  URL.revokeObjectURL(pendingImport.videoUrl);

  storeLogger.debug("Cancelled video import:", {
    assetId: pendingImport.assetId,
  });
}

/**
 * Complete video import after user specifies fps (for unknown fps scenario)
 * Continues the normal import flow with user-provided fps
 */
export async function completeVideoImportWithUserFps(
  store: VideoStore,
  pendingImport: VideoImportFpsUnknown["pendingImport"],
  fileName: string,
  userFps: number,
  autoResizeComposition: boolean = true,
): Promise<VideoImportResult> {
  const { metadata, assetId } = pendingImport;

  // Update metadata with user-specified fps
  const updatedMetadata: VideoMetadata = {
    ...metadata,
    fps: userFps,
    frameCount: Math.ceil(metadata.duration * userFps),
  };

  // Update the asset with correct fps
  const asset = store.project.assets[assetId];
  if (asset) {
    asset.fps = userFps;
    asset.frameCount = updatedMetadata.frameCount;
  }

  storeLogger.debug("User specified fps:", {
    fileName,
    fps: userFps,
    frameCount: updatedMetadata.frameCount,
  });

  // Now check for fps mismatch with composition
  const compHasLayers = store.getActiveCompLayers().length > 0;
  const fpsMismatch = Math.abs(userFps - store.project.composition.fps) > 0.5;

  if (autoResizeComposition && compHasLayers && fpsMismatch) {
    // Return fps_mismatch for dialog handling
    return {
      status: "fps_mismatch",
      importedFps: userFps,
      compositionFps: store.project.composition.fps,
      fileName,
      videoDuration: metadata.duration,
      pendingImport: {
        ...pendingImport,
        metadata: updatedMetadata,
      },
    };
  }

  // Auto-resize composition if requested (empty comp or matching fps)
  if (autoResizeComposition) {
    const compSettings = calculateCompositionFromVideo(updatedMetadata);
    const comp = store.getActiveComp();

    // Update composition settings including fps
    store.project.composition.width = compSettings.width;
    store.project.composition.height = compSettings.height;
    store.project.composition.frameCount = compSettings.frameCount;
    store.project.composition.fps = compSettings.fps;
    store.project.composition.duration =
      compSettings.frameCount / compSettings.fps;

    if (comp) {
      comp.settings.width = compSettings.width;
      comp.settings.height = compSettings.height;
      comp.settings.frameCount = compSettings.frameCount;
      comp.settings.fps = compSettings.fps;
      comp.settings.duration = compSettings.frameCount / compSettings.fps;
    }
  }

  // Create the layer
  const layer = createVideoLayerFromAsset(
    store,
    assetId,
    updatedMetadata,
    fileName,
  );

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return { status: "success", layer, metadata: updatedMetadata };
}
