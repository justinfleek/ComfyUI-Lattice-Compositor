/**
 * Video Actions
 *
 * Video layer creation, metadata handling, and composition resizing.
 * Handles fps mismatch detection and resolution (match/conform).
 *
 * Extracted from compositorStore.ts for modularity.
 */

import { storeLogger } from '@/utils/logger';
import type {
  Layer,
  Composition,
  AssetReference,
  VideoData
} from '@/types/project';
import type { VideoMetadata } from '@/engine/layers/VideoLayer';
import { extractVideoMetadata, calculateCompositionFromVideo } from '@/engine/layers/VideoLayer';

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
  createLayer(type: Layer['type'], name?: string): Layer;
  pushHistory(): void;
  selectAllLayers?(): void;
  nestSelectedLayers?(name: string): Composition | null;
  timeStretchLayer?(layerId: string, options: {
    stretchFactor: number;
    holdInPlace: 'in-point' | 'current-frame' | 'out-point';
    reverse: boolean;
    newStartFrame: number;
    newEndFrame: number;
    speed: number;
  }): void;
}

// ============================================================================
// VIDEO IMPORT RESULT TYPES
// ============================================================================

export interface VideoImportSuccess {
  status: 'success';
  layer: Layer;
  metadata: VideoMetadata;
}

export interface VideoImportFpsMismatch {
  status: 'fps_mismatch';
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
  status: 'fps_unknown';
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
  status: 'error';
  error: string;
}

export type VideoImportResult = VideoImportSuccess | VideoImportFpsMismatch | VideoImportFpsUnknown | VideoImportError;

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
  autoResizeComposition: boolean = true
): Promise<VideoImportResult> {
  // First extract metadata to determine dimensions and duration
  let videoUrl: string;
  try {
    videoUrl = URL.createObjectURL(file);
  } catch {
    return { status: 'error', error: 'Failed to create URL for video file' };
  }

  let metadata: VideoMetadata;
  try {
    metadata = await extractVideoMetadata(videoUrl);
  } catch (error) {
    URL.revokeObjectURL(videoUrl);
    return { status: 'error', error: `Failed to load video metadata: ${(error as Error).message}` };
  }

  // Create asset reference (stored regardless of fps decision)
  const assetId = `video_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const asset: AssetReference = {
    id: assetId,
    type: 'video',
    source: 'file',
    width: metadata.width,
    height: metadata.height,
    data: videoUrl,
    // Video-specific metadata
    duration: metadata.duration,
    frameCount: metadata.frameCount,
    fps: metadata.fps ?? undefined,
    hasAudio: metadata.hasAudio
  };

  store.project.assets[assetId] = asset;

  // Check if fps could not be detected - user must specify
  if (metadata.fps === null) {
    storeLogger.debug('FPS unknown - user must specify:', {
      fileName: file.name,
      duration: metadata.duration
    });

    return {
      status: 'fps_unknown',
      fileName: file.name,
      videoDuration: metadata.duration,
      pendingImport: {
        videoUrl,
        metadata,
        assetId
      }
    };
  }

  // Check for fps mismatch scenario (only if fps is known)
  const compHasLayers = store.getActiveCompLayers().length > 0;
  const fpsMismatch = Math.abs(metadata.fps - store.project.composition.fps) > 0.5; // Allow small tolerance

  if (autoResizeComposition && compHasLayers && fpsMismatch) {
    // Return fps_mismatch for dialog handling
    storeLogger.debug('FPS mismatch detected:', {
      videoFps: metadata.fps,
      compositionFps: store.project.composition.fps,
      fileName: file.name
    });

    return {
      status: 'fps_mismatch',
      importedFps: metadata.fps,
      compositionFps: store.project.composition.fps,
      fileName: file.name,
      videoDuration: metadata.duration,
      pendingImport: {
        videoUrl,
        metadata,
        assetId
      }
    };
  }

  // Auto-resize composition if requested (empty comp or matching fps)
  if (autoResizeComposition) {
    const compSettings = calculateCompositionFromVideo(metadata);
    const comp = store.getActiveComp();

    storeLogger.debug('Auto-resizing composition for video:', {
      originalWidth: store.project.composition.width,
      originalHeight: store.project.composition.height,
      originalFrameCount: store.project.composition.frameCount,
      originalFps: store.project.composition.fps,
      newWidth: compSettings.width,
      newHeight: compSettings.height,
      newFrameCount: compSettings.frameCount,
      newFps: compSettings.fps,
      videoDuration: metadata.duration
    });

    // Update composition settings including fps
    store.project.composition.width = compSettings.width;
    store.project.composition.height = compSettings.height;
    store.project.composition.frameCount = compSettings.frameCount;
    store.project.composition.fps = compSettings.fps;
    store.project.composition.duration = compSettings.frameCount / compSettings.fps;

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

  storeLogger.debug('Created video layer:', {
    layerId: layer.id,
    assetId,
    dimensions: `${metadata.width}x${metadata.height}`,
    duration: `${metadata.duration.toFixed(2)}s`,
    frameCount: metadata.frameCount,
    fps: metadata.fps,
    hasAudio: metadata.hasAudio
  });

  return { status: 'success', layer, metadata };
}

/**
 * Create video layer from existing asset (used after fps decision)
 */
function createVideoLayerFromAsset(
  store: VideoStore,
  assetId: string,
  metadata: VideoMetadata,
  fileName: string,
  timeStretch: number = 100
): Layer {
  // Create the layer
  const layer = store.createLayer('video', fileName.replace(/\.[^.]+$/, ''));

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
    frameBlending: 'none',
    audioEnabled: metadata.hasAudio,
    audioLevel: 100,
    posterFrame: 0
  };

  layer.data = videoData;

  // Apply time stretch if not 100%
  if (timeStretch !== 100) {
    layer.timeStretch = timeStretch;
  }

  // Set layer duration based on video at composition fps
  const videoFrameCount = Math.ceil(metadata.duration * store.project.composition.fps);
  layer.outPoint = Math.min(videoFrameCount - 1, store.project.composition.frameCount - 1);
  layer.endFrame = layer.outPoint;

  return layer;
}

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
  pendingImport: VideoImportFpsMismatch['pendingImport'],
  fileName: string
): Promise<Layer | null> {
  const { metadata, assetId } = pendingImport;
  const originalFps = store.project.composition.fps;
  const comp = store.getActiveComp();

  if (!comp) return null;

  // Step 1: Select all existing layers and precomp them
  const existingLayers = store.getActiveCompLayers();
  if (existingLayers.length > 0 && store.selectAllLayers && store.nestSelectedLayers) {
    // Store current selection
    const previousSelection = [...store.selectedLayerIds];

    // Select all layers
    store.selectAllLayers();

    // Precomp them with original fps name
    const precompName = `Original ${originalFps}fps Layers`;
    const nestedComp = store.nestSelectedLayers(precompName);

    if (nestedComp) {
      storeLogger.debug('Precomposed existing layers:', {
        precompName,
        layerCount: existingLayers.length,
        originalFps
      });
    }

    // Restore selection (will be empty now since layers moved)
    store.selectedLayerIds = previousSelection.filter(id =>
      store.getActiveCompLayers().some(l => l.id === id)
    );
  }

  // Step 2: Change composition fps to match video
  const compSettings = calculateCompositionFromVideo(metadata);

  store.project.composition.fps = compSettings.fps;
  store.project.composition.frameCount = compSettings.frameCount;
  store.project.composition.width = compSettings.width;
  store.project.composition.height = compSettings.height;
  store.project.composition.duration = compSettings.frameCount / compSettings.fps;

  if (comp) {
    comp.settings.fps = compSettings.fps;
    comp.settings.frameCount = compSettings.frameCount;
    comp.settings.width = compSettings.width;
    comp.settings.height = compSettings.height;
    comp.settings.duration = compSettings.frameCount / compSettings.fps;
  }

  storeLogger.debug('Changed composition fps:', {
    from: originalFps,
    to: compSettings.fps
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
  pendingImport: VideoImportFpsMismatch['pendingImport'],
  fileName: string,
  compositionFps: number
): Layer {
  const { metadata, assetId } = pendingImport;

  // This function is only called from fps_mismatch path where fps is guaranteed non-null
  const videoFps = metadata.fps!;

  // Validate fps values to prevent division by zero
  const safeCompFps = (Number.isFinite(compositionFps) && compositionFps > 0) ? compositionFps : 16;
  const safeVideoFps = (Number.isFinite(videoFps) && videoFps > 0) ? videoFps : safeCompFps;

  // Calculate time stretch factor
  // If video is 30fps and comp is 16fps: video should play slower
  // stretchFactor = compFps / videoFps * 100 = 16/30 * 100 = 53.3%
  // But timeStretch is inverted: 100% = normal, 200% = half speed
  // So: timeStretch = videoFps / compFps * 100 = 30/16 * 100 = 187.5%
  const timeStretch = (safeVideoFps / safeCompFps) * 100;

  storeLogger.debug('Conforming video to composition fps:', {
    videoFps: metadata.fps,
    compositionFps,
    timeStretch: `${timeStretch.toFixed(1)}%`
  });

  // Create video layer with time stretch
  const layer = createVideoLayerFromAsset(store, assetId, metadata, fileName, timeStretch);

  // Adjust layer duration for stretched video (use safe fps values)
  const stretchedDuration = metadata.duration * (safeVideoFps / safeCompFps);
  const frameCount = Math.ceil(stretchedDuration * safeCompFps);
  layer.outPoint = Math.min(frameCount - 1, store.project.composition.frameCount - 1);
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
  pendingImport: VideoImportFpsMismatch['pendingImport'] | VideoImportFpsUnknown['pendingImport']
): void {
  // Remove the asset that was pre-created
  delete store.project.assets[pendingImport.assetId];

  // Revoke the object URL
  URL.revokeObjectURL(pendingImport.videoUrl);

  storeLogger.debug('Cancelled video import:', { assetId: pendingImport.assetId });
}

/**
 * Complete video import after user specifies fps (for unknown fps scenario)
 * Continues the normal import flow with user-provided fps
 */
export async function completeVideoImportWithUserFps(
  store: VideoStore,
  pendingImport: VideoImportFpsUnknown['pendingImport'],
  fileName: string,
  userFps: number,
  autoResizeComposition: boolean = true
): Promise<VideoImportResult> {
  const { metadata, assetId } = pendingImport;

  // Update metadata with user-specified fps
  const updatedMetadata: VideoMetadata = {
    ...metadata,
    fps: userFps,
    frameCount: Math.ceil(metadata.duration * userFps)
  };

  // Update the asset with correct fps
  const asset = store.project.assets[assetId];
  if (asset) {
    asset.fps = userFps;
    asset.frameCount = updatedMetadata.frameCount;
  }

  storeLogger.debug('User specified fps:', {
    fileName,
    fps: userFps,
    frameCount: updatedMetadata.frameCount
  });

  // Now check for fps mismatch with composition
  const compHasLayers = store.getActiveCompLayers().length > 0;
  const fpsMismatch = Math.abs(userFps - store.project.composition.fps) > 0.5;

  if (autoResizeComposition && compHasLayers && fpsMismatch) {
    // Return fps_mismatch for dialog handling
    return {
      status: 'fps_mismatch',
      importedFps: userFps,
      compositionFps: store.project.composition.fps,
      fileName,
      videoDuration: metadata.duration,
      pendingImport: {
        ...pendingImport,
        metadata: updatedMetadata
      }
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
    store.project.composition.duration = compSettings.frameCount / compSettings.fps;

    if (comp) {
      comp.settings.width = compSettings.width;
      comp.settings.height = compSettings.height;
      comp.settings.frameCount = compSettings.frameCount;
      comp.settings.fps = compSettings.fps;
      comp.settings.duration = compSettings.frameCount / compSettings.fps;
    }
  }

  // Create the layer
  const layer = createVideoLayerFromAsset(store, assetId, updatedMetadata, fileName);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return { status: 'success', layer, metadata: updatedMetadata };
}

// ============================================================================
// VIDEO LAYER DATA UPDATES
// ============================================================================

/**
 * Update video layer data
 */
export function updateVideoLayerData(
  store: VideoStore,
  layerId: string,
  updates: Partial<VideoData>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'video') return;

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
  metadata: VideoMetadata
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'video') return;

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

  storeLogger.debug('Video metadata loaded:', { layerId, metadata });
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
  frameCount?: number
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
    store.project.composition.duration = frameCount / store.project.composition.fps;

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

  storeLogger.debug('Composition resized:', {
    width,
    height,
    frameCount: comp.settings.frameCount
  });
}
