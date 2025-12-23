/**
 * Video Actions
 *
 * Video layer creation, metadata handling, and composition resizing.
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
    meta: { modified: string };
  };

  // Methods the actions need to call
  getActiveComp(): Composition | null;
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer['type'], name?: string): Layer;
  pushHistory(): void;
}

// ============================================================================
// VIDEO LAYER CREATION
// ============================================================================

/**
 * Create a video layer from a file
 */
export async function createVideoLayer(
  store: VideoStore,
  file: File,
  autoResizeComposition: boolean = true
): Promise<Layer> {
  // First extract metadata to determine dimensions and duration
  let videoUrl: string;
  try {
    videoUrl = URL.createObjectURL(file);
  } catch {
    throw new Error('Failed to create URL for video file');
  }

  let metadata: VideoMetadata;
  try {
    metadata = await extractVideoMetadata(videoUrl);
  } catch (error) {
    URL.revokeObjectURL(videoUrl);
    throw new Error(`Failed to load video metadata: ${(error as Error).message}`);
  }

  // Create asset reference
  const assetId = `video_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
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
    fps: metadata.fps,
    hasAudio: metadata.hasAudio
  };

  store.project.assets[assetId] = asset;

  // Auto-resize composition if requested
  if (autoResizeComposition) {
    const compSettings = calculateCompositionFromVideo(metadata, store.project.composition.fps);

    storeLogger.debug('Auto-resizing composition for video:', {
      originalWidth: store.project.composition.width,
      originalHeight: store.project.composition.height,
      originalFrameCount: store.project.composition.frameCount,
      newWidth: compSettings.width,
      newHeight: compSettings.height,
      newFrameCount: compSettings.frameCount,
      videoDuration: metadata.duration
    });

    store.project.composition.width = compSettings.width;
    store.project.composition.height = compSettings.height;
    store.project.composition.frameCount = compSettings.frameCount;
    store.project.composition.duration = compSettings.frameCount / store.project.composition.fps;
  }

  // Create the layer
  const layer = store.createLayer('video', file.name.replace(/\.[^.]+$/, ''));

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

  // Set layer duration to match video (in frames)
  if (!autoResizeComposition) {
    // If not auto-resizing, set layer out point to video duration
    const videoFrameCount = Math.ceil(metadata.duration * store.project.composition.fps);
    layer.outPoint = Math.min(videoFrameCount - 1, store.project.composition.frameCount - 1);
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug('Created video layer:', {
    layerId: layer.id,
    assetId,
    dimensions: `${metadata.width}x${metadata.height}`,
    duration: `${metadata.duration.toFixed(2)}s`,
    frameCount: metadata.frameCount,
    hasAudio: metadata.hasAudio
  });

  return layer;
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
    asset.fps = metadata.fps;
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
