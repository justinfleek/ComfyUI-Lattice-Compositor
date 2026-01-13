/**
 * Video Store
 *
 * Domain store for video layer creation, metadata handling, and composition resizing.
 * Handles FPS mismatch detection and resolution (match/conform).
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import type { VideoMetadata } from "@/engine/layers/VideoLayer";
import {
  calculateCompositionFromVideo,
  extractVideoMetadata,
} from "@/engine/layers/VideoLayer";
import type {
  AssetReference,
  Composition,
  Layer,
  VideoData,
} from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";

// ============================================================================
// TYPES
// ============================================================================

export interface VideoStoreAccess {
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

// ============================================================================
// PINIA STORE
// ============================================================================

export const useVideoStore = defineStore("video", {
  state: () => ({}),

  getters: {},

  actions: {
    // ========================================================================
    // VIDEO LAYER CREATION
    // ========================================================================

    /**
     * Create a video layer from a file.
     * Returns fps_mismatch status if comp has layers and fps differs.
     */
    async createVideoLayer(
      store: VideoStoreAccess,
      file: File,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
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

      // Create asset reference
      const assetId = `video_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const asset: AssetReference = {
        id: assetId,
        type: "video",
        source: "file",
        width: metadata.width,
        height: metadata.height,
        data: videoUrl,
        duration: metadata.duration,
        frameCount: metadata.frameCount,
        fps: metadata.fps ?? undefined,
        hasAudio: metadata.hasAudio,
      };

      store.project.assets[assetId] = asset;

      // Check if fps could not be detected
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

      // Check for fps mismatch
      const compHasLayers = store.getActiveCompLayers().length > 0;
      const fpsMismatch =
        Math.abs(metadata.fps - store.project.composition.fps) > 0.5;

      if (autoResizeComposition && compHasLayers && fpsMismatch) {
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

      // Auto-resize composition if requested
      if (autoResizeComposition) {
        const compSettings = calculateCompositionFromVideo(metadata);
        const comp = store.getActiveComp();

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
      const layer = this.createVideoLayerFromAsset(store, assetId, metadata, file.name);

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
    },

    /**
     * Create video layer from existing asset (used after fps decision).
     */
    createVideoLayerFromAsset(
      store: VideoStoreAccess,
      assetId: string,
      metadata: VideoMetadata,
      fileName: string,
      timeStretch: number = 100,
    ): Layer {
      const layerStore = useLayerStore();
      // Type assertion: compositorStore passed at runtime implements required interface
      const layer = layerStore.createLayer(
        store as unknown as Parameters<typeof layerStore.createLayer>[0],
        "video",
        fileName.replace(/\.[^.]+$/, "")
      );

      const videoData: VideoData = {
        assetId,
        loop: false,
        pingPong: false,
        startTime: 0,
        endTime: undefined,
        speed: 1,
        speedMapEnabled: false,
        speedMap: undefined,
        timeRemapEnabled: false,
        timeRemap: undefined,
        frameBlending: "none",
        audioEnabled: metadata.hasAudio,
        audioLevel: 100,
        posterFrame: 0,
      };

      layer.data = videoData;

      if (timeStretch !== 100) {
        layer.timeStretch = timeStretch;
      }

      const videoFrameCount = Math.ceil(
        metadata.duration * store.project.composition.fps,
      );
      layer.outPoint = Math.min(
        videoFrameCount - 1,
        store.project.composition.frameCount - 1,
      );
      layer.endFrame = layer.outPoint;

      return layer;
    },

    // ========================================================================
    // FPS MISMATCH RESOLUTION
    // ========================================================================

    /**
     * Complete video import with "Match" choice:
     * Precomp existing layers, change composition to video's fps, add video layer.
     */
    async completeVideoImportWithMatch(
      store: VideoStoreAccess,
      pendingImport: VideoImportFpsMismatch["pendingImport"],
      fileName: string,
    ): Promise<Layer | null> {
      const { metadata, assetId } = pendingImport;
      const originalFps = store.project.composition.fps;
      const comp = store.getActiveComp();

      if (!comp) return null;

      // Step 1: Precomp existing layers
      const existingLayers = store.getActiveCompLayers();
      const layerStore = useLayerStore();
      if (existingLayers.length > 0 && store.nestSelectedLayers) {
        layerStore.selectAllLayers(store);
        const precompName = `Original ${originalFps}fps Layers`;
        store.nestSelectedLayers(precompName);
      }

      // Step 2: Change composition fps
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

      // Step 3: Create video layer
      const layer = this.createVideoLayerFromAsset(store, assetId, metadata, fileName);

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      return layer;
    },

    /**
     * Complete video import with "Conform" choice:
     * Keep composition fps, add video layer with time stretch.
     */
    completeVideoImportWithConform(
      store: VideoStoreAccess,
      pendingImport: VideoImportFpsMismatch["pendingImport"],
      fileName: string,
      compositionFps: number,
    ): Layer {
      const { metadata, assetId } = pendingImport;
      const videoFps = metadata.fps!;

      const safeCompFps =
        Number.isFinite(compositionFps) && compositionFps > 0 ? compositionFps : 16;
      const safeVideoFps =
        Number.isFinite(videoFps) && videoFps > 0 ? videoFps : safeCompFps;

      const timeStretch = (safeVideoFps / safeCompFps) * 100;

      storeLogger.debug("Conforming video to composition fps:", {
        videoFps: metadata.fps,
        compositionFps,
        timeStretch: `${timeStretch.toFixed(1)}%`,
      });

      const layer = this.createVideoLayerFromAsset(
        store,
        assetId,
        metadata,
        fileName,
        timeStretch,
      );

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
    },

    /**
     * Cancel pending video import (cleanup).
     */
    cancelVideoImport(
      store: VideoStoreAccess,
      pendingImport:
        | VideoImportFpsMismatch["pendingImport"]
        | VideoImportFpsUnknown["pendingImport"],
    ): void {
      delete store.project.assets[pendingImport.assetId];
      URL.revokeObjectURL(pendingImport.videoUrl);
      storeLogger.debug("Cancelled video import:", { assetId: pendingImport.assetId });
    },

    /**
     * Complete video import after user specifies fps (for unknown fps scenario).
     */
    async completeVideoImportWithUserFps(
      store: VideoStoreAccess,
      pendingImport: VideoImportFpsUnknown["pendingImport"],
      fileName: string,
      userFps: number,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
      const { metadata, assetId } = pendingImport;

      const updatedMetadata: VideoMetadata = {
        ...metadata,
        fps: userFps,
        frameCount: Math.ceil(metadata.duration * userFps),
      };

      const asset = store.project.assets[assetId];
      if (asset) {
        asset.fps = userFps;
        asset.frameCount = updatedMetadata.frameCount;
      }

      const compHasLayers = store.getActiveCompLayers().length > 0;
      const fpsMismatch = Math.abs(userFps - store.project.composition.fps) > 0.5;

      if (autoResizeComposition && compHasLayers && fpsMismatch) {
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

      if (autoResizeComposition) {
        const compSettings = calculateCompositionFromVideo(updatedMetadata);
        const comp = store.getActiveComp();

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

      const layer = this.createVideoLayerFromAsset(
        store,
        assetId,
        updatedMetadata,
        fileName,
      );

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      return { status: "success", layer, metadata: updatedMetadata };
    },

    // ========================================================================
    // VIDEO LAYER DATA UPDATES
    // ========================================================================

    /**
     * Update video layer data.
     */
    updateVideoLayerData(
      store: VideoStoreAccess,
      layerId: string,
      updates: Partial<VideoData>,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "video") return;

      const data = layer.data as VideoData;
      Object.assign(data, updates);
      store.project.meta.modified = new Date().toISOString();
    },

    /**
     * Handle video metadata loaded callback from engine.
     */
    onVideoMetadataLoaded(
      store: VideoStoreAccess,
      layerId: string,
      metadata: VideoMetadata,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "video") return;

      const videoData = layer.data as VideoData;
      if (!videoData.assetId) return;

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
    },

    // ========================================================================
    // COMPOSITION RESIZE
    // ========================================================================

    /**
     * Resize composition settings.
     */
    resizeComposition(
      store: VideoStoreAccess,
      width: number,
      height: number,
      frameCount?: number,
    ): void {
      const comp = store.getActiveComp();
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      comp.settings.width = width;
      comp.settings.height = height;

      store.project.composition.width = width;
      store.project.composition.height = height;

      if (frameCount !== undefined) {
        comp.settings.frameCount = frameCount;
        comp.settings.duration = frameCount / comp.settings.fps;

        store.project.composition.frameCount = frameCount;
        store.project.composition.duration =
          frameCount / store.project.composition.fps;

        if (frameCount > oldFrameCount) {
          for (const layer of comp.layers) {
            if (layer.outPoint === oldFrameCount - 1) {
              layer.outPoint = frameCount - 1;
            }
          }
        }
      }

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
    },
  },
});
