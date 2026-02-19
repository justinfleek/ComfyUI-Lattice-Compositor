/**
 * Video Store
 *
 * Domain store for video layer creation, metadata handling, and composition resizing.
 * Handles FPS mismatch detection and resolution (match/conform).
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber, assertDefined } from "@/utils/typeGuards";
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
import { useProjectStore } from "./projectStore";
import { useSelectionStore } from "./selectionStore";
import { useLayerStore } from "./layerStore";
import { useCompositionStore } from "./compositionStore";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                           // pinia // store
// ═══════════════════════════════════════════════════════════════════════════

export const useVideoStore = defineStore("video", {
  state: () => ({}),

  getters: {},

  actions: {
    // ═══════════════════════════════════════════════════════════════════════════
    //                                               // video // layer // creation
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Create a video layer from a file.
     * Returns fps_mismatch status if comp has layers and fps differs.
     */
    async createVideoLayer(
      file: File,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      let videoUrl: string;
      try {
        videoUrl = URL.createObjectURL(file);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : "Unknown error";
        throw new Error(`[VideoStore] Failed to create URL for video file: ${errorMessage}. Check file format and browser support.`);
      }

      let metadata: VideoMetadata;
      try {
        metadata = await extractVideoMetadata(videoUrl);
      } catch (error) {
        URL.revokeObjectURL(videoUrl);
        const errorMessage = error instanceof Error ? error.message : "Unknown error";
        throw new Error(`[VideoStore] Failed to load video metadata: ${errorMessage}. Video file may be corrupted or unsupported format.`);
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
        // Type proof: fps ∈ ℝ | undefined → ℝ | undefined
        fps: (() => {
          const fpsValue = metadata.fps;
          return isFiniteNumber(fpsValue) && fpsValue > 0 ? fpsValue : undefined;
        })(),
        hasAudio: metadata.hasAudio,
      };

      projectStore.project.assets[assetId] = asset;

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
      const compHasLayers = projectStore.getActiveCompLayers().length > 0;
      const fpsMismatch =
        Math.abs(metadata.fps - projectStore.project.composition.fps) > 0.5;

      if (autoResizeComposition && compHasLayers && fpsMismatch) {
        storeLogger.debug("FPS mismatch detected:", {
          videoFps: metadata.fps,
          compositionFps: projectStore.project.composition.fps,
          fileName: file.name,
        });

        return {
          status: "fps_mismatch",
          importedFps: metadata.fps,
          compositionFps: projectStore.project.composition.fps,
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
        const comp = projectStore.getActiveComp();

        projectStore.project.composition.width = compSettings.width;
        projectStore.project.composition.height = compSettings.height;
        projectStore.project.composition.frameCount = compSettings.frameCount;
        projectStore.project.composition.fps = compSettings.fps;
        projectStore.project.composition.duration =
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
      const layer = this.createVideoLayerFromAsset(assetId, metadata, file.name);

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

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
      assetId: string,
      metadata: VideoMetadata,
      fileName: string,
      timeStretch: number = 100,
    ): Layer {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const layer = layerStore.createLayer("video", fileName.replace(/\.[^.]+$/, ""));

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
        metadata.duration * projectStore.project.composition.fps,
      );
      layer.outPoint = Math.min(
        videoFrameCount - 1,
        projectStore.project.composition.frameCount - 1,
      );
      layer.endFrame = layer.outPoint;

      return layer;
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                            // fps // mismatch // resolution
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Complete video import with "Match" choice:
     * Precomp existing layers, change composition to video's fps, add video layer.
     */
    async completeVideoImportWithMatch(
      pendingImport: VideoImportFpsMismatch["pendingImport"],
      fileName: string,
    ): Promise<Layer | null> {
      const { metadata, assetId } = pendingImport;
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const compositionStore = useCompositionStore();
      const selectionStore = useSelectionStore();

      const originalFps = projectStore.project.composition.fps;
      const comp = projectStore.getActiveComp();

      if (!comp) {
        throw new Error("[VideoStore] Cannot create video from layers: No active composition found");
      }

      // Step 1: Precomp existing layers
      const existingLayers = projectStore.getActiveCompLayers();
      if (existingLayers.length > 0) {
        layerStore.selectAllLayers();
        const precompName = `Original ${originalFps}fps Layers`;
        compositionStore.nestSelectedLayers(precompName);
      }

      // Step 2: Change composition fps
      const compSettings = calculateCompositionFromVideo(metadata);

      projectStore.project.composition.fps = compSettings.fps;
      projectStore.project.composition.frameCount = compSettings.frameCount;
      projectStore.project.composition.width = compSettings.width;
      projectStore.project.composition.height = compSettings.height;
      projectStore.project.composition.duration =
        compSettings.frameCount / compSettings.fps;

      if (comp) {
        comp.settings.fps = compSettings.fps;
        comp.settings.frameCount = compSettings.frameCount;
        comp.settings.width = compSettings.width;
        comp.settings.height = compSettings.height;
        comp.settings.duration = compSettings.frameCount / compSettings.fps;
      }

      // Step 3: Create video layer
      const layer = this.createVideoLayerFromAsset(assetId, metadata, fileName);

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

      return layer;
    },

    /**
     * Complete video import with "Conform" choice:
     * Keep composition fps, add video layer with time stretch.
     */
    completeVideoImportWithConform(
      pendingImport: VideoImportFpsMismatch["pendingImport"],
      fileName: string,
      compositionFps: number,
    ): Layer {
      const { metadata, assetId } = pendingImport;
      const projectStore = useProjectStore();
      // Type proof: fps is guaranteed non-null when VideoImportFpsMismatch status occurs (fps was detected)
      assertDefined(metadata.fps, "metadata.fps must exist when completing fps mismatch import");
      const videoFps = metadata.fps;

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
        assetId,
        metadata,
        fileName,
        timeStretch,
      );

      const stretchedDuration = metadata.duration * (safeVideoFps / safeCompFps);
      const frameCount = Math.ceil(stretchedDuration * safeCompFps);
      layer.outPoint = Math.min(
        frameCount - 1,
        projectStore.project.composition.frameCount - 1,
      );
      layer.endFrame = layer.outPoint;

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

      return layer;
    },

    /**
     * Cancel pending video import (cleanup).
     */
    cancelVideoImport(
      pendingImport:
        | VideoImportFpsMismatch["pendingImport"]
        | VideoImportFpsUnknown["pendingImport"],
    ): void {
      const projectStore = useProjectStore();
      delete projectStore.project.assets[pendingImport.assetId];
      URL.revokeObjectURL(pendingImport.videoUrl);
      storeLogger.debug("Cancelled video import:", { assetId: pendingImport.assetId });
    },

    /**
     * Complete video import after user specifies fps (for unknown fps scenario).
     */
    async completeVideoImportWithUserFps(
      pendingImport: VideoImportFpsUnknown["pendingImport"],
      fileName: string,
      userFps: number,
      autoResizeComposition: boolean = true,
    ): Promise<VideoImportResult> {
      const { metadata, assetId } = pendingImport;
      const projectStore = useProjectStore();

      const updatedMetadata: VideoMetadata = {
        ...metadata,
        fps: userFps,
        frameCount: Math.ceil(metadata.duration * userFps),
      };

      const asset = projectStore.project.assets[assetId];
      if (asset) {
        asset.fps = userFps;
        asset.frameCount = updatedMetadata.frameCount;
      }

      const compHasLayers = projectStore.getActiveCompLayers().length > 0;
      const fpsMismatch = Math.abs(userFps - projectStore.project.composition.fps) > 0.5;

      if (autoResizeComposition && compHasLayers && fpsMismatch) {
        return {
          status: "fps_mismatch",
          importedFps: userFps,
          compositionFps: projectStore.project.composition.fps,
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
        const comp = projectStore.getActiveComp();

        projectStore.project.composition.width = compSettings.width;
        projectStore.project.composition.height = compSettings.height;
        projectStore.project.composition.frameCount = compSettings.frameCount;
        projectStore.project.composition.fps = compSettings.fps;
        projectStore.project.composition.duration =
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
        assetId,
        updatedMetadata,
        fileName,
      );

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

      return { status: "success", layer, metadata: updatedMetadata };
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                        // video // layer // data // updates
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Update video layer data.
     */
    updateVideoLayerData(
      layerId: string,
      updates: Partial<VideoData>,
    ): void {
      const projectStore = useProjectStore();
      const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "video") return;

      const data = layer.data as VideoData;
      Object.assign(data, updates);
      projectStore.project.meta.modified = new Date().toISOString();
    },

    /**
     * Handle video metadata loaded callback from engine.
     */
    onVideoMetadataLoaded(
      layerId: string,
      metadata: VideoMetadata,
    ): void {
      const projectStore = useProjectStore();
      const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "video") return;

      const videoData = layer.data as VideoData;
      if (!videoData.assetId) return;

      const asset = projectStore.project.assets[videoData.assetId];
      if (asset) {
        asset.width = metadata.width;
        asset.height = metadata.height;
        asset.duration = metadata.duration;
        asset.frameCount = metadata.frameCount;
        // Type proof: fps ∈ ℝ | undefined → ℝ | undefined
        const fpsValue = metadata.fps;
        asset.fps = isFiniteNumber(fpsValue) && fpsValue > 0 ? fpsValue : undefined;
        asset.hasAudio = metadata.hasAudio;
      }

      storeLogger.debug("Video metadata loaded:", { layerId, metadata });
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                    // composition // resize
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Resize composition settings.
     */
    resizeComposition(
      width: number,
      height: number,
      frameCount?: number,
    ): void {
      const projectStore = useProjectStore();
      const comp = projectStore.getActiveComp();
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      comp.settings.width = width;
      comp.settings.height = height;

      projectStore.project.composition.width = width;
      projectStore.project.composition.height = height;

      if (frameCount !== undefined) {
        comp.settings.frameCount = frameCount;
        comp.settings.duration = frameCount / comp.settings.fps;

        projectStore.project.composition.frameCount = frameCount;
        projectStore.project.composition.duration =
          frameCount / projectStore.project.composition.fps;

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

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

      storeLogger.debug("Composition resized:", {
        width,
        height,
        frameCount: comp.settings.frameCount,
      });
    },
  },
});
