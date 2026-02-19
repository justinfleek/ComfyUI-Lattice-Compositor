/**
 * Segmentation Store
 *
 * Domain store for AI-powered image segmentation operations.
 * Integrates with SAM2 and MatSeg vision models for creating layers
 * from segmented images.
 *
 * NOTE: Segmentation UI state (segmentToolActive, segmentMode, segmentBoxStart,
 * segmentPendingMask, segmentIsLoading) remains in compositorStore until
 * Phase 5 consumer migration is complete.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import {
  applyMaskToImage,
  autoSegment,
  type SegmentationMask,
  type SegmentationPoint,
  segmentByBox,
  segmentByMultiplePoints,
  segmentByPoint,
} from "@/services/segmentation";
import type { AssetReference, ImageLayerData, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                             // store // access // interface
// ═══════════════════════════════════════════════════════════════════════════

export interface SegmentationStoreAccess {
  sourceImage: string | null;
  project: {
    assets: Record<string, AssetReference>;
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  createLayer(type: Layer["type"], name?: string): Layer;
  pushHistory(): void;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // options // interfaces
// ═══════════════════════════════════════════════════════════════════════════

export interface SegmentationOptions {
  model?: "sam2" | "matseg";
  layerName?: string;
  positionAtCenter?: boolean;
}

export interface AutoSegmentOptions extends SegmentationOptions {
  minArea?: number;
  maxMasks?: number;
  namePrefix?: string;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                           // pinia // store
// ═══════════════════════════════════════════════════════════════════════════

export const useSegmentationStore = defineStore("segmentation", {
  state: () => ({
    segmentToolActive: false,
    segmentMode: "point" as "point" | "box",
    segmentPendingMask: null as {
      mask: string;
      bounds: { x: number; y: number; width: number; height: number };
      area: number;
      score: number;
    } | null,
    segmentBoxStart: null as { x: number; y: number } | null,
    segmentIsLoading: false,
  }),

  getters: {},

  actions: {
    setSegmentToolActive(active: boolean): void {
      this.segmentToolActive = active;
    },

    setSegmentMode(mode: "point" | "box"): void {
      this.segmentMode = mode;
    },

    setSegmentPendingMask(mask: {
      mask: string;
      bounds: { x: number; y: number; width: number; height: number };
      area: number;
      score: number;
    } | null): void {
      this.segmentPendingMask = mask;
    },

    setSegmentBoxStart(point: { x: number; y: number } | null): void {
      this.segmentBoxStart = point;
    },

    setSegmentIsLoading(loading: boolean): void {
      this.segmentIsLoading = loading;
    },

    clearSegmentPendingMask(): void {
      this.segmentPendingMask = null;
      this.segmentBoxStart = null;
    },

    async createLayerFromMask(
      sourceImageBase64: string,
      mask: SegmentationMask,
      name?: string,
      positionAtCenter: boolean = false,
    ): Promise<Layer | null> {
      try {
        const maskedImageBase64 = await applyMaskToImage(
          sourceImageBase64,
          mask.mask,
          mask.bounds,
        );

        const assetId = `seg_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

        const asset: AssetReference = {
          id: assetId,
          type: "image",
          source: "generated",
          width: mask.bounds.width,
          height: mask.bounds.height,
          data: maskedImageBase64,
        };

        const projectStore = useProjectStore();
        projectStore.project.assets[assetId] = asset;

        const layerStore = useLayerStore();
        const layer = layerStore.createLayer("image", name || "Segmented");

        const imageData: ImageLayerData = {
          assetId,
          source: "",
          fit: "none",
          cropEnabled: false,
          cropRect: { x: 0, y: 0, width: 0, height: 0 },
          sourceType: "segmented",
          segmentationMaskId: "",
        };
        layer.data = imageData;

        if (positionAtCenter) {
          layer.transform.position.value = {
            x: projectStore.project.composition.width / 2,
            y: projectStore.project.composition.height / 2,
          };
        } else {
          layer.transform.position.value = {
            x: mask.bounds.x + mask.bounds.width / 2,
            y: mask.bounds.y + mask.bounds.height / 2,
          };
        }

        const originProp = layer.transform.origin || layer.transform.anchorPoint;
        if (originProp) {
          originProp.value = {
            x: mask.bounds.width / 2,
            y: mask.bounds.height / 2,
          };
        }

        projectStore.project.meta.modified = new Date().toISOString();
        projectStore.pushHistory();

        storeLogger.info(
          `Created segmented layer: ${layer.name} (${mask.bounds.width}x${mask.bounds.height})`,
        );
        return layer;
      } catch (err) {
        if (err instanceof Error && err.message.startsWith("[SegmentationStore]")) {
          throw err;
        }
        throw new Error(`[SegmentationStore] Failed to create layer from mask: ${err instanceof Error ? err.message : String(err)}`);
      }
    },

    async segmentToLayerByPoint(
      point: SegmentationPoint,
      options: SegmentationOptions = {},
    ): Promise<Layer> {
      const projectStore = useProjectStore();
      if (!projectStore.sourceImage) {
        throw new Error("[SegmentationStore] Cannot segment by point: No source image available");
      }

      try {
        const result = await segmentByPoint(projectStore.sourceImage, point, options.model);

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const resultMasks = (result != null && typeof result === "object" && "masks" in result && result.masks != null && Array.isArray(result.masks)) ? result.masks : undefined;
        const masksLength = resultMasks != null ? resultMasks.length : 0;
        if (result.status !== "success" || masksLength === 0 || resultMasks === undefined) {
          throw new Error(`[SegmentationStore] Segmentation by point failed: ${result.message || "No masks returned"}`);
        }

        const mask = resultMasks[0];
        const layer = await this.createLayerFromMask(
          projectStore.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
        if (layer === null) {
          throw new Error("[SegmentationStore] Failed to create layer from mask: createLayerFromMask returned null");
        }
        return layer;
      } catch (err) {
        if (err instanceof Error && err.message.startsWith("[SegmentationStore]")) {
          throw err;
        }
        throw new Error(`[SegmentationStore] Segmentation by point failed: ${err instanceof Error ? err.message : String(err)}`);
      }
    },

    async segmentToLayerByMultiplePoints(
      foregroundPoints: SegmentationPoint[],
      backgroundPoints: SegmentationPoint[] = [],
      options: SegmentationOptions = {},
    ): Promise<Layer> {
      const projectStore = useProjectStore();
      if (!projectStore.sourceImage) {
        throw new Error("[SegmentationStore] Cannot segment by multiple points: No source image available");
      }

      try {
        const result = await segmentByMultiplePoints(projectStore.sourceImage, foregroundPoints, backgroundPoints, options.model);

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const resultMasks = (result != null && typeof result === "object" && "masks" in result && result.masks != null && Array.isArray(result.masks)) ? result.masks : undefined;
        const masksLength = resultMasks != null ? resultMasks.length : 0;
        if (result.status !== "success" || masksLength === 0 || resultMasks === undefined) {
          throw new Error(`[SegmentationStore] Segmentation by multiple points failed: ${result.message || "No masks returned"}`);
        }

        const mask = resultMasks[0];
        const layer = await this.createLayerFromMask(
          projectStore.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
        if (layer === null) {
          throw new Error("[SegmentationStore] Failed to create layer from mask: createLayerFromMask returned null");
        }
        return layer;
      } catch (err) {
        if (err instanceof Error && err.message.startsWith("[SegmentationStore]")) {
          throw err;
        }
        throw new Error(`[SegmentationStore] Segmentation by multiple points failed: ${err instanceof Error ? err.message : String(err)}`);
      }
    },

    async segmentToLayerByBox(
      box: [number, number, number, number],
      options: SegmentationOptions = {},
    ): Promise<Layer> {
      const projectStore = useProjectStore();
      if (!projectStore.sourceImage) {
        throw new Error("[SegmentationStore] Cannot segment by box: No source image available");
      }

      try {
        const result = await segmentByBox(projectStore.sourceImage, box, options.model);

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const resultMasks = (result != null && typeof result === "object" && "masks" in result && result.masks != null && Array.isArray(result.masks)) ? result.masks : undefined;
        const masksLength = resultMasks != null ? resultMasks.length : 0;
        if (result.status !== "success" || masksLength === 0 || resultMasks === undefined) {
          throw new Error(`[SegmentationStore] Segmentation by box failed: ${result.message || "No masks returned"}`);
        }

        const mask = resultMasks[0];
        const layer = await this.createLayerFromMask(
          projectStore.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
        if (layer === null) {
          throw new Error("[SegmentationStore] Failed to create layer from mask: createLayerFromMask returned null");
        }
        return layer;
      } catch (err) {
        if (err instanceof Error && err.message.startsWith("[SegmentationStore]")) {
          throw err;
        }
        throw new Error(`[SegmentationStore] Segmentation by box failed: ${err instanceof Error ? err.message : String(err)}`);
      }
    },

    async autoSegmentToLayers(
      options: AutoSegmentOptions = {},
    ): Promise<Layer[]> {
      const projectStore = useProjectStore();
      if (!projectStore.sourceImage) {
        storeLogger.warn("No source image for auto segmentation");
        return [];
      }

      try {
        const result = await autoSegment(projectStore.sourceImage, {
          model: options.model,
          minArea: options.minArea,
          maxMasks: options.maxMasks,
        });

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const resultMasks = (result != null && typeof result === "object" && "masks" in result && result.masks != null && Array.isArray(result.masks)) ? result.masks : undefined;
        const masksLength = resultMasks != null ? resultMasks.length : 0;
        if (result.status !== "success" || masksLength === 0 || resultMasks === undefined) {
          storeLogger.warn("Auto segmentation returned no masks:", result.message);
          return [];
        }

        const layers: Layer[] = [];
        const namePrefix = options.namePrefix || "Segment";

        for (let i = 0; i < resultMasks.length; i++) {
          const mask = resultMasks[i];
          const layer = await this.createLayerFromMask(
            projectStore.sourceImage,
            mask,
            `${namePrefix}_${i + 1}`,
            options.positionAtCenter,
          );
          if (layer) {
            layers.push(layer);
          }
        }

        storeLogger.info(`Auto segmentation created ${layers.length} layers`);
        return layers;
      } catch (err) {
        storeLogger.error("Auto segmentation failed:", err);
        return [];
      }
    },
  },
});
