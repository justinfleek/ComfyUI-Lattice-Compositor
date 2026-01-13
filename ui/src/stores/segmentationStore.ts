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

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

export interface SegmentationStoreAccess {
  sourceImage: string | null;
  project: {
    assets: Record<string, AssetReference>;
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  createLayer(type: string, name: string): Layer;
  pushHistory(): void;
}

// ============================================================================
// OPTIONS INTERFACES
// ============================================================================

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

// ============================================================================
// PINIA STORE
// ============================================================================

export const useSegmentationStore = defineStore("segmentation", {
  state: () => ({}),

  getters: {},

  actions: {
    /**
     * Create an image layer from a segmentation mask.
     *
     * @param store - Compositor store access
     * @param sourceImageBase64 - Base64-encoded source image
     * @param mask - Segmentation mask to apply
     * @param name - Optional layer name
     * @param positionAtCenter - If true, center in composition; otherwise use mask position
     * @returns The created layer or null on failure
     */
    async createLayerFromMask(
      store: SegmentationStoreAccess,
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

        store.project.assets[assetId] = asset;

        const layerStore = useLayerStore();
        const layer = layerStore.createLayer(store as any, "image", name || "Segmented");

        const imageData: ImageLayerData = {
          assetId,
          fit: "none",
          sourceType: "segmented",
        };
        layer.data = imageData;

        if (positionAtCenter) {
          layer.transform.position.value = {
            x: store.project.composition.width / 2,
            y: store.project.composition.height / 2,
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

        store.project.meta.modified = new Date().toISOString();
        store.pushHistory();

        storeLogger.info(
          `Created segmented layer: ${layer.name} (${mask.bounds.width}x${mask.bounds.height})`,
        );
        return layer;
      } catch (err) {
        storeLogger.error("Failed to create layer from mask:", err);
        return null;
      }
    },

    /**
     * Segment source image by clicking a point and create a layer.
     */
    async segmentToLayerByPoint(
      store: SegmentationStoreAccess,
      point: SegmentationPoint,
      options: SegmentationOptions = {},
    ): Promise<Layer | null> {
      if (!store.sourceImage) {
        storeLogger.warn("No source image for segmentation");
        return null;
      }

      try {
        const result = await segmentByPoint(store.sourceImage, point, options.model);

        if (result.status !== "success" || !result.masks?.length) {
          storeLogger.warn("Segmentation returned no masks:", result.message);
          return null;
        }

        const mask = result.masks[0];
        return this.createLayerFromMask(
          store,
          store.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
      } catch (err) {
        storeLogger.error("Segmentation by point failed:", err);
        return null;
      }
    },

    /**
     * Segment source image by multiple points and create a layer.
     * @param foregroundPoints - Points indicating foreground objects
     * @param backgroundPoints - Points indicating background (optional)
     */
    async segmentToLayerByMultiplePoints(
      store: SegmentationStoreAccess,
      foregroundPoints: SegmentationPoint[],
      backgroundPoints: SegmentationPoint[] = [],
      options: SegmentationOptions = {},
    ): Promise<Layer | null> {
      if (!store.sourceImage) {
        storeLogger.warn("No source image for segmentation");
        return null;
      }

      try {
        const result = await segmentByMultiplePoints(store.sourceImage, foregroundPoints, backgroundPoints, options.model);

        if (result.status !== "success" || !result.masks?.length) {
          storeLogger.warn("Segmentation returned no masks:", result.message);
          return null;
        }

        const mask = result.masks[0];
        return this.createLayerFromMask(
          store,
          store.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
      } catch (err) {
        storeLogger.error("Segmentation by multiple points failed:", err);
        return null;
      }
    },

    /**
     * Segment source image by bounding box and create a layer.
     * @param box - Bounding box as [x1, y1, x2, y2] tuple
     */
    async segmentToLayerByBox(
      store: SegmentationStoreAccess,
      box: [number, number, number, number],
      options: SegmentationOptions = {},
    ): Promise<Layer | null> {
      if (!store.sourceImage) {
        storeLogger.warn("No source image for segmentation");
        return null;
      }

      try {
        const result = await segmentByBox(store.sourceImage, box, options.model);

        if (result.status !== "success" || !result.masks?.length) {
          storeLogger.warn("Segmentation returned no masks:", result.message);
          return null;
        }

        const mask = result.masks[0];
        return this.createLayerFromMask(
          store,
          store.sourceImage,
          mask,
          options.layerName,
          options.positionAtCenter,
        );
      } catch (err) {
        storeLogger.error("Segmentation by box failed:", err);
        return null;
      }
    },

    /**
     * Auto-segment entire image and create multiple layers.
     */
    async autoSegmentToLayers(
      store: SegmentationStoreAccess,
      options: AutoSegmentOptions = {},
    ): Promise<Layer[]> {
      if (!store.sourceImage) {
        storeLogger.warn("No source image for auto segmentation");
        return [];
      }

      try {
        const result = await autoSegment(store.sourceImage, {
          model: options.model,
          minArea: options.minArea,
          maxMasks: options.maxMasks,
        });

        if (result.status !== "success" || !result.masks?.length) {
          storeLogger.warn("Auto segmentation returned no masks:", result.message);
          return [];
        }

        const layers: Layer[] = [];
        const namePrefix = options.namePrefix || "Segment";

        for (let i = 0; i < result.masks.length; i++) {
          const mask = result.masks[i];
          const layer = await this.createLayerFromMask(
            store,
            store.sourceImage,
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
