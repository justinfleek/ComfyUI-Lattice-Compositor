/**
 * Segmentation Actions
 *
 * Vision model integration for creating layers from segmented images.
 * Used by Time-to-Move and other diffusion model integrations.
 */

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

export interface SegmentationStore {
  sourceImage: string | null;
  project: {
    assets: Record<string, AssetReference>;
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  createLayer(type: string, name: string): Layer;
  pushHistory(): void;
}

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

/**
 * Create an image layer from a segmentation mask
 */
export async function createLayerFromMask(
  store: SegmentationStore,
  sourceImageBase64: string,
  mask: SegmentationMask,
  name?: string,
  positionAtCenter: boolean = false,
): Promise<Layer | null> {
  try {
    // Apply mask to source image to get transparent PNG
    const maskedImageBase64 = await applyMaskToImage(
      sourceImageBase64,
      mask.mask,
      mask.bounds,
    );

    // Generate asset ID
    const assetId = `seg_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

    // Create asset reference
    const asset: AssetReference = {
      id: assetId,
      type: "image",
      source: "generated",
      width: mask.bounds.width,
      height: mask.bounds.height,
      data: maskedImageBase64,
    };

    // Add asset to project
    store.project.assets[assetId] = asset;

    // Create image layer
    const layer = store.createLayer("image", name || "Segmented");

    // Set image data
    const imageData: ImageLayerData = {
      assetId,
      fit: "none", // Don't scale - use original size
      sourceType: "segmented",
    };
    layer.data = imageData;

    // Position layer at the correct location
    if (positionAtCenter) {
      // Center of composition
      layer.transform.position.value = {
        x: store.project.composition.width / 2,
        y: store.project.composition.height / 2,
      };
    } else {
      // Position at the mask's center in the original image
      layer.transform.position.value = {
        x: mask.bounds.x + mask.bounds.width / 2,
        y: mask.bounds.y + mask.bounds.height / 2,
      };
    }

    // Set origin (formerly anchor point) to center of layer
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
}

/**
 * Segment source image by clicking a point and create a layer from the result.
 */
export async function segmentToLayerByPoint(
  store: SegmentationStore,
  point: SegmentationPoint,
  options: SegmentationOptions = {},
): Promise<Layer | null> {
  const sourceImage = store.sourceImage;
  if (!sourceImage) {
    storeLogger.error("No source image available for segmentation");
    return null;
  }

  try {
    const result = await segmentByPoint(
      sourceImage,
      point,
      options.model || "sam2",
    );

    if (
      result.status !== "success" ||
      !result.masks ||
      result.masks.length === 0
    ) {
      storeLogger.error("Segmentation failed:", result.message);
      return null;
    }

    // Use the first (best) mask
    const mask = result.masks[0];
    return createLayerFromMask(
      store,
      sourceImage,
      mask,
      options.layerName,
      options.positionAtCenter,
    );
  } catch (err) {
    storeLogger.error("Segmentation error:", err);
    return null;
  }
}

/**
 * Segment source image by box selection and create a layer from the result.
 */
export async function segmentToLayerByBox(
  store: SegmentationStore,
  box: [number, number, number, number],
  options: SegmentationOptions = {},
): Promise<Layer | null> {
  const sourceImage = store.sourceImage;
  if (!sourceImage) {
    storeLogger.error("No source image available for segmentation");
    return null;
  }

  try {
    const result = await segmentByBox(
      sourceImage,
      box,
      options.model || "sam2",
    );

    if (
      result.status !== "success" ||
      !result.masks ||
      result.masks.length === 0
    ) {
      storeLogger.error("Segmentation failed:", result.message);
      return null;
    }

    const mask = result.masks[0];
    return createLayerFromMask(
      store,
      sourceImage,
      mask,
      options.layerName,
      options.positionAtCenter,
    );
  } catch (err) {
    storeLogger.error("Segmentation error:", err);
    return null;
  }
}

/**
 * Segment source image with multiple positive/negative points.
 */
export async function segmentToLayerByMultiplePoints(
  store: SegmentationStore,
  foregroundPoints: SegmentationPoint[],
  backgroundPoints: SegmentationPoint[] = [],
  options: SegmentationOptions = {},
): Promise<Layer | null> {
  const sourceImage = store.sourceImage;
  if (!sourceImage) {
    storeLogger.error("No source image available for segmentation");
    return null;
  }

  try {
    const result = await segmentByMultiplePoints(
      sourceImage,
      foregroundPoints,
      backgroundPoints,
      options.model || "sam2",
    );

    if (
      result.status !== "success" ||
      !result.masks ||
      result.masks.length === 0
    ) {
      storeLogger.error("Segmentation failed:", result.message);
      return null;
    }

    const mask = result.masks[0];
    return createLayerFromMask(
      store,
      sourceImage,
      mask,
      options.layerName,
      options.positionAtCenter,
    );
  } catch (err) {
    storeLogger.error("Segmentation error:", err);
    return null;
  }
}

/**
 * Auto-segment all objects in the source image and create layers.
 */
export async function autoSegmentToLayers(
  store: SegmentationStore,
  options: AutoSegmentOptions = {},
): Promise<Layer[]> {
  const sourceImage = store.sourceImage;
  if (!sourceImage) {
    storeLogger.error("No source image available for segmentation");
    return [];
  }

  try {
    const result = await autoSegment(sourceImage, {
      model: options.model || "sam2",
      minArea: options.minArea || 1000,
      maxMasks: options.maxMasks || 10,
    });

    if (
      result.status !== "success" ||
      !result.masks ||
      result.masks.length === 0
    ) {
      storeLogger.error("Auto-segmentation failed:", result.message);
      return [];
    }

    const layers: Layer[] = [];
    const prefix = options.namePrefix || "Segment";

    for (let i = 0; i < result.masks.length; i++) {
      const mask = result.masks[i];
      const layer = await createLayerFromMask(
        store,
        sourceImage,
        mask,
        `${prefix} ${i + 1}`,
        false, // Don't center - preserve original position
      );
      if (layer) {
        layers.push(layer);
      }
    }

    return layers;
  } catch (err) {
    storeLogger.error("Auto-segmentation error:", err);
    return [];
  }
}
