/**
 * Decomposition Store
 *
 * Domain store for AI-powered image layer decomposition using the
 * Qwen-Image-Layered model. Automatically creates layers with depth-based
 * z-space positioning.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import {
  type DepthEstimationResult,
  estimateDepthsHeuristic,
  getLLMDepthEstimator,
  type LayerAnalysisInput,
  type LLMProvider,
} from "@/services/ai/depthEstimation";
import {
  type DecomposedLayer,
  getLayerDecompositionService,
} from "@/services/layerDecomposition";
import type { AssetReference, ImageLayerData, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";

// ============================================================================
// TYPES
// ============================================================================

export interface DecompositionStoreAccess {
  project: {
    assets: Record<string, AssetReference>;
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  createLayer(type: string, name: string): Layer;
  setLayerParent(layerId: string, parentId: string | null): void;
  pushHistory(): void;
}

export interface DecomposeAndCreateOptions {
  /** Number of layers to generate (3-16, default 4) */
  numLayers?: number;
  /** Enable LLM-based depth estimation (default true) */
  autoDepthEstimation?: boolean;
  /** LLM provider for depth estimation */
  depthProvider?: LLMProvider;
  /** Z-space scale for layer placement (default 500) */
  zSpaceScale?: number;
  /** Auto-unload model after decomposition to free GPU memory */
  autoUnload?: boolean;
  /** Progress callback */
  onProgress?: (stage: string, message: string, progress?: number) => void;
  /** Group all created layers under a null parent */
  groupLayers?: boolean;
  /** Custom group name */
  groupName?: string;
}

export interface DecompositionResult {
  success: boolean;
  layers: Layer[];
  groupLayerId?: string;
  depthEstimation?: DepthEstimationResult;
  error?: string;
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Get image dimensions from a data URL.
 */
function getImageDimensions(
  dataUrl: string,
): Promise<{ width: number; height: number }> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () =>
      resolve({ width: img.naturalWidth, height: img.naturalHeight });
    img.onerror = () => reject(new Error("Failed to load image"));
    img.src = dataUrl;
  });
}

/**
 * Create a single layer from a decomposed RGBA image.
 */
async function createLayerFromDecomposed(
  store: DecompositionStoreAccess,
  decomposed: DecomposedLayer,
  name: string,
  zPosition: number,
): Promise<Layer | null> {
  try {
    const assetId = `decomp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
    const dimensions = await getImageDimensions(decomposed.image);

    const asset: AssetReference = {
      id: assetId,
      type: "image",
      source: "generated",
      width: dimensions.width,
      height: dimensions.height,
      data: decomposed.image,
    };

    store.project.assets[assetId] = asset;

    const layerStore = useLayerStore();
    const layer = layerStore.createLayer(store as any, "image", name);

    const imageData: ImageLayerData = {
      assetId,
      fit: "none",
      sourceType: "generated",
    };
    layer.data = imageData;

    layer.transform.position.value = {
      x: store.project.composition.width / 2,
      y: store.project.composition.height / 2,
      z: zPosition,
    };

    if (layer.transform.origin) {
      layer.transform.origin.value = {
        x: dimensions.width / 2,
        y: dimensions.height / 2,
      };
    }

    storeLogger.info(
      `Created decomposed layer: ${name} at z=${zPosition.toFixed(0)}`,
    );
    return layer;
  } catch (error) {
    storeLogger.error("Failed to create layer from decomposed:", error);
    return null;
  }
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useDecompositionStore = defineStore("decomposition", {
  state: () => ({}),

  getters: {},

  actions: {
    /**
     * Decompose an image and create layers with automatic z-space placement.
     *
     * @param store - Compositor store access
     * @param imageDataUrl - Base64 data URL of image to decompose
     * @param options - Decomposition options
     * @returns Decomposition result with created layers
     */
    async decomposeImageToLayers(
      store: DecompositionStoreAccess,
      imageDataUrl: string,
      options: DecomposeAndCreateOptions = {},
    ): Promise<DecompositionResult> {
      const {
        numLayers = 4,
        autoDepthEstimation = true,
        depthProvider = "openai",
        zSpaceScale = 500,
        autoUnload = true,
        onProgress,
        groupLayers = true,
        groupName = "Decomposed Layers",
      } = options;

      const service = getLayerDecompositionService();
      const createdLayers: Layer[] = [];

      try {
        // Step 1: Decompose image using Qwen model
        onProgress?.("decomposing", "Decomposing image into layers...", 0);

        const decomposed = await service.decomposeWithAutoSetup(
          imageDataUrl,
          {
            numLayers,
            autoUnload,
            generateSemanticLabels: true,
          },
          onProgress,
        );

        if (!decomposed || decomposed.length === 0) {
          throw new Error("Decomposition returned no layers");
        }

        storeLogger.info(`Decomposition complete: ${decomposed.length} layers`);

        // Step 2: Prepare layer analysis for depth estimation
        onProgress?.("analyzing", "Analyzing layer depths...", 50);

        const layerInputs: LayerAnalysisInput[] = decomposed.map(
          (layer, index) => ({
            index,
            label: layer.label,
            imageDataUrl: layer.image,
          }),
        );

        // Step 3: Estimate depths
        let depthResult: DepthEstimationResult;

        if (autoDepthEstimation) {
          try {
            onProgress?.("estimating", "Estimating layer depths with AI...", 60);
            const estimator = getLLMDepthEstimator();
            depthResult = await estimator.estimateDepths(layerInputs, {
              provider: depthProvider,
              zSpaceScale,
              includeReasoning: true,
            });
          } catch (depthError) {
            storeLogger.warn(
              "LLM depth estimation failed, using heuristics:",
              depthError,
            );
            depthResult = estimateDepthsHeuristic(layerInputs, zSpaceScale);
          }
        } else {
          depthResult = estimateDepthsHeuristic(layerInputs, zSpaceScale);
        }

        // Step 4: Create group layer if requested
        let groupLayerId: string | undefined;
        if (groupLayers) {
          onProgress?.("creating", "Creating layer group...", 70);
          const layerStore = useLayerStore();
          const groupLayer = layerStore.createLayer(store as any, "null", groupName);
          groupLayerId = groupLayer.id;
        }

        // Step 5: Create image layers sorted by depth (farthest first)
        onProgress?.("creating", "Creating layers...", 75);

        const sortedLayers = [...decomposed]
          .map((layer, index) => ({
            decomposed: layer,
            depth:
              depthResult.layers.find((d) => d.layerIndex === index) ||
              depthResult.layers[index],
          }))
          .sort(
            (a, b) =>
              (b.depth?.estimatedDepth || 0) - (a.depth?.estimatedDepth || 0),
          );

        for (let i = 0; i < sortedLayers.length; i++) {
          const { decomposed: layer, depth } = sortedLayers[i];

          onProgress?.(
            "creating",
            `Creating layer ${i + 1}/${sortedLayers.length}...`,
            75 + (i / sortedLayers.length) * 20,
          );

          const createdLayer = await createLayerFromDecomposed(
            store,
            layer,
            depth?.contentDescription || layer.label,
            depth?.suggestedZPosition || 0,
          );

          if (createdLayer) {
            if (groupLayerId) {
              const layerStore = useLayerStore();
              layerStore.setLayerParent(store as any, createdLayer.id, groupLayerId);
            }
            createdLayers.push(createdLayer);
          }
        }

        // Step 6: Finalize
        onProgress?.("complete", `Created ${createdLayers.length} layers`, 100);
        store.project.meta.modified = new Date().toISOString();
        store.pushHistory();

        storeLogger.info(
          `Layer decomposition complete: ${createdLayers.length} layers created`,
        );

        return {
          success: true,
          layers: createdLayers,
          groupLayerId,
          depthEstimation: depthResult,
        };
      } catch (error) {
        const errorMsg = error instanceof Error ? error.message : "Unknown error";
        storeLogger.error("Layer decomposition failed:", error);
        onProgress?.("error", errorMsg, 0);

        return {
          success: false,
          layers: createdLayers,
          error: errorMsg,
        };
      }
    },

    /**
     * Check if the decomposition model is available.
     */
    async checkDecompositionModelStatus(): Promise<{
      downloaded: boolean;
      loaded: boolean;
      verified: boolean;
      error?: string;
    }> {
      try {
        const service = getLayerDecompositionService();
        const status = await service.getStatus();

        return {
          downloaded: status.downloaded,
          loaded: status.loaded,
          verified: status.verification?.verified ?? false,
          error: status.error || undefined,
        };
      } catch (error) {
        return {
          downloaded: false,
          loaded: false,
          verified: false,
          error: error instanceof Error ? error.message : "Unknown error",
        };
      }
    },

    /**
     * Download the decomposition model with progress tracking.
     */
    async downloadDecompositionModel(
      onProgress?: (progress: {
        stage: string;
        bytesDownloaded: number;
        totalBytes: number;
        percent: number;
      }) => void,
    ): Promise<{ success: boolean; error?: string }> {
      const service = getLayerDecompositionService();

      try {
        let stopPolling: (() => void) | null = null;

        if (onProgress) {
          stopPolling = service.pollDownloadProgress((progress) => {
            const percent =
              progress.total_bytes > 0
                ? (progress.bytes_downloaded / progress.total_bytes) * 100
                : 0;

            onProgress({
              stage: progress.stage,
              bytesDownloaded: progress.bytes_downloaded,
              totalBytes: progress.total_bytes,
              percent,
            });
          });
        }

        await service.downloadModel();
        stopPolling?.();

        return { success: true };
      } catch (error) {
        return {
          success: false,
          error: error instanceof Error ? error.message : "Download failed",
        };
      }
    },

    /**
     * Verify model integrity.
     */
    async verifyDecompositionModel(): Promise<{
      verified: boolean;
      filesChecked: number;
      filesValid: number;
      filesInvalid: string[];
      message: string;
    }> {
      const service = getLayerDecompositionService();

      try {
        const result = await service.verifyModel();
        return {
          verified: result.verified,
          filesChecked: result.files_checked,
          filesValid: result.files_valid,
          filesInvalid: result.files_invalid,
          message: result.message,
        };
      } catch (error) {
        return {
          verified: false,
          filesChecked: 0,
          filesValid: 0,
          filesInvalid: [],
          message: error instanceof Error ? error.message : "Verification failed",
        };
      }
    },
  },
});
