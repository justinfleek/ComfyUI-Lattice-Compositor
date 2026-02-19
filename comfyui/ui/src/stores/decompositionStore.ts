/**
 * Decomposition Store
 *
 * Domain store for AI-powered image layer decomposition using the
 * Qwen-Image-Layered model. Automatically creates layers with depth-based
 * z-space positioning.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber, safeCoordinateDefault } from "@/utils/typeGuards";
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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface DecompositionStoreAccess {
  project: {
    assets: Record<string, AssetReference>;
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  createLayer(type: Layer["type"], name?: string): Layer;
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

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

    const layer = store.createLayer("image", name);

    const imageData: ImageLayerData = {
      assetId,
      source: "",
      fit: "none",
      cropEnabled: false,
      cropRect: { x: 0, y: 0, width: 0, height: 0 },
      sourceType: "generated",
      segmentationMaskId: "",
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
    if (error instanceof Error && error.message.startsWith("[DecompositionStore]")) {
      throw error;
    }
    throw new Error(`[DecompositionStore] Failed to create layer from decomposed: ${error instanceof Error ? error.message : String(error)}`);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                           // pinia // store
// ═══════════════════════════════════════════════════════════════════════════

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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("decomposing", "Decomposing image into layers...", 0);
        }

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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("analyzing", "Analyzing layer depths...", 50);
        }

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
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            if (onProgress != null && typeof onProgress === "function") {
              onProgress("estimating", "Estimating layer depths with AI...", 60);
            }
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
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          if (onProgress != null && typeof onProgress === "function") {
            onProgress("creating", "Creating layer group...", 70);
          }
          const groupLayer = store.createLayer("null", groupName);
          groupLayerId = groupLayer.id;
        }

        // Step 5: Create image layers sorted by depth (farthest first)
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("creating", "Creating layers...", 75);
        }

        const sortedLayers = [...decomposed]
          .map((layer, index) => ({
            decomposed: layer,
            depth:
              depthResult.layers.find((d) => d.layerIndex === index) ||
              depthResult.layers[index],
          }))
          .sort(
            (a, b) => {
              // Type proof: estimatedDepth ∈ number | undefined → number (coordinate-like, can be negative)
              // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
              const depthAObj = a.depth;
              const depthA = safeCoordinateDefault((depthAObj != null && typeof depthAObj === "object" && "estimatedDepth" in depthAObj && typeof depthAObj.estimatedDepth === "number") ? depthAObj.estimatedDepth : undefined, 0, "a.depth.estimatedDepth");
              const depthBObj = b.depth;
              const depthB = safeCoordinateDefault((depthBObj != null && typeof depthBObj === "object" && "estimatedDepth" in depthBObj && typeof depthBObj.estimatedDepth === "number") ? depthBObj.estimatedDepth : undefined, 0, "b.depth.estimatedDepth");
              return depthB - depthA;
            },
          );

        for (let i = 0; i < sortedLayers.length; i++) {
          const { decomposed: layer, depth } = sortedLayers[i];

          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          if (onProgress != null && typeof onProgress === "function") {
            onProgress(
              "creating",
              `Creating layer ${i + 1}/${sortedLayers.length}...`,
              75 + (i / sortedLayers.length) * 20,
            );
          }

          // Type proof: suggestedZPosition ∈ number | undefined → number (coordinate-like, can be negative)
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const zPosition = safeCoordinateDefault((depth != null && typeof depth === "object" && "suggestedZPosition" in depth && typeof depth.suggestedZPosition === "number") ? depth.suggestedZPosition : undefined, 0, "depth.suggestedZPosition");
          const contentDescription = (depth != null && typeof depth === "object" && "contentDescription" in depth && typeof depth.contentDescription === "string") ? depth.contentDescription : undefined;
          const createdLayer = await createLayerFromDecomposed(
            store,
            layer,
            contentDescription || layer.label,
            zPosition,
          );

          if (createdLayer) {
            if (groupLayerId) {
              store.setLayerParent(createdLayer.id, groupLayerId);
            }
            createdLayers.push(createdLayer);
          }
        }

        // Step 6: Finalize
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("complete", `Created ${createdLayers.length} layers`, 100);
        }
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("error", errorMsg, 0);
        }
        throw new Error(`[DecompositionStore] Layer decomposition failed: ${errorMsg}. Check model availability and input image.`);
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
      const service = getLayerDecompositionService();
      const status = await service.getStatus();

      return {
        downloaded: status.downloaded,
        loaded: status.loaded,
        // Type proof: verified ∈ boolean | undefined → boolean
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        verified: (() => {
          const verification = (status != null && typeof status === "object" && "verification" in status && status.verification != null && typeof status.verification === "object") ? status.verification : undefined;
          const verifiedValue = (verification != null && typeof verification === "object" && "verified" in verification && typeof verification.verified === "boolean") ? verification.verified : undefined;
          return verifiedValue === true;
        })(),
        error: status.error || undefined,
      };
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (stopPolling != null && typeof stopPolling === "function") {
          stopPolling();
        }

        return { success: true };
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : "Download failed";
        throw new Error(`[DecompositionStore] Model download failed: ${errorMessage}. Check network connection and storage space.`);
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
      const result = await service.verifyModel();
      
      return {
        verified: result.verified,
        filesChecked: result.files_checked,
        filesValid: result.files_valid,
        filesInvalid: result.files_invalid,
        message: result.message,
      };
    },
  },
});
