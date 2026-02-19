/**
 * Layer Decomposition Service
 *
 * Frontend service for AI-powered image layer decomposition using
 * the Qwen-Image-Layered model. Communicates with the backend via
 * the /lattice/decomposition/* API endpoints.
 *
 * Model: Qwen/Qwen-Image-Layered (28.8GB)
 * Capabilities: Decomposes single images into 3-16+ RGBA layers
 */

import { createLogger } from "@/utils/logger";
import { getComfyUIClient } from "./comfyui/comfyuiClient";
import { isFiniteNumber } from "@/utils/typeGuards";
import {
  canAllocate,
  registerAllocation,
  unregisterAllocation,
  VRAM_ESTIMATES,
} from "./memoryBudget";

const logger = createLogger("LayerDecomposition");

const MODEL_ALLOCATION_ID = "model:qwen-image-layered";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export interface ModelVerification {
  verified: boolean;
  files_checked: number;
  files_valid: number;
  files_invalid: string[];
  files_missing: string[];
  message: string;
}

export interface DownloadProgress {
  current_file: string;
  files_completed: number;
  total_files: number;
  bytes_downloaded: number;
  total_bytes: number;
  stage:
    | "idle"
    | "starting"
    | "downloading"
    | "verifying"
    | "complete"
    | "error";
}

export interface DecompositionModelStatus {
  downloaded: boolean;
  loaded: boolean;
  loading: boolean;
  error: string | null;
  model_path: string;
  model_size_gb: number;
  verification: ModelVerification | null;
  download_progress: DownloadProgress | null;
}

export interface DecomposedLayer {
  index: number;
  label: string;
  image: string; // data URL (data:image/png;base64,...)
  has_alpha: boolean;
}

export interface DecompositionOptions {
  numLayers?: number; // 3-16, default 4
  guidanceScale?: number; // default 3.0
  numInferenceSteps?: number; // default 50
  seed?: number | null; // null for random
  autoUnload?: boolean; // Unload model after decomposition (default true)
  generateSemanticLabels?: boolean; // Use vision LLM to label layers (default true)
}

export interface DecompositionResult {
  status: "success" | "error";
  message: string;
  layers?: DecomposedLayer[];
}

// ═══════════════════════════════════════════════════════════════════════════
// Service Class
// ═══════════════════════════════════════════════════════════════════════════

export class LayerDecompositionService {
  private baseUrl: string;

  constructor(serverAddress?: string) {
    const client = getComfyUIClient(serverAddress);
    this.baseUrl = `http://${client.server}`;
  }

  /**
   * Get current model status (downloaded, loaded, errors)
   */
  async getStatus(): Promise<DecompositionModelStatus> {
    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/status`,
      );
      const result = await response.json();

      if (result.status === "success") {
        return result.data;
      }

      throw new Error(result.message || "Failed to get model status");
    } catch (error) {
      logger.error("Failed to get model status:", error);
      throw error;
    }
  }

  /**
   * Download the model (28.8GB, may take a while)
   *
   * @param onProgress - Optional callback for download progress
   */
  async downloadModel(
    onProgress?: (stage: string, progress: number) => void,
  ): Promise<void> {
    try {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("starting", 0);
      }

      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/download`,
        {
          method: "POST",
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      // Check verification result
      if (
        result.verification &&
        !result.verification.verified &&
        result.verification.files_invalid.length > 0
      ) {
        throw new Error(
          `Model verification failed: ${result.verification.message}`,
        );
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("complete", 100);
      }
      logger.info("Model download complete");
    } catch (error) {
      logger.error("Model download failed:", error);
      throw error;
    }
  }

  /**
   * Get current download progress
   */
  async getDownloadProgress(): Promise<DownloadProgress> {
    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/progress`,
      );
      const result = await response.json();

      if (result.status === "success") {
        return result.data;
      }

      throw new Error(result.message || "Failed to get download progress");
    } catch (error) {
      logger.error("Failed to get download progress:", error);
      throw error;
    }
  }

  /**
   * Verify model integrity using SHA256 hashes
   */
  async verifyModel(): Promise<ModelVerification> {
    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/verify`,
        {
          method: "POST",
        },
      );
      const result = await response.json();

      return result.data;
    } catch (error) {
      logger.error("Failed to verify model:", error);
      throw error;
    }
  }

  /**
   * Poll download progress at intervals
   *
   * @param onProgress - Callback for progress updates
   * @param intervalMs - Polling interval (default 1000ms)
   * @returns Stop function to cancel polling
   */
  pollDownloadProgress(
    onProgress: (progress: DownloadProgress) => void,
    intervalMs: number = 1000,
  ): () => void {
    let stopped = false;

    const poll = async () => {
      if (stopped) return;

      try {
        const progress = await this.getDownloadProgress();
        onProgress(progress);

        // Stop polling if download is complete or errored
        if (
          progress.stage === "complete" ||
          progress.stage === "error" ||
          progress.stage === "idle"
        ) {
          return;
        }

        // Continue polling
        setTimeout(poll, intervalMs);
      } catch (error) {
        logger.warn("Progress poll failed:", error);
        if (!stopped) {
          setTimeout(poll, intervalMs * 2); // Backoff on error
        }
      }
    };

    poll();

    return () => {
      stopped = true;
    };
  }

  /**
   * Load the model into GPU memory
   */
  async loadModel(): Promise<void> {
    // Check if we have enough memory before loading
    const memCheck = canAllocate(VRAM_ESTIMATES["model:qwen-image-layered"]);
    if (!memCheck.canProceed) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const warningMessage = (memCheck.warning != null && typeof memCheck.warning === "object" && "message" in memCheck.warning && typeof memCheck.warning.message === "string") ? memCheck.warning.message : undefined;
      throw new Error(warningMessage != null ? warningMessage : "Insufficient GPU memory");
    }

    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/load`,
        {
          method: "POST",
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      // Register memory allocation
      registerAllocation(
        MODEL_ALLOCATION_ID,
        "Qwen Image Layered Model",
        "model",
        VRAM_ESTIMATES["model:qwen-image-layered"],
        {
          canUnload: true,
          unloadFn: () => this.unloadModel(),
        },
      );

      logger.info("Model loaded:", result.message);
    } catch (error) {
      logger.error("Model load failed:", error);
      throw error;
    }
  }

  /**
   * Unload the model from GPU memory
   */
  async unloadModel(): Promise<void> {
    try {
      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/unload`,
        {
          method: "POST",
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      // Unregister memory allocation
      unregisterAllocation(MODEL_ALLOCATION_ID);

      logger.info("Model unloaded");
    } catch (error) {
      logger.error("Model unload failed:", error);
      throw error;
    }
  }

  /**
   * Decompose an image into RGBA layers
   *
   * @param imageDataUrl - Image as data URL (data:image/...;base64,...)
   * @param options - Decomposition options
   * @returns Array of decomposed layers
   */
  async decompose(
    imageDataUrl: string,
    options: DecompositionOptions = {},
  ): Promise<DecomposedLayer[]> {
    try {
      // Type proof: numLayers ∈ number | undefined → number
      const numLayers = isFiniteNumber(options.numLayers) &&
        options.numLayers >= 3 && options.numLayers <= 16
        ? options.numLayers
        : 4;
      // Type proof: guidanceScale ∈ number | undefined → number
      const guidanceScale = isFiniteNumber(options.guidanceScale) &&
        options.guidanceScale > 0
        ? options.guidanceScale
        : 3.0;
      // Type proof: numInferenceSteps ∈ number | undefined → number
      const numInferenceSteps = isFiniteNumber(options.numInferenceSteps) &&
        options.numInferenceSteps > 0
        ? options.numInferenceSteps
        : 50;
      // Type proof: seed ∈ number | null | undefined → number | null
      const seed = isFiniteNumber(options.seed) ? options.seed : null;

      const response = await fetch(
        `${this.baseUrl}/lattice/decomposition/decompose`,
        {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({
            image: imageDataUrl,
            num_layers: numLayers,
            guidance_scale: guidanceScale,
            num_inference_steps: numInferenceSteps,
            seed,
          }),
        },
      );

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message);
      }

      logger.info(`Decomposition complete: ${result.layers.length} layers`);
      return result.layers;
    } catch (error) {
      logger.error("Decomposition failed:", error);
      throw error;
    }
  }

  /**
   * One-click decomposition: handles download, load, decompose, and cleanup
   *
   * @param imageDataUrl - Image as data URL
   * @param options - Decomposition options
   * @param onProgress - Progress callback
   */
  async decomposeWithAutoSetup(
    imageDataUrl: string,
    options: DecompositionOptions = {},
    onProgress?: (stage: string, message: string) => void,
  ): Promise<DecomposedLayer[]> {
    const autoUnload = options.autoUnload !== false; // Default true
    const generateLabels = options.generateSemanticLabels !== false; // Default true

    try {
      // Check status
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("checking", "Checking model status...");
      }
      const status = await this.getStatus();

      // Download if needed
      if (!status.downloaded) {
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("downloading", "Downloading model (28.8GB)...");
        }
        await this.downloadModel();
      }

      // Load if needed
      if (!status.loaded) {
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("loading", "Loading model into GPU memory...");
        }
        await this.loadModel();
      }

      // Decompose
      if (onProgress != null && typeof onProgress === "function") {
        onProgress("decomposing", "Decomposing image into layers...");
      }
      const layers = await this.decompose(imageDataUrl, options);

      // Generate semantic labels if requested
      if (generateLabels && layers.length > 0) {
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("labeling", "Generating semantic labels...");
        }
        await this.generateSemanticLabels(layers);
      }

      if (onProgress != null && typeof onProgress === "function") {
        onProgress("complete", `Generated ${layers.length} layers`);
      }
      return layers;
    } finally {
      // Auto-unload to free GPU memory (critical for large workflows)
      if (autoUnload) {
        if (onProgress != null && typeof onProgress === "function") {
          onProgress("cleanup", "Freeing GPU memory...");
        }
        try {
          await this.unloadModel();
          logger.info("Model auto-unloaded to free GPU memory");
        } catch (unloadError) {
          logger.warn("Failed to auto-unload model:", unloadError);
        }
      }
    }
  }

  /**
   * Generate semantic labels for decomposed layers using simple heuristics
   * Analyzes alpha channel coverage and position to assign meaningful names
   */
  private async generateSemanticLabels(
    layers: DecomposedLayer[],
  ): Promise<void> {
    // Analyze each layer to generate semantic labels
    for (let i = 0; i < layers.length; i++) {
      const layer = layers[i];

      try {
        // Load image to analyze
        const img = await dataUrlToImage(layer.image);
        const canvas = document.createElement("canvas");
        canvas.width = img.naturalWidth;
        canvas.height = img.naturalHeight;
        const ctx = canvas.getContext("2d")!;
        ctx.drawImage(img, 0, 0);

        const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const analysis = analyzeLayerContent(imageData);

        // Generate semantic label based on analysis
        layer.label = generateLabelFromAnalysis(analysis, i, layers.length);
      } catch (error) {
        logger.warn(`Failed to analyze layer ${i}:`, error);
        // Keep default label
      }
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// Singleton Instance
// ═══════════════════════════════════════════════════════════════════════════

let defaultService: LayerDecompositionService | null = null;

export function getLayerDecompositionService(
  serverAddress?: string,
): LayerDecompositionService {
  if (!defaultService) {
    defaultService = new LayerDecompositionService(serverAddress);
  }
  return defaultService;
}

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Convert a canvas to a data URL
 */
export function canvasToDataUrl(canvas: HTMLCanvasElement): string {
  return canvas.toDataURL("image/png");
}

/**
 * Convert an Image element to a data URL
 */
export function imageToDataUrl(img: HTMLImageElement): string {
  const canvas = document.createElement("canvas");
  canvas.width = img.naturalWidth;
  canvas.height = img.naturalHeight;
  const ctx = canvas.getContext("2d")!;
  ctx.drawImage(img, 0, 0);
  return canvas.toDataURL("image/png");
}

/**
 * Load an image from a data URL
 */
export function dataUrlToImage(dataUrl: string): Promise<HTMLImageElement> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = reject;
    img.src = dataUrl;
  });
}

// ═══════════════════════════════════════════════════════════════════════════
// Layer Analysis Utilities
// ═══════════════════════════════════════════════════════════════════════════

interface LayerAnalysis {
  /** Percentage of pixels with alpha > 0 (0-1) */
  coverage: number;
  /** Percentage of pixels with alpha > 200 (0-1) */
  solidCoverage: number;
  /** Vertical center of mass (0=top, 1=bottom) */
  verticalCenter: number;
  /** Horizontal center of mass (0=left, 1=right) */
  horizontalCenter: number;
  /** Average color (RGB) */
  avgColor: { r: number; g: number; b: number };
  /** Is mostly transparent (coverage < 10%) */
  isSparse: boolean;
  /** Is mostly opaque (solidCoverage > 80%) */
  isDense: boolean;
  /** Is primarily in upper half */
  isUpper: boolean;
  /** Is primarily in lower half */
  isLower: boolean;
  /** Is edge/outline (low solid coverage, medium total coverage) */
  isEdge: boolean;
}

/**
 * Analyze layer content to determine semantic characteristics
 */
function analyzeLayerContent(imageData: ImageData): LayerAnalysis {
  const { data, width, height } = imageData;
  const totalPixels = width * height;

  let visiblePixels = 0;
  let solidPixels = 0;
  let weightedX = 0;
  let weightedY = 0;
  let totalR = 0,
    totalG = 0,
    totalB = 0;
  let colorSamples = 0;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      const r = data[i];
      const g = data[i + 1];
      const b = data[i + 2];
      const a = data[i + 3];

      if (a > 0) {
        visiblePixels++;
        const weight = a / 255;
        weightedX += x * weight;
        weightedY += y * weight;

        if (a > 200) {
          solidPixels++;
          totalR += r;
          totalG += g;
          totalB += b;
          colorSamples++;
        }
      }
    }
  }

  const coverage = visiblePixels / totalPixels;
  const solidCoverage = solidPixels / totalPixels;

  const centerX = visiblePixels > 0 ? weightedX / visiblePixels / width : 0.5;
  const centerY = visiblePixels > 0 ? weightedY / visiblePixels / height : 0.5;

  const avgColor =
    colorSamples > 0
      ? {
          r: totalR / colorSamples,
          g: totalG / colorSamples,
          b: totalB / colorSamples,
        }
      : { r: 128, g: 128, b: 128 };

  return {
    coverage,
    solidCoverage,
    verticalCenter: centerY,
    horizontalCenter: centerX,
    avgColor,
    isSparse: coverage < 0.1,
    isDense: solidCoverage > 0.8,
    isUpper: centerY < 0.4,
    isLower: centerY > 0.6,
    isEdge: coverage > 0.1 && coverage < 0.4 && solidCoverage < coverage * 0.5,
  };
}

/**
 * Generate semantic label based on layer analysis
 */
function generateLabelFromAnalysis(
  analysis: LayerAnalysis,
  index: number,
  totalLayers: number,
): string {
  const position = index / (totalLayers - 1); // 0 = first, 1 = last

  // First layer is typically background
  if (index === 0) {
    if (analysis.isDense) {
      return "Background (Solid)";
    }
    if (analysis.isUpper && analysis.coverage > 0.3) {
      return "Background (Sky)";
    }
    return "Background";
  }

  // Last layer is typically foreground subject
  if (index === totalLayers - 1) {
    if (analysis.isSparse) {
      return "Foreground (Details)";
    }
    return "Foreground (Subject)";
  }

  // Middle layers - analyze characteristics
  if (analysis.isEdge) {
    return `Edges/Outlines (${index + 1})`;
  }

  if (analysis.isSparse) {
    if (analysis.isUpper) {
      return `Upper Details (${index + 1})`;
    }
    if (analysis.isLower) {
      return `Lower Details (${index + 1})`;
    }
    return `Sparse Elements (${index + 1})`;
  }

  if (analysis.isDense) {
    return `Solid Region (${index + 1})`;
  }

  // Position-based naming for mid layers
  if (position < 0.33) {
    return `Back Elements (${index + 1})`;
  }
  if (position > 0.66) {
    return `Front Elements (${index + 1})`;
  }

  return `Mid Elements (${index + 1})`;
}
