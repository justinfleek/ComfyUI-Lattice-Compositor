/**
 * AI Generation Service
 *
 * Provides lazy-loaded AI model inference via ComfyUI backend.
 * Models are loaded on-demand and unloaded under memory pressure.
 *
 * Supported models:
 * - DepthAnything: Monocular depth estimation
 * - NormalCrafter: Normal map generation
 * - MatSeg: Material segmentation
 * - SAM: Segment Anything Model
 */

// ============================================================================
// TYPES
// ============================================================================

export type AIModelType =
  | "depth-anything"
  | "depth-anything-v2"
  | "normal-crafter"
  | "mat-seg"
  | "segment-anything"
  | "segment-anything-2"
  | "stable-diffusion"
  | "sdxl"
  | "flux";

export type ModelStatus =
  | "not-loaded"
  | "loading"
  | "ready"
  | "error"
  | "unloading";

export interface ModelInfo {
  type: AIModelType;
  name: string;
  description: string;
  memoryRequired: number; // MB
  status: ModelStatus;
  error?: string;
  loadTime?: number; // ms
}

export interface DepthEstimationOptions {
  model: "depth-anything" | "depth-anything-v2";
  outputSize?: { width: number; height: number };
  normalize?: boolean;
  colorMap?: "grayscale" | "viridis" | "plasma" | "magma";
}

export interface NormalMapOptions {
  model: "normal-crafter";
  outputSize?: { width: number; height: number };
  strength?: number; // 0-1
  smoothing?: number; // 0-1
}

export interface SegmentationOptions {
  model: "mat-seg" | "segment-anything" | "segment-anything-2";
  outputSize?: { width: number; height: number };
  point?: { x: number; y: number }; // For SAM point prompt
  box?: { x1: number; y1: number; x2: number; y2: number }; // For SAM box prompt
  labels?: string[]; // For MatSeg
}

export interface GenerationOptions {
  model: "stable-diffusion" | "sdxl" | "flux";
  prompt: string;
  negativePrompt?: string;
  width: number;
  height: number;
  steps?: number;
  cfg?: number;
  seed?: number;
  denoise?: number;
}

export interface InferenceResult<T = ImageData | Uint8ClampedArray> {
  success: boolean;
  data?: T;
  error?: string;
  processingTime: number;
  modelUsed: AIModelType;
}

export interface SegmentationResult extends InferenceResult<ImageData> {
  masks?: ImageData[];
  labels?: string[];
  confidence?: number[];
}

// ============================================================================
// MODEL REGISTRY
// ============================================================================

const MODEL_INFO: Record<
  AIModelType,
  Omit<ModelInfo, "status" | "error" | "loadTime">
> = {
  "depth-anything": {
    type: "depth-anything",
    name: "Depth Anything",
    description: "Monocular depth estimation with high accuracy",
    memoryRequired: 1500,
  },
  "depth-anything-v2": {
    type: "depth-anything-v2",
    name: "Depth Anything V2",
    description: "Improved depth estimation with better details",
    memoryRequired: 2000,
  },
  "normal-crafter": {
    type: "normal-crafter",
    name: "NormalCrafter",
    description: "Normal map generation from images",
    memoryRequired: 1200,
  },
  "mat-seg": {
    type: "mat-seg",
    name: "Material Segmentation",
    description: "Segment materials and surfaces",
    memoryRequired: 800,
  },
  "segment-anything": {
    type: "segment-anything",
    name: "Segment Anything (SAM)",
    description: "Zero-shot image segmentation",
    memoryRequired: 2500,
  },
  "segment-anything-2": {
    type: "segment-anything-2",
    name: "Segment Anything 2",
    description: "Improved segmentation with video support",
    memoryRequired: 3000,
  },
  "stable-diffusion": {
    type: "stable-diffusion",
    name: "Stable Diffusion 1.5",
    description: "Text-to-image generation",
    memoryRequired: 4000,
  },
  sdxl: {
    type: "sdxl",
    name: "Stable Diffusion XL",
    description: "High-resolution text-to-image",
    memoryRequired: 6000,
  },
  flux: {
    type: "flux",
    name: "FLUX",
    description: "State-of-the-art text-to-image",
    memoryRequired: 8000,
  },
};

// ============================================================================
// AI GENERATION SERVICE
// ============================================================================

class AIGenerationService {
  private modelStatus: Map<AIModelType, ModelStatus> = new Map();
  private loadErrors: Map<AIModelType, string> = new Map();
  private loadTimes: Map<AIModelType, number> = new Map();
  private baseUrl: string = "/lattice/ai";

  constructor() {
    // Initialize all models as not loaded
    for (const type of Object.keys(MODEL_INFO) as AIModelType[]) {
      this.modelStatus.set(type, "not-loaded");
    }
  }

  // ========================================
  // MODEL MANAGEMENT
  // ========================================

  /**
   * Get information about a model
   */
  getModelInfo(type: AIModelType): ModelInfo {
    const base = MODEL_INFO[type];
    return {
      ...base,
      status: this.modelStatus.get(type) || "not-loaded",
      error: this.loadErrors.get(type),
      loadTime: this.loadTimes.get(type),
    };
  }

  /**
   * Get all available models
   */
  getAllModels(): ModelInfo[] {
    return (Object.keys(MODEL_INFO) as AIModelType[]).map((type) =>
      this.getModelInfo(type),
    );
  }

  /**
   * Get currently loaded models
   */
  getLoadedModels(): ModelInfo[] {
    return this.getAllModels().filter((m) => m.status === "ready");
  }

  /**
   * Check if a model is available
   */
  isModelAvailable(type: AIModelType): boolean {
    return this.modelStatus.get(type) === "ready";
  }

  /**
   * Load a model
   */
  async loadModel(type: AIModelType): Promise<boolean> {
    const currentStatus = this.modelStatus.get(type);

    if (currentStatus === "ready") return true;
    if (currentStatus === "loading") {
      // Wait for existing load
      return this.waitForModelReady(type);
    }

    this.modelStatus.set(type, "loading");
    this.loadErrors.delete(type);

    const startTime = performance.now();

    try {
      const response = await fetch(`${this.baseUrl}/load`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ model: type }),
      });

      if (!response.ok) {
        const errorData = await response.json().catch(() => ({}));
        throw new Error(
          errorData.error || `Failed to load model: ${response.status}`,
        );
      }

      this.loadTimes.set(type, performance.now() - startTime);
      this.modelStatus.set(type, "ready");
      return true;
    } catch (error) {
      const message = error instanceof Error ? error.message : "Unknown error";
      this.loadErrors.set(type, message);
      this.modelStatus.set(type, "error");
      return false;
    }
  }

  /**
   * Unload a model to free memory
   */
  async unloadModel(type: AIModelType): Promise<boolean> {
    const currentStatus = this.modelStatus.get(type);

    if (currentStatus !== "ready") return true;

    this.modelStatus.set(type, "unloading");

    try {
      const response = await fetch(`${this.baseUrl}/unload`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ model: type }),
      });

      if (!response.ok) {
        throw new Error(`Failed to unload model: ${response.status}`);
      }

      this.modelStatus.set(type, "not-loaded");
      this.loadTimes.delete(type);
      return true;
    } catch (_error) {
      // Reset to ready if unload fails
      this.modelStatus.set(type, "ready");
      return false;
    }
  }

  private async waitForModelReady(
    type: AIModelType,
    timeout: number = 60000,
  ): Promise<boolean> {
    const start = Date.now();

    while (Date.now() - start < timeout) {
      const status = this.modelStatus.get(type);
      if (status === "ready") return true;
      if (status === "error") return false;

      await new Promise((resolve) => setTimeout(resolve, 100));
    }

    return false;
  }

  // ========================================
  // DEPTH ESTIMATION
  // ========================================

  /**
   * Estimate depth from an image
   */
  async estimateDepth(
    image: ImageData | HTMLCanvasElement | Blob,
    options: DepthEstimationOptions = { model: "depth-anything" },
  ): Promise<InferenceResult<ImageData>> {
    const startTime = performance.now();

    // Ensure model is loaded
    const loaded = await this.loadModel(options.model);
    if (!loaded) {
      throw new Error(`[AIGeneration] Failed to load model "${options.model}". Model may not be available or initialization failed.`);
    }

    try {
      const formData = new FormData();
      formData.append("image", await this.imageToBlob(image));
      formData.append("options", JSON.stringify(options));

      const response = await fetch(`${this.baseUrl}/depth`, {
        method: "POST",
        body: formData,
      });

      if (!response.ok) {
        throw new Error(`Depth estimation failed: ${response.status}`);
      }

      const blob = await response.blob();
      const imageData = await this.blobToImageData(blob);

      return {
        success: true,
        data: imageData,
        processingTime: performance.now() - startTime,
        modelUsed: options.model,
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : "Unknown error";
      throw new Error(`[AIGeneration] Depth estimation failed: ${errorMessage}. Check model availability and input image format.`);
    }
  }

  // ========================================
  // NORMAL MAP GENERATION
  // ========================================

  /**
   * Generate normal map from an image
   */
  async generateNormalMap(
    image: ImageData | HTMLCanvasElement | Blob,
    options: NormalMapOptions = { model: "normal-crafter" },
  ): Promise<InferenceResult<ImageData>> {
    const startTime = performance.now();

    const loaded = await this.loadModel(options.model);
    if (!loaded) {
      throw new Error(`[AIGeneration] Failed to load model "${options.model}". Model may not be available or initialization failed.`);
    }

    try {
      const formData = new FormData();
      formData.append("image", await this.imageToBlob(image));
      formData.append("options", JSON.stringify(options));

      const response = await fetch(`${this.baseUrl}/normal`, {
        method: "POST",
        body: formData,
      });

      if (!response.ok) {
        throw new Error(`Normal map generation failed: ${response.status}`);
      }

      const blob = await response.blob();
      const imageData = await this.blobToImageData(blob);

      return {
        success: true,
        data: imageData,
        processingTime: performance.now() - startTime,
        modelUsed: options.model,
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : "Unknown error";
      throw new Error(`[AIGeneration] Normal map generation failed: ${errorMessage}. Check model availability and input image format.`);
    }
  }

  // ========================================
  // SEGMENTATION
  // ========================================

  /**
   * Segment an image
   */
  async segment(
    image: ImageData | HTMLCanvasElement | Blob,
    options: SegmentationOptions,
  ): Promise<SegmentationResult> {
    const startTime = performance.now();

    const loaded = await this.loadModel(options.model);
    if (!loaded) {
      throw new Error(`[AIGeneration] Failed to load model "${options.model}". Model may not be available or initialization failed.`);
    }

    try {
      const formData = new FormData();
      formData.append("image", await this.imageToBlob(image));
      formData.append("options", JSON.stringify(options));

      const response = await fetch(`${this.baseUrl}/segment`, {
        method: "POST",
        body: formData,
      });

      if (!response.ok) {
        throw new Error(`Segmentation failed: ${response.status}`);
      }

      const result = await response.json();

      // Convert mask data to ImageData
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const masksRaw = result.masks;
      const masksArray = (masksRaw !== null && masksRaw !== undefined && Array.isArray(masksRaw)) ? masksRaw : [];
      const masks = await Promise.all(
        masksArray.map((maskBase64: string) =>
          this.base64ToImageData(maskBase64),
        ),
      );

      return {
        success: true,
        data: masks[0], // Primary mask
        masks,
        labels: result.labels,
        confidence: result.confidence,
        processingTime: performance.now() - startTime,
        modelUsed: options.model,
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : "Unknown error";
      throw new Error(`[AIGeneration] Segmentation failed: ${errorMessage}. Check model availability and input image format.`);
    }
  }

  /**
   * Interactive segmentation with point/box prompts (SAM)
   */
  async segmentInteractive(
    image: ImageData | HTMLCanvasElement | Blob,
    point?: { x: number; y: number },
    box?: { x1: number; y1: number; x2: number; y2: number },
  ): Promise<SegmentationResult> {
    return this.segment(image, {
      model: "segment-anything-2",
      point,
      box,
    });
  }

  // ========================================
  // IMAGE GENERATION
  // ========================================

  /**
   * Generate an image from text prompt
   */
  async generate(
    options: GenerationOptions,
  ): Promise<InferenceResult<ImageData>> {
    const startTime = performance.now();

    const loaded = await this.loadModel(options.model);
    if (!loaded) {
      throw new Error(`[AIGeneration] Failed to load model "${options.model}". Model may not be available or initialization failed.`);
    }

    try {
      const response = await fetch(`${this.baseUrl}/generate`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(options),
      });

      if (!response.ok) {
        throw new Error(`Generation failed: ${response.status}`);
      }

      const blob = await response.blob();
      const imageData = await this.blobToImageData(blob);

      return {
        success: true,
        data: imageData,
        processingTime: performance.now() - startTime,
        modelUsed: options.model,
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : "Unknown error";
      throw new Error(`[AIGeneration] Depth estimation failed: ${errorMessage}. Check model availability and input image format.`);
    }
  }

  // ========================================
  // UTILITY METHODS
  // ========================================

  private async imageToBlob(
    image: ImageData | HTMLCanvasElement | Blob,
  ): Promise<Blob> {
    if (image instanceof Blob) {
      return image;
    }

    if (image instanceof HTMLCanvasElement) {
      return new Promise((resolve, reject) => {
        image.toBlob((blob) => {
          if (blob) resolve(blob);
          else reject(new Error("Failed to convert canvas to blob"));
        }, "image/png");
      });
    }

    // ImageData
    const canvas = new OffscreenCanvas(image.width, image.height);
    const ctx = canvas.getContext("2d")!;
    ctx.putImageData(image, 0, 0);
    return canvas.convertToBlob({ type: "image/png" });
  }

  private async blobToImageData(blob: Blob): Promise<ImageData> {
    const bitmap = await createImageBitmap(blob);
    const canvas = new OffscreenCanvas(bitmap.width, bitmap.height);
    const ctx = canvas.getContext("2d")!;
    ctx.drawImage(bitmap, 0, 0);
    return ctx.getImageData(0, 0, bitmap.width, bitmap.height);
  }

  private async base64ToImageData(base64: string): Promise<ImageData> {
    const response = await fetch(`data:image/png;base64,${base64}`);
    const blob = await response.blob();
    return this.blobToImageData(blob);
  }

  /**
   * Check backend connection
   */
  async checkConnection(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/status`);
      return response.ok;
    } catch {
      return false;
    }
  }

  /**
   * Get backend status
   */
  async getBackendStatus(): Promise<{
    connected: boolean;
    gpuAvailable: boolean;
    vramTotal: number;
    vramUsed: number;
    loadedModels: string[];
  }> {
    try {
      const response = await fetch(`${this.baseUrl}/status`);
      if (!response.ok) {
        throw new Error("Backend unavailable");
      }
      return await response.json();
    } catch {
      return {
        connected: false,
        gpuAvailable: false,
        vramTotal: 0,
        vramUsed: 0,
        loadedModels: [],
      };
    }
  }

  /**
   * Set the base URL for AI backend
   */
  setBaseUrl(url: string): void {
    this.baseUrl = url;
  }
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const aiGeneration = new AIGenerationService();
export default aiGeneration;

// ============================================================================
// CONVENIENCE FUNCTIONS
// ============================================================================

import { assertDefined } from "@/utils/typeGuards";

/**
 * Quick depth estimation with default settings
 */
export async function estimateDepth(
  image: ImageData | HTMLCanvasElement | Blob,
): Promise<ImageData> {
  const result = await aiGeneration.estimateDepth(image);
  if (result.success) {
    // Type proof: data is guaranteed non-null when success is true
    assertDefined(result.data, "data must exist when result.success is true");
    return result.data;
  }
  throw new Error(`[AIGeneration] Failed to estimate depth: ${result.error || "Unknown error"}`);
}

/**
 * Quick normal map generation with default settings
 */
export async function generateNormalMap(
  image: ImageData | HTMLCanvasElement | Blob,
): Promise<ImageData> {
  const result = await aiGeneration.generateNormalMap(image);
  if (result.success) {
    // Type proof: data is guaranteed non-null when success is true
    assertDefined(result.data, "data must exist when result.success is true");
    return result.data;
  }
  throw new Error(`[AIGeneration] Cannot generate normal map: Generation failed. ${result.error || "Unknown error"}`);
}

/**
 * Quick interactive segmentation
 */
export async function segmentAtPoint(
  image: ImageData | HTMLCanvasElement | Blob,
  x: number,
  y: number,
): Promise<ImageData> {
  const result = await aiGeneration.segmentInteractive(image, { x, y });
  if (result.success) {
    // Type proof: data is guaranteed non-null when success is true
    assertDefined(result.data, "data must exist when result.success is true");
    return result.data;
  }
  throw new Error(`[AIGeneration] Cannot segment at point (${x}, ${y}): Segmentation failed. ${result.error || "Unknown error"}`);
}

/**
 * Get list of available AI models
 */
export function getAvailableModels(): ModelInfo[] {
  return aiGeneration.getAllModels();
}

/**
 * Check if AI backend is connected
 */
export async function isAIBackendConnected(): Promise<boolean> {
  return aiGeneration.checkConnection();
}
