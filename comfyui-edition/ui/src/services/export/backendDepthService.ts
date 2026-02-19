/**
 * Backend Depth & Normal Map Service
 *
 * Calls the Python backend endpoints (/lattice/depth, /lattice/normal) for
 * real AI-powered depth estimation using DepthAnything V3 and normal map
 * generation using algebraic or NormalCrafter methods.
 *
 * This service should be used by ExportDialog.vue instead of the mock
 * client-side depth simulation.
 */

import { createLogger } from "@/utils/logger";
import { getComfyUIClient } from "../comfyui/comfyuiClient";

const logger = createLogger("BackendDepthService");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ════════════════════════════════════════════════════════════════════════════

export interface DepthGenerationOptions {
  model?: "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1";
  returnConfidence?: boolean;
  returnIntrinsics?: boolean;
}

export interface DepthGenerationResult {
  status: "success" | "error";
  depth: string; // base64 encoded PNG (grayscale)
  confidence?: string; // base64 encoded PNG (optional)
  intrinsics?: number[][]; // Camera intrinsics matrix (optional)
  fallback?: boolean; // True if using fallback estimation
  message?: string;
  metadata?: {
    model: string;
    width: number;
    height: number;
    depth_min?: number;
    depth_max?: number;
  };
}

export interface NormalGenerationOptions {
  method?: "algebraic" | "normalcrafter";
  depthModel?: "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1";
}

/**
 * Request body for normal map generation API
 */
interface NormalGenerationRequestBody {
  method: "algebraic" | "normalcrafter";
  depth_model: "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1";
  image?: string; // Base64 encoded image
  depth?: string; // Base64 encoded depth map
}

export interface NormalGenerationResult {
  status: "success" | "error";
  normal: string; // base64 encoded PNG (RGB normal map)
  depth?: string; // base64 depth map used (if generated)
  fallback?: boolean;
  message?: string;
  metadata?: {
    method: string;
    width: number;
    height: number;
  };
}

// ════════════════════════════════════════════════════════════════════════════
// Service Class
// ════════════════════════════════════════════════════════════════════════════

export class BackendDepthService {
  private baseUrl: string;

  constructor(serverAddress?: string) {
    const client = getComfyUIClient(serverAddress);
    this.baseUrl = `http://${client.server}`;
  }

  /**
   * Generate depth map from an image using DepthAnything V3 backend
   *
   * @param imageBase64 - Base64 encoded PNG/JPEG image (without data URL prefix)
   * @param options - Depth generation options
   * @returns Depth map result with base64 encoded grayscale PNG
   */
  async generateDepth(
    imageBase64: string,
    options: DepthGenerationOptions = {},
  ): Promise<DepthGenerationResult> {
    const {
      model = "DA3-LARGE-1.1",
      returnConfidence = false,
      returnIntrinsics = false,
    } = options;

    try {
      logger.info(`Generating depth map using ${model}`);

      const response = await fetch(`${this.baseUrl}/lattice/depth`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          image: imageBase64,
          model,
          return_confidence: returnConfidence,
          return_intrinsics: returnIntrinsics,
        }),
      });

      if (!response.ok) {
        throw new Error(`Depth API error: ${response.status} ${response.statusText}`);
      }

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message || "Depth generation failed");
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const metadata = (result != null && typeof result === "object" && "metadata" in result && result.metadata != null && typeof result.metadata === "object") ? result.metadata : undefined;
      const width = (metadata != null && typeof metadata === "object" && "width" in metadata && typeof metadata.width === "number") ? metadata.width : undefined;
      const height = (metadata != null && typeof metadata === "object" && "height" in metadata && typeof metadata.height === "number") ? metadata.height : undefined;
      const dimensions = (width != null && height != null) ? `${width}x${height}` : "unknown dimensions";
      logger.info(`Depth map generated: ${dimensions}`);

      return result as DepthGenerationResult;
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : "Unknown error";
      logger.error("Depth generation failed:", error);

      return {
        status: "error",
        depth: "",
        message: errorMsg,
      };
    }
  }

  /**
   * Generate normal map from an image or depth map
   *
   * @param imageBase64 - Base64 encoded RGB image (optional if depth provided)
   * @param depthBase64 - Base64 encoded depth map (optional)
   * @param options - Normal generation options
   * @returns Normal map result with base64 encoded RGB PNG
   */
  async generateNormal(
    imageBase64?: string,
    depthBase64?: string,
    options: NormalGenerationOptions = {},
  ): Promise<NormalGenerationResult> {
    const { method = "algebraic", depthModel = "DA3-LARGE-1.1" } = options;

    if (!imageBase64 && !depthBase64) {
      return {
        status: "error",
        normal: "",
        message: "Either image or depth must be provided",
      };
    }

    try {
      logger.info(`Generating normal map using ${method} method`);

      const requestBody: NormalGenerationRequestBody = {
        method,
        depth_model: depthModel,
        ...(imageBase64 && { image: imageBase64 }),
        ...(depthBase64 && { depth: depthBase64 }),
      };

      const response = await fetch(`${this.baseUrl}/lattice/normal`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(requestBody),
      });

      if (!response.ok) {
        throw new Error(`Normal API error: ${response.status} ${response.statusText}`);
      }

      const result = await response.json();

      if (result.status === "error") {
        throw new Error(result.message || "Normal generation failed");
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const metadata = (result != null && typeof result === "object" && "metadata" in result && result.metadata != null && typeof result.metadata === "object") ? result.metadata : undefined;
      const width = (metadata != null && typeof metadata === "object" && "width" in metadata && typeof metadata.width === "number") ? metadata.width : undefined;
      const height = (metadata != null && typeof metadata === "object" && "height" in metadata && typeof metadata.height === "number") ? metadata.height : undefined;
      const dimensions = (width != null && height != null) ? `${width}x${height}` : "unknown dimensions";
      logger.info(`Normal map generated: ${dimensions}`);

      return result as NormalGenerationResult;
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : "Unknown error";
      logger.error("Normal generation failed:", error);

      return {
        status: "error",
        normal: "",
        message: errorMsg,
      };
    }
  }

  /**
   * Generate both depth and normal maps in sequence
   * Uses the generated depth for normal map calculation (more efficient)
   */
  async generateDepthAndNormal(
    imageBase64: string,
    depthOptions: DepthGenerationOptions = {},
    normalOptions: NormalGenerationOptions = {},
  ): Promise<{
    depth: DepthGenerationResult;
    normal: NormalGenerationResult;
  }> {
    // First generate depth
    const depthResult = await this.generateDepth(imageBase64, depthOptions);

    if (depthResult.status === "error" || !depthResult.depth) {
      return {
        depth: depthResult,
        normal: {
          status: "error",
          normal: "",
          message: "Cannot generate normal without depth",
        },
      };
    }

    // Use the generated depth for normal map (more efficient than regenerating)
    const normalResult = await this.generateNormal(
      undefined,
      depthResult.depth,
      normalOptions,
    );

    return {
      depth: depthResult,
      normal: normalResult,
    };
  }

  /**
   * Check if backend depth services are available
   */
  async checkAvailability(): Promise<{
    depthAvailable: boolean;
    normalAvailable: boolean;
    fallbackOnly: boolean;
  }> {
    try {
      // Create a tiny test image (1x1 white pixel)
      const testImage = "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mP8/5/hPwAIAgL/4d1j8wAAAABJRU5ErkJggg==";

      const depthResult = await this.generateDepth(testImage);
      const depthAvailable = depthResult.status === "success";
      const fallbackOnly = depthResult.fallback === true;

      return {
        depthAvailable,
        normalAvailable: depthAvailable, // Normal depends on depth
        fallbackOnly,
      };
    } catch {
      return {
        depthAvailable: false,
        normalAvailable: false,
        fallbackOnly: true,
      };
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
// Singleton Instance
// ════════════════════════════════════════════════════════════════════════════

let defaultService: BackendDepthService | null = null;

export function getBackendDepthService(serverAddress?: string): BackendDepthService {
  if (!defaultService) {
    defaultService = new BackendDepthService(serverAddress);
  }
  return defaultService;
}

// ════════════════════════════════════════════════════════════════════════════
// Utility Functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert canvas/ImageData to base64 for API calls
 */
export function canvasToBase64(canvas: HTMLCanvasElement | OffscreenCanvas): string {
  if (canvas instanceof HTMLCanvasElement) {
    const dataUrl = canvas.toDataURL("image/png");
    return dataUrl.replace(/^data:image\/png;base64,/, "");
  }

  // OffscreenCanvas doesn't have toDataURL, need to use transferToImageBitmap
  // For now, create a regular canvas to extract data
  const tempCanvas = document.createElement("canvas");
  tempCanvas.width = canvas.width;
  tempCanvas.height = canvas.height;
  const ctx = tempCanvas.getContext("2d");
  if (ctx && canvas instanceof HTMLCanvasElement) {
    ctx.drawImage(canvas, 0, 0);
  }
  const dataUrl = tempCanvas.toDataURL("image/png");
  return dataUrl.replace(/^data:image\/png;base64,/, "");
}

/**
 * Convert base64 PNG to Blob for ZIP packaging
 */
export function base64ToBlob(base64: string, mimeType = "image/png"): Blob {
  const byteCharacters = atob(base64);
  const byteNumbers = new Array(byteCharacters.length);
  for (let i = 0; i < byteCharacters.length; i++) {
    byteNumbers[i] = byteCharacters.charCodeAt(i);
  }
  const byteArray = new Uint8Array(byteNumbers);
  return new Blob([byteArray], { type: mimeType });
}

/**
 * Convert base64 PNG to data URL
 */
export function base64ToDataUrl(base64: string, mimeType = "image/png"): string {
  return `data:${mimeType};base64,${base64}`;
}
