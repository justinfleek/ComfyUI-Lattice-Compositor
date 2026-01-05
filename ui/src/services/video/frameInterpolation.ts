/**
 * Frame Interpolation Service
 *
 * Frontend service for RIFE-based frame interpolation.
 * Used for smooth slow-motion and frame rate upscaling.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes: https://github.com/filliptm/ComfyUI_Fill-Nodes
 * - RIFE (Megvii Research): https://github.com/megvii-research/ECCV2022-RIFE
 * - Practical-RIFE: https://github.com/hzwer/Practical-RIFE
 *
 * @module services/video/frameInterpolation
 */

// ============================================================================
// Types
// ============================================================================

/**
 * RIFE model variants
 */
export type RIFEModel = "rife-v4.6" | "rife-v4.0" | "rife-v3.9" | "film";

/**
 * Interpolation factor (frame multiplication)
 */
export type InterpolationFactor = 2 | 4 | 8;

/**
 * Model information from backend
 */
export interface InterpolationModel {
  id: RIFEModel;
  name: string;
  description: string;
  supports_ensemble: boolean;
  recommended: boolean;
}

/**
 * Interpolation result for a frame pair
 */
export interface PairInterpolationResult {
  status: "success" | "error";
  message?: string;
  frames?: string[]; // base64 PNG images
  count?: number;
  model?: string;
}

/**
 * Interpolation result for a sequence
 */
export interface SequenceInterpolationResult {
  status: "success" | "error";
  message?: string;
  frames?: string[]; // base64 PNG images
  original_count?: number;
  interpolated_count?: number;
  factor?: number;
  model?: string;
}

/**
 * Slow-mo result
 */
export interface SlowMoResult {
  status: "success" | "error";
  message?: string;
  frames?: string[];
  original_count?: number;
  slowmo_count?: number;
  effective_slowdown?: number;
  model?: string;
}

/**
 * Progress callback
 */
export type InterpolationProgressCallback = (
  progress: number,
  message: string,
) => void;

// ============================================================================
// API Communication
// ============================================================================

const API_BASE = "/lattice/video/interpolation";

/**
 * Get available interpolation models
 */
export async function getInterpolationModels(): Promise<InterpolationModel[]> {
  try {
    const response = await fetch(`${API_BASE}/models`);
    const data = await response.json();

    if (data.status === "success") {
      return data.models;
    }

    console.warn("Failed to get interpolation models:", data.message);
    return getDefaultModels();
  } catch (error) {
    console.warn("Frame interpolation backend not available:", error);
    return getDefaultModels();
  }
}

/**
 * Default models when backend is unavailable
 */
function getDefaultModels(): InterpolationModel[] {
  return [
    {
      id: "rife-v4.6",
      name: "RIFE v4.6",
      description: "Latest RIFE - Best quality and speed balance",
      supports_ensemble: true,
      recommended: true,
    },
    {
      id: "rife-v4.0",
      name: "RIFE v4.0",
      description: "Stable RIFE v4 - Good all-around performance",
      supports_ensemble: true,
      recommended: false,
    },
    {
      id: "film",
      name: "FILM",
      description: "Frame Interpolation for Large Motion - Google Research",
      supports_ensemble: false,
      recommended: false,
    },
  ];
}

/**
 * Interpolate between two frames
 *
 * @param frame1 - First frame as base64, Blob, or ImageData
 * @param frame2 - Second frame
 * @param options - Interpolation options
 * @returns Array of interpolated frames (between frame1 and frame2)
 *
 * @example
 * ```typescript
 * const result = await interpolateFramePair(frame1, frame2, {
 *   count: 3,
 *   model: 'rife-v4.6'
 * });
 *
 * if (result.status === 'success') {
 *   // result.frames contains 3 intermediate frames
 *   for (const frameB64 of result.frames) {
 *     const img = new Image();
 *     img.src = `data:image/png;base64,${frameB64}`;
 *   }
 * }
 * ```
 */
export async function interpolateFramePair(
  frame1: string | Blob | ImageData,
  frame2: string | Blob | ImageData,
  options: {
    count?: number;
    model?: RIFEModel;
    ensemble?: boolean;
  } = {},
): Promise<PairInterpolationResult> {
  try {
    const frame1B64 = await frameToBase64(frame1);
    const frame2B64 = await frameToBase64(frame2);

    const response = await fetch(`${API_BASE}/pair`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frame1: frame1B64,
        frame2: frame2B64,
        count: options.count ?? 1,
        model: options.model ?? "rife-v4.6",
        ensemble: options.ensemble ?? false,
      }),
    });

    const result = await response.json();

    if (!response.ok) {
      return {
        status: "error",
        message: result.message || `HTTP ${response.status}`,
      };
    }

    return result;
  } catch (error) {
    console.error("Frame pair interpolation failed:", error);
    return {
      status: "error",
      message: error instanceof Error ? error.message : "Unknown error",
    };
  }
}

/**
 * Interpolate an entire frame sequence
 *
 * @param frames - Array of frames
 * @param options - Interpolation options
 * @returns Interpolated sequence with (factor * original - factor + 1) frames
 *
 * @example
 * ```typescript
 * // Double the frame rate of a 30-frame sequence
 * const result = await interpolateSequence(frames, { factor: 2 });
 *
 * if (result.status === 'success') {
 *   // result.frames contains ~59 frames (2x - 1)
 *   console.log(`Upscaled from ${result.original_count} to ${result.interpolated_count}`);
 * }
 * ```
 */
export async function interpolateSequence(
  frames: (string | Blob | ImageData)[],
  options: {
    factor?: InterpolationFactor;
    model?: RIFEModel;
    ensemble?: boolean;
  } = {},
): Promise<SequenceInterpolationResult> {
  try {
    const framesB64 = await Promise.all(frames.map((f) => frameToBase64(f)));

    const response = await fetch(`${API_BASE}/sequence`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: framesB64,
        factor: options.factor ?? 2,
        model: options.model ?? "rife-v4.6",
        ensemble: options.ensemble ?? false,
      }),
    });

    const result = await response.json();

    if (!response.ok) {
      return {
        status: "error",
        message: result.message || `HTTP ${response.status}`,
      };
    }

    return result;
  } catch (error) {
    console.error("Sequence interpolation failed:", error);
    return {
      status: "error",
      message: error instanceof Error ? error.message : "Unknown error",
    };
  }
}

/**
 * Create slow-motion effect from frames
 *
 * @param frames - Array of frames
 * @param slowdown - Slowdown factor (2.0 = half speed)
 * @param model - RIFE model to use
 * @returns Slow-motion frame sequence
 *
 * @example
 * ```typescript
 * // Create 2x slow-motion
 * const result = await createSlowMotion(frames, 2.0);
 *
 * // Create 4x slow-motion
 * const result = await createSlowMotion(frames, 4.0);
 * ```
 */
export async function createSlowMotion(
  frames: (string | Blob | ImageData)[],
  slowdown: number = 2.0,
  model: RIFEModel = "rife-v4.6",
): Promise<SlowMoResult> {
  try {
    const framesB64 = await Promise.all(frames.map((f) => frameToBase64(f)));

    const response = await fetch(`${API_BASE}/slowmo`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: framesB64,
        slowdown,
        model,
      }),
    });

    const result = await response.json();

    if (!response.ok) {
      return {
        status: "error",
        message: result.message || `HTTP ${response.status}`,
      };
    }

    return result;
  } catch (error) {
    console.error("Slow-motion creation failed:", error);
    return {
      status: "error",
      message: error instanceof Error ? error.message : "Unknown error",
    };
  }
}

// ============================================================================
// Client-Side Interpolation (Fallback)
// ============================================================================

/**
 * Simple client-side frame blending (fallback when backend unavailable)
 *
 * This uses linear blending and is NOT as good as RIFE,
 * but provides basic functionality without a GPU backend.
 */
export function blendFrames(
  frame1: ImageData,
  frame2: ImageData,
  t: number,
): ImageData {
  const width = frame1.width;
  const height = frame1.height;
  const result = new ImageData(width, height);

  for (let i = 0; i < frame1.data.length; i++) {
    result.data[i] = Math.round(frame1.data[i] * (1 - t) + frame2.data[i] * t);
  }

  return result;
}

/**
 * Client-side linear interpolation between frames
 *
 * Fallback when RIFE backend is unavailable
 */
export function interpolateFramesClient(
  frame1: ImageData,
  frame2: ImageData,
  count: number,
): ImageData[] {
  const results: ImageData[] = [];

  for (let i = 0; i < count; i++) {
    const t = (i + 1) / (count + 1);
    results.push(blendFrames(frame1, frame2, t));
  }

  return results;
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Convert frame to base64 string
 */
async function frameToBase64(
  frame: string | Blob | ImageData,
): Promise<string> {
  if (typeof frame === "string") {
    // Already base64 or data URL
    return frame.includes(",") ? frame.split(",")[1] : frame;
  }

  if (frame instanceof Blob) {
    return blobToBase64(frame);
  }

  // ImageData
  return imageDataToBase64(frame);
}

/**
 * Convert Blob to base64
 */
function blobToBase64(blob: Blob): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onloadend = () => {
      const result = reader.result as string;
      resolve(result.split(",")[1]);
    };
    reader.onerror = reject;
    reader.readAsDataURL(blob);
  });
}

/**
 * Convert ImageData to base64 PNG
 */
function imageDataToBase64(imageData: ImageData): string {
  const canvas = document.createElement("canvas");
  canvas.width = imageData.width;
  canvas.height = imageData.height;

  const ctx = canvas.getContext("2d")!;
  ctx.putImageData(imageData, 0, 0);

  const dataUrl = canvas.toDataURL("image/png");
  return dataUrl.split(",")[1];
}

/**
 * Convert base64 to ImageData
 */
export async function base64ToImageData(base64: string): Promise<ImageData> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => {
      const canvas = document.createElement("canvas");
      canvas.width = img.width;
      canvas.height = img.height;

      const ctx = canvas.getContext("2d")!;
      ctx.drawImage(img, 0, 0);

      resolve(ctx.getImageData(0, 0, img.width, img.height));
    };
    img.onerror = reject;
    img.src = base64.startsWith("data:")
      ? base64
      : `data:image/png;base64,${base64}`;
  });
}

/**
 * Convert base64 to Blob
 */
export function base64ToBlob(
  base64: string,
  mimeType: string = "image/png",
): Blob {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return new Blob([bytes], { type: mimeType });
}

// ============================================================================
// Presets
// ============================================================================

/**
 * Preset configurations for common interpolation tasks
 */
export const INTERPOLATION_PRESETS = {
  /**
   * Quick 2x interpolation - fast and good quality
   */
  quick2x: {
    factor: 2 as InterpolationFactor,
    model: "rife-v4.6" as RIFEModel,
    ensemble: false,
    description: "Fast 2x frame rate increase",
  },

  /**
   * Quality 2x interpolation - better but slower
   */
  quality2x: {
    factor: 2 as InterpolationFactor,
    model: "rife-v4.6" as RIFEModel,
    ensemble: true,
    description: "High-quality 2x frame rate increase",
  },

  /**
   * 4x interpolation for smooth slow-mo
   */
  slowmo4x: {
    factor: 4 as InterpolationFactor,
    model: "rife-v4.6" as RIFEModel,
    ensemble: false,
    description: "4x slow-motion effect",
  },

  /**
   * 8x interpolation for ultra slow-mo
   */
  ultraSlowmo: {
    factor: 8 as InterpolationFactor,
    model: "rife-v4.6" as RIFEModel,
    ensemble: false,
    description: "8x ultra slow-motion effect",
  },

  /**
   * Film-style interpolation for large motion
   */
  film: {
    factor: 2 as InterpolationFactor,
    model: "film" as RIFEModel,
    ensemble: false,
    description: "FILM model for scenes with large motion",
  },
} as const;

/**
 * Check if frame interpolation backend is available
 */
export async function isInterpolationAvailable(): Promise<boolean> {
  try {
    const response = await fetch(`${API_BASE}/models`, {
      method: "GET",
      signal: AbortSignal.timeout(3000),
    });
    return response.ok;
  } catch {
    return false;
  }
}
