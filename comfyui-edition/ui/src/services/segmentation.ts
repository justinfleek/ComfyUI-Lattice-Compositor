/**
 * Segmentation Service
 *
 * Communicates with the /lattice/segment backend endpoint for SAM2/MatSeg
 * segmentation to enable Vision → Layer pipeline for diffusion models.
 */

export interface SegmentationPoint {
  x: number;
  y: number;
}

export interface SegmentationRequest {
  /** Base64 encoded PNG image */
  image: string;
  /** Segmentation mode */
  mode: "point" | "box" | "auto";
  /** Segmentation model */
  model?: "sam2" | "matseg";
  /** Points for point mode (x, y coordinates) */
  points?: SegmentationPoint[];
  /** Labels for points (1 = foreground, 0 = background) */
  labels?: number[];
  /** Box for box mode [x1, y1, x2, y2] */
  box?: [number, number, number, number];
  /** Minimum mask area for auto mode */
  minArea?: number;
  /** Maximum masks to return for auto mode */
  maxMasks?: number;
  /** Color tolerance for fallback point selection */
  tolerance?: number;
}

export interface SegmentationMask {
  /** Base64 encoded PNG mask (white = selected, black = background) */
  mask: string;
  /** Bounding box of the mask in the original image */
  bounds: {
    x: number;
    y: number;
    width: number;
    height: number;
  };
  /** Area of the mask in pixels */
  area: number;
  /** Confidence score (0-1) */
  score: number;
}

export interface SegmentationResult {
  status: "success" | "error";
  masks?: SegmentationMask[];
  /** True if using fallback (non-AI) segmentation */
  fallback?: boolean;
  /** Human-readable message */
  message?: string;
}

/**
 * Base URL for the Lattice API
 * In ComfyUI context, this will be the same origin
 */
function getApiBase(): string {
  // In development, use relative URL
  // In ComfyUI context, the routes are registered on the ComfyUI server
  return "";
}

/**
 * Segment an image using SAM2 or MatSeg
 */
export async function segmentImage(
  request: SegmentationRequest,
): Promise<SegmentationResult> {
  const response = await fetch(`${getApiBase()}/lattice/segment`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
    },
    body: JSON.stringify(request),
  });

  if (!response.ok) {
    const errorData = await response.json().catch(() => ({}));
    throw new Error(
      errorData.message || `Segmentation failed: ${response.status}`,
    );
  }

  return response.json();
}

/**
 * Segment by clicking a point on the image
 */
export async function segmentByPoint(
  imageBase64: string,
  point: SegmentationPoint,
  model: "sam2" | "matseg" = "sam2",
): Promise<SegmentationResult> {
  return segmentImage({
    image: imageBase64,
    mode: "point",
    model,
    points: [point],
    labels: [1], // Foreground
  });
}

/**
 * Segment by drawing a box around the target
 */
export async function segmentByBox(
  imageBase64: string,
  box: [number, number, number, number],
  model: "sam2" | "matseg" = "sam2",
): Promise<SegmentationResult> {
  return segmentImage({
    image: imageBase64,
    mode: "box",
    model,
    box,
  });
}

/**
 * Segment with multiple points (positive and negative)
 */
export async function segmentByMultiplePoints(
  imageBase64: string,
  foregroundPoints: SegmentationPoint[],
  backgroundPoints: SegmentationPoint[] = [],
  model: "sam2" | "matseg" = "sam2",
): Promise<SegmentationResult> {
  const points = [...foregroundPoints, ...backgroundPoints];
  const labels = [
    ...foregroundPoints.map(() => 1), // Foreground
    ...backgroundPoints.map(() => 0), // Background
  ];

  return segmentImage({
    image: imageBase64,
    mode: "point",
    model,
    points,
    labels,
  });
}

/**
 * Auto-segment all objects in the image
 */
export async function autoSegment(
  imageBase64: string,
  options: {
    model?: "sam2" | "matseg";
    minArea?: number;
    maxMasks?: number;
  } = {},
): Promise<SegmentationResult> {
  return segmentImage({
    image: imageBase64,
    mode: "auto",
    model: options.model || "sam2",
    minArea: options.minArea || 100,
    maxMasks: options.maxMasks || 20,
  });
}

/**
 * Apply a mask to an image, extracting the masked region as a new image
 * Returns base64 PNG with transparency
 */
export function applyMaskToImage(
  sourceImageBase64: string,
  maskBase64: string,
  bounds: { x: number; y: number; width: number; height: number },
): Promise<string> {
  return new Promise((resolve, reject) => {
    const sourceImg = new Image();
    const maskImg = new Image();

    let sourceLoaded = false;
    let maskLoaded = false;

    const checkComplete = () => {
      if (!sourceLoaded || !maskLoaded) return;

      try {
        // Create canvas at the masked bounds size
        const canvas = document.createElement("canvas");
        canvas.width = bounds.width;
        canvas.height = bounds.height;
        const ctx = canvas.getContext("2d");
        if (!ctx) {
          reject(new Error("Failed to get canvas context"));
          return;
        }

        // Create full-size mask canvas
        const maskCanvas = document.createElement("canvas");
        maskCanvas.width = maskImg.width;
        maskCanvas.height = maskImg.height;
        const maskCtx = maskCanvas.getContext("2d");
        if (!maskCtx) {
          reject(new Error("Failed to get mask canvas context"));
          return;
        }
        maskCtx.drawImage(maskImg, 0, 0);
        const maskData = maskCtx.getImageData(
          bounds.x,
          bounds.y,
          bounds.width,
          bounds.height,
        );

        // Draw source image region
        ctx.drawImage(
          sourceImg,
          bounds.x,
          bounds.y,
          bounds.width,
          bounds.height,
          0,
          0,
          bounds.width,
          bounds.height,
        );

        // Get image data and apply mask as alpha
        const imageData = ctx.getImageData(0, 0, bounds.width, bounds.height);
        for (let i = 0; i < imageData.data.length; i += 4) {
          // Use mask luminance as alpha
          imageData.data[i + 3] = maskData.data[i]; // Red channel of mask = alpha
        }
        ctx.putImageData(imageData, 0, 0);

        // Convert to base64
        const resultBase64 = canvas.toDataURL("image/png").split(",")[1];
        resolve(resultBase64);
      } catch (err) {
        reject(err);
      }
    };

    sourceImg.onload = () => {
      sourceLoaded = true;
      checkComplete();
    };
    sourceImg.onerror = () => reject(new Error("Failed to load source image"));

    maskImg.onload = () => {
      maskLoaded = true;
      checkComplete();
    };
    maskImg.onerror = () => reject(new Error("Failed to load mask image"));

    sourceImg.src = `data:image/png;base64,${sourceImageBase64}`;
    maskImg.src = `data:image/png;base64,${maskBase64}`;
  });
}

/**
 * Create a cropped version of an image based on bounds
 * without applying a mask (for simple box selection)
 */
export function cropImage(
  sourceImageBase64: string,
  bounds: { x: number; y: number; width: number; height: number },
): Promise<string> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => {
      try {
        const canvas = document.createElement("canvas");
        canvas.width = bounds.width;
        canvas.height = bounds.height;
        const ctx = canvas.getContext("2d");
        if (!ctx) {
          reject(new Error("Failed to get canvas context"));
          return;
        }

        ctx.drawImage(
          img,
          bounds.x,
          bounds.y,
          bounds.width,
          bounds.height,
          0,
          0,
          bounds.width,
          bounds.height,
        );

        const resultBase64 = canvas.toDataURL("image/png").split(",")[1];
        resolve(resultBase64);
      } catch (err) {
        reject(err);
      }
    };
    img.onerror = () => reject(new Error("Failed to load image"));
    img.src = `data:image/png;base64,${sourceImageBase64}`;
  });
}

// Re-export mask conversion utilities
export {
  type BezierFitOptions,
  batchSegmentationToMasks,
  type ContourOptions,
  extractContour,
  fitBezierToContour,
  refineMask,
  type SegmentToMaskOptions,
  type SimplifyOptions,
  segmentationToMask,
  simplifyContour,
} from "./segmentToMask";
