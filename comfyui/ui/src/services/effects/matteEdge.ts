/**
 * Matte Edge Effects
 *
 * Professional compositing tools for refining matte edges:
 * - Choker: Shrink or expand matte edges
 * - Spill Suppressor: Remove color contamination from edges
 * - Edge Feathering: Soften matte edges
 */

import { createLogger } from "@/utils/logger";

const _logger = createLogger("MatteEdge");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ════════════════════════════════════════════════════════════════════════════

export interface ChokerParams {
  /** Choke amount: negative shrinks, positive expands (pixels) */
  amount: number;
  /** Edge softness/blur (pixels) */
  softness: number;
  /** Number of iterations for stronger effect */
  iterations: number;
}

export interface SpillSuppressorParams {
  /** Color to suppress (RGB 0-255) */
  spillColor: { r: number; g: number; b: number };
  /** Tolerance for color matching (0-1) */
  tolerance: number;
  /** Amount to desaturate spill areas (0-1) */
  desaturate: number;
  /** Replacement color for spill areas */
  replaceColor?: { r: number; g: number; b: number };
  /** Only affect edge pixels (partial alpha) */
  edgesOnly: boolean;
}

export interface EdgeFeatherParams {
  /** Feather radius in pixels */
  radius: number;
  /** Feather direction: 'both', 'inward', 'outward' */
  direction: "both" | "inward" | "outward";
}

// ════════════════════════════════════════════════════════════════════════════
// Choker Effect
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply choker effect to an alpha channel
 *
 * Shrinks (negative amount) or expands (positive amount) the matte
 */
export function applyChoker(
  alpha: Float32Array,
  width: number,
  height: number,
  params: ChokerParams,
): Float32Array {
  let result = alpha.slice();

  for (let iter = 0; iter < params.iterations; iter++) {
    if (params.amount < 0) {
      // Shrink: erode the alpha
      result = erodeAlpha(
        result,
        width,
        height,
        Math.abs(params.amount) / params.iterations,
      ) as Float32Array<ArrayBuffer>;
    } else if (params.amount > 0) {
      // Expand: dilate the alpha
      result = dilateAlpha(
        result,
        width,
        height,
        params.amount / params.iterations,
      ) as Float32Array<ArrayBuffer>;
    }
  }

  // Apply softness (edge blur)
  if (params.softness > 0) {
    result = gaussianBlurAlpha(
      result,
      width,
      height,
      params.softness,
    ) as Float32Array<ArrayBuffer>;
  }

  return result;
}

/**
 * Erode (shrink) alpha channel
 */
function erodeAlpha(
  alpha: Float32Array,
  width: number,
  height: number,
  amount: number,
): Float32Array {
  const result = new Float32Array(alpha.length);
  const radius = Math.ceil(amount);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = y * width + x;
      let minAlpha = alpha[idx];

      // Sample in a circle
      for (let dy = -radius; dy <= radius; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > amount) continue;

          const nx = x + dx;
          const ny = y + dy;
          if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;

          const nidx = ny * width + nx;
          minAlpha = Math.min(minAlpha, alpha[nidx]);
        }
      }

      result[idx] = minAlpha;
    }
  }

  return result;
}

/**
 * Dilate (expand) alpha channel
 */
function dilateAlpha(
  alpha: Float32Array,
  width: number,
  height: number,
  amount: number,
): Float32Array {
  const result = new Float32Array(alpha.length);
  const radius = Math.ceil(amount);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = y * width + x;
      let maxAlpha = alpha[idx];

      // Sample in a circle
      for (let dy = -radius; dy <= radius; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > amount) continue;

          const nx = x + dx;
          const ny = y + dy;
          if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;

          const nidx = ny * width + nx;
          maxAlpha = Math.max(maxAlpha, alpha[nidx]);
        }
      }

      result[idx] = maxAlpha;
    }
  }

  return result;
}

/**
 * Apply Gaussian blur to alpha channel
 */
function gaussianBlurAlpha(
  alpha: Float32Array,
  width: number,
  height: number,
  sigma: number,
): Float32Array {
  // Generate 1D Gaussian kernel
  const radius = Math.ceil(sigma * 3);
  const kernel: number[] = [];
  let sum = 0;

  for (let i = -radius; i <= radius; i++) {
    const value = Math.exp(-(i * i) / (2 * sigma * sigma));
    kernel.push(value);
    sum += value;
  }

  // Normalize kernel
  for (let i = 0; i < kernel.length; i++) {
    kernel[i] /= sum;
  }

  // Horizontal pass
  const temp = new Float32Array(alpha.length);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let value = 0;
      for (let i = -radius; i <= radius; i++) {
        const nx = Math.min(Math.max(x + i, 0), width - 1);
        value += alpha[y * width + nx] * kernel[i + radius];
      }
      temp[y * width + x] = value;
    }
  }

  // Vertical pass
  const result = new Float32Array(alpha.length);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let value = 0;
      for (let i = -radius; i <= radius; i++) {
        const ny = Math.min(Math.max(y + i, 0), height - 1);
        value += temp[ny * width + x] * kernel[i + radius];
      }
      result[y * width + x] = value;
    }
  }

  return result;
}

// ════════════════════════════════════════════════════════════════════════════
// Spill Suppressor Effect
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply spill suppressor to an RGBA image
 *
 * Removes color contamination (typically green/blue screen spill) from edges
 */
export function applySpillSuppressor(
  imageData: ImageData,
  alpha: Float32Array,
  params: SpillSuppressorParams,
): ImageData {
  const result = new ImageData(
    new Uint8ClampedArray(imageData.data),
    imageData.width,
    imageData.height,
  );
  const data = result.data;

  const spillR = params.spillColor.r;
  const spillG = params.spillColor.g;
  const spillB = params.spillColor.b;

  // Normalize spill color for comparison
  const spillLength =
    Math.sqrt(spillR * spillR + spillG * spillG + spillB * spillB) || 1;
  const normSpillR = spillR / spillLength;
  const normSpillG = spillG / spillLength;
  const normSpillB = spillB / spillLength;

  for (let i = 0; i < data.length; i += 4) {
    const pixelIndex = i / 4;
    const a = alpha[pixelIndex];

    // Only process edge pixels if edgesOnly is true
    if (params.edgesOnly && (a <= 0.01 || a >= 0.99)) {
      continue;
    }

    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    // Calculate spill amount using color similarity
    const spillAmount = calculateSpillAmount(
      r,
      g,
      b,
      normSpillR,
      normSpillG,
      normSpillB,
      spillR,
      spillG,
      spillB,
      params.tolerance,
    );

    if (spillAmount > 0) {
      // Apply spill suppression
      const [newR, newG, newB] = suppressSpill(
        r,
        g,
        b,
        spillAmount,
        params.desaturate,
        params.replaceColor,
      );

      data[i] = newR;
      data[i + 1] = newG;
      data[i + 2] = newB;
    }
  }

  return result;
}

/**
 * Calculate how much a pixel is affected by spill
 */
function calculateSpillAmount(
  r: number,
  g: number,
  b: number,
  normSpillR: number,
  normSpillG: number,
  normSpillB: number,
  spillR: number,
  spillG: number,
  spillB: number,
  tolerance: number,
): number {
  // Calculate color similarity using dot product
  const length = Math.sqrt(r * r + g * g + b * b) || 1;
  const normR = r / length;
  const normG = g / length;
  const normB = b / length;

  const similarity =
    normR * normSpillR + normG * normSpillG + normB * normSpillB;

  // Map similarity to spill amount based on tolerance
  const threshold = 1 - tolerance;
  if (similarity < threshold) return 0;

  // Also check if this channel is dominant (for green/blue screen)
  // This helps target actual spill rather than just similar colors
  let spillDominance = 0;
  if (spillG > spillR && spillG > spillB) {
    // Green screen spill
    spillDominance = (g - Math.max(r, b)) / 255;
  } else if (spillB > spillR && spillB > spillG) {
    // Blue screen spill
    spillDominance = (b - Math.max(r, g)) / 255;
  } else if (spillR > spillG && spillR > spillB) {
    // Red screen spill (rare)
    spillDominance = (r - Math.max(g, b)) / 255;
  }

  spillDominance = Math.max(0, spillDominance);

  // Combine similarity and dominance
  const amount =
    ((similarity - threshold) / tolerance) * (0.5 + spillDominance * 0.5);
  return Math.min(1, Math.max(0, amount));
}

/**
 * Suppress spill in a pixel
 */
function suppressSpill(
  r: number,
  g: number,
  b: number,
  spillAmount: number,
  desaturate: number,
  replaceColor?: { r: number; g: number; b: number },
): [number, number, number] {
  let newR = r;
  let newG = g;
  let newB = b;

  // Calculate luminance
  const luminance = 0.299 * r + 0.587 * g + 0.114 * b;

  // Desaturate based on spill amount
  const desatAmount = spillAmount * desaturate;
  newR = r + (luminance - r) * desatAmount;
  newG = g + (luminance - g) * desatAmount;
  newB = b + (luminance - b) * desatAmount;

  // Optionally blend with replacement color
  if (replaceColor) {
    const blendAmount = spillAmount * 0.5; // Subtle replacement
    newR = newR * (1 - blendAmount) + replaceColor.r * blendAmount;
    newG = newG * (1 - blendAmount) + replaceColor.g * blendAmount;
    newB = newB * (1 - blendAmount) + replaceColor.b * blendAmount;
  }

  return [
    Math.round(Math.min(255, Math.max(0, newR))),
    Math.round(Math.min(255, Math.max(0, newG))),
    Math.round(Math.min(255, Math.max(0, newB))),
  ];
}

// ════════════════════════════════════════════════════════════════════════════
// Edge Feathering
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply edge feathering to alpha channel
 */
export function applyEdgeFeather(
  alpha: Float32Array,
  width: number,
  height: number,
  params: EdgeFeatherParams,
): Float32Array {
  const { radius, direction } = params;

  if (radius <= 0) return alpha.slice();

  // First, detect edges
  const edges = detectEdges(alpha, width, height);

  // Create distance field from edges
  const distanceField = computeDistanceField(
    edges,
    alpha,
    width,
    height,
    radius,
    direction,
  );

  // Apply feathering based on distance
  const result = new Float32Array(alpha.length);

  for (let i = 0; i < alpha.length; i++) {
    const dist = distanceField[i];
    const originalAlpha = alpha[i];

    if (direction === "both") {
      // Feather both inward and outward
      const t = Math.max(0, Math.min(1, (dist + radius) / (2 * radius)));
      result[i] = t;
    } else if (direction === "inward") {
      // Only feather inward (reduce alpha at edges)
      if (dist < 0) {
        const t = Math.max(0, 1 + dist / radius);
        result[i] = originalAlpha * t;
      } else {
        result[i] = originalAlpha;
      }
    } else {
      // Only feather outward (expand alpha at edges)
      if (dist > 0 && dist < radius) {
        const t = 1 - dist / radius;
        result[i] = Math.max(originalAlpha, t);
      } else {
        result[i] = originalAlpha;
      }
    }
  }

  return result;
}

/**
 * Detect edge pixels (pixels with partial alpha neighbors)
 */
function detectEdges(
  alpha: Float32Array,
  width: number,
  height: number,
): Float32Array {
  const edges = new Float32Array(alpha.length);

  for (let y = 1; y < height - 1; y++) {
    for (let x = 1; x < width - 1; x++) {
      const idx = y * width + x;
      const a = alpha[idx];

      // Check if this pixel is on an edge
      if (a > 0.01 && a < 0.99) {
        edges[idx] = 1;
        continue;
      }

      // Check neighbors for alpha transition
      let hasTransition = false;
      for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++) {
          if (dx === 0 && dy === 0) continue;
          const nidx = (y + dy) * width + (x + dx);
          if (Math.abs(alpha[nidx] - a) > 0.1) {
            hasTransition = true;
            break;
          }
        }
        if (hasTransition) break;
      }

      if (hasTransition) {
        edges[idx] = 1;
      }
    }
  }

  return edges;
}

/**
 * Compute signed distance field from edges
 */
function computeDistanceField(
  edges: Float32Array,
  alpha: Float32Array,
  width: number,
  height: number,
  maxDist: number,
  _direction: string,
): Float32Array {
  const result = new Float32Array(alpha.length);
  const searchRadius = Math.ceil(maxDist);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = y * width + x;

      // Find distance to nearest edge
      let minDist = maxDist + 1;
      for (let dy = -searchRadius; dy <= searchRadius; dy++) {
        for (let dx = -searchRadius; dx <= searchRadius; dx++) {
          const nx = x + dx;
          const ny = y + dy;
          if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;

          const nidx = ny * width + nx;
          if (edges[nidx] > 0) {
            const dist = Math.sqrt(dx * dx + dy * dy);
            minDist = Math.min(minDist, dist);
          }
        }
      }

      // Sign based on whether inside or outside
      const sign = alpha[idx] > 0.5 ? -1 : 1;
      result[idx] = sign * minDist;
    }
  }

  return result;
}

// ════════════════════════════════════════════════════════════════════════════
// Utility Functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Extract alpha channel from ImageData as Float32Array
 */
export function extractAlpha(imageData: ImageData): Float32Array {
  const alpha = new Float32Array(imageData.width * imageData.height);
  const data = imageData.data;

  for (let i = 0; i < alpha.length; i++) {
    alpha[i] = data[i * 4 + 3] / 255;
  }

  return alpha;
}

/**
 * Apply alpha channel to ImageData
 */
export function applyAlpha(
  imageData: ImageData,
  alpha: Float32Array,
): ImageData {
  const result = new ImageData(
    new Uint8ClampedArray(imageData.data),
    imageData.width,
    imageData.height,
  );

  for (let i = 0; i < alpha.length; i++) {
    result.data[i * 4 + 3] = Math.round(alpha[i] * 255);
  }

  return result;
}

/**
 * Analyze edge quality of an alpha channel
 *
 * Returns metrics about edge sharpness, suggesting appropriate feathering
 */
export function analyzeEdgeQuality(
  alpha: Float32Array,
  width: number,
  height: number,
): {
  averageEdgeWidth: number;
  edgeSharpness: number; // 0 (soft) to 1 (hard)
  suggestedFeather: number; // Recommended feather amount
  edgePixelRatio: number; // Ratio of edge to solid pixels
} {
  let edgePixels = 0;
  let totalEdgeWidth = 0;
  let sharpEdges = 0;
  let softEdges = 0;
  let totalPixels = 0;

  for (let y = 1; y < height - 1; y++) {
    for (let x = 1; x < width - 1; x++) {
      const idx = y * width + x;
      const a = alpha[idx];

      if (a > 0.01 && a < 0.99) {
        edgePixels++;

        // Check gradient magnitude
        const dx = alpha[idx + 1] - alpha[idx - 1];
        const dy = alpha[idx + width] - alpha[idx - width];
        const gradient = Math.sqrt(dx * dx + dy * dy);

        if (gradient > 0.5) {
          sharpEdges++;
        } else {
          softEdges++;
        }

        totalEdgeWidth += 1 / (gradient + 0.01);
      }

      if (a > 0.5) {
        totalPixels++;
      }
    }
  }

  const edgeCount = sharpEdges + softEdges || 1;
  const edgeSharpness = sharpEdges / edgeCount;
  const averageEdgeWidth = edgePixels > 0 ? totalEdgeWidth / edgePixels : 1;
  const edgePixelRatio = edgePixels / (totalPixels || 1);

  // Suggest feather based on current edge quality
  // Sharp edges may need more feathering, soft edges less
  const suggestedFeather =
    edgeSharpness > 0.7 ? 2 : edgeSharpness > 0.4 ? 1 : 0;

  return {
    averageEdgeWidth,
    edgeSharpness,
    suggestedFeather,
    edgePixelRatio,
  };
}

/**
 * Create default choker params
 */
export function createDefaultChokerParams(): ChokerParams {
  return {
    amount: 0,
    softness: 0,
    iterations: 1,
  };
}

/**
 * Create default spill suppressor params for green screen
 */
export function createGreenScreenSpillParams(): SpillSuppressorParams {
  return {
    spillColor: { r: 0, g: 255, b: 0 },
    tolerance: 0.3,
    desaturate: 0.7,
    replaceColor: undefined,
    edgesOnly: true,
  };
}

/**
 * Create default spill suppressor params for blue screen
 */
export function createBlueScreenSpillParams(): SpillSuppressorParams {
  return {
    spillColor: { r: 0, g: 0, b: 255 },
    tolerance: 0.3,
    desaturate: 0.7,
    replaceColor: undefined,
    edgesOnly: true,
  };
}
