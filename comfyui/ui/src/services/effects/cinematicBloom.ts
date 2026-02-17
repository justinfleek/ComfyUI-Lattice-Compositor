/**
 * Cinematic Bloom Effect Renderer
 *
 * Professional-grade bloom/glow effect with physically-based features:
 * - Inverse-square light falloff for realistic glow spread
 * - Multiple tonemapping algorithms (ACES, Reinhard, Hable)
 * - Per-channel RGB radius multipliers
 * - Chromatic aberration
 * - Procedural and texture-based lens dirt
 * - Multiple blend modes (add, screen, overlay, soft_light)
 *
 * Based on cinematic post-processing techniques used in film and games.
 */

import {
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams,
  registerEffectRenderer,
} from "../effectProcessor";
import { isFiniteNumber } from "@/utils/typeGuards";

// ============================================================================
// TYPES
// ============================================================================

export type TonemapOperator = "none" | "aces" | "reinhard" | "hable";
export type BloomBlendMode = "add" | "screen" | "overlay" | "soft_light";

export interface CinematicBloomParams {
  // Core glow
  intensity: number; // 0-10 (default 1.0)
  threshold: number; // 0-1 (default 0.8)
  radius: number; // 0-200 pixels (default 50)

  // Inverse-square falloff
  falloffMode: "gaussian" | "inverse_square" | "exponential";
  falloffExponent: number; // For exponential mode (default 2.0)

  // Per-channel radius multipliers (for color fringing)
  radiusR: number; // 0-2 (default 1.0)
  radiusG: number; // 0-2 (default 1.0)
  radiusB: number; // 0-2 (default 1.0)

  // Tonemapping
  tonemap: TonemapOperator;
  exposure: number; // -5 to 5 (default 0)

  // Chromatic aberration
  chromaticAberration: number; // 0-20 pixels (default 0)

  // Lens dirt
  lensDirtEnabled: boolean;
  lensDirtIntensity: number; // 0-1 (default 0.5)
  lensDirtScale: number; // 0.5-2 (default 1)
  lensDirtTexture?: string; // Optional texture data URL

  // Blending
  blendMode: BloomBlendMode;
}

// ============================================================================
// TONEMAPPING OPERATORS
// ============================================================================

/**
 * ACES Filmic Tonemapping (Academy Color Encoding System)
 * Industry standard for cinematic color grading
 */
export function tonemapACES(x: number): number {
  const a = 2.51;
  const b = 0.03;
  const c = 2.43;
  const d = 0.59;
  const e = 0.14;
  return Math.max(0, Math.min(1, (x * (a * x + b)) / (x * (c * x + d) + e)));
}

/**
 * Reinhard Tonemapping
 * Simple and effective, preserves highlights
 */
export function tonemapReinhard(x: number, whitePoint: number = 4.0): number {
  const numerator = x * (1 + x / (whitePoint * whitePoint));
  return numerator / (1 + x);
}

/**
 * Hable/Uncharted 2 Tonemapping
 * Popular in games, good highlight rolloff
 */
export function tonemapHable(x: number): number {
  const A = 0.15; // Shoulder Strength
  const B = 0.5; // Linear Strength
  const C = 0.1; // Linear Angle
  const D = 0.2; // Toe Strength
  const E = 0.02; // Toe Numerator
  const F = 0.3; // Toe Denominator

  return (x * (A * x + C * B) + D * E) / (x * (A * x + B) + D * F) - E / F;
}

/**
 * Apply tonemapping to an RGB value (0-1 range input, 0-1 range output)
 */
function applyTonemap(
  r: number,
  g: number,
  b: number,
  operator: TonemapOperator,
): [number, number, number] {
  switch (operator) {
    case "aces":
      return [tonemapACES(r), tonemapACES(g), tonemapACES(b)];
    case "reinhard":
      return [tonemapReinhard(r), tonemapReinhard(g), tonemapReinhard(b)];
    case "hable": {
      const W = 11.2; // White point
      const whiteScale = 1.0 / tonemapHable(W);
      return [
        tonemapHable(r) * whiteScale,
        tonemapHable(g) * whiteScale,
        tonemapHable(b) * whiteScale,
      ];
    }
    default:
      return [Math.min(1, r), Math.min(1, g), Math.min(1, b)];
  }
}

// ============================================================================
// INVERSE-SQUARE FALLOFF BLUR
// ============================================================================

/**
 * Generate kernel weights with inverse-square falloff
 * This is the key differentiator from standard Gaussian blur
 *
 * Standard Gaussian: weight = exp(-x²/2σ²)
 * Inverse-square: weight = 1 / (1 + x²/σ²)
 *
 * Inverse-square creates a longer tail, more like physical light spread
 */
export function generateInverseSquareKernel(radius: number): Float32Array {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3; // Controls falloff rate

  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = i - center;
    // Inverse-square falloff: 1 / (1 + (x/σ)²)
    const weight = 1.0 / (1.0 + (x * x) / (sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }

  // Normalize
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }

  return kernel;
}

/**
 * Generate kernel with exponential falloff
 * weight = exp(-|x|^exponent / σ)
 */
function generateExponentialKernel(
  radius: number,
  exponent: number,
): Float32Array {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3;

  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = Math.abs(i - center);
    const weight = Math.exp(-(x ** exponent) / (sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }

  // Normalize
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }

  return kernel;
}

/**
 * Generate standard Gaussian kernel
 */
export function generateGaussianKernel(radius: number): Float32Array {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3;

  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = i - center;
    const weight = Math.exp(-(x * x) / (2 * sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }

  // Normalize
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }

  return kernel;
}

/**
 * Apply separable 1D blur pass (horizontal or vertical)
 */
function applyBlur1D(
  src: Float32Array,
  dst: Float32Array,
  width: number,
  height: number,
  kernel: Float32Array,
  horizontal: boolean,
  channel: number, // 0=R, 1=G, 2=B, 3=A
): void {
  const kernelSize = kernel.length;
  const kernelHalf = Math.floor(kernelSize / 2);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let sum = 0;

      for (let k = 0; k < kernelSize; k++) {
        const offset = k - kernelHalf;
        let sx: number, sy: number;

        if (horizontal) {
          sx = Math.max(0, Math.min(width - 1, x + offset));
          sy = y;
        } else {
          sx = x;
          sy = Math.max(0, Math.min(height - 1, y + offset));
        }

        const idx = (sy * width + sx) * 4 + channel;
        sum += src[idx] * kernel[k];
      }

      dst[(y * width + x) * 4 + channel] = sum;
    }
  }
}

/**
 * Multi-pass separable blur with per-channel radius support
 */
function applyBloomBlur(
  imageData: Float32Array,
  width: number,
  height: number,
  radiusR: number,
  radiusG: number,
  radiusB: number,
  falloffMode: "gaussian" | "inverse_square" | "exponential",
  falloffExponent: number,
): Float32Array {
  const result = new Float32Array(imageData.length);
  const temp = new Float32Array(imageData.length);

  // Copy input
  result.set(imageData);

  // Process each channel with its own radius
  const radii = [radiusR, radiusG, radiusB];

  for (let channel = 0; channel < 3; channel++) {
    const radius = radii[channel];
    if (radius <= 0) continue;

    // Generate kernel based on falloff mode
    let kernel: Float32Array;
    switch (falloffMode) {
      case "inverse_square":
        kernel = generateInverseSquareKernel(radius);
        break;
      case "exponential":
        kernel = generateExponentialKernel(radius, falloffExponent);
        break;
      default:
        kernel = generateGaussianKernel(radius);
        break;
    }

    // Horizontal pass
    applyBlur1D(result, temp, width, height, kernel, true, channel);
    // Vertical pass
    applyBlur1D(temp, result, width, height, kernel, false, channel);
  }

  // Copy alpha unchanged
  for (let i = 3; i < imageData.length; i += 4) {
    result[i] = imageData[i];
  }

  return result;
}

// ============================================================================
// THRESHOLD EXTRACTION
// ============================================================================

/**
 * Extract bright areas above threshold into floating-point buffer
 * Returns values in linear space (0-unbounded)
 */
function extractBrightAreas(
  imageData: ImageData,
  threshold: number,
  exposure: number,
): Float32Array {
  const { data, width, height } = imageData;
  const result = new Float32Array(width * height * 4);

  const exposureMult = 2 ** exposure;

  for (let i = 0; i < data.length; i += 4) {
    // Convert to linear space (approximate gamma 2.2)
    const r = (data[i] / 255) ** 2.2 * exposureMult;
    const g = (data[i + 1] / 255) ** 2.2 * exposureMult;
    const b = (data[i + 2] / 255) ** 2.2 * exposureMult;
    const a = data[i + 3] / 255;

    // Calculate luminance
    const luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b;

    // Soft knee threshold (smoother transition)
    const knee = 0.1;
    const soft = luminance - threshold + knee;
    const contribution = Math.max(0, (soft * soft) / (4 * knee));
    const factor =
      luminance > threshold
        ? 1
        : threshold - knee < luminance
          ? contribution / luminance
          : 0;

    result[i] = r * factor;
    result[i + 1] = g * factor;
    result[i + 2] = b * factor;
    result[i + 3] = a;
  }

  return result;
}

// ============================================================================
// CHROMATIC ABERRATION
// ============================================================================

/**
 * Apply chromatic aberration by offsetting color channels radially
 */
export function applyChromaticAberration(
  imageData: ImageData,
  amount: number,
): ImageData {
  if (amount <= 0) return imageData;

  const { width, height, data } = imageData;
  const result = new ImageData(width, height);
  const dst = result.data;

  const centerX = width / 2;
  const centerY = height / 2;
  const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;

      // Direction from center
      const dx = x - centerX;
      const dy = y - centerY;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const normalizedDist = dist / maxDist;

      // Offset increases with distance from center
      const offset = amount * normalizedDist;

      // Red channel - offset outward
      const rxR = Math.round(x + (dx * offset) / dist);
      const ryR = Math.round(y + (dy * offset) / dist);
      // Blue channel - offset inward
      const rxB = Math.round(x - (dx * offset) / dist);
      const ryB = Math.round(y - (dy * offset) / dist);

      // Clamp coordinates
      const clampX = (v: number) => Math.max(0, Math.min(width - 1, v));
      const clampY = (v: number) => Math.max(0, Math.min(height - 1, v));

      // Sample each channel from different positions
      const idxR = (clampY(ryR) * width + clampX(rxR)) * 4;
      const idxB = (clampY(ryB) * width + clampX(rxB)) * 4;

      dst[idx] = data[idxR]; // Red from outer
      dst[idx + 1] = data[idx + 1]; // Green stays centered
      dst[idx + 2] = data[idxB + 2]; // Blue from inner
      dst[idx + 3] = data[idx + 3]; // Alpha unchanged
    }
  }

  return result;
}

// ============================================================================
// LENS DIRT
// ============================================================================

/**
 * Generate procedural lens dirt texture
 * Creates scattered bright spots and smudges
 */
export function generateLensDirt(
  width: number,
  height: number,
  scale: number,
  seed: number = 12345,
): Float32Array {
  const result = new Float32Array(width * height);

  // Simple seeded random
  let state = seed;
  const random = () => {
    state = (state * 1103515245 + 12345) & 0x7fffffff;
    return state / 0x7fffffff;
  };

  // Fill with base noise
  for (let i = 0; i < result.length; i++) {
    result[i] = random() * 0.1;
  }

  // Add bright spots (dust particles)
  const numSpots = Math.floor(50 * scale);
  for (let i = 0; i < numSpots; i++) {
    const cx = random() * width;
    const cy = random() * height;
    const r = (5 + random() * 20) * scale;
    const brightness = 0.3 + random() * 0.7;

    const minX = Math.max(0, Math.floor(cx - r));
    const maxX = Math.min(width - 1, Math.ceil(cx + r));
    const minY = Math.max(0, Math.floor(cy - r));
    const maxY = Math.min(height - 1, Math.ceil(cy + r));

    for (let y = minY; y <= maxY; y++) {
      for (let x = minX; x <= maxX; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < r) {
          const falloff = 1 - dist / r;
          const idx = y * width + x;
          result[idx] = Math.max(result[idx], falloff * falloff * brightness);
        }
      }
    }
  }

  // Add smudges (larger, dimmer areas)
  const numSmudges = Math.floor(10 * scale);
  for (let i = 0; i < numSmudges; i++) {
    const cx = random() * width;
    const cy = random() * height;
    const rx = (30 + random() * 60) * scale;
    const ry = (20 + random() * 40) * scale;
    const brightness = 0.15 + random() * 0.25;
    const angle = random() * Math.PI;
    const cosA = Math.cos(angle);
    const sinA = Math.sin(angle);

    const maxR = Math.max(rx, ry);
    const minX = Math.max(0, Math.floor(cx - maxR));
    const maxX = Math.min(width - 1, Math.ceil(cx + maxR));
    const minY = Math.max(0, Math.floor(cy - maxR));
    const maxY = Math.min(height - 1, Math.ceil(cy + maxR));

    for (let y = minY; y <= maxY; y++) {
      for (let x = minX; x <= maxX; x++) {
        const dx = x - cx;
        const dy = y - cy;
        // Rotate
        const rx2 = dx * cosA + dy * sinA;
        const ry2 = -dx * sinA + dy * cosA;
        // Ellipse distance
        const dist = Math.sqrt(
          (rx2 * rx2) / (rx * rx) + (ry2 * ry2) / (ry * ry),
        );
        if (dist < 1) {
          const falloff = 1 - dist;
          const idx = y * width + x;
          result[idx] = Math.max(result[idx], falloff * falloff * brightness);
        }
      }
    }
  }

  return result;
}

/**
 * Apply lens dirt to bloom
 */
function applyLensDirt(
  bloom: Float32Array,
  dirt: Float32Array,
  width: number,
  height: number,
  intensity: number,
): void {
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dirtIdx = y * width + x;
      const bloomIdx = dirtIdx * 4;
      const dirtValue = dirt[dirtIdx] * intensity;

      bloom[bloomIdx] *= 1 + dirtValue;
      bloom[bloomIdx + 1] *= 1 + dirtValue;
      bloom[bloomIdx + 2] *= 1 + dirtValue;
    }
  }
}

// ============================================================================
// BLEND MODES
// ============================================================================

/**
 * Screen blend: 1 - (1 - a) * (1 - b)
 */
function blendScreen(base: number, blend: number): number {
  return 1 - (1 - base) * (1 - blend);
}

/**
 * Overlay blend: combines multiply and screen
 */
function blendOverlay(base: number, blend: number): number {
  return base < 0.5 ? 2 * base * blend : 1 - 2 * (1 - base) * (1 - blend);
}

/**
 * Soft light blend: gentler than overlay
 */
function blendSoftLight(base: number, blend: number): number {
  if (blend <= 0.5) {
    return base - (1 - 2 * blend) * base * (1 - base);
  } else {
    const d =
      base <= 0.25 ? ((16 * base - 12) * base + 4) * base : Math.sqrt(base);
    return base + (2 * blend - 1) * (d - base);
  }
}

/**
 * Blend bloom with original image
 */
function blendBloom(
  original: ImageData,
  bloom: Float32Array,
  intensity: number,
  mode: BloomBlendMode,
  tonemap: TonemapOperator,
): ImageData {
  const { width, height, data } = original;
  const result = new ImageData(width, height);
  const dst = result.data;

  for (let i = 0; i < data.length; i += 4) {
    // Original in linear space
    const origR = (data[i] / 255) ** 2.2;
    const origG = (data[i + 1] / 255) ** 2.2;
    const origB = (data[i + 2] / 255) ** 2.2;

    // Bloom contribution (already in linear space)
    const bloomR = bloom[i] * intensity;
    const bloomG = bloom[i + 1] * intensity;
    const bloomB = bloom[i + 2] * intensity;

    let finalR: number, finalG: number, finalB: number;

    switch (mode) {
      case "screen":
        finalR = blendScreen(origR, bloomR);
        finalG = blendScreen(origG, bloomG);
        finalB = blendScreen(origB, bloomB);
        break;
      case "overlay":
        finalR = blendOverlay(origR, bloomR);
        finalG = blendOverlay(origG, bloomG);
        finalB = blendOverlay(origB, bloomB);
        break;
      case "soft_light":
        finalR = blendSoftLight(origR, bloomR);
        finalG = blendSoftLight(origG, bloomG);
        finalB = blendSoftLight(origB, bloomB);
        break;
      default:
        finalR = origR + bloomR;
        finalG = origG + bloomG;
        finalB = origB + bloomB;
        break;
    }

    // Apply tonemapping
    [finalR, finalG, finalB] = applyTonemap(finalR, finalG, finalB, tonemap);

    // Convert back to sRGB
    dst[i] = Math.round(Math.max(0, Math.min(1, finalR)) ** (1 / 2.2) * 255);
    dst[i + 1] = Math.round(
      Math.max(0, Math.min(1, finalG)) ** (1 / 2.2) * 255,
    );
    dst[i + 2] = Math.round(
      Math.max(0, Math.min(1, finalB)) ** (1 / 2.2) * 255,
    );
    dst[i + 3] = data[i + 3];
  }

  return result;
}

// ============================================================================
// MAIN RENDERER
// ============================================================================

// Cache for lens dirt texture
let cachedLensDirt: Float32Array | null = null;
let cachedLensDirtWidth = 0;
let cachedLensDirtHeight = 0;
let cachedLensDirtScale = 0;

/**
 * Cinematic Bloom effect renderer
 *
 * Parameters:
 * - intensity: 0-10 (default 1.0) - Overall bloom strength
 * - threshold: 0-1 (default 0.8) - Brightness threshold for bloom
 * - radius: 0-200 (default 50) - Base blur radius
 * - falloff_mode: 'gaussian' | 'inverse_square' | 'exponential' (default 'inverse_square')
 * - falloff_exponent: 1-4 (default 2) - For exponential mode
 * - radius_r: 0-2 (default 1.0) - Red channel radius multiplier
 * - radius_g: 0-2 (default 1.0) - Green channel radius multiplier
 * - radius_b: 0-2 (default 1.0) - Blue channel radius multiplier
 * - tonemap: 'none' | 'aces' | 'reinhard' | 'hable' (default 'aces')
 * - exposure: -5 to 5 (default 0) - Exposure adjustment
 * - chromatic_aberration: 0-20 (default 0) - Chromatic aberration strength
 * - lens_dirt_enabled: boolean (default false)
 * - lens_dirt_intensity: 0-1 (default 0.5)
 * - lens_dirt_scale: 0.5-2 (default 1)
 * - blend_mode: 'add' | 'screen' | 'overlay' | 'soft_light' (default 'add')
 */
export function cinematicBloomRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Extract parameters with defaults
  // Type proof: intensity ∈ ℝ ∧ finite(intensity) → intensity ∈ [0, 10]
  const intensityValue = params.intensity;
  const intensity = isFiniteNumber(intensityValue)
    ? Math.max(0, Math.min(10, intensityValue))
    : 1.0;
  // Type proof: threshold ∈ ℝ ∧ finite(threshold) → threshold ∈ [0, 1]
  const thresholdValue = params.threshold;
  const threshold = isFiniteNumber(thresholdValue)
    ? Math.max(0, Math.min(1, thresholdValue))
    : 0.8;
  // Type proof: radius ∈ ℝ ∧ finite(radius) → radius ∈ [0, 200]
  const radiusValue = params.radius;
  const radius = isFiniteNumber(radiusValue)
    ? Math.max(0, Math.min(200, radiusValue))
    : 50;
  // Type proof: falloff_mode ∈ {"gaussian", "inverse_square", "exponential"} ∪ {undefined}
  const falloffModeValue = params.falloff_mode;
  const falloffMode = (typeof falloffModeValue === "string" ? falloffModeValue : "inverse_square") as
    | "gaussian"
    | "inverse_square"
    | "exponential";
  // Type proof: falloff_exponent ∈ ℝ ∧ finite(falloff_exponent) → falloff_exponent ∈ [1, 4]
  const falloffExponentValue = params.falloff_exponent;
  const falloffExponent = isFiniteNumber(falloffExponentValue)
    ? Math.max(1, Math.min(4, falloffExponentValue))
    : 2;
  // Type proof: radius_r ∈ ℝ ∧ finite(radius_r) → radius_r ∈ [0, 2]
  const radiusRValue = params.radius_r;
  const radiusR = (isFiniteNumber(radiusRValue)
    ? Math.max(0, Math.min(2, radiusRValue))
    : 1.0) * radius;
  // Type proof: radius_g ∈ ℝ ∧ finite(radius_g) → radius_g ∈ [0, 2]
  const radiusGValue = params.radius_g;
  const radiusG = (isFiniteNumber(radiusGValue)
    ? Math.max(0, Math.min(2, radiusGValue))
    : 1.0) * radius;
  // Type proof: radius_b ∈ ℝ ∧ finite(radius_b) → radius_b ∈ [0, 2]
  const radiusBValue = params.radius_b;
  const radiusB = (isFiniteNumber(radiusBValue)
    ? Math.max(0, Math.min(2, radiusBValue))
    : 1.0) * radius;
  // Type proof: tonemap ∈ {"none", "aces", "reinhard", "hable"} ∪ {undefined}
  const tonemapValue = params.tonemap;
  const tonemap = (typeof tonemapValue === "string" ? tonemapValue : "aces") as TonemapOperator;
  // Type proof: exposure ∈ ℝ ∧ finite(exposure) → exposure ∈ [-5, 5]
  const exposureValue = params.exposure;
  const exposure = isFiniteNumber(exposureValue)
    ? Math.max(-5, Math.min(5, exposureValue))
    : 0;
  // Type proof: chromatic_aberration ∈ ℝ ∧ finite(chromatic_aberration) → chromatic_aberration ∈ [0, 20]
  const chromaticAberrationValue = params.chromatic_aberration;
  const chromaticAberration = isFiniteNumber(chromaticAberrationValue)
    ? Math.max(0, Math.min(20, chromaticAberrationValue))
    : 0;
  // Type proof: lens_dirt_enabled ∈ {true, false}
  const lensDirtEnabled = typeof params.lens_dirt_enabled === "boolean" ? params.lens_dirt_enabled : false;
  // Type proof: lens_dirt_intensity ∈ ℝ ∧ finite(lens_dirt_intensity) → lens_dirt_intensity ∈ [0, 1]
  const lensDirtIntensityValue = params.lens_dirt_intensity;
  const lensDirtIntensity = isFiniteNumber(lensDirtIntensityValue)
    ? Math.max(0, Math.min(1, lensDirtIntensityValue))
    : 0.5;
  // Type proof: lens_dirt_scale ∈ ℝ ∧ finite(lens_dirt_scale) → lens_dirt_scale ∈ [0.5, 2]
  const lensDirtScaleValue = params.lens_dirt_scale;
  const lensDirtScale = isFiniteNumber(lensDirtScaleValue)
    ? Math.max(0.5, Math.min(2, lensDirtScaleValue))
    : 1;
  // Type proof: blend_mode ∈ {"add", "screen", "overlay", "soft_light"} ∪ {undefined}
  const blendModeValue = params.blend_mode;
  const blendMode = (typeof blendModeValue === "string" ? blendModeValue : "add") as BloomBlendMode;

  // Skip if intensity is zero
  if (intensity <= 0 || radius <= 0) {
    return input;
  }

  const { width, height } = input.canvas;

  // Get original image data
  // Use _sourceCanvas if provided (for additive stacking), otherwise use input
  // This ensures stacked blooms extract from original layer, not from previous bloom output
  const sourceCanvas = params._sourceCanvas as HTMLCanvasElement | undefined;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const sourceCtx = (sourceCanvas != null && typeof sourceCanvas === "object" && typeof sourceCanvas.getContext === "function") ? sourceCanvas.getContext("2d") : undefined;
  let originalData = sourceCtx
    ? sourceCtx.getImageData(0, 0, width, height)
    : input.ctx.getImageData(0, 0, width, height);

  // Apply chromatic aberration to original if enabled
  if (chromaticAberration > 0) {
    originalData = applyChromaticAberration(originalData, chromaticAberration);
  }

  // Extract bright areas into floating-point buffer
  const brightAreas = extractBrightAreas(originalData, threshold, exposure);

  // Apply bloom blur with per-channel radii and inverse-square falloff
  const blurred = applyBloomBlur(
    brightAreas,
    width,
    height,
    radiusR,
    radiusG,
    radiusB,
    falloffMode,
    falloffExponent,
  );

  // Apply lens dirt if enabled
  if (lensDirtEnabled) {
    // Generate or use cached lens dirt
    if (
      !cachedLensDirt ||
      cachedLensDirtWidth !== width ||
      cachedLensDirtHeight !== height ||
      cachedLensDirtScale !== lensDirtScale
    ) {
      cachedLensDirt = generateLensDirt(width, height, lensDirtScale);
      cachedLensDirtWidth = width;
      cachedLensDirtHeight = height;
      cachedLensDirtScale = lensDirtScale;
    }
    applyLensDirt(blurred, cachedLensDirt, width, height, lensDirtIntensity);
  }

  // Blend bloom with original
  const result = blendBloom(
    originalData,
    blurred,
    intensity,
    blendMode,
    tonemap,
  );

  // Output
  const output = createMatchingCanvas(input.canvas);
  output.ctx.putImageData(result, 0, 0);

  return output;
}

// ============================================================================
// SIMPLE GLOW VARIANT
// ============================================================================

/**
 * Simple glow effect - lighter weight version
 * Uses basic parameters for quick glow effects
 *
 * Parameters:
 * - glow_threshold: 0-100 (default 50) - Luminance threshold %
 * - glow_radius: 0-200 (default 25) - Blur radius
 * - glow_intensity: 0-500 (default 100) - Glow strength %
 */
export function glowRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Type proof: glow_threshold ∈ ℝ ∧ finite(glow_threshold) → glow_threshold ∈ [0, 100]
  const thresholdValue = params.glow_threshold;
  const thresholdRaw = isFiniteNumber(thresholdValue)
    ? Math.max(0, Math.min(100, thresholdValue))
    : 50;
  const threshold = thresholdRaw / 100;
  // Type proof: glow_radius ∈ ℝ ∧ finite(glow_radius) → glow_radius ∈ ℝ₊
  const radiusValue = params.glow_radius;
  const radius = isFiniteNumber(radiusValue) && radiusValue >= 0 ? radiusValue : 25;
  // Type proof: glow_intensity ∈ ℝ ∧ finite(glow_intensity) → glow_intensity ∈ ℝ₊
  const intensityValue = params.glow_intensity;
  const intensityRaw = isFiniteNumber(intensityValue) && intensityValue >= 0 ? intensityValue : 100;
  const intensity = intensityRaw / 100;

  if (intensity <= 0 || radius <= 0) {
    return input;
  }

  // Use cinematic bloom with simplified settings
  // Pass through _sourceCanvas for additive stacking support
  return cinematicBloomRenderer(input, {
    intensity,
    threshold,
    radius,
    falloff_mode: "gaussian",
    falloff_exponent: 2,
    radius_r: 1,
    radius_g: 1,
    radius_b: 1,
    tonemap: "none",
    exposure: 0,
    chromatic_aberration: 0,
    lens_dirt_enabled: false,
    lens_dirt_intensity: 0,
    lens_dirt_scale: 1,
    blend_mode: "add",
    _sourceCanvas: params._sourceCanvas,
  });
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register cinematic bloom effect renderers
 */
export function registerCinematicBloomEffects(): void {
  registerEffectRenderer("cinematic-bloom", cinematicBloomRenderer);
  registerEffectRenderer("glow", glowRenderer);
}

export default {
  cinematicBloomRenderer,
  glowRenderer,
  registerCinematicBloomEffects,
  // Export utilities for advanced use
  tonemapACES,
  tonemapReinhard,
  tonemapHable,
  generateInverseSquareKernel,
  generateGaussianKernel,
  generateLensDirt,
  applyChromaticAberration,
};
