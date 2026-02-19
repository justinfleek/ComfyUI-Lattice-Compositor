/**
 * Color & Depth Reactivity Service
 *
 * Provides pixel-based reactive values from layers. Inspired by
 * RyanOnTheInside's ComfyUI nodes for color/depth-driven animations.
 *
 * Features:
 * - Sample color at position (point, area average)
 * - Extract brightness, hue, saturation
 * - Depth map sampling for z-based reactivity
 * - Region-based color analysis
 * - Motion detection (frame differencing)
 *
 * All values are deterministic and frame-based for scrub-safe playback.
 *
 * @module services/colorDepthReactivity
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ════════════════════════════════════════════════════════════════════════════

export interface ColorSample {
  r: number; // 0-1
  g: number; // 0-1
  b: number; // 0-1
  a: number; // 0-1
  brightness: number; // 0-1 (luminance)
  hue: number; // 0-1 (0 = red, 0.33 = green, 0.67 = blue)
  saturation: number; // 0-1
  value: number; // 0-1 (HSV value)
}

export interface DepthSample {
  depth: number; // 0-1 (0 = near, 1 = far)
  normalized: number; // 0-1 after range mapping
  gradient: number; // Depth gradient magnitude
}

export type SampleMode =
  | "point" // Single pixel
  | "average" // Area average
  | "max" // Maximum in area
  | "min" // Minimum in area
  | "dominant"; // Dominant color (k-means)

export type ColorFeature =
  | "brightness"
  | "hue"
  | "saturation"
  | "value"
  | "red"
  | "green"
  | "blue"
  | "alpha";

export interface ColorReactivityConfig {
  id: string;
  enabled: boolean;

  // Source
  sourceLayerId: string;
  sampleMode: SampleMode;

  // Sample position (normalized 0-1)
  position: { x: number; y: number };
  sampleRadius: number; // For area modes (pixels)

  // Feature extraction
  feature: ColorFeature;

  // Target property
  targetLayerId: string;
  targetPropertyPath: string;

  // Value mapping
  sensitivity: number;
  smoothing: number;
  min: number;
  max: number;
  invert: boolean;
}

export interface DepthReactivityConfig {
  id: string;
  enabled: boolean;

  // Source depth map layer
  sourceLayerId: string;

  // Sample position (normalized 0-1)
  position: { x: number; y: number };
  sampleRadius: number;

  // Depth range mapping
  nearPlane: number; // Depth value considered "near"
  farPlane: number; // Depth value considered "far"

  // Target property
  targetLayerId: string;
  targetPropertyPath: string;

  // Value mapping
  sensitivity: number;
  smoothing: number;
  min: number;
  max: number;
  invert: boolean;
}

export interface MotionDetectionConfig {
  id: string;
  enabled: boolean;

  // Source layer
  sourceLayerId: string;

  // Detection region (normalized 0-1)
  region: { x: number; y: number; width: number; height: number };

  // Threshold for motion detection
  threshold: number; // 0-1

  // Target property
  targetLayerId: string;
  targetPropertyPath: string;

  // Value mapping
  sensitivity: number;
  smoothing: number;
  min: number;
  max: number;
}

// ════════════════════════════════════════════════════════════════════════════
// Color Conversion Utilities
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert RGB to HSV
 */
export function rgbToHsv(
  r: number,
  g: number,
  b: number,
): { h: number; s: number; v: number } {
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const d = max - min;

  let h = 0;
  const s = max === 0 ? 0 : d / max;
  const v = max;

  if (max !== min) {
    switch (max) {
      case r:
        h = (g - b) / d + (g < b ? 6 : 0);
        break;
      case g:
        h = (b - r) / d + 2;
        break;
      case b:
        h = (r - g) / d + 4;
        break;
    }
    h /= 6;
  }

  return { h, s, v };
}

/**
 * Calculate brightness (ITU-R BT.709 luminance)
 */
export function calculateBrightness(r: number, g: number, b: number): number {
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}

/**
 * Create color sample from RGBA values
 */
export function createColorSample(
  r: number,
  g: number,
  b: number,
  a: number,
): ColorSample {
  const hsv = rgbToHsv(r, g, b);
  return {
    r,
    g,
    b,
    a,
    brightness: calculateBrightness(r, g, b),
    hue: hsv.h,
    saturation: hsv.s,
    value: hsv.v,
  };
}

// ════════════════════════════════════════════════════════════════════════════
// Pixel Sampling
// ════════════════════════════════════════════════════════════════════════════

/**
 * Sample a single pixel from ImageData
 */
export function samplePixel(
  imageData: ImageData,
  x: number,
  y: number,
): ColorSample {
  const px = Math.floor(x);
  const py = Math.floor(y);

  // Clamp to bounds
  const cx = Math.max(0, Math.min(imageData.width - 1, px));
  const cy = Math.max(0, Math.min(imageData.height - 1, py));

  const idx = (cy * imageData.width + cx) * 4;
  const r = imageData.data[idx] / 255;
  const g = imageData.data[idx + 1] / 255;
  const b = imageData.data[idx + 2] / 255;
  const a = imageData.data[idx + 3] / 255;

  return createColorSample(r, g, b, a);
}

/**
 * Sample area average from ImageData
 */
export function sampleAreaAverage(
  imageData: ImageData,
  centerX: number,
  centerY: number,
  radius: number,
): ColorSample {
  let totalR = 0,
    totalG = 0,
    totalB = 0,
    totalA = 0;
  let count = 0;

  const startX = Math.max(0, Math.floor(centerX - radius));
  const endX = Math.min(imageData.width - 1, Math.ceil(centerX + radius));
  const startY = Math.max(0, Math.floor(centerY - radius));
  const endY = Math.min(imageData.height - 1, Math.ceil(centerY + radius));

  for (let y = startY; y <= endY; y++) {
    for (let x = startX; x <= endX; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      if (dx * dx + dy * dy <= radius * radius) {
        const idx = (y * imageData.width + x) * 4;
        totalR += imageData.data[idx];
        totalG += imageData.data[idx + 1];
        totalB += imageData.data[idx + 2];
        totalA += imageData.data[idx + 3];
        count++;
      }
    }
  }

  if (count === 0) {
    return createColorSample(0, 0, 0, 0);
  }

  return createColorSample(
    totalR / count / 255,
    totalG / count / 255,
    totalB / count / 255,
    totalA / count / 255,
  );
}

/**
 * Sample maximum brightness in area
 */
export function sampleAreaMax(
  imageData: ImageData,
  centerX: number,
  centerY: number,
  radius: number,
  feature: ColorFeature = "brightness",
): ColorSample {
  let maxValue = -Infinity;
  let maxSample: ColorSample | null = null;

  const startX = Math.max(0, Math.floor(centerX - radius));
  const endX = Math.min(imageData.width - 1, Math.ceil(centerX + radius));
  const startY = Math.max(0, Math.floor(centerY - radius));
  const endY = Math.min(imageData.height - 1, Math.ceil(centerY + radius));

  for (let y = startY; y <= endY; y++) {
    for (let x = startX; x <= endX; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      if (dx * dx + dy * dy <= radius * radius) {
        const sample = samplePixel(imageData, x, y);
        const value = getFeatureValue(sample, feature);
        if (value > maxValue) {
          maxValue = value;
          maxSample = sample;
        }
      }
    }
  }

  return maxSample || createColorSample(0, 0, 0, 0);
}

/**
 * Sample minimum brightness in area
 */
export function sampleAreaMin(
  imageData: ImageData,
  centerX: number,
  centerY: number,
  radius: number,
  feature: ColorFeature = "brightness",
): ColorSample {
  let minValue = Infinity;
  let minSample: ColorSample | null = null;

  const startX = Math.max(0, Math.floor(centerX - radius));
  const endX = Math.min(imageData.width - 1, Math.ceil(centerX + radius));
  const startY = Math.max(0, Math.floor(centerY - radius));
  const endY = Math.min(imageData.height - 1, Math.ceil(centerY + radius));

  for (let y = startY; y <= endY; y++) {
    for (let x = startX; x <= endX; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      if (dx * dx + dy * dy <= radius * radius) {
        const sample = samplePixel(imageData, x, y);
        const value = getFeatureValue(sample, feature);
        if (value < minValue) {
          minValue = value;
          minSample = sample;
        }
      }
    }
  }

  return minSample || createColorSample(0, 0, 0, 0);
}

/**
 * Get specific feature value from color sample
 */
export function getFeatureValue(
  sample: ColorSample,
  feature: ColorFeature,
): number {
  switch (feature) {
    case "brightness":
      return sample.brightness;
    case "hue":
      return sample.hue;
    case "saturation":
      return sample.saturation;
    case "value":
      return sample.value;
    case "red":
      return sample.r;
    case "green":
      return sample.g;
    case "blue":
      return sample.b;
    case "alpha":
      return sample.a;
    default:
      return sample.brightness;
  }
}

// ════════════════════════════════════════════════════════════════════════════
// Color Reactivity
// ════════════════════════════════════════════════════════════════════════════

/**
 * Sample color from image data based on config
 */
export function sampleColorFromImageData(
  imageData: ImageData,
  config: {
    position: { x: number; y: number };
    sampleMode: SampleMode;
    sampleRadius: number;
    feature: ColorFeature;
  },
): number {
  // Convert normalized position to pixel coordinates
  const px = config.position.x * imageData.width;
  const py = config.position.y * imageData.height;

  let sample: ColorSample;

  switch (config.sampleMode) {
    case "point":
      sample = samplePixel(imageData, px, py);
      break;
    case "average":
      sample = sampleAreaAverage(imageData, px, py, config.sampleRadius);
      break;
    case "max":
      sample = sampleAreaMax(
        imageData,
        px,
        py,
        config.sampleRadius,
        config.feature,
      );
      break;
    case "min":
      sample = sampleAreaMin(
        imageData,
        px,
        py,
        config.sampleRadius,
        config.feature,
      );
      break;
    case "dominant":
      // For dominant, fall back to average (k-means would be expensive)
      sample = sampleAreaAverage(imageData, px, py, config.sampleRadius);
      break;
    default:
      sample = samplePixel(imageData, px, py);
  }

  return getFeatureValue(sample, config.feature);
}

/**
 * Get mapped color reactivity value
 */
export function getMappedColorValue(
  imageData: ImageData,
  config: ColorReactivityConfig,
  previousValue?: number,
): number {
  if (!config.enabled) return config.min;

  // Get raw feature value
  let rawValue = sampleColorFromImageData(imageData, {
    position: config.position,
    sampleMode: config.sampleMode,
    sampleRadius: config.sampleRadius,
    feature: config.feature,
  });

  // Apply sensitivity
  rawValue *= config.sensitivity;

  // Clamp to 0-1
  rawValue = Math.max(0, Math.min(1, rawValue));

  // Invert if needed
  if (config.invert) {
    rawValue = 1 - rawValue;
  }

  // Map to output range
  let outputValue = config.min + rawValue * (config.max - config.min);

  // Apply smoothing
  if (previousValue !== undefined && config.smoothing > 0) {
    outputValue =
      previousValue * config.smoothing + outputValue * (1 - config.smoothing);
  }

  return outputValue;
}

// ════════════════════════════════════════════════════════════════════════════
// Depth Reactivity
// ════════════════════════════════════════════════════════════════════════════

/**
 * Sample depth value from grayscale depth map
 */
export function sampleDepth(
  imageData: ImageData,
  x: number,
  y: number,
): number {
  const sample = samplePixel(imageData, x, y);
  // Depth maps are typically grayscale, use brightness
  return sample.brightness;
}

/**
 * Sample depth with gradient information
 */
export function sampleDepthWithGradient(
  imageData: ImageData,
  x: number,
  y: number,
): DepthSample {
  const depth = sampleDepth(imageData, x, y);

  // Calculate gradient using Sobel-like approach
  const dx =
    sampleDepth(imageData, x + 1, y) - sampleDepth(imageData, x - 1, y);
  const dy =
    sampleDepth(imageData, x, y + 1) - sampleDepth(imageData, x, y - 1);
  const gradient = Math.sqrt(dx * dx + dy * dy);

  return {
    depth,
    normalized: depth,
    gradient,
  };
}

/**
 * Get mapped depth reactivity value
 */
export function getMappedDepthValue(
  imageData: ImageData,
  config: DepthReactivityConfig,
  previousValue?: number,
): number {
  if (!config.enabled) return config.min;

  // Convert normalized position to pixel coordinates
  const px = config.position.x * imageData.width;
  const py = config.position.y * imageData.height;

  // Sample depth
  let depthValue: number;
  if (config.sampleRadius > 1) {
    // Average depth in area
    const sample = sampleAreaAverage(imageData, px, py, config.sampleRadius);
    depthValue = sample.brightness;
  } else {
    depthValue = sampleDepth(imageData, px, py);
  }

  // Map depth to near/far range
  const range = config.farPlane - config.nearPlane;
  let normalizedDepth =
    range > 0 ? (depthValue - config.nearPlane) / range : depthValue;
  normalizedDepth = Math.max(0, Math.min(1, normalizedDepth));

  // Apply sensitivity
  normalizedDepth *= config.sensitivity;
  normalizedDepth = Math.max(0, Math.min(1, normalizedDepth));

  // Invert if needed
  if (config.invert) {
    normalizedDepth = 1 - normalizedDepth;
  }

  // Map to output range
  let outputValue = config.min + normalizedDepth * (config.max - config.min);

  // Apply smoothing
  if (previousValue !== undefined && config.smoothing > 0) {
    outputValue =
      previousValue * config.smoothing + outputValue * (1 - config.smoothing);
  }

  return outputValue;
}

// ════════════════════════════════════════════════════════════════════════════
// Motion Detection
// ════════════════════════════════════════════════════════════════════════════

/**
 * Calculate motion amount between two frames
 */
export function calculateMotion(
  currentFrame: ImageData,
  previousFrame: ImageData,
  region: { x: number; y: number; width: number; height: number },
  threshold: number = 0.1,
): number {
  if (
    currentFrame.width !== previousFrame.width ||
    currentFrame.height !== previousFrame.height
  ) {
    return 0;
  }

  const startX = Math.floor(region.x * currentFrame.width);
  const startY = Math.floor(region.y * currentFrame.height);
  const endX = Math.min(
    currentFrame.width,
    Math.ceil((region.x + region.width) * currentFrame.width),
  );
  const endY = Math.min(
    currentFrame.height,
    Math.ceil((region.y + region.height) * currentFrame.height),
  );

  let totalDiff = 0;
  let pixelCount = 0;

  for (let y = startY; y < endY; y++) {
    for (let x = startX; x < endX; x++) {
      const idx = (y * currentFrame.width + x) * 4;

      // Calculate per-pixel difference
      const dr =
        Math.abs(currentFrame.data[idx] - previousFrame.data[idx]) / 255;
      const dg =
        Math.abs(currentFrame.data[idx + 1] - previousFrame.data[idx + 1]) /
        255;
      const db =
        Math.abs(currentFrame.data[idx + 2] - previousFrame.data[idx + 2]) /
        255;

      const diff = (dr + dg + db) / 3;

      // Only count if above threshold
      if (diff > threshold) {
        totalDiff += diff;
      }
      pixelCount++;
    }
  }

  return pixelCount > 0 ? totalDiff / pixelCount : 0;
}

/**
 * Get mapped motion detection value
 */
export function getMappedMotionValue(
  currentFrame: ImageData,
  previousFrame: ImageData | null,
  config: MotionDetectionConfig,
  previousValue?: number,
): number {
  if (!config.enabled || !previousFrame) return config.min;

  // Calculate motion
  let motionValue = calculateMotion(
    currentFrame,
    previousFrame,
    config.region,
    config.threshold,
  );

  // Apply sensitivity
  motionValue *= config.sensitivity;
  motionValue = Math.max(0, Math.min(1, motionValue));

  // Map to output range
  let outputValue = config.min + motionValue * (config.max - config.min);

  // Apply smoothing
  if (previousValue !== undefined && config.smoothing > 0) {
    outputValue =
      previousValue * config.smoothing + outputValue * (1 - config.smoothing);
  }

  return outputValue;
}

// ════════════════════════════════════════════════════════════════════════════
// Region Analysis
// ════════════════════════════════════════════════════════════════════════════

/**
 * Analyze color distribution in a region
 */
export function analyzeRegion(
  imageData: ImageData,
  region: { x: number; y: number; width: number; height: number },
): {
  averageColor: ColorSample;
  brightest: ColorSample;
  darkest: ColorSample;
  averageBrightness: number;
  colorVariance: number;
} {
  const startX = Math.floor(region.x * imageData.width);
  const startY = Math.floor(region.y * imageData.height);
  const endX = Math.min(
    imageData.width,
    Math.ceil((region.x + region.width) * imageData.width),
  );
  const endY = Math.min(
    imageData.height,
    Math.ceil((region.y + region.height) * imageData.height),
  );

  let totalR = 0,
    totalG = 0,
    totalB = 0,
    totalA = 0;
  let maxBrightness = 0,
    minBrightness = 1;
  let brightest: ColorSample | null = null;
  let darkest: ColorSample | null = null;
  let pixelCount = 0;
  const brightnesses: number[] = [];

  for (let y = startY; y < endY; y++) {
    for (let x = startX; x < endX; x++) {
      const sample = samplePixel(imageData, x, y);

      totalR += sample.r;
      totalG += sample.g;
      totalB += sample.b;
      totalA += sample.a;

      brightnesses.push(sample.brightness);

      if (sample.brightness > maxBrightness) {
        maxBrightness = sample.brightness;
        brightest = sample;
      }
      if (sample.brightness < minBrightness) {
        minBrightness = sample.brightness;
        darkest = sample;
      }

      pixelCount++;
    }
  }

  if (pixelCount === 0) {
    const empty = createColorSample(0, 0, 0, 0);
    return {
      averageColor: empty,
      brightest: empty,
      darkest: empty,
      averageBrightness: 0,
      colorVariance: 0,
    };
  }

  const averageColor = createColorSample(
    totalR / pixelCount,
    totalG / pixelCount,
    totalB / pixelCount,
    totalA / pixelCount,
  );

  const averageBrightness =
    brightnesses.reduce((a, b) => a + b, 0) / brightnesses.length;
  const variance =
    brightnesses.reduce((sum, b) => sum + (b - averageBrightness) ** 2, 0) /
    brightnesses.length;

  return {
    averageColor,
    brightest: brightest || averageColor,
    darkest: darkest || averageColor,
    averageBrightness,
    colorVariance: Math.sqrt(variance),
  };
}

// ════════════════════════════════════════════════════════════════════════════
// Exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  // Color utilities
  rgbToHsv,
  calculateBrightness,
  createColorSample,

  // Sampling
  samplePixel,
  sampleAreaAverage,
  sampleAreaMax,
  sampleAreaMin,
  getFeatureValue,
  sampleColorFromImageData,

  // Color reactivity
  getMappedColorValue,

  // Depth reactivity
  sampleDepth,
  sampleDepthWithGradient,
  getMappedDepthValue,

  // Motion detection
  calculateMotion,
  getMappedMotionValue,

  // Region analysis
  analyzeRegion,
};
