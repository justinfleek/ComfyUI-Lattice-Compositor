/**
 * Histogram Analysis Service
 *
 * Provides histogram computation and analysis for color correction
 * monitoring and auto-correction algorithms.
 */

import { BT709_B, BT709_G, BT709_R } from "../../utils/labColorUtils";

/**
 * Statistics for a single channel
 */
export interface ChannelStats {
  min: number; // Minimum value (0-255)
  max: number; // Maximum value (0-255)
  mean: number; // Average value
  median: number; // Median value
  stdDev: number; // Standard deviation
  clippedLow: number; // Percentage of pixels at 0 (0-100)
  clippedHigh: number; // Percentage of pixels at 255 (0-100)
  mode: number; // Most common value
  percentile5: number; // 5th percentile
  percentile95: number; // 95th percentile
}

/**
 * Complete histogram data for an image
 */
export interface HistogramData {
  red: Uint32Array; // 256 bins
  green: Uint32Array;
  blue: Uint32Array;
  luminance: Uint32Array;

  // Cumulative histograms for percentile calculations
  redCumulative: Uint32Array;
  greenCumulative: Uint32Array;
  blueCumulative: Uint32Array;
  luminanceCumulative: Uint32Array;

  // Statistics per channel
  stats: {
    red: ChannelStats;
    green: ChannelStats;
    blue: ChannelStats;
    luminance: ChannelStats;
  };

  // Image info
  pixelCount: number;
  width: number;
  height: number;
}

/**
 * Waveform data for scope display
 */
export interface WaveformData {
  // For each column, array of luminance values (0-255)
  // columns[x] = Uint8Array of all Y values in that column
  columns: Uint8Array[];
  width: number;
  height: number;
  mode: "luma" | "rgb";

  //                                                                       // rgb
  redColumns?: Uint8Array[];
  greenColumns?: Uint8Array[];
  blueColumns?: Uint8Array[];
}

/**
 * RGB Parade data
 */
export interface ParadeData {
  red: WaveformData;
  green: WaveformData;
  blue: WaveformData;
}

/**
 * Vectorscope data
 */
export interface VectorscopeData {
  // 2D array: vectorscope[u + 128][v + 128] = count
  // U: -128 to +127 (B-Y chrominance)
  // V: -128 to +127 (R-Y chrominance)
  data: Uint32Array; // 256x256 flattened
  maxCount: number; // For normalization
  width: 256;
  height: 256;
}

/**
 * Compute histogram from ImageData
 */
export function computeHistogram(imageData: ImageData): HistogramData {
  const { data, width, height } = imageData;
  const pixelCount = width * height;

  // Initialize histogram bins
  const red = new Uint32Array(256);
  const green = new Uint32Array(256);
  const blue = new Uint32Array(256);
  const luminance = new Uint32Array(256);

  // Process all pixels
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    // Skip alpha

    red[r]++;
    green[g]++;
    blue[b]++;

    //                                                                        // bt
    const lum = Math.round(BT709_R * r + BT709_G * g + BT709_B * b);
    luminance[Math.min(255, Math.max(0, lum))]++;
  }

  // Compute cumulative histograms
  const redCumulative = computeCumulativeHistogram(red);
  const greenCumulative = computeCumulativeHistogram(green);
  const blueCumulative = computeCumulativeHistogram(blue);
  const luminanceCumulative = computeCumulativeHistogram(luminance);

  // Compute statistics
  const stats = {
    red: computeChannelStats(red, redCumulative, pixelCount),
    green: computeChannelStats(green, greenCumulative, pixelCount),
    blue: computeChannelStats(blue, blueCumulative, pixelCount),
    luminance: computeChannelStats(luminance, luminanceCumulative, pixelCount),
  };

  return {
    red,
    green,
    blue,
    luminance,
    redCumulative,
    greenCumulative,
    blueCumulative,
    luminanceCumulative,
    stats,
    pixelCount,
    width,
    height,
  };
}

/**
 * Compute cumulative histogram from histogram
 */
export function computeCumulativeHistogram(
  histogram: Uint32Array,
): Uint32Array {
  const cumulative = new Uint32Array(256);
  cumulative[0] = histogram[0];

  for (let i = 1; i < 256; i++) {
    cumulative[i] = cumulative[i - 1] + histogram[i];
  }

  return cumulative;
}

/**
 * Find histogram value at percentile (0-100)
 */
export function findHistogramPercentile(
  cumulative: Uint32Array,
  percentile: number,
  totalPixels: number,
): number {
  const target = (percentile / 100) * totalPixels;

  for (let i = 0; i < 256; i++) {
    if (cumulative[i] >= target) {
      return i;
    }
  }

  return 255;
}

/**
 * Compute statistics for a channel
 */
function computeChannelStats(
  histogram: Uint32Array,
  cumulative: Uint32Array,
  pixelCount: number,
): ChannelStats {
  // Find min/max
  let min = 0;
  let max = 255;

  for (let i = 0; i < 256; i++) {
    if (histogram[i] > 0) {
      min = i;
      break;
    }
  }

  for (let i = 255; i >= 0; i--) {
    if (histogram[i] > 0) {
      max = i;
      break;
    }
  }

  // Calculate mean
  let sum = 0;
  for (let i = 0; i < 256; i++) {
    sum += i * histogram[i];
  }
  const mean = sum / pixelCount;

  // Calculate standard deviation
  let variance = 0;
  for (let i = 0; i < 256; i++) {
    variance += histogram[i] * (i - mean) ** 2;
  }
  const stdDev = Math.sqrt(variance / pixelCount);

  // Find median (50th percentile)
  const median = findHistogramPercentile(cumulative, 50, pixelCount);

  // Find mode (most common value)
  let mode = 0;
  let maxCount = 0;
  for (let i = 0; i < 256; i++) {
    if (histogram[i] > maxCount) {
      maxCount = histogram[i];
      mode = i;
    }
  }

  // Clipping percentages
  const clippedLow = (histogram[0] / pixelCount) * 100;
  const clippedHigh = (histogram[255] / pixelCount) * 100;

  // Percentiles
  const percentile5 = findHistogramPercentile(cumulative, 5, pixelCount);
  const percentile95 = findHistogramPercentile(cumulative, 95, pixelCount);

  return {
    min,
    max,
    mean,
    median,
    stdDev,
    clippedLow,
    clippedHigh,
    mode,
    percentile5,
    percentile95,
  };
}

/**
 * Compute waveform data from ImageData
 */
export function computeWaveform(
  imageData: ImageData,
  mode: "luma" | "rgb" = "luma",
): WaveformData {
  const { data, width, height } = imageData;

  // Initialize columns
  const columns: Uint8Array[] = [];
  for (let x = 0; x < width; x++) {
    columns[x] = new Uint8Array(height);
  }

  let redColumns: Uint8Array[] | undefined;
  let greenColumns: Uint8Array[] | undefined;
  let blueColumns: Uint8Array[] | undefined;

  if (mode === "rgb") {
    redColumns = [];
    greenColumns = [];
    blueColumns = [];
    for (let x = 0; x < width; x++) {
      redColumns[x] = new Uint8Array(height);
      greenColumns[x] = new Uint8Array(height);
      blueColumns[x] = new Uint8Array(height);
    }
  }

  // Process pixels
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      const r = data[i];
      const g = data[i + 1];
      const b = data[i + 2];

      // Luminance
      const lum = Math.round(BT709_R * r + BT709_G * g + BT709_B * b);
      columns[x][y] = Math.min(255, Math.max(0, lum));

      //                                                                       // rgb
      if (mode === "rgb" && redColumns && greenColumns && blueColumns) {
        redColumns[x][y] = r;
        greenColumns[x][y] = g;
        blueColumns[x][y] = b;
      }
    }
  }

  return {
    columns,
    width,
    height,
    mode,
    redColumns,
    greenColumns,
    blueColumns,
  };
}

/**
 * Compute RGB Parade data
 */
export function computeParade(imageData: ImageData): ParadeData {
  const { data, width, height } = imageData;

  // Initialize columns for each channel
  const redColumns: Uint8Array[] = [];
  const greenColumns: Uint8Array[] = [];
  const blueColumns: Uint8Array[] = [];

  for (let x = 0; x < width; x++) {
    redColumns[x] = new Uint8Array(height);
    greenColumns[x] = new Uint8Array(height);
    blueColumns[x] = new Uint8Array(height);
  }

  // Process pixels
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      redColumns[x][y] = data[i];
      greenColumns[x][y] = data[i + 1];
      blueColumns[x][y] = data[i + 2];
    }
  }

  return {
    red: {
      columns: redColumns,
      width,
      height,
      mode: "luma",
    },
    green: {
      columns: greenColumns,
      width,
      height,
      mode: "luma",
    },
    blue: {
      columns: blueColumns,
      width,
      height,
      mode: "luma",
    },
  };
}

/**
 * Compute Vectorscope data
 * Maps chrominance (U, V) to a 2D distribution
 */
export function computeVectorscope(imageData: ImageData): VectorscopeData {
  const { data, width, height } = imageData;

  // 256x256 grid for U/V values (-128 to +127 mapped to 0-255)
  const vectorData = new Uint32Array(256 * 256);
  let maxCount = 0;

  // Process pixels
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i] / 255;
    const g = data[i + 1] / 255;
    const b = data[i + 2] / 255;

    //                                                                        // bt
    const Y = BT709_R * r + BT709_G * g + BT709_B * b;

    // Chrominance (scaled for display)
    // U = 0.5 * (B - Y) / (1 - BT709_B)
    // V = 0.5 * (R - Y) / (1 - BT709_R)
    const U = (0.5 * (b - Y)) / (1 - BT709_B);
    const V = (0.5 * (r - Y)) / (1 - BT709_R);

    // Map to grid coordinates (0-255)
    // U and V range from approximately -0.5 to +0.5
    const uIdx = Math.round((U + 0.5) * 255);
    const vIdx = Math.round((V + 0.5) * 255);

    // Clamp to valid range
    const uClamped = Math.max(0, Math.min(255, uIdx));
    const vClamped = Math.max(0, Math.min(255, vIdx));

    // Increment count (V is Y axis, inverted for display)
    const idx = (255 - vClamped) * 256 + uClamped;
    vectorData[idx]++;

    if (vectorData[idx] > maxCount) {
      maxCount = vectorData[idx];
    }
  }

  return {
    data: vectorData,
    maxCount,
    width: 256,
    height: 256,
  };
}

/**
 * Build histogram matching LUT
 * Creates a lookup table that maps source histogram to match target histogram
 */
export function buildHistogramMatchingLUT(
  sourceHist: Uint32Array,
  targetHist: Uint32Array,
  sourcePixels: number,
  targetPixels: number,
): Uint8Array {
  // Compute cumulative histograms (normalized to 0-1)
  const sourceCDF = new Float32Array(256);
  const targetCDF = new Float32Array(256);

  sourceCDF[0] = sourceHist[0] / sourcePixels;
  targetCDF[0] = targetHist[0] / targetPixels;

  for (let i = 1; i < 256; i++) {
    sourceCDF[i] = sourceCDF[i - 1] + sourceHist[i] / sourcePixels;
    targetCDF[i] = targetCDF[i - 1] + targetHist[i] / targetPixels;
  }

  // Build LUT by finding closest match in target CDF
  const lut = new Uint8Array(256);

  for (let i = 0; i < 256; i++) {
    const sourceVal = sourceCDF[i];

    // Find target level with closest cumulative value
    let bestMatch = 0;
    let bestDiff = Math.abs(targetCDF[0] - sourceVal);

    for (let j = 1; j < 256; j++) {
      const diff = Math.abs(targetCDF[j] - sourceVal);
      if (diff < bestDiff) {
        bestDiff = diff;
        bestMatch = j;
      }
    }

    lut[i] = bestMatch;
  }

  return lut;
}

/**
 * Apply histogram matching to ImageData
 */
export function applyHistogramMatching(
  imageData: ImageData,
  redLUT: Uint8Array,
  greenLUT: Uint8Array,
  blueLUT: Uint8Array,
  strength: number = 1.0,
): ImageData {
  const { data, width, height } = imageData;
  const output = new ImageData(width, height);

  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const a = data[i + 3];

    // Apply LUT with strength blending
    output.data[i] = Math.round(r + (redLUT[r] - r) * strength);
    output.data[i + 1] = Math.round(g + (greenLUT[g] - g) * strength);
    output.data[i + 2] = Math.round(b + (blueLUT[b] - b) * strength);
    output.data[i + 3] = a;
  }

  return output;
}

/**
 * Auto-levels calculation
 * Returns input black/white levels for contrast stretch
 */
export function calculateAutoLevels(
  histogram: HistogramData,
  clipPercent: number = 0.1,
): { inputBlack: number; inputWhite: number } {
  const _stats = histogram.stats.luminance;

  // Use percentiles to avoid outlier influence
  const inputBlack = findHistogramPercentile(
    histogram.luminanceCumulative,
    clipPercent,
    histogram.pixelCount,
  );

  const inputWhite = findHistogramPercentile(
    histogram.luminanceCumulative,
    100 - clipPercent,
    histogram.pixelCount,
  );

  return { inputBlack, inputWhite };
}

/**
 * Calculate white balance correction from a sampled "should be gray" point
 * Returns temperature and tint adjustments
 */
export function calculateWhiteBalanceCorrection(
  sampledR: number,
  sampledG: number,
  sampledB: number,
): { temperature: number; tint: number } {
  // Target is neutral gray (equal RGB)
  const _targetGray = (sampledR + sampledG + sampledB) / 3;

  // Calculate deviation from neutral
  // Temperature: blue-yellow axis (more blue = higher temp, more yellow = lower temp)
  // Tint: green-magenta axis (more green = negative tint, more magenta = positive tint)

  // Simple algorithm: compare R and B for temperature, G vs avg(R,B) for tint
  const rbAvg = (sampledR + sampledB) / 2;

  // Temperature: if blue > red, scene is too warm, need cooler (negative temp)
  // Scale to -100 to +100 range
  const temperature = ((sampledR - sampledB) / 255) * 100;

  // Tint: if green > rb average, scene is too magenta, need more green (negative tint)
  const tint = ((rbAvg - sampledG) / 255) * 100;

  return {
    temperature: Math.max(-100, Math.min(100, temperature)),
    tint: Math.max(-100, Math.min(100, tint)),
  };
}

/**
 * Check if histogram is clipped (over/under exposed)
 */
export function isClipped(histogram: HistogramData): {
  shadowsClipped: boolean;
  highlightsClipped: boolean;
} {
  const threshold = 1; // 1% clipping threshold

  return {
    shadowsClipped: histogram.stats.luminance.clippedLow > threshold,
    highlightsClipped: histogram.stats.luminance.clippedHigh > threshold,
  };
}

/**
 * Calculate dynamic range of image
 * Returns number of stops
 */
export function calculateDynamicRange(histogram: HistogramData): number {
  const stats = histogram.stats.luminance;
  const range = stats.percentile95 - stats.percentile5;

  // Convert to stops (each doubling = 1 stop)
  // 255 levels = ~8 stops in 8-bit
  if (range <= 0) return 0;

  return Math.log2(255 / range) * 8;
}
