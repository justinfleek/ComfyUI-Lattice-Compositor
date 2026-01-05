/**
 * Scope Analysis Web Worker
 *
 * Performs color analysis in a background thread to prevent UI blocking.
 * Computes histogram, waveform, vectorscope, and RGB parade data.
 */

// BT.709 luminance coefficients
const BT709_R = 0.2126;
const BT709_G = 0.7152;
const BT709_B = 0.0722;

// Message types
interface ScopeRequest {
  type: "analyze";
  payload: {
    imageData: Uint8ClampedArray;
    width: number;
    height: number;
    scopes: ("histogram" | "waveform" | "vectorscope" | "parade")[];
  };
}

interface ScopeResponse {
  type: "complete" | "error";
  payload: {
    histogram?: HistogramResult;
    waveform?: WaveformResult;
    vectorscope?: VectorscopeResult;
    parade?: ParadeResult;
    error?: string;
  };
}

interface HistogramResult {
  red: number[];
  green: number[];
  blue: number[];
  luminance: number[];
  maxCount: number;
}

interface WaveformResult {
  // Each entry is an array of [x, y] pixel positions to render
  // For efficiency, we sample rather than plot every pixel
  lumaPoints: Float32Array; // Flattened [x1, y1, x2, y2, ...]
  rgbPoints?: {
    red: Float32Array;
    green: Float32Array;
    blue: Float32Array;
  };
  width: number;
  height: number;
}

interface VectorscopeResult {
  // UV grid data (256x256)
  data: Uint32Array;
  maxCount: number;
  // Pre-calculated graticule target positions
  targets: {
    r: [number, number];
    y: [number, number];
    g: [number, number];
    c: [number, number];
    b: [number, number];
    m: [number, number];
    skinLine: [[number, number], [number, number]];
  };
}

interface ParadeResult {
  red: WaveformResult;
  green: WaveformResult;
  blue: WaveformResult;
}

// Worker message handler
self.onmessage = (e: MessageEvent<ScopeRequest>) => {
  const { type, payload } = e.data;

  if (type === "analyze") {
    try {
      const result: ScopeResponse["payload"] = {};
      const { imageData, width, height, scopes } = payload;

      // Create ImageData-like object for processing
      const pixels = imageData;

      if (scopes.includes("histogram")) {
        result.histogram = computeHistogram(pixels, width, height);
      }

      if (scopes.includes("waveform")) {
        result.waveform = computeWaveform(pixels, width, height);
      }

      if (scopes.includes("vectorscope")) {
        result.vectorscope = computeVectorscope(pixels, width, height);
      }

      if (scopes.includes("parade")) {
        result.parade = computeParade(pixels, width, height);
      }

      self.postMessage({ type: "complete", payload: result } as ScopeResponse);
    } catch (error) {
      self.postMessage({
        type: "error",
        payload: {
          error: error instanceof Error ? error.message : "Unknown error",
        },
      } as ScopeResponse);
    }
  }
};

/**
 * Compute histogram data
 */
function computeHistogram(
  pixels: Uint8ClampedArray,
  _width: number,
  _height: number,
): HistogramResult {
  const red = new Array(256).fill(0);
  const green = new Array(256).fill(0);
  const blue = new Array(256).fill(0);
  const luminance = new Array(256).fill(0);
  let maxCount = 0;

  for (let i = 0; i < pixels.length; i += 4) {
    const r = pixels[i];
    const g = pixels[i + 1];
    const b = pixels[i + 2];

    red[r]++;
    green[g]++;
    blue[b]++;

    // BT.709 luminance
    const lum = Math.round(BT709_R * r + BT709_G * g + BT709_B * b);
    luminance[Math.min(255, lum)]++;
  }

  // Find max for normalization
  for (let i = 0; i < 256; i++) {
    maxCount = Math.max(maxCount, red[i], green[i], blue[i], luminance[i]);
  }

  return { red, green, blue, luminance, maxCount };
}

/**
 * Compute waveform data (sampled for performance)
 */
function computeWaveform(
  pixels: Uint8ClampedArray,
  width: number,
  height: number,
): WaveformResult {
  // Sample every Nth column for performance
  const sampleRate = Math.max(1, Math.floor(width / 256));
  const sampledWidth = Math.ceil(width / sampleRate);

  // Store points as [x, y] pairs (normalized 0-1)
  const points: number[] = [];

  for (let sx = 0; sx < sampledWidth; sx++) {
    const x = sx * sampleRate;
    if (x >= width) continue;

    // Sample every Nth row too
    const ySampleRate = Math.max(1, Math.floor(height / 256));

    for (let sy = 0; sy < height; sy += ySampleRate) {
      const idx = (sy * width + x) * 4;
      const r = pixels[idx];
      const g = pixels[idx + 1];
      const b = pixels[idx + 2];

      // Luminance value (0-255)
      const lum = BT709_R * r + BT709_G * g + BT709_B * b;

      // Normalize to 0-1 range
      const normalizedX = sx / sampledWidth;
      const normalizedY = 1 - lum / 255; // Invert Y for display

      points.push(normalizedX, normalizedY);
    }
  }

  return {
    lumaPoints: new Float32Array(points),
    width: sampledWidth,
    height: 256,
  };
}

/**
 * Compute vectorscope data
 */
function computeVectorscope(
  pixels: Uint8ClampedArray,
  width: number,
  height: number,
): VectorscopeResult {
  // 256x256 grid for UV values
  const data = new Uint32Array(256 * 256);
  let maxCount = 0;

  // Sample for performance (every 2nd pixel)
  const sampleRate = 2;

  for (let y = 0; y < height; y += sampleRate) {
    for (let x = 0; x < width; x += sampleRate) {
      const idx = (y * width + x) * 4;
      const r = pixels[idx] / 255;
      const g = pixels[idx + 1] / 255;
      const b = pixels[idx + 2] / 255;

      // BT.709 Y
      const Y = BT709_R * r + BT709_G * g + BT709_B * b;

      // Chrominance (Cb/Cr style, scaled for display)
      // U = B - Y, V = R - Y
      const U = (b - Y) * 0.5;
      const V = (r - Y) * 0.5;

      // Map to grid coordinates (0-255)
      // U and V range from approximately -0.5 to +0.5
      const uIdx = Math.round((U + 0.5) * 255);
      const vIdx = Math.round((V + 0.5) * 255);

      // Clamp to valid range
      const uClamped = Math.max(0, Math.min(255, uIdx));
      const vClamped = Math.max(0, Math.min(255, vIdx));

      // V is Y axis, inverted for display (higher V = lower on screen)
      const gridIdx = (255 - vClamped) * 256 + uClamped;
      data[gridIdx]++;

      if (data[gridIdx] > maxCount) {
        maxCount = data[gridIdx];
      }
    }
  }

  // Calculate graticule target positions
  // Standard color bar values in vectorscope coordinates
  const targets = calculateVectorscopeTargets();

  return { data, maxCount, targets };
}

/**
 * Calculate standard vectorscope graticule targets
 */
function calculateVectorscopeTargets() {
  // Standard SMPTE color bars to UV coordinates
  const colorToUV = (r: number, g: number, b: number): [number, number] => {
    const Y = BT709_R * r + BT709_G * g + BT709_B * b;
    const U = (b - Y) * 0.5;
    const V = (r - Y) * 0.5;
    // Map to 0-255 grid
    return [
      Math.round((U + 0.5) * 255),
      Math.round((0.5 - V) * 255), // Inverted V for display
    ];
  };

  return {
    r: colorToUV(1, 0, 0), // Red
    y: colorToUV(1, 1, 0), // Yellow
    g: colorToUV(0, 1, 0), // Green
    c: colorToUV(0, 1, 1), // Cyan
    b: colorToUV(0, 0, 1), // Blue
    m: colorToUV(1, 0, 1), // Magenta
    // Skin tone line (I-line) - approximately from center toward skin tones
    skinLine: [
      [128, 128], // Center
      [175, 95], // Toward typical skin tones
    ] as [[number, number], [number, number]],
  };
}

/**
 * Compute RGB parade data
 */
function computeParade(
  pixels: Uint8ClampedArray,
  width: number,
  height: number,
): ParadeResult {
  // Sample rate for performance
  const sampleRate = Math.max(1, Math.floor(width / 256));
  const sampledWidth = Math.ceil(width / sampleRate);
  const ySampleRate = Math.max(1, Math.floor(height / 256));

  const redPoints: number[] = [];
  const greenPoints: number[] = [];
  const bluePoints: number[] = [];

  for (let sx = 0; sx < sampledWidth; sx++) {
    const x = sx * sampleRate;
    if (x >= width) continue;

    for (let sy = 0; sy < height; sy += ySampleRate) {
      const idx = (sy * width + x) * 4;
      const r = pixels[idx];
      const g = pixels[idx + 1];
      const b = pixels[idx + 2];

      const normalizedX = sx / sampledWidth;

      // Red channel
      redPoints.push(normalizedX, 1 - r / 255);

      // Green channel
      greenPoints.push(normalizedX, 1 - g / 255);

      // Blue channel
      bluePoints.push(normalizedX, 1 - b / 255);
    }
  }

  return {
    red: {
      lumaPoints: new Float32Array(redPoints),
      width: sampledWidth,
      height: 256,
    },
    green: {
      lumaPoints: new Float32Array(greenPoints),
      width: sampledWidth,
      height: 256,
    },
    blue: {
      lumaPoints: new Float32Array(bluePoints),
      width: sampledWidth,
      height: 256,
    },
  };
}

// Export types for the main thread
export type {
  ScopeRequest,
  ScopeResponse,
  HistogramResult,
  WaveformResult,
  VectorscopeResult,
  ParadeResult,
};
