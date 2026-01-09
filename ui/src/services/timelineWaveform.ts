/**
 * Timeline Waveform Service
 *
 * Phase 7: Audio Waveform in Timeline Implementation
 *
 * Features:
 * - Multi-resolution waveform peaks (mipmap approach)
 * - Efficient canvas rendering
 * - Beat marker overlay
 * - Per-layer waveform caching
 */

import { createLogger } from "@/utils/logger";

const logger = createLogger("TimelineWaveform");

// ============================================================================
// TYPES
// ============================================================================

export interface WaveformData {
  /** Audio layer/asset ID */
  id: string;
  /** Sample rate of source audio */
  sampleRate: number;
  /** Duration in seconds */
  duration: number;
  /** Total number of samples */
  totalSamples: number;
  /** Pre-computed peaks at different resolutions */
  peaks: Map<number, Float32Array>; // samplesPerPixel -> peaks
  /** Beat positions in seconds */
  beats?: number[];
  /** BPM if detected */
  bpm?: number;
}

export interface WaveformRenderOptions {
  /** Canvas width in pixels */
  width: number;
  /** Canvas height in pixels */
  height: number;
  /** Start time in seconds */
  startTime: number;
  /** End time in seconds */
  endTime: number;
  /** Waveform color */
  color: string;
  /** Background color (transparent if not set) */
  backgroundColor?: string;
  /** Show beat markers */
  showBeats?: boolean;
  /** Beat marker color */
  beatColor?: string;
  /** Waveform style */
  style?: "bars" | "line" | "filled";
  /** Opacity (0-1) */
  opacity?: number;
}

export interface WaveformPeakOptions {
  /** Samples per pixel at this resolution */
  samplesPerPixel: number;
  /** Channel to use (0 = left, 1 = right, -1 = mix) */
  channel?: number;
}

// ============================================================================
// WAVEFORM CACHE
// ============================================================================

const waveformCache: Map<string, WaveformData> = new Map();

// ============================================================================
// PEAK COMPUTATION
// ============================================================================

/**
 * Compute peaks from audio buffer at a specific resolution
 */
export function computePeaks(
  audioBuffer: AudioBuffer,
  samplesPerPixel: number,
  channel: number = -1,
): Float32Array {
  const numChannels = audioBuffer.numberOfChannels;
  const totalSamples = audioBuffer.length;
  const numPeaks = Math.ceil(totalSamples / samplesPerPixel);

  // Get channel data
  const channelData: Float32Array[] = [];
  if (channel >= 0 && channel < numChannels) {
    channelData.push(audioBuffer.getChannelData(channel));
  } else {
    // Mix all channels
    for (let c = 0; c < numChannels; c++) {
      channelData.push(audioBuffer.getChannelData(c));
    }
  }

  const peaks = new Float32Array(numPeaks * 2); // min/max pairs

  for (let i = 0; i < numPeaks; i++) {
    const startSample = i * samplesPerPixel;
    const endSample = Math.min(startSample + samplesPerPixel, totalSamples);

    let min = 1;
    let max = -1;

    for (let s = startSample; s < endSample; s++) {
      let sample = 0;
      for (const data of channelData) {
        sample += data[s];
      }
      sample /= channelData.length;

      if (sample < min) min = sample;
      if (sample > max) max = sample;
    }

    peaks[i * 2] = min;
    peaks[i * 2 + 1] = max;
  }

  return peaks;
}

/**
 * Generate peaks at multiple resolutions (mipmap levels)
 */
export function generatePeakMipmap(
  audioBuffer: AudioBuffer,
): Map<number, Float32Array> {
  const peaks = new Map<number, Float32Array>();

  // Generate at standard zoom levels
  // 256, 512, 1024, 2048, 4096, 8192 samples per pixel
  const resolutions = [256, 512, 1024, 2048, 4096, 8192];

  for (const samplesPerPixel of resolutions) {
    peaks.set(samplesPerPixel, computePeaks(audioBuffer, samplesPerPixel));
  }

  return peaks;
}

/**
 * Get peaks at the closest available resolution
 */
export function getPeaksAtResolution(
  waveform: WaveformData,
  samplesPerPixel: number,
): Float32Array | null {
  // Find closest available resolution
  let closestRes = 256;
  let closestDiff = Math.abs(samplesPerPixel - closestRes);

  for (const res of waveform.peaks.keys()) {
    const diff = Math.abs(samplesPerPixel - res);
    if (diff < closestDiff) {
      closestDiff = diff;
      closestRes = res;
    }
  }

  return waveform.peaks.get(closestRes) || null;
}

// ============================================================================
// WAVEFORM ANALYSIS
// ============================================================================

/**
 * Create waveform data from audio buffer
 */
export async function createWaveformData(
  id: string,
  audioBuffer: AudioBuffer,
  beats?: number[],
  bpm?: number,
): Promise<WaveformData> {
  // Check cache
  const cached = waveformCache.get(id);
  if (cached) return cached;

  // Generate peaks
  const peaks = generatePeakMipmap(audioBuffer);

  const waveform: WaveformData = {
    id,
    sampleRate: audioBuffer.sampleRate,
    duration: audioBuffer.duration,
    totalSamples: audioBuffer.length,
    peaks,
    beats,
    bpm,
  };

  waveformCache.set(id, waveform);
  logger.debug(`Created waveform data for ${id}: ${peaks.size} resolutions`);

  return waveform;
}

/**
 * Get cached waveform data
 */
export function getWaveformData(id: string): WaveformData | undefined {
  return waveformCache.get(id);
}

/**
 * Clear waveform cache for an ID
 */
export function clearWaveformCache(id?: string): void {
  if (id) {
    waveformCache.delete(id);
  } else {
    waveformCache.clear();
  }
}

// ============================================================================
// WAVEFORM RENDERING
// ============================================================================

/**
 * Render waveform to canvas
 */
export function renderWaveform(
  canvas: HTMLCanvasElement,
  waveform: WaveformData,
  options: WaveformRenderOptions,
): void {
  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  const { width, height, startTime, endTime, color, style = "bars" } = options;

  // Resize canvas if needed
  if (canvas.width !== width || canvas.height !== height) {
    canvas.width = width;
    canvas.height = height;
  }

  // Clear
  ctx.clearRect(0, 0, width, height);

  if (options.backgroundColor) {
    ctx.fillStyle = options.backgroundColor;
    ctx.fillRect(0, 0, width, height);
  }

  // Calculate samples per pixel for this view
  const viewDuration = endTime - startTime;
  const samplesPerPixel = Math.round(
    (viewDuration * waveform.sampleRate) / width,
  );

  // Get peaks at appropriate resolution
  const peaks = getPeaksAtResolution(waveform, samplesPerPixel);
  if (!peaks) return;

  // Calculate which peaks to render
  const startSample = Math.floor(startTime * waveform.sampleRate);
  const endSample = Math.ceil(endTime * waveform.sampleRate);
  const peakResolution =
    Array.from(waveform.peaks.keys()).find(
      (k) => waveform.peaks.get(k) === peaks,
    ) || 256;

  const startPeak = Math.floor(startSample / peakResolution);
  const endPeak = Math.ceil(endSample / peakResolution);

  const centerY = height / 2;

  // Set styles
  ctx.globalAlpha = options.opacity ?? 1;
  ctx.fillStyle = color;
  ctx.strokeStyle = color;

  if (style === "line") {
    ctx.lineWidth = 1;
    ctx.beginPath();
  }

  // Render peaks
  for (let i = 0; i < width; i++) {
    const peakIndex =
      startPeak + Math.floor((i / width) * (endPeak - startPeak));

    if (peakIndex * 2 + 1 >= peaks.length) break;

    const min = peaks[peakIndex * 2];
    const max = peaks[peakIndex * 2 + 1];

    const minY = centerY - min * centerY;
    const maxY = centerY - max * centerY;

    if (style === "bars") {
      // Vertical bar from min to max
      ctx.fillRect(i, maxY, 1, minY - maxY);
    } else if (style === "filled") {
      // Filled from center
      ctx.fillRect(i, maxY, 1, centerY - maxY);
      ctx.fillRect(i, centerY, 1, minY - centerY);
    } else if (style === "line") {
      if (i === 0) {
        ctx.moveTo(i, centerY - ((min + max) / 2) * centerY);
      } else {
        ctx.lineTo(i, centerY - ((min + max) / 2) * centerY);
      }
    }
  }

  if (style === "line") {
    ctx.stroke();
  }

  // Render beat markers
  if (options.showBeats && waveform.beats) {
    ctx.globalAlpha = 0.7;
    ctx.strokeStyle = options.beatColor || "#f59e0b";
    ctx.lineWidth = 1;

    for (const beat of waveform.beats) {
      if (beat >= startTime && beat <= endTime) {
        const x = ((beat - startTime) / viewDuration) * width;
        ctx.beginPath();
        ctx.moveTo(x, 0);
        ctx.lineTo(x, height);
        ctx.stroke();
      }
    }
  }

  ctx.globalAlpha = 1;
}

/**
 * Render waveform to offscreen canvas and return as ImageBitmap
 */
export async function renderWaveformToImage(
  waveform: WaveformData,
  options: WaveformRenderOptions,
): Promise<ImageBitmap> {
  const canvas = new OffscreenCanvas(options.width, options.height);
  const ctx = canvas.getContext("2d")!;

  // Create a temporary regular canvas for rendering
  const tempCanvas = document.createElement("canvas");
  tempCanvas.width = options.width;
  tempCanvas.height = options.height;

  renderWaveform(tempCanvas, waveform, options);

  // Copy to offscreen canvas
  ctx.drawImage(tempCanvas, 0, 0);

  return createImageBitmap(canvas);
}

// ============================================================================
// TIMELINE INTEGRATION
// ============================================================================

export interface TimelineWaveformConfig {
  /** Layer ID */
  layerId: string;
  /** Audio asset ID */
  audioId: string;
  /** Layer color for waveform */
  layerColor: string;
  /** Layer start frame */
  startFrame: number;
  /** Layer end frame */
  endFrame: number;
  /** Timeline visible range (frames) */
  visibleStart: number;
  visibleEnd: number;
  /** Frames per second */
  fps: number;
  /** Track width in pixels */
  trackWidth: number;
  /** Track height in pixels */
  trackHeight: number;
}

/**
 * Render waveform for timeline layer track
 */
export function renderTimelineWaveform(
  canvas: HTMLCanvasElement,
  waveform: WaveformData,
  config: TimelineWaveformConfig,
): void {
  const {
    layerColor,
    startFrame,
    endFrame,
    visibleStart,
    visibleEnd,
    fps,
    trackWidth,
    trackHeight,
  } = config;

  // Calculate visible portion of layer
  const layerVisibleStart = Math.max(startFrame, visibleStart);
  const layerVisibleEnd = Math.min(endFrame, visibleEnd);

  if (layerVisibleStart >= layerVisibleEnd) return;

  // Calculate pixel positions
  const visibleDuration = visibleEnd - visibleStart;
  const pixelsPerFrame = trackWidth / visibleDuration;

  const layerStartX = (layerVisibleStart - visibleStart) * pixelsPerFrame;
  const layerEndX = (layerVisibleEnd - visibleStart) * pixelsPerFrame;
  const layerWidth = layerEndX - layerStartX;

  // Calculate time range for waveform
  const audioStartTime = (layerVisibleStart - startFrame) / fps;
  const audioEndTime = (layerVisibleEnd - startFrame) / fps;

  // Render waveform
  renderWaveform(canvas, waveform, {
    width: Math.ceil(layerWidth),
    height: trackHeight,
    startTime: Math.max(0, audioStartTime),
    endTime: Math.min(waveform.duration, audioEndTime),
    color: layerColor,
    style: "filled",
    opacity: 0.5,
    showBeats: true,
    beatColor: "#8B5CF6",
  });
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  computePeaks,
  generatePeakMipmap,
  createWaveformData,
  getWaveformData,
  clearWaveformCache,
  renderWaveform,
  renderWaveformToImage,
  renderTimelineWaveform,
};
