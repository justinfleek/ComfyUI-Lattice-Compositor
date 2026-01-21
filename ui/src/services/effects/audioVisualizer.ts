/**
 * Audio Visualizer Effect Renderers
 *
 * Implements Audio Spectrum and Audio Waveform effects for visual audio representation.
 * These effects render frequency and amplitude data as visual elements.
 *
 * Audio visualization effects for frequency spectrum and waveform display.
 */
import {
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams,
  registerEffectRenderer,
} from "../effectProcessor";
import { safeNonNegativeDefault } from "@/utils/typeGuards";

// ============================================================================
// TYPES
// ============================================================================

export interface AudioSpectrumParams extends EvaluatedEffectParams {
  // Audio source (reference to audio analysis data)
  audioLayerId?: string;

  // Geometry
  startPointX: number; // Start X position
  startPointY: number; // Start Y position
  endPointX: number; // End X position
  endPointY: number; // End Y position
  pathType: "line" | "circle"; // Use line between points or circular path

  // Frequency range
  startFrequency: number; // Hz (default: 20)
  endFrequency: number; // Hz (default: 10000)
  frequencyBands: number; // Number of bars (default: 64)

  // Display
  maxHeight: number; // Maximum bar height in pixels (default: 100)
  displayMode: "digital" | "analog_lines" | "analog_dots";
  sideOptions: "side_a" | "side_b" | "side_a_b"; // Mirroring

  // Appearance
  thickness: number; // Line/bar width (default: 3)
  softness: number; // Edge softness (default: 0)
  insideColor: string; // Inner color (default: white)
  outsideColor: string; // Outer/gradient color (default: white)

  // Audio timing
  audioDuration: number; // Smoothing in ms (default: 50)
  audioOffset: number; // Time offset in ms (default: 0)
}

export interface AudioWaveformParams extends EvaluatedEffectParams {
  // Audio source
  audioLayerId?: string;

  // Geometry
  startPointX: number;
  startPointY: number;
  endPointX: number;
  endPointY: number;
  pathType: "line" | "circle";

  // Display
  displayedSamples: number; // How many samples to show (default: 200)
  maxHeight: number; // Maximum amplitude height (default: 100)
  displayMode: "digital" | "analog_lines" | "analog_dots";

  // Appearance
  thickness: number;
  softness: number;
  insideColor: string;
  outsideColor: string;

  // Audio timing
  audioDuration: number;
  audioOffset: number;
}

// ============================================================================
// AUDIO SPECTRUM EFFECT
// ============================================================================

/**
 * Audio Spectrum Effect
 *
 * Displays frequency content as vertical bars or continuous line.
 * Left = low frequencies (bass), Right = high frequencies (treble)
 */
export function renderAudioSpectrum(
  input: EffectStackResult,
  params: AudioSpectrumParams,
  frame: number,
  audioData?: {
    frequencyBands?: {
      sub: number[];
      bass: number[];
      lowMid: number[];
      mid: number[];
      highMid: number[];
      high: number[];
    };
    spectralFlux?: number[];
    frameCount: number;
  },
): EffectStackResult {
  const { canvas, ctx } = createMatchingCanvas(input.canvas);

  // Draw input first
  ctx.drawImage(input.canvas, 0, 0);

  // Get parameters with defaults
  const {
    startPointX = 0,
    startPointY = canvas.height / 2,
    endPointX = canvas.width,
    endPointY = canvas.height / 2,
    frequencyBands = 64,
    maxHeight = 100,
    displayMode = "digital",
    sideOptions = "side_a",
    thickness = 3,
    softness = 0,
    insideColor = "#ffffff",
    outsideColor = "#ffffff",
  } = params;

  // Generate spectrum data (use actual audio data if available, else simulate)
  const spectrumData = generateSpectrumData(frame, frequencyBands, audioData);

  // Calculate line vector
  const dx = endPointX - startPointX;
  const dy = endPointY - startPointY;
  const length = Math.sqrt(dx * dx + dy * dy);

  // Guard against zero-length line (start === end point)
  if (length === 0) {
    return { canvas, ctx };
  }

  const perpX = -dy / length;
  const perpY = dx / length;

  // Bar spacing
  const _bandWidth = length / frequencyBands;

  ctx.save();

  // Apply softness as blur
  if (softness > 0) {
    ctx.filter = `blur(${softness}px)`;
  }

  // Render each frequency band
  for (let i = 0; i < frequencyBands; i++) {
    const t = (i + 0.5) / frequencyBands;
    const x = startPointX + dx * t;
    const y = startPointY + dy * t;
    const amplitude = spectrumData[i];
    const barHeight = amplitude * maxHeight;

    // Create gradient for bar
    const gradient = ctx.createLinearGradient(
      x,
      y,
      x + perpX * barHeight,
      y + perpY * barHeight,
    );
    gradient.addColorStop(0, insideColor);
    gradient.addColorStop(1, outsideColor);
    ctx.fillStyle = gradient;
    ctx.strokeStyle = gradient;
    ctx.lineWidth = thickness;

    if (displayMode === "digital") {
      // Digital: segmented bars
      const segments = Math.ceil(barHeight / 4);
      for (let s = 0; s < segments; s++) {
        const segY = s * 4;
        if (segY < barHeight) {
          ctx.fillRect(
            x - thickness / 2 + perpX * segY,
            y + perpY * segY,
            thickness,
            3,
          );
          // Mirror if side_a_b
          if (sideOptions === "side_a_b" || sideOptions === "side_b") {
            ctx.fillRect(
              x - thickness / 2 - perpX * segY,
              y - perpY * segY,
              thickness,
              3,
            );
          }
        }
      }
    } else if (displayMode === "analog_lines") {
      // Analog lines: continuous
      ctx.beginPath();
      ctx.moveTo(x, y);
      ctx.lineTo(x + perpX * barHeight, y + perpY * barHeight);
      ctx.stroke();

      if (sideOptions === "side_a_b" || sideOptions === "side_b") {
        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.lineTo(x - perpX * barHeight, y - perpY * barHeight);
        ctx.stroke();
      }
    } else {
      // Analog dots
      const dotSpacing = 4;
      const dots = Math.ceil(barHeight / dotSpacing);
      for (let d = 0; d < dots; d++) {
        const dotY = d * dotSpacing;
        ctx.beginPath();
        ctx.arc(
          x + perpX * dotY,
          y + perpY * dotY,
          thickness / 2,
          0,
          Math.PI * 2,
        );
        ctx.fill();

        if (sideOptions === "side_a_b" || sideOptions === "side_b") {
          ctx.beginPath();
          ctx.arc(
            x - perpX * dotY,
            y - perpY * dotY,
            thickness / 2,
            0,
            Math.PI * 2,
          );
          ctx.fill();
        }
      }
    }
  }

  ctx.restore();

  return { canvas, ctx };
}

/**
 * Generate spectrum data from audio analysis or simulate
 */
function generateSpectrumData(
  frame: number,
  bands: number,
  audioData?: {
    frequencyBands?: {
      sub: number[];
      bass: number[];
      lowMid: number[];
      mid: number[];
      highMid: number[];
      high: number[];
    };
    frameCount: number;
  },
): number[] {
  const spectrum: number[] = new Array(bands).fill(0);

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const audioDataFrequencyBands = (audioData != null && typeof audioData === "object" && "frequencyBands" in audioData && audioData.frequencyBands != null && typeof audioData.frequencyBands === "object") ? audioData.frequencyBands : undefined;
  const audioDataFrameCount = (audioData != null && typeof audioData === "object" && "frameCount" in audioData && typeof audioData.frameCount === "number") ? audioData.frameCount : undefined;
  if (audioDataFrequencyBands != null && audioDataFrameCount != null && frame < audioDataFrameCount) {
    // Use real audio data
    const { sub, bass, lowMid, mid, highMid, high } = audioDataFrequencyBands;

    // Map frequency bands to spectrum
    // sub: 0-5%, bass: 5-15%, lowMid: 15-30%, mid: 30-50%, highMid: 50-70%, high: 70-100%
    for (let i = 0; i < bands; i++) {
      const t = i / bands;
      let value = 0;

      // Type proof: audio frequency values ∈ number | undefined → number (≥ 0, amplitude)
      if (t < 0.05) {
        value = safeNonNegativeDefault(sub[frame], 0, "sub[frame]");
      } else if (t < 0.15) {
        value = safeNonNegativeDefault(bass[frame], 0, "bass[frame]");
      } else if (t < 0.3) {
        value = safeNonNegativeDefault(lowMid[frame], 0, "lowMid[frame]");
      } else if (t < 0.5) {
        value = safeNonNegativeDefault(mid[frame], 0, "mid[frame]");
      } else if (t < 0.7) {
        value = safeNonNegativeDefault(highMid[frame], 0, "highMid[frame]");
      } else {
        value = safeNonNegativeDefault(high[frame], 0, "high[frame]");
      }

      // Add some variation within bands
      const variation = Math.sin(i * 0.5 + frame * 0.1) * 0.1 + 0.9;
      spectrum[i] = Math.min(1, value * variation);
    }
  } else {
    // Simulate spectrum when no audio data
    for (let i = 0; i < bands; i++) {
      const t = i / bands;
      // Create a pleasing default visualization
      const baseFreq = 0.1 + t * 0.05;
      const phase = frame * baseFreq;
      const decay = 1 - t * 0.5; // Higher frequencies lower amplitude
      spectrum[i] = (Math.sin(phase) * 0.5 + 0.5) * decay * 0.6;
    }
  }

  return spectrum;
}

// ============================================================================
// AUDIO WAVEFORM EFFECT
// ============================================================================

/**
 * Audio Waveform Effect
 *
 * Displays amplitude over time as oscillating line.
 * Shows the classic "sound wave" visualization.
 */
export function renderAudioWaveform(
  input: EffectStackResult,
  params: AudioWaveformParams,
  frame: number,
  audioData?: {
    amplitudeEnvelope?: number[];
    rmsEnergy?: number[];
    frameCount: number;
  },
): EffectStackResult {
  const { canvas, ctx } = createMatchingCanvas(input.canvas);

  // Draw input first
  ctx.drawImage(input.canvas, 0, 0);

  // Get parameters with defaults
  const {
    startPointX = 0,
    startPointY = canvas.height / 2,
    endPointX = canvas.width,
    endPointY = canvas.height / 2,
    displayedSamples = 200,
    maxHeight = 100,
    displayMode = "analog_lines",
    thickness = 2,
    softness = 0,
    insideColor = "#ffffff",
    outsideColor = "#ffffff",
  } = params;

  // Generate waveform data
  const waveformData = generateWaveformData(frame, displayedSamples, audioData);

  // Calculate line vector
  const dx = endPointX - startPointX;
  const dy = endPointY - startPointY;
  const length = Math.sqrt(dx * dx + dy * dy);

  // Guard against zero-length line (start === end point)
  if (length === 0) {
    return { canvas, ctx };
  }

  const perpX = -dy / length;
  const perpY = dx / length;

  ctx.save();

  if (softness > 0) {
    ctx.filter = `blur(${softness}px)`;
  }

  // Create gradient
  const gradient = ctx.createLinearGradient(
    startPointX + perpX * maxHeight,
    startPointY + perpY * maxHeight,
    startPointX - perpX * maxHeight,
    startPointY - perpY * maxHeight,
  );
  gradient.addColorStop(0, outsideColor);
  gradient.addColorStop(0.5, insideColor);
  gradient.addColorStop(1, outsideColor);

  ctx.strokeStyle = gradient;
  ctx.fillStyle = gradient;
  ctx.lineWidth = thickness;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";

  if (displayMode === "analog_lines") {
    // Draw continuous waveform line
    ctx.beginPath();

    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;

      const px = x + perpX * offset;
      const py = y + perpY * offset;

      if (i === 0) {
        ctx.moveTo(px, py);
      } else {
        ctx.lineTo(px, py);
      }
    }

    ctx.stroke();
  } else if (displayMode === "digital") {
    // Digital: vertical lines at each sample
    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;

      ctx.beginPath();
      ctx.moveTo(x - perpX * offset, y - perpY * offset);
      ctx.lineTo(x + perpX * offset, y + perpY * offset);
      ctx.stroke();
    }
  } else {
    // Analog dots
    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;

      ctx.beginPath();
      ctx.arc(
        x + perpX * offset,
        y + perpY * offset,
        thickness,
        0,
        Math.PI * 2,
      );
      ctx.fill();
    }
  }

  ctx.restore();

  return { canvas, ctx };
}

/**
 * Generate waveform data centered around current frame
 */
function generateWaveformData(
  frame: number,
  samples: number,
  audioData?: {
    amplitudeEnvelope?: number[];
    rmsEnergy?: number[];
    frameCount: number;
  },
): number[] {
  const waveform: number[] = new Array(samples).fill(0);
  const halfSamples = Math.floor(samples / 2);

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const audioDataAmplitudeEnvelope = (audioData != null && typeof audioData === "object" && "amplitudeEnvelope" in audioData && audioData.amplitudeEnvelope != null && Array.isArray(audioData.amplitudeEnvelope)) ? audioData.amplitudeEnvelope : undefined;
  const audioDataFrameCount = (audioData != null && typeof audioData === "object" && "frameCount" in audioData && typeof audioData.frameCount === "number") ? audioData.frameCount : undefined;
  if (audioDataAmplitudeEnvelope != null && audioDataFrameCount != null && frame < audioDataFrameCount) {
    // Use real audio data, centered on current frame
    for (let i = 0; i < samples; i++) {
      const sampleFrame = frame - halfSamples + i;
      if (
        sampleFrame >= 0 &&
        sampleFrame < audioData.amplitudeEnvelope.length
      ) {
        // Convert amplitude (0-1) to waveform (-1 to 1) with oscillation
        const amp = audioData.amplitudeEnvelope[sampleFrame];
        const oscillation = Math.sin(sampleFrame * 0.5); // Add oscillation
        waveform[i] = amp * oscillation;
      }
    }
  } else {
    // Simulate waveform when no audio data
    for (let i = 0; i < samples; i++) {
      const _t = i / samples;
      // Create pleasing sine wave pattern
      const freq1 = Math.sin((frame + i) * 0.2) * 0.4;
      const freq2 = Math.sin((frame + i) * 0.07) * 0.3;
      const freq3 = Math.sin((frame + i) * 0.02) * 0.2;
      waveform[i] = freq1 + freq2 + freq3;
    }
  }

  return waveform;
}

// ============================================================================
// EFFECT REGISTRATION
// ============================================================================

/**
 * Register audio visualizer effects with the effect processor
 */
export function registerAudioVisualizerEffects(): void {
  // Audio Spectrum Effect
  registerEffectRenderer(
    "audio-spectrum",
    (input: EffectStackResult, params: EvaluatedEffectParams) => {
      // AudioSpectrumParams extends EvaluatedEffectParams, so direct cast is safe
      return renderAudioSpectrum(
        input,
        params as AudioSpectrumParams,
        0,
      );
    },
  );

  // Audio Waveform Effect
  registerEffectRenderer(
    "audio-waveform",
    (input: EffectStackResult, params: EvaluatedEffectParams) => {
      // AudioWaveformParams extends EvaluatedEffectParams, so direct cast is safe
      return renderAudioWaveform(
        input,
        params as AudioWaveformParams,
        0,
      );
    },
  );
}

// ============================================================================
// DEFAULT PARAMETERS
// ============================================================================

export const AUDIO_SPECTRUM_DEFAULTS: AudioSpectrumParams = {
  effectId: "audio-spectrum",
  enabled: true,
  startPointX: 0,
  startPointY: 360,
  endPointX: 1920,
  endPointY: 360,
  pathType: "line",
  startFrequency: 20,
  endFrequency: 10000,
  frequencyBands: 64,
  maxHeight: 100,
  displayMode: "digital",
  sideOptions: "side_a",
  thickness: 3,
  softness: 0,
  insideColor: "#ffffff",
  outsideColor: "#4a90d9",
  audioDuration: 50,
  audioOffset: 0,
};

export const AUDIO_WAVEFORM_DEFAULTS: AudioWaveformParams = {
  effectId: "audio-waveform",
  enabled: true,
  startPointX: 0,
  startPointY: 360,
  endPointX: 1920,
  endPointY: 360,
  pathType: "line",
  displayedSamples: 200,
  maxHeight: 100,
  displayMode: "analog_lines",
  thickness: 2,
  softness: 0,
  insideColor: "#ffffff",
  outsideColor: "#ffffff",
  audioDuration: 50,
  audioOffset: 0,
};
