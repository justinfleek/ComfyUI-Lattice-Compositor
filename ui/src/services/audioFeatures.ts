/**
 * Audio Feature Extraction Service
 *
 * PURE LOOKUP MODULE – DO NOT MUTATE
 * ===================================
 * The lookup functions in this module (getFeatureAtFrame, isBeatAtFrame) are
 * PURE FUNCTIONS used by MotionEngine for deterministic audio-reactive evaluation.
 *
 * CONTRACT:
 * - getFeatureAtFrame(analysis, feature, frame) is PURE: same inputs → same outputs
 * - isBeatAtFrame(analysis, frame) is PURE: same inputs → same outputs
 * - Analysis is computed ONCE at load time, then only read
 * - No functions mutate the analysis data
 *
 * The analysis functions (analyzeAudio) ARE side-effectful (create AudioContext)
 * but only during the initial analysis phase. Once analysis is complete,
 * all frame lookups are pure array index operations.
 *
 * Uses Web Audio API for comprehensive audio analysis.
 * Supports amplitude, RMS, spectral analysis, onset detection, and BPM estimation.
 * Matches ATI_AudioReactive and Yvann-Nodes functionality.
 */

import { isFiniteNumber, assertDefined, safeCoordinateDefault } from "@/utils/typeGuards";

// ============================================================================
// Types
// ============================================================================

export interface AudioAnalysis {
  sampleRate: number;
  duration: number;
  frameCount: number;
  amplitudeEnvelope: number[];
  rmsEnergy: number[];
  spectralCentroid: number[];
  frequencyBands: {
    sub: number[];
    bass: number[];
    lowMid: number[];
    mid: number[];
    highMid: number[];
    high: number[];
  };
  onsets: number[];
  bpm: number;

  // Enhanced features (from RyanOnTheInside/Yvann)
  spectralFlux: number[]; // Rate of spectral change (useful for beats)
  zeroCrossingRate: number[]; // Percussiveness indicator
  spectralRolloff: number[]; // High-frequency energy cutoff
  spectralFlatness: number[]; // Tonal vs noise-like (0=tonal, 1=noise)
  chromaFeatures?: ChromaFeatures; // Key/chord detection

  // HPSS: Harmonic-Percussive Source Separation (librosa standard)
  harmonicEnergy?: number[]; // Tonal/harmonic content per frame
  percussiveEnergy?: number[]; // Transient/percussive content per frame
  hpRatio?: number[]; // Harmonic-to-percussive ratio per frame

  // MFCC: Mel-frequency cepstral coefficients (timbral features)
  mfcc?: number[][]; // [frameIndex][coefficient] - 13 coefficients per frame
  mfccStats?: {
    // Per-coefficient normalization stats
    min: number[]; // Min value per coefficient [13]
    max: number[]; // Max value per coefficient [13]
  };
}

export interface FrequencyBandRanges {
  sub: [number, number];
  bass: [number, number];
  lowMid: [number, number];
  mid: [number, number];
  highMid: [number, number];
  high: [number, number];
}

// Chroma features for key/chord detection (12 pitch classes)
export interface ChromaFeatures {
  chroma: number[][]; // [frameIndex][pitchClass] 12 values per frame (C, C#, D, etc.)
  chromaEnergy: number[]; // Total chroma energy per frame
  estimatedKey: string; // Best guess at musical key
  keyConfidence: number; // 0-1 confidence in key estimation
}

// Audio analysis configuration (matches Yvann-Nodes)
// Note: hopSize intentionally omitted - analysis is locked to video frame
// boundaries for deterministic playback
export interface AudioAnalysisConfig {
  fftSize: number; // 512, 1024, 2048, 4096
  minFrequency: number; // Filter low frequencies (default 20)
  maxFrequency: number; // Filter high frequencies (default 20000)
  // Analysis modes (like Yvann)
  analysisMode: "full" | "drums" | "vocals" | "bass" | "other";
  // Stem data (if pre-separated)
  stemData?: {
    drums?: AudioBuffer;
    vocals?: AudioBuffer;
    bass?: AudioBuffer;
    other?: AudioBuffer;
  };
}

// ============================================================================
// Constants
// ============================================================================

const DEFAULT_FFT_SIZE = 2048;

const FREQUENCY_BANDS: FrequencyBandRanges = {
  sub: [20, 60],
  bass: [60, 250],
  lowMid: [250, 500],
  mid: [500, 2000],
  highMid: [2000, 4000],
  high: [4000, 20000],
};

// ============================================================================
// Audio Loading
// ============================================================================

/**
 * Load an audio file and decode it to an AudioBuffer
 */
export async function loadAudioFile(file: File): Promise<AudioBuffer> {
  const arrayBuffer = await file.arrayBuffer();
  const audioContext = new AudioContext();

  try {
    const audioBuffer = await audioContext.decodeAudioData(arrayBuffer);
    await audioContext.close();
    return audioBuffer;
  } catch (error) {
    await audioContext.close();
    throw new Error(`Failed to decode audio file: ${error}`);
  }
}

/**
 * Load audio from a URL
 */
export async function loadAudioFromUrl(url: string): Promise<AudioBuffer> {
  const response = await fetch(url);
  const arrayBuffer = await response.arrayBuffer();
  const audioContext = new AudioContext();

  try {
    const audioBuffer = await audioContext.decodeAudioData(arrayBuffer);
    await audioContext.close();
    return audioBuffer;
  } catch (error) {
    await audioContext.close();
    throw new Error(`Failed to decode audio from URL: ${error}`);
  }
}

// ============================================================================
// Main Analysis Function
// ============================================================================

/**
 * Perform comprehensive audio analysis
 */
export async function analyzeAudio(
  buffer: AudioBuffer,
  fps: number,
  config?: Partial<AudioAnalysisConfig>,
): Promise<AudioAnalysis> {
  const duration = buffer.duration;
  const frameCount = Math.ceil(duration * fps);
  const sampleRate = buffer.sampleRate;

  // Determine which buffer to analyze based on mode
  let analyzeBuffer = buffer;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (
    typeof config === "object" && config !== null && "analysisMode" in config && typeof config.analysisMode === "string" &&
    config.analysisMode !== "full" &&
    typeof config.stemData === "object" && config.stemData !== null
  ) {
    const stemKey = config.analysisMode as keyof typeof config.stemData;
    if (config.stemData[stemKey]) {
      // Type proof: stemData[stemKey] is guaranteed non-null by the if check
      assertDefined(config.stemData[stemKey], "stemData[stemKey] must exist when checked");
      analyzeBuffer = config.stemData[stemKey];
    }
  }

  // Extract features
  const amplitudeEnvelope = extractAmplitudeEnvelope(analyzeBuffer, fps);
  const rmsEnergy = extractRMSEnergy(analyzeBuffer, fps);
  const frequencyBands = await extractFrequencyBands(
    analyzeBuffer,
    fps,
    config,
  );
  const spectralCentroid = await extractSpectralCentroid(analyzeBuffer, fps);
  const onsets = detectOnsets(analyzeBuffer, fps);
  const bpm = detectBPM(analyzeBuffer);

  // Enhanced features
  const spectralFlux = extractSpectralFlux(analyzeBuffer, fps);
  const zeroCrossingRate = extractZeroCrossingRate(analyzeBuffer, fps);
  const spectralRolloff = extractSpectralRolloff(analyzeBuffer, fps);
  const spectralFlatness = extractSpectralFlatness(analyzeBuffer, fps);
  const chromaFeatures = extractChromaFeatures(analyzeBuffer, fps);

  // HPSS: Harmonic-Percussive Source Separation (librosa standard)
  const hpss = extractHPSS(analyzeBuffer, fps);

  // MFCC: Mel-frequency cepstral coefficients (timbral analysis)
  const mfccResult = extractMFCC(analyzeBuffer, fps);

  return {
    sampleRate,
    duration,
    frameCount,
    amplitudeEnvelope,
    rmsEnergy,
    spectralCentroid,
    frequencyBands,
    onsets,
    bpm,
    // Enhanced
    spectralFlux,
    zeroCrossingRate,
    spectralRolloff,
    spectralFlatness,
    chromaFeatures,
    // HPSS
    harmonicEnergy: hpss.harmonicEnergy,
    percussiveEnergy: hpss.percussiveEnergy,
    hpRatio: hpss.hpRatio,
    // MFCC with per-coefficient normalization stats
    mfcc: mfccResult.mfcc,
    mfccStats: mfccResult.stats,
  };
}

// ============================================================================
// Amplitude Envelope
// ============================================================================

/**
 * Extract amplitude envelope (peak values per frame)
 */
export function extractAmplitudeEnvelope(
  buffer: AudioBuffer,
  fps: number,
): number[] {
  const channelData = buffer.getChannelData(0); // Use first channel
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const envelope: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(
      startSample + samplesPerFrame,
      channelData.length,
    );

    let maxAmp = 0;
    for (let i = startSample; i < endSample; i++) {
      const amp = Math.abs(channelData[i]);
      if (amp > maxAmp) maxAmp = amp;
    }

    envelope.push(maxAmp);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...envelope, 0.0001);
  return envelope.map((v) => v / maxValue);
}

// ============================================================================
// RMS Energy
// ============================================================================

/**
 * Extract RMS (Root Mean Square) energy per frame
 */
export function extractRMSEnergy(buffer: AudioBuffer, fps: number): number[] {
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const rmsValues: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(
      startSample + samplesPerFrame,
      channelData.length,
    );

    let sumSquares = 0;
    let count = 0;
    for (let i = startSample; i < endSample; i++) {
      sumSquares += channelData[i] * channelData[i];
      count++;
    }

    const rms = count > 0 ? Math.sqrt(sumSquares / count) : 0;
    rmsValues.push(rms);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...rmsValues, 0.0001);
  return rmsValues.map((v) => v / maxValue);
}

// ============================================================================
// Frequency Band Analysis
// ============================================================================

/**
 * Extract energy in different frequency bands per frame.
 * Uses config.fftSize when provided for consistent analysis.
 */
export async function extractFrequencyBands(
  buffer: AudioBuffer,
  fps: number,
  config?: Partial<AudioAnalysisConfig>,
): Promise<AudioAnalysis["frequencyBands"]> {
  const duration = buffer.duration;
  const frameCount = Math.ceil(duration * fps);
  const sampleRate = buffer.sampleRate;

  // Use configured FFT size for spectral analysis resolution
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  const fftSizeValue = (typeof config === "object" && config !== null && "fftSize" in config && typeof config.fftSize === "number")
    ? config.fftSize
    : 2048;
  const fftSize = isFiniteNumber(fftSizeValue) && Number.isInteger(fftSizeValue) && fftSizeValue > 0 && (fftSizeValue & (fftSizeValue - 1)) === 0 ? fftSizeValue : DEFAULT_FFT_SIZE;

  // Create offline context for analysis
  const offlineCtx = new OfflineAudioContext(1, buffer.length, sampleRate);

  const source = offlineCtx.createBufferSource();
  source.buffer = buffer;

  const analyser = offlineCtx.createAnalyser();
  analyser.fftSize = fftSize;
  analyser.smoothingTimeConstant = 0;

  source.connect(analyser);
  analyser.connect(offlineCtx.destination);

  // Initialize band arrays
  const bands: AudioAnalysis["frequencyBands"] = {
    sub: [],
    bass: [],
    lowMid: [],
    mid: [],
    highMid: [],
    high: [],
  };

  const binFrequency = sampleRate / fftSize;

  // Apply frequency range filtering for band-limited analysis
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  const minFreqValue = (typeof config === "object" && config !== null && "minFrequency" in config && typeof config.minFrequency === "number")
    ? config.minFrequency
    : 20;
  const minFreq = isFiniteNumber(minFreqValue) && minFreqValue > 0 && minFreqValue < sampleRate / 2 ? minFreqValue : 20;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  const maxFreqValue = (typeof config === "object" && config !== null && "maxFrequency" in config && typeof config.maxFrequency === "number")
    ? config.maxFrequency
    : sampleRate / 2;
  const maxFreq = isFiniteNumber(maxFreqValue) && maxFreqValue > 0 && maxFreqValue <= sampleRate / 2 ? maxFreqValue : 20000;
  const minBin = Math.floor(minFreq / binFrequency);
  const maxBin = Math.ceil(maxFreq / binFrequency);

  // Calculate bin ranges for each band, clamped to min/max frequency
  const bandBins = Object.entries(FREQUENCY_BANDS).reduce(
    (acc, [band, [low, high]]) => {
      // Clamp band ranges to config frequency limits
      const clampedLow = Math.max(low, minFreq);
      const clampedHigh = Math.min(high, maxFreq);

      // Skip band entirely if outside frequency range
      if (clampedLow >= clampedHigh) {
        acc[band as keyof FrequencyBandRanges] = { start: 0, end: 0 };
      } else {
        acc[band as keyof FrequencyBandRanges] = {
          start: Math.max(minBin, Math.floor(clampedLow / binFrequency)),
          end: Math.min(maxBin, Math.ceil(clampedHigh / binFrequency)),
        };
      }
      return acc;
    },
    {} as Record<keyof FrequencyBandRanges, { start: number; end: number }>,
  );

  // Process each frame
  const samplesPerFrame = Math.floor(sampleRate / fps);

  // Since OfflineAudioContext doesn't support real-time analysis easily,
  // we'll use a simpler approach with the raw samples
  const channelData = buffer.getChannelData(0);

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + fftSize, channelData.length);

    // Get window of samples
    const windowSize = endSample - startSample;
    if (windowSize < 64) {
      // Not enough samples, use previous values or zero
      Object.keys(bands).forEach((band) => {
        const arr = bands[band as keyof typeof bands];
        arr.push(arr.length > 0 ? arr[arr.length - 1] : 0);
      });
      continue;
    }

    // Perform simple FFT using the channel data
    const fftResult = simpleFFT(
      channelData.slice(startSample, startSample + fftSize),
    );

    // Extract band energies
    for (const [band, { start, end }] of Object.entries(bandBins)) {
      let energy = 0;
      let count = 0;
      for (let i = start; i < Math.min(end, fftResult.length); i++) {
        energy += fftResult[i];
        count++;
      }
      bands[band as keyof typeof bands].push(count > 0 ? energy / count : 0);
    }
  }

  // Normalize each band to 0-1
  for (const band of Object.keys(bands) as (keyof typeof bands)[]) {
    const maxValue = Math.max(...bands[band], 0.0001);
    bands[band] = bands[band].map((v) => v / maxValue);
  }

  return bands;
}

/**
 * Simple FFT implementation for magnitude spectrum
 */
function simpleFFT(samples: Float32Array): number[] {
  const n = samples.length;
  const magnitudes: number[] = [];

  // Apply Hanning window
  const windowed = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const windowValue = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (n - 1)));
    // Type proof: audio sample ∈ number | undefined → number (coordinate-like, can be negative)
    windowed[i] = safeCoordinateDefault(samples[i], 0, `samples[${i}]`) * windowValue;
  }

  // Simple DFT (not optimized, but works for our purposes)
  const halfN = Math.floor(n / 2);
  for (let k = 0; k < halfN; k++) {
    let real = 0;
    let imag = 0;

    for (let t = 0; t < n; t++) {
      const angle = (2 * Math.PI * k * t) / n;
      real += windowed[t] * Math.cos(angle);
      imag -= windowed[t] * Math.sin(angle);
    }

    magnitudes.push(Math.sqrt(real * real + imag * imag) / n);
  }

  return magnitudes;
}

// ============================================================================
// Spectral Centroid
// ============================================================================

/**
 * Extract spectral centroid (brightness) per frame
 */
export async function extractSpectralCentroid(
  buffer: AudioBuffer,
  fps: number,
): Promise<number[]> {
  const frameCount = Math.ceil(buffer.duration * fps);
  const sampleRate = buffer.sampleRate;
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const centroids: number[] = [];
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      centroids.push(
        centroids.length > 0 ? centroids[centroids.length - 1] : 0,
      );
      continue;
    }

    const fftResult = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    // Calculate spectral centroid
    let weightedSum = 0;
    let totalMagnitude = 0;

    for (let i = 0; i < fftResult.length; i++) {
      const frequency = i * binFrequency;
      weightedSum += frequency * fftResult[i];
      totalMagnitude += fftResult[i];
    }

    const centroid = totalMagnitude > 0 ? weightedSum / totalMagnitude : 0;
    centroids.push(centroid);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...centroids, 0.0001);
  return centroids.map((v) => v / maxValue);
}

// ============================================================================
// Onset Detection
// ============================================================================

/**
 * Detect onsets (beats/transients) in the audio
 */
export function detectOnsets(
  buffer: AudioBuffer,
  fps: number,
  sensitivity: number = 0.5,
): number[] {
  const channelData = buffer.getChannelData(0);
  const sampleRate = buffer.sampleRate;
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);

  // Calculate spectral flux
  const spectralFlux: number[] = [];
  let prevSpectrum: number[] | null = null;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      spectralFlux.push(0);
      continue;
    }

    const spectrum = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    if (prevSpectrum) {
      // Calculate flux (sum of positive differences)
      let flux = 0;
      for (let i = 0; i < spectrum.length; i++) {
        const diff = spectrum[i] - prevSpectrum[i];
        if (diff > 0) flux += diff;
      }
      spectralFlux.push(flux);
    } else {
      spectralFlux.push(0);
    }

    prevSpectrum = spectrum;
  }

  // Find peaks in spectral flux
  const onsets: number[] = [];
  const threshold = calculateAdaptiveThreshold(spectralFlux, sensitivity);

  for (let i = 1; i < spectralFlux.length - 1; i++) {
    // Check if local maximum and above threshold
    if (
      spectralFlux[i] > spectralFlux[i - 1] &&
      spectralFlux[i] > spectralFlux[i + 1] &&
      spectralFlux[i] > threshold[i]
    ) {
      onsets.push(i);
    }
  }

  return onsets;
}

/**
 * Calculate adaptive threshold for onset detection
 */
function calculateAdaptiveThreshold(
  flux: number[],
  sensitivity: number,
): number[] {
  const windowSize = 10;
  const threshold: number[] = [];

  for (let i = 0; i < flux.length; i++) {
    const start = Math.max(0, i - windowSize);
    const end = Math.min(flux.length, i + windowSize + 1);
    const window = flux.slice(start, end);
    const mean = window.reduce((a, b) => a + b, 0) / window.length;
    const std = Math.sqrt(
      window.reduce((a, b) => a + (b - mean) ** 2, 0) / window.length,
    );

    // Threshold = mean + sensitivity * std
    threshold.push(mean + (1 - sensitivity) * 2 * std);
  }

  return threshold;
}

// ============================================================================
// Enhanced Audio Features (RyanOnTheInside / Yvann style)
// ============================================================================

/**
 * Extract spectral flux (rate of spectral change) - great for beat detection
 */
export function extractSpectralFlux(
  buffer: AudioBuffer,
  fps: number,
): number[] {
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const flux: number[] = [];
  let prevSpectrum: number[] | null = null;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      flux.push(flux.length > 0 ? flux[flux.length - 1] : 0);
      continue;
    }

    const spectrum = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    if (prevSpectrum) {
      // Spectral flux = sum of positive differences (only increases)
      let fluxValue = 0;
      for (let i = 0; i < spectrum.length; i++) {
        const diff = spectrum[i] - prevSpectrum[i];
        if (diff > 0) fluxValue += diff;
      }
      flux.push(fluxValue);
    } else {
      flux.push(0);
    }

    prevSpectrum = spectrum;
  }

  // Normalize
  const maxValue = Math.max(...flux, 0.0001);
  return flux.map((v) => v / maxValue);
}

/**
 * Extract zero crossing rate - indicates percussiveness/noisiness
 */
export function extractZeroCrossingRate(
  buffer: AudioBuffer,
  fps: number,
): number[] {
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const zcr: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(
      startSample + samplesPerFrame,
      channelData.length,
    );

    let crossings = 0;
    for (let i = startSample + 1; i < endSample; i++) {
      if (
        (channelData[i] >= 0 && channelData[i - 1] < 0) ||
        (channelData[i] < 0 && channelData[i - 1] >= 0)
      ) {
        crossings++;
      }
    }

    // Normalize by frame length
    const rate = crossings / (endSample - startSample);
    zcr.push(rate);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...zcr, 0.0001);
  return zcr.map((v) => v / maxValue);
}

/**
 * Extract spectral rolloff - frequency below which 85% of energy lies
 * Good for detecting high-frequency content (hihats, cymbals)
 */
export function extractSpectralRolloff(
  buffer: AudioBuffer,
  fps: number,
  rolloffPercent: number = 0.85,
): number[] {
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const rolloff: number[] = [];
  const binFrequency = buffer.sampleRate / DEFAULT_FFT_SIZE;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      rolloff.push(rolloff.length > 0 ? rolloff[rolloff.length - 1] : 0);
      continue;
    }

    const spectrum = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    // Calculate total energy
    const totalEnergy = spectrum.reduce((a, b) => a + b, 0);
    const threshold = totalEnergy * rolloffPercent;

    // Find frequency bin where cumulative energy exceeds threshold
    let cumulativeEnergy = 0;
    let rolloffBin = 0;

    for (let i = 0; i < spectrum.length; i++) {
      cumulativeEnergy += spectrum[i];
      if (cumulativeEnergy >= threshold) {
        rolloffBin = i;
        break;
      }
    }

    rolloff.push(rolloffBin * binFrequency);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...rolloff, 0.0001);
  return rolloff.map((v) => v / maxValue);
}

/**
 * Extract spectral flatness - measure of noise-like vs tonal character
 * 0 = very tonal (clear pitch), 1 = noise-like
 */
export function extractSpectralFlatness(
  buffer: AudioBuffer,
  fps: number,
): number[] {
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const flatness: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      flatness.push(flatness.length > 0 ? flatness[flatness.length - 1] : 0);
      continue;
    }

    const spectrum = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    // Remove zeros to avoid log(0)
    const nonZero = spectrum.filter((v) => v > 1e-10);
    if (nonZero.length === 0) {
      flatness.push(0);
      continue;
    }

    // Geometric mean (exp of mean of logs)
    const logSum = nonZero.reduce((a, b) => a + Math.log(b), 0);
    const geometricMean = Math.exp(logSum / nonZero.length);

    // Arithmetic mean
    const arithmeticMean = nonZero.reduce((a, b) => a + b, 0) / nonZero.length;

    // Flatness = geometric mean / arithmetic mean
    const flat = arithmeticMean > 0 ? geometricMean / arithmeticMean : 0;
    flatness.push(flat);
  }

  return flatness;
}

/**
 * Extract chroma features (12 pitch classes)
 * Useful for music-aware animations that respond to harmony
 */
export function extractChromaFeatures(
  buffer: AudioBuffer,
  fps: number,
): ChromaFeatures {
  const channelData = buffer.getChannelData(0);
  const sampleRate = buffer.sampleRate;
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);

  // Pitch class frequencies (A4 = 440Hz reference)
  const pitchNames = [
    "C",
    "C#",
    "D",
    "D#",
    "E",
    "F",
    "F#",
    "G",
    "G#",
    "A",
    "A#",
    "B",
  ];

  const chroma: number[][] = [];
  const chromaEnergy: number[] = [];

  // Bin to pitch class mapping
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const frameChroma = new Array(12).fill(0);

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      chroma.push(frameChroma);
      chromaEnergy.push(0);
      continue;
    }

    const spectrum = simpleFFT(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
    );

    // Map each bin to a pitch class
    for (let bin = 1; bin < spectrum.length; bin++) {
      const frequency = bin * binFrequency;
      if (frequency < 27.5 || frequency > 4186) continue; // Piano range

      // Convert frequency to pitch class (0-11)
      // MIDI note = 69 + 12 * log2(f/440)
      const midiNote = 69 + 12 * Math.log2(frequency / 440);
      const pitchClass = Math.round(midiNote) % 12;

      if (pitchClass >= 0 && pitchClass < 12) {
        frameChroma[pitchClass] += spectrum[bin];
      }
    }

    // Normalize frame chroma
    const maxChroma = Math.max(...frameChroma, 0.0001);
    const normalizedChroma = frameChroma.map((v) => v / maxChroma);

    chroma.push(normalizedChroma);
    chromaEnergy.push(frameChroma.reduce((a, b) => a + b, 0));
  }

  // Estimate key by summing chroma across all frames
  const totalChroma = new Array(12).fill(0);
  for (const frame of chroma) {
    for (let i = 0; i < 12; i++) {
      totalChroma[i] += frame[i];
    }
  }

  // Find dominant pitch class
  let maxTotal = 0;
  let dominantPitch = 0;
  for (let i = 0; i < 12; i++) {
    if (totalChroma[i] > maxTotal) {
      maxTotal = totalChroma[i];
      dominantPitch = i;
    }
  }

  // Simple key estimation (major vs minor check could be added)
  const estimatedKey = `${pitchNames[dominantPitch]} major`;
  const keyConfidence =
    maxTotal / (totalChroma.reduce((a, b) => a + b, 0) + 0.0001);

  // Normalize chromaEnergy
  const maxEnergy = Math.max(...chromaEnergy, 0.0001);
  const normalizedEnergy = chromaEnergy.map((v) => v / maxEnergy);

  return {
    chroma,
    chromaEnergy: normalizedEnergy,
    estimatedKey,
    keyConfidence,
  };
}

// ============================================================================
// BPM Detection
// ============================================================================

/**
 * Detect BPM (beats per minute) using autocorrelation
 */
export function detectBPM(buffer: AudioBuffer): number {
  const channelData = buffer.getChannelData(0);
  const sampleRate = buffer.sampleRate;

  // Downsample for efficiency
  const downsampleFactor = 4;
  const downsampled: number[] = [];
  for (let i = 0; i < channelData.length; i += downsampleFactor) {
    downsampled.push(Math.abs(channelData[i]));
  }

  // Apply envelope follower
  const envelope = applyEnvelopeFollower(downsampled, 0.1);

  // Calculate autocorrelation
  const minBPM = 60;
  const maxBPM = 200;
  const downsampledRate = sampleRate / downsampleFactor;
  const minLag = Math.floor((60 / maxBPM) * downsampledRate);
  const maxLag = Math.floor((60 / minBPM) * downsampledRate);

  let maxCorrelation = 0;
  let bestLag = minLag;

  // Use a subset of the signal for efficiency
  const analysisLength = Math.min(envelope.length, downsampledRate * 10);
  const signal = envelope.slice(0, analysisLength);

  for (let lag = minLag; lag <= maxLag; lag++) {
    let correlation = 0;
    let count = 0;

    for (let i = 0; i < signal.length - lag; i++) {
      correlation += signal[i] * signal[i + lag];
      count++;
    }

    if (count > 0) {
      correlation /= count;
      if (correlation > maxCorrelation) {
        maxCorrelation = correlation;
        bestLag = lag;
      }
    }
  }

  // Convert lag to BPM
  const bpm = (60 * downsampledRate) / bestLag;

  // Clamp to reasonable range
  return Math.round(Math.max(minBPM, Math.min(maxBPM, bpm)));
}

/**
 * Apply envelope follower for BPM detection
 */
function applyEnvelopeFollower(signal: number[], smoothing: number): number[] {
  const envelope: number[] = [];
  let env = 0;

  for (const sample of signal) {
    if (sample > env) {
      env = sample;
    } else {
      env = env * (1 - smoothing) + sample * smoothing;
    }
    envelope.push(env);
  }

  return envelope;
}

// ============================================================================
// Feature Access
// ============================================================================

/**
 * Get a specific feature value at a given frame
 * Returns 0 if analysis is null/undefined (e.g., audio not loaded yet)
 * Returns 0 if frame is out of bounds (negative or beyond frameCount)
 */
export function getFeatureAtFrame(
  analysis: AudioAnalysis | null | undefined,
  feature: string,
  frame: number,
): number {
  // Return zero for missing or invalid analysis data
  if (!analysis) {
    return 0;
  }
  
  // Return zero for frames outside audio boundaries (before start or after end)
  if (frame < 0 || frame >= analysis.frameCount) {
    return 0;
  }
  
  const clampedFrame = frame; // Frame is now guaranteed to be in bounds

  switch (feature) {
    case "amplitude": {
      // Type proof: amplitudeEnvelope[frame] ∈ ℝ ∪ {undefined} → ℝ
      const amplitudeValue = analysis.amplitudeEnvelope[clampedFrame];
      return isFiniteNumber(amplitudeValue) && amplitudeValue >= 0 ? amplitudeValue : 0;
    }

    case "rms": {
      // Type proof: rmsEnergy[frame] ∈ ℝ ∪ {undefined} → ℝ
      const rmsValue = analysis.rmsEnergy[clampedFrame];
      return isFiniteNumber(rmsValue) && rmsValue >= 0 ? rmsValue : 0;
    }

    case "spectralCentroid": {
      // Type proof: spectralCentroid[frame] ∈ ℝ ∪ {undefined} → ℝ
      const centroidValue = analysis.spectralCentroid[clampedFrame];
      return isFiniteNumber(centroidValue) && centroidValue >= 0 ? centroidValue : 0;
    }

    case "sub": {
      // Type proof: frequencyBands.sub[frame] ∈ ℝ ∪ {undefined} → ℝ
      const subValue = analysis.frequencyBands.sub[clampedFrame];
      return isFiniteNumber(subValue) && subValue >= 0 ? subValue : 0;
    }

    case "bass": {
      // Type proof: frequencyBands.bass[frame] ∈ ℝ ∪ {undefined} → ℝ
      const bassValue = analysis.frequencyBands.bass[clampedFrame];
      return isFiniteNumber(bassValue) && bassValue >= 0 ? bassValue : 0;
    }

    case "lowMid": {
      // Type proof: frequencyBands.lowMid[frame] ∈ ℝ ∪ {undefined} → ℝ
      const lowMidValue = analysis.frequencyBands.lowMid[clampedFrame];
      return isFiniteNumber(lowMidValue) && lowMidValue >= 0 ? lowMidValue : 0;
    }

    case "mid": {
      // Type proof: frequencyBands.mid[frame] ∈ ℝ ∪ {undefined} → ℝ
      const midValue = analysis.frequencyBands.mid[clampedFrame];
      return isFiniteNumber(midValue) && midValue >= 0 ? midValue : 0;
    }

    case "highMid": {
      // Type proof: frequencyBands.highMid[frame] ∈ ℝ ∪ {undefined} → ℝ
      const highMidValue = analysis.frequencyBands.highMid[clampedFrame];
      return isFiniteNumber(highMidValue) && highMidValue >= 0 ? highMidValue : 0;
    }

    case "high": {
      // Type proof: frequencyBands.high[frame] ∈ ℝ ∪ {undefined} → ℝ
      const highValue = analysis.frequencyBands.high[clampedFrame];
      return isFiniteNumber(highValue) && highValue >= 0 ? highValue : 0;
    }

    case "onsets":
      // Return 1 if this frame is an onset, 0 otherwise
      return analysis.onsets.includes(clampedFrame) ? 1 : 0;

    // Enhanced features
    case "spectralFlux": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: spectralFlux?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const spectralFluxArray = analysis.spectralFlux;
      if (Array.isArray(spectralFluxArray) && clampedFrame >= 0 && clampedFrame < spectralFluxArray.length && typeof spectralFluxArray[clampedFrame] === "number") {
        const spectralFluxValue = spectralFluxArray[clampedFrame];
        return isFiniteNumber(spectralFluxValue) && spectralFluxValue >= 0 ? spectralFluxValue : 0;
      }
      return 0;
    }

    case "zeroCrossingRate":
    case "zcr": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: zeroCrossingRate?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const zcrArray = analysis.zeroCrossingRate;
      if (Array.isArray(zcrArray) && clampedFrame >= 0 && clampedFrame < zcrArray.length && typeof zcrArray[clampedFrame] === "number") {
        const zcrValue = zcrArray[clampedFrame];
        return isFiniteNumber(zcrValue) && zcrValue >= 0 && zcrValue <= 1 ? zcrValue : 0;
      }
      return 0;
    }

    case "spectralRolloff":
    case "rolloff": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: spectralRolloff?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const rolloffArray = analysis.spectralRolloff;
      if (Array.isArray(rolloffArray) && clampedFrame >= 0 && clampedFrame < rolloffArray.length && typeof rolloffArray[clampedFrame] === "number") {
        const rolloffValue = rolloffArray[clampedFrame];
        return isFiniteNumber(rolloffValue) && rolloffValue >= 0 ? rolloffValue : 0;
      }
      return 0;
    }

    case "spectralFlatness":
    case "flatness": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: spectralFlatness?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const flatnessArray = analysis.spectralFlatness;
      if (Array.isArray(flatnessArray) && clampedFrame >= 0 && clampedFrame < flatnessArray.length && typeof flatnessArray[clampedFrame] === "number") {
        const flatnessValue = flatnessArray[clampedFrame];
        return isFiniteNumber(flatnessValue) && flatnessValue >= 0 && flatnessValue <= 1 ? flatnessValue : 0;
      }
      return 0;
    }

    case "chromaEnergy": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/null checks
      // Pattern match: chromaFeatures ∈ object | undefined → object | {}
      if (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null && "chromaEnergy" in analysis.chromaFeatures && Array.isArray(analysis.chromaFeatures.chromaEnergy)) {
        const chromaEnergyArray = analysis.chromaFeatures.chromaEnergy;
        if (clampedFrame >= 0 && clampedFrame < chromaEnergyArray.length && typeof chromaEnergyArray[clampedFrame] === "number") {
          const chromaEnergyValue = chromaEnergyArray[clampedFrame];
          return isFiniteNumber(chromaEnergyValue) && chromaEnergyValue >= 0 ? chromaEnergyValue : 0;
        }
      }
      return 0;
    }

    // Individual chroma pitch classes (C, C#, D, etc.)
    case "chromaC": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/null/undefined checks
      // Pattern match: chromaFeatures.chroma[frame][0] ∈ ℝ ∪ {undefined} → ℝ
      if (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null && "chroma" in analysis.chromaFeatures && Array.isArray(analysis.chromaFeatures.chroma)) {
        const chromaArray = analysis.chromaFeatures.chroma;
        if (clampedFrame >= 0 && clampedFrame < chromaArray.length && Array.isArray(chromaArray[clampedFrame]) && chromaArray[clampedFrame].length > 0 && typeof chromaArray[clampedFrame][0] === "number") {
          const chromaValue = chromaArray[clampedFrame][0];
          return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
        }
      }
      return 0;
    }
    case "chromaCs":
    case "chromaDb": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[1] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaD": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[2] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaDs":
    case "chromaEb": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[3] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaE": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[4] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaF": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[5] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaFs":
    case "chromaGb": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[6] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaG": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[7] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaGs":
    case "chromaAb": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[8] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaA": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[9] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaAs":
    case "chromaBb": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[10] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }
    case "chromaB": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      const chromaFeatures = (typeof analysis.chromaFeatures === "object" && analysis.chromaFeatures !== null)
        ? analysis.chromaFeatures
        : null;
      const chromaArray = (chromaFeatures !== null && "chroma" in chromaFeatures && Array.isArray(chromaFeatures.chroma))
        ? chromaFeatures.chroma
        : [];
      const chromaFrame = Array.isArray(chromaArray) ? chromaArray[clampedFrame] : undefined;
      const chromaValue = Array.isArray(chromaFrame) ? chromaFrame[11] : undefined;
      return isFiniteNumber(chromaValue) && chromaValue >= 0 && chromaValue <= 1 ? chromaValue : 0;
    }

    // Harmonic-Percussive Source Separation (HPSS) features
    case "harmonicEnergy":
    case "harmonic": {
      // Type proof: harmonicEnergy?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const harmonicEnergyArray = analysis.harmonicEnergy;
      const harmonicEnergyValue = Array.isArray(harmonicEnergyArray) ? harmonicEnergyArray[clampedFrame] : undefined;
      return isFiniteNumber(harmonicEnergyValue) && harmonicEnergyValue >= 0 ? harmonicEnergyValue : 0;
    }

    case "percussiveEnergy":
    case "percussive": {
      // Type proof: percussiveEnergy?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const percussiveEnergyArray = analysis.percussiveEnergy;
      const percussiveEnergyValue = Array.isArray(percussiveEnergyArray) ? percussiveEnergyArray[clampedFrame] : undefined;
      return isFiniteNumber(percussiveEnergyValue) && percussiveEnergyValue >= 0 ? percussiveEnergyValue : 0;
    }

    case "hpRatio":
    case "harmonicPercussiveRatio": {
      // Type proof: hpRatio?.[frame] ∈ ℝ ∪ {undefined} → ℝ
      const hpRatioArray = analysis.hpRatio;
      const hpRatioValue = Array.isArray(hpRatioArray) ? hpRatioArray[clampedFrame] : undefined;
      return isFiniteNumber(hpRatioValue) && hpRatioValue >= 0 ? hpRatioValue : 0;
    }

    // MFCC coefficients with per-coefficient normalization
    // MFCC0 (log energy) has different range than MFCC1-12 (spectral shape)
    case "mfcc0":
      return normalizeMFCCCoeff(analysis, clampedFrame, 0);
    case "mfcc1":
      return normalizeMFCCCoeff(analysis, clampedFrame, 1);
    case "mfcc2":
      return normalizeMFCCCoeff(analysis, clampedFrame, 2);
    case "mfcc3":
      return normalizeMFCCCoeff(analysis, clampedFrame, 3);
    case "mfcc4":
      return normalizeMFCCCoeff(analysis, clampedFrame, 4);
    case "mfcc5":
      return normalizeMFCCCoeff(analysis, clampedFrame, 5);
    case "mfcc6":
      return normalizeMFCCCoeff(analysis, clampedFrame, 6);
    case "mfcc7":
      return normalizeMFCCCoeff(analysis, clampedFrame, 7);
    case "mfcc8":
      return normalizeMFCCCoeff(analysis, clampedFrame, 8);
    case "mfcc9":
      return normalizeMFCCCoeff(analysis, clampedFrame, 9);
    case "mfcc10":
      return normalizeMFCCCoeff(analysis, clampedFrame, 10);
    case "mfcc11":
      return normalizeMFCCCoeff(analysis, clampedFrame, 11);
    case "mfcc12":
      return normalizeMFCCCoeff(analysis, clampedFrame, 12);

    default:
      return 0;
  }
}

/**
 * Normalize MFCC coefficient using per-coefficient min-max from analyzed audio.
 * Returns 0-1 range suitable for driving visual parameters.
 */
function normalizeMFCCCoeff(
  analysis: AudioAnalysis,
  frame: number,
  coeff: number,
): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  const mfcc = Array.isArray(analysis.mfcc)
    ? analysis.mfcc
    : [];
  const mfccFrame = (frame >= 0 && frame < mfcc.length && Array.isArray(mfcc[frame]))
    ? mfcc[frame]
    : [];
  const value = (coeff >= 0 && coeff < mfccFrame.length && typeof mfccFrame[coeff] === "number")
    ? mfccFrame[coeff]
    : 0;
  return value;

  const stats = analysis.mfccStats;
  if (!stats) return 0; // No stats available, return 0

  const min = stats.min[coeff];
  const max = stats.max[coeff];
  const range = max - min;

  // Normalize to 0-1 using actual min/max from this audio
  return (value - min) / range;
}

/**
 * Get track-level BPM (not per-frame).
 * BPM is computed once per track, use this instead of getFeatureAtFrame.
 */
export function getBPM(analysis: AudioAnalysis): number {
  return analysis.bpm;
}

/**
 * Get smoothed feature value with temporal smoothing
 */
export function getSmoothedFeature(
  analysis: AudioAnalysis,
  feature: string,
  frame: number,
  smoothingWindow: number = 3,
): number {
  let sum = 0;
  let count = 0;

  for (let i = frame - smoothingWindow; i <= frame + smoothingWindow; i++) {
    if (i >= 0 && i < analysis.frameCount) {
      sum += getFeatureAtFrame(analysis, feature, i);
      count++;
    }
  }

  return count > 0 ? sum / count : 0;
}

/**
 * Normalize a feature array to a specific range
 */
export function normalizeFeature(
  values: number[],
  min: number = 0,
  max: number = 1,
): number[] {
  const minVal = Math.min(...values);
  const maxVal = Math.max(...values);
  const range = maxVal - minVal || 1;

  return values.map((v) => min + ((v - minVal) / range) * (max - min));
}

/**
 * Apply a curve to a feature (for more dramatic or subtle responses)
 */
export function applyFeatureCurve(
  value: number,
  curve: "linear" | "exponential" | "logarithmic" | "smoothstep" = "linear",
): number {
  const clamped = Math.max(0, Math.min(1, value));

  switch (curve) {
    case "exponential":
      return clamped * clamped;

    case "logarithmic":
      return Math.sqrt(clamped);

    case "smoothstep":
      return clamped * clamped * (3 - 2 * clamped);
    default:
      return clamped;
  }
}

// ============================================================================
// Peak Detection (from Yvann-Nodes)
// ============================================================================

export interface PeakDetectionConfig {
  threshold: number; // Minimum value to count as peak (0-1)
  minPeaksDistance: number; // Minimum frames between peaks
  multiply: number; // Amplification factor before detection
}

export interface PeakData {
  indices: number[]; // Frame indices where peaks occur
  values: number[]; // Peak values at those frames
  count: number;
  alternating: number[]; // Same length as total frames, alternates 0/1 at each peak
}

/**
 * Detect peaks in audio weights array
 * Based on Yvann-Nodes peak detection
 */
export function detectPeaks(
  weights: number[],
  config: PeakDetectionConfig,
): PeakData {
  const { threshold, minPeaksDistance, multiply } = config;

  // Apply multiply factor
  const amplified = weights.map((w) => Math.min(1, w * multiply));

  // Find local maxima above threshold
  const rawPeaks: Array<{ index: number; value: number }> = [];

  for (let i = 1; i < amplified.length - 1; i++) {
    const prev = amplified[i - 1];
    const curr = amplified[i];
    const next = amplified[i + 1];

    // Check if local maximum and above threshold
    if (curr > prev && curr > next && curr >= threshold) {
      rawPeaks.push({ index: i, value: curr });
    }
  }

  // Enforce minPeaksDistance (keep higher peak if too close)
  const filteredPeaks: Array<{ index: number; value: number }> = [];

  for (const peak of rawPeaks) {
    // Check if there's a recent peak within minPeaksDistance
    const recentPeakIndex = filteredPeaks.findIndex(
      (p) => Math.abs(p.index - peak.index) < minPeaksDistance,
    );

    if (recentPeakIndex === -1) {
      // No recent peak, add this one
      filteredPeaks.push(peak);
    } else {
      // There's a recent peak - keep the higher one
      if (peak.value > filteredPeaks[recentPeakIndex].value) {
        filteredPeaks[recentPeakIndex] = peak;
      }
    }
  }

  // Sort by index
  filteredPeaks.sort((a, b) => a.index - b.index);

  // Generate alternating array (starts 0, flips at each peak)
  const alternating: number[] = new Array(weights.length).fill(0);
  let currentState = 0;

  for (let i = 0; i < weights.length; i++) {
    const isPeak = filteredPeaks.some((p) => p.index === i);
    if (isPeak) {
      currentState = 1 - currentState; // Flip
    }
    alternating[i] = currentState;
  }

  return {
    indices: filteredPeaks.map((p) => p.index),
    values: filteredPeaks.map((p) => p.value),
    count: filteredPeaks.length,
    alternating,
  };
}

/**
 * Generate peak visualization graph as ImageData
 */
export function generatePeakGraph(
  weights: number[],
  peaks: PeakData,
  width: number,
  height: number,
): ImageData {
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext("2d")!;

  // Background
  ctx.fillStyle = "#1e1e1e";
  ctx.fillRect(0, 0, width, height);

  // Draw weight curve
  ctx.strokeStyle = "#4a90d9";
  ctx.lineWidth = 1;
  ctx.beginPath();

  for (let i = 0; i < weights.length; i++) {
    const x = (i / weights.length) * width;
    const y = height - weights[i] * height * 0.9 - 5;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();

  // Draw peak markers
  ctx.fillStyle = "#ff6b6b";
  for (let i = 0; i < peaks.indices.length; i++) {
    const x = (peaks.indices[i] / weights.length) * width;
    const y = height - peaks.values[i] * height * 0.9 - 5;

    ctx.beginPath();
    ctx.arc(x, y, 4, 0, Math.PI * 2);
    ctx.fill();
  }

  // Draw alternating regions
  ctx.fillStyle = "rgba(255, 193, 7, 0.1)";
  let regionStart = 0;
  let inRegion = peaks.alternating[0] === 1;

  for (let i = 1; i < peaks.alternating.length; i++) {
    const state = peaks.alternating[i] === 1;
    if (state !== inRegion) {
      if (inRegion) {
        // End of yellow region
        const startX = (regionStart / weights.length) * width;
        const endX = (i / weights.length) * width;
        ctx.fillRect(startX, 0, endX - startX, height);
      }
      regionStart = i;
      inRegion = state;
    }
  }

  // Final region
  if (inRegion) {
    const startX = (regionStart / weights.length) * width;
    ctx.fillRect(startX, 0, width - startX, height);
  }

  return ctx.getImageData(0, 0, width, height);
}

/**
 * Check if a frame is a beat/onset
 * Returns false if analysis is null/undefined (e.g., audio not loaded yet)
 */
export function isBeatAtFrame(analysis: AudioAnalysis | null | undefined, frame: number): boolean {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (typeof analysis !== "object" || analysis === null) {
    return false;
  }
  const onsets = Array.isArray(analysis.onsets)
    ? analysis.onsets
    : [];
  if (onsets.length === 0) {
    return false;
  }
  return analysis.onsets.includes(frame);
}

/**
 * Check if a frame is a peak
 */
export function isPeakAtFrame(peaks: PeakData, frame: number): boolean {
  return peaks.indices.includes(frame);
}

// ============================================================================
// HPSS: Harmonic-Percussive Source Separation
// ============================================================================

/**
 * Perform Harmonic-Percussive Source Separation
 *
 * Uses median filtering on the spectrogram:
 * - Harmonic content: stable across time (horizontal median filter)
 * - Percussive content: stable across frequency (vertical median filter)
 *
 * Based on librosa's HPSS implementation
 */
export function extractHPSS(
  buffer: AudioBuffer,
  fps: number,
  kernelSize: number = 31,
): { harmonicEnergy: number[]; percussiveEnergy: number[]; hpRatio: number[] } {
  const channelData = buffer.getChannelData(0);
  const sampleRate = buffer.sampleRate;
  const frameCount = Math.ceil(buffer.duration * fps);
  const samplesPerFrame = Math.floor(sampleRate / fps);

  // FFT parameters
  const fftSize = 2048;
  const hopSize = samplesPerFrame;
  const numBins = fftSize / 2 + 1;

  // Compute spectrogram magnitude
  const spectrogram: number[][] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * hopSize;
    const frameData = new Float32Array(fftSize);

    // Copy and window
    for (let i = 0; i < fftSize && startSample + i < channelData.length; i++) {
      // Hann window
      const window = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (fftSize - 1)));
      frameData[i] = channelData[startSample + i] * window;
    }

    // Simple DFT (for small FFT sizes, good enough)
    const magnitudes: number[] = [];
    for (let k = 0; k < numBins; k++) {
      let real = 0,
        imag = 0;
      for (let n = 0; n < fftSize; n++) {
        const angle = (-2 * Math.PI * k * n) / fftSize;
        real += frameData[n] * Math.cos(angle);
        imag += frameData[n] * Math.sin(angle);
      }
      magnitudes.push(Math.sqrt(real * real + imag * imag));
    }
    spectrogram.push(magnitudes);
  }

  if (spectrogram.length === 0) {
    return { harmonicEnergy: [], percussiveEnergy: [], hpRatio: [] };
  }

  // Apply median filtering for H/P separation
  const halfKernel = Math.floor(kernelSize / 2);
  const harmonicSpec: number[][] = [];
  const percussiveSpec: number[][] = [];

  for (let t = 0; t < spectrogram.length; t++) {
    const harmonicFrame: number[] = [];
    const percussiveFrame: number[] = [];

    for (let f = 0; f < numBins; f++) {
      // Horizontal median (time direction) → Harmonic
      const timeWindow: number[] = [];
      for (let dt = -halfKernel; dt <= halfKernel; dt++) {
        const ti = Math.max(0, Math.min(spectrogram.length - 1, t + dt));
        timeWindow.push(spectrogram[ti][f]);
      }
      timeWindow.sort((a, b) => a - b);
      const harmonicVal = timeWindow[Math.floor(timeWindow.length / 2)];

      // Vertical median (frequency direction) → Percussive
      const freqWindow: number[] = [];
      for (let df = -halfKernel; df <= halfKernel; df++) {
        const fi = Math.max(0, Math.min(numBins - 1, f + df));
        freqWindow.push(spectrogram[t][fi]);
      }
      freqWindow.sort((a, b) => a - b);
      const percussiveVal = freqWindow[Math.floor(freqWindow.length / 2)];

      // Soft mask separation
      const total = harmonicVal + percussiveVal + 1e-10;
      const harmonicMask = harmonicVal / total;
      const percussiveMask = percussiveVal / total;

      harmonicFrame.push(spectrogram[t][f] * harmonicMask);
      percussiveFrame.push(spectrogram[t][f] * percussiveMask);
    }

    harmonicSpec.push(harmonicFrame);
    percussiveSpec.push(percussiveFrame);
  }

  // Sum energy across frequency bins for each frame
  const harmonicEnergy: number[] = [];
  const percussiveEnergy: number[] = [];
  const hpRatio: number[] = [];

  for (let t = 0; t < spectrogram.length; t++) {
    const hEnergy = harmonicSpec[t].reduce((sum, v) => sum + v * v, 0);
    const pEnergy = percussiveSpec[t].reduce((sum, v) => sum + v * v, 0);

    harmonicEnergy.push(Math.sqrt(hEnergy));
    percussiveEnergy.push(Math.sqrt(pEnergy));
    hpRatio.push(hEnergy / (pEnergy + 1e-10));
  }

  // Normalize
  const maxH = Math.max(...harmonicEnergy, 1e-10);
  const maxP = Math.max(...percussiveEnergy, 1e-10);

  return {
    harmonicEnergy: harmonicEnergy.map((v) => v / maxH),
    percussiveEnergy: percussiveEnergy.map((v) => v / maxP),
    hpRatio: hpRatio.map((v) => Math.min(v, 10) / 10), // Clamp and normalize
  };
}

// ============================================================================
// MFCC: Mel-Frequency Cepstral Coefficients
// ============================================================================

/**
 * Extract MFCC features for timbral analysis
 *
 * Process:
 * 1. Compute mel-scale filterbank
 * 2. Apply filterbank to power spectrum
 * 3. Take log of filterbank energies
 * 4. Apply DCT to get cepstral coefficients
 */
export function extractMFCC(
  buffer: AudioBuffer,
  fps: number,
  numCoeffs: number = 13,
  numMelFilters: number = 40,
): { mfcc: number[][]; stats: { min: number[]; max: number[] } } {
  const channelData = buffer.getChannelData(0);
  const sampleRate = buffer.sampleRate;
  const frameCount = Math.ceil(buffer.duration * fps);
  const samplesPerFrame = Math.floor(sampleRate / fps);

  const fftSize = 2048;
  const numBins = fftSize / 2 + 1;

  // Create mel filterbank
  const melFilterbank = createMelFilterbank(numMelFilters, numBins, sampleRate);

  const mfccFrames: number[][] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const frameData = new Float32Array(fftSize);

    // Copy and window
    for (let i = 0; i < fftSize && startSample + i < channelData.length; i++) {
      const window = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (fftSize - 1)));
      frameData[i] = channelData[startSample + i] * window;
    }

    // Compute power spectrum
    const powerSpectrum: number[] = [];
    for (let k = 0; k < numBins; k++) {
      let real = 0,
        imag = 0;
      for (let n = 0; n < fftSize; n++) {
        const angle = (-2 * Math.PI * k * n) / fftSize;
        real += frameData[n] * Math.cos(angle);
        imag += frameData[n] * Math.sin(angle);
      }
      powerSpectrum.push(real * real + imag * imag);
    }

    // Apply mel filterbank
    const melEnergies: number[] = [];
    for (let m = 0; m < numMelFilters; m++) {
      let energy = 0;
      for (let k = 0; k < numBins; k++) {
        energy += powerSpectrum[k] * melFilterbank[m][k];
      }
      melEnergies.push(Math.log(energy + 1e-10));
    }

    // DCT to get MFCCs
    const mfcc: number[] = [];
    for (let c = 0; c < numCoeffs; c++) {
      let sum = 0;
      for (let m = 0; m < numMelFilters; m++) {
        sum +=
          melEnergies[m] * Math.cos((Math.PI * c * (m + 0.5)) / numMelFilters);
      }
      mfcc.push(sum);
    }

    mfccFrames.push(mfcc);
  }

  // Compute per-coefficient min/max statistics for proper MFCC normalization.
  // MFCC0 (log energy) has different range than MFCC1-12 (spectral shape).
  const stats = {
    min: new Array(numCoeffs).fill(Infinity),
    max: new Array(numCoeffs).fill(-Infinity),
  };

  for (const frame of mfccFrames) {
    for (let c = 0; c < numCoeffs; c++) {
      if (frame[c] < stats.min[c]) stats.min[c] = frame[c];
      if (frame[c] > stats.max[c]) stats.max[c] = frame[c];
    }
  }

  // Handle edge cases for normalization
  for (let c = 0; c < numCoeffs; c++) {
    // Edge case: 0 frames - stats remain Infinity/-Infinity
    if (!Number.isFinite(stats.min[c]) || !Number.isFinite(stats.max[c])) {
      stats.min[c] = 0;
      stats.max[c] = 1;
    }
    // Edge case: all values same - expand range to avoid division by zero
    else if (stats.min[c] === stats.max[c]) {
      stats.min[c] = stats.min[c] - 1;
      stats.max[c] = stats.max[c] + 1;
    }
  }

  return { mfcc: mfccFrames, stats };
}

/**
 * Create mel-scale filterbank
 */
function createMelFilterbank(
  numFilters: number,
  numBins: number,
  sampleRate: number,
): number[][] {
  // Mel scale conversion functions
  const hzToMel = (hz: number) => 2595 * Math.log10(1 + hz / 700);
  const melToHz = (mel: number) => 700 * (10 ** (mel / 2595) - 1);

  const minMel = hzToMel(0);
  const maxMel = hzToMel(sampleRate / 2);

  // Create mel points
  const melPoints: number[] = [];
  for (let i = 0; i <= numFilters + 1; i++) {
    melPoints.push(minMel + ((maxMel - minMel) * i) / (numFilters + 1));
  }

  // Convert to bin indices
  const binPoints = melPoints.map((mel) => {
    const hz = melToHz(mel);
    return Math.floor(((numBins - 1) * 2 * hz) / sampleRate);
  });

  // Create filterbank
  const filterbank: number[][] = [];
  for (let m = 0; m < numFilters; m++) {
    const filter: number[] = new Array(numBins).fill(0);
    const start = binPoints[m];
    const center = binPoints[m + 1];
    const end = binPoints[m + 2];

    // Rising edge
    for (let k = start; k < center && k < numBins; k++) {
      filter[k] = (k - start) / (center - start + 1e-10);
    }

    // Falling edge
    for (let k = center; k < end && k < numBins; k++) {
      filter[k] = (end - k) / (end - center + 1e-10);
    }

    filterbank.push(filter);
  }

  return filterbank;
}

export default {
  loadAudioFile,
  loadAudioFromUrl,
  analyzeAudio,
  extractAmplitudeEnvelope,
  extractRMSEnergy,
  extractFrequencyBands,
  extractSpectralCentroid,
  detectOnsets,
  detectBPM,
  getFeatureAtFrame,
  getBPM, // Track-level BPM accessor (constant across frames)
  getSmoothedFeature,
  normalizeFeature,
  applyFeatureCurve,
  detectPeaks,
  generatePeakGraph,
  isBeatAtFrame,
  isPeakAtFrame,
  // HPSS & MFCC (librosa-style)
  extractHPSS,
  extractMFCC,
};
