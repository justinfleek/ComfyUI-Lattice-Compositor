/**
 * Audio Feature Extraction Service
 *
 * Uses Web Audio API for comprehensive audio analysis.
 * Supports amplitude, RMS, spectral analysis, onset detection, and BPM estimation.
 * Matches ATI_AudioReactive and Yvann-Nodes functionality.
 */

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
}

export interface FrequencyBandRanges {
  sub: [number, number];
  bass: [number, number];
  lowMid: [number, number];
  mid: [number, number];
  highMid: [number, number];
  high: [number, number];
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
  high: [4000, 20000]
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
export async function analyzeAudio(buffer: AudioBuffer, fps: number): Promise<AudioAnalysis> {
  const duration = buffer.duration;
  const frameCount = Math.ceil(duration * fps);
  const sampleRate = buffer.sampleRate;

  // Extract features
  const amplitudeEnvelope = extractAmplitudeEnvelope(buffer, fps);
  const rmsEnergy = extractRMSEnergy(buffer, fps);
  const frequencyBands = await extractFrequencyBands(buffer, fps);
  const spectralCentroid = await extractSpectralCentroid(buffer, fps);
  const onsets = detectOnsets(buffer, fps);
  const bpm = detectBPM(buffer);

  return {
    sampleRate,
    duration,
    frameCount,
    amplitudeEnvelope,
    rmsEnergy,
    spectralCentroid,
    frequencyBands,
    onsets,
    bpm
  };
}

// ============================================================================
// Amplitude Envelope
// ============================================================================

/**
 * Extract amplitude envelope (peak values per frame)
 */
export function extractAmplitudeEnvelope(buffer: AudioBuffer, fps: number): number[] {
  const channelData = buffer.getChannelData(0); // Use first channel
  const samplesPerFrame = Math.floor(buffer.sampleRate / fps);
  const frameCount = Math.ceil(buffer.duration * fps);
  const envelope: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + samplesPerFrame, channelData.length);

    let maxAmp = 0;
    for (let i = startSample; i < endSample; i++) {
      const amp = Math.abs(channelData[i]);
      if (amp > maxAmp) maxAmp = amp;
    }

    envelope.push(maxAmp);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...envelope, 0.0001);
  return envelope.map(v => v / maxValue);
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
    const endSample = Math.min(startSample + samplesPerFrame, channelData.length);

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
  return rmsValues.map(v => v / maxValue);
}

// ============================================================================
// Frequency Band Analysis
// ============================================================================

/**
 * Extract energy in different frequency bands per frame
 */
export async function extractFrequencyBands(
  buffer: AudioBuffer,
  fps: number
): Promise<AudioAnalysis['frequencyBands']> {
  const duration = buffer.duration;
  const frameCount = Math.ceil(duration * fps);
  const sampleRate = buffer.sampleRate;

  // Create offline context for analysis
  const offlineCtx = new OfflineAudioContext(
    1,
    buffer.length,
    sampleRate
  );

  const source = offlineCtx.createBufferSource();
  source.buffer = buffer;

  const analyser = offlineCtx.createAnalyser();
  analyser.fftSize = DEFAULT_FFT_SIZE;
  analyser.smoothingTimeConstant = 0;

  source.connect(analyser);
  analyser.connect(offlineCtx.destination);

  // Initialize band arrays
  const bands: AudioAnalysis['frequencyBands'] = {
    sub: [],
    bass: [],
    lowMid: [],
    mid: [],
    highMid: [],
    high: []
  };

  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;

  // Calculate bin ranges for each band
  const bandBins = Object.entries(FREQUENCY_BANDS).reduce((acc, [band, [low, high]]) => {
    acc[band as keyof FrequencyBandRanges] = {
      start: Math.floor(low / binFrequency),
      end: Math.ceil(high / binFrequency)
    };
    return acc;
  }, {} as Record<keyof FrequencyBandRanges, { start: number; end: number }>);

  // Process each frame
  const samplesPerFrame = Math.floor(sampleRate / fps);

  // Since OfflineAudioContext doesn't support real-time analysis easily,
  // we'll use a simpler approach with the raw samples
  const channelData = buffer.getChannelData(0);

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + DEFAULT_FFT_SIZE, channelData.length);

    // Get window of samples
    const windowSize = endSample - startSample;
    if (windowSize < 64) {
      // Not enough samples, use previous values or zero
      Object.keys(bands).forEach(band => {
        const arr = bands[band as keyof typeof bands];
        arr.push(arr.length > 0 ? arr[arr.length - 1] : 0);
      });
      continue;
    }

    // Perform simple FFT using the channel data
    const fftResult = simpleFFT(channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE));

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
    bands[band] = bands[band].map(v => v / maxValue);
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
    windowed[i] = (samples[i] || 0) * windowValue;
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
export async function extractSpectralCentroid(buffer: AudioBuffer, fps: number): Promise<number[]> {
  const frameCount = Math.ceil(buffer.duration * fps);
  const sampleRate = buffer.sampleRate;
  const channelData = buffer.getChannelData(0);
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const centroids: number[] = [];
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      centroids.push(centroids.length > 0 ? centroids[centroids.length - 1] : 0);
      continue;
    }

    const fftResult = simpleFFT(channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE));

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
  return centroids.map(v => v / maxValue);
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
  sensitivity: number = 0.5
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

    const spectrum = simpleFFT(channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE));

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
function calculateAdaptiveThreshold(flux: number[], sensitivity: number): number[] {
  const windowSize = 10;
  const threshold: number[] = [];

  for (let i = 0; i < flux.length; i++) {
    const start = Math.max(0, i - windowSize);
    const end = Math.min(flux.length, i + windowSize + 1);
    const window = flux.slice(start, end);
    const mean = window.reduce((a, b) => a + b, 0) / window.length;
    const std = Math.sqrt(
      window.reduce((a, b) => a + (b - mean) ** 2, 0) / window.length
    );

    // Threshold = mean + sensitivity * std
    threshold.push(mean + (1 - sensitivity) * 2 * std);
  }

  return threshold;
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
 */
export function getFeatureAtFrame(
  analysis: AudioAnalysis,
  feature: string,
  frame: number
): number {
  const clampedFrame = Math.max(0, Math.min(frame, analysis.frameCount - 1));

  switch (feature) {
    case 'amplitude':
      return analysis.amplitudeEnvelope[clampedFrame] ?? 0;

    case 'rms':
      return analysis.rmsEnergy[clampedFrame] ?? 0;

    case 'spectralCentroid':
      return analysis.spectralCentroid[clampedFrame] ?? 0;

    case 'sub':
      return analysis.frequencyBands.sub[clampedFrame] ?? 0;

    case 'bass':
      return analysis.frequencyBands.bass[clampedFrame] ?? 0;

    case 'lowMid':
      return analysis.frequencyBands.lowMid[clampedFrame] ?? 0;

    case 'mid':
      return analysis.frequencyBands.mid[clampedFrame] ?? 0;

    case 'highMid':
      return analysis.frequencyBands.highMid[clampedFrame] ?? 0;

    case 'high':
      return analysis.frequencyBands.high[clampedFrame] ?? 0;

    case 'onsets':
      // Return 1 if this frame is an onset, 0 otherwise
      return analysis.onsets.includes(clampedFrame) ? 1 : 0;

    default:
      return 0;
  }
}

/**
 * Get smoothed feature value with temporal smoothing
 */
export function getSmoothedFeature(
  analysis: AudioAnalysis,
  feature: string,
  frame: number,
  smoothingWindow: number = 3
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
  max: number = 1
): number[] {
  const minVal = Math.min(...values);
  const maxVal = Math.max(...values);
  const range = maxVal - minVal || 1;

  return values.map(v => min + ((v - minVal) / range) * (max - min));
}

/**
 * Apply a curve to a feature (for more dramatic or subtle responses)
 */
export function applyFeatureCurve(
  value: number,
  curve: 'linear' | 'exponential' | 'logarithmic' | 'smoothstep' = 'linear'
): number {
  const clamped = Math.max(0, Math.min(1, value));

  switch (curve) {
    case 'exponential':
      return clamped * clamped;

    case 'logarithmic':
      return Math.sqrt(clamped);

    case 'smoothstep':
      return clamped * clamped * (3 - 2 * clamped);

    case 'linear':
    default:
      return clamped;
  }
}

// ============================================================================
// Peak Detection (from Yvann-Nodes)
// ============================================================================

export interface PeakDetectionConfig {
  threshold: number;          // Minimum value to count as peak (0-1)
  minPeaksDistance: number;   // Minimum frames between peaks
  multiply: number;           // Amplification factor before detection
}

export interface PeakData {
  indices: number[];          // Frame indices where peaks occur
  values: number[];           // Peak values at those frames
  count: number;
  alternating: number[];      // Same length as total frames, alternates 0/1 at each peak
}

/**
 * Detect peaks in audio weights array
 * Based on Yvann-Nodes peak detection
 */
export function detectPeaks(
  weights: number[],
  config: PeakDetectionConfig
): PeakData {
  const { threshold, minPeaksDistance, multiply } = config;

  // Apply multiply factor
  const amplified = weights.map(w => Math.min(1, w * multiply));

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
      p => Math.abs(p.index - peak.index) < minPeaksDistance
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
    const isPeak = filteredPeaks.some(p => p.index === i);
    if (isPeak) {
      currentState = 1 - currentState; // Flip
    }
    alternating[i] = currentState;
  }

  return {
    indices: filteredPeaks.map(p => p.index),
    values: filteredPeaks.map(p => p.value),
    count: filteredPeaks.length,
    alternating
  };
}

/**
 * Generate peak visualization graph as ImageData
 */
export function generatePeakGraph(
  weights: number[],
  peaks: PeakData,
  width: number,
  height: number
): ImageData {
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext('2d')!;

  // Background
  ctx.fillStyle = '#1e1e1e';
  ctx.fillRect(0, 0, width, height);

  // Draw weight curve
  ctx.strokeStyle = '#4a90d9';
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
  ctx.fillStyle = '#ff6b6b';
  for (let i = 0; i < peaks.indices.length; i++) {
    const x = (peaks.indices[i] / weights.length) * width;
    const y = height - peaks.values[i] * height * 0.9 - 5;

    ctx.beginPath();
    ctx.arc(x, y, 4, 0, Math.PI * 2);
    ctx.fill();
  }

  // Draw alternating regions
  ctx.fillStyle = 'rgba(255, 193, 7, 0.1)';
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
 */
export function isBeatAtFrame(analysis: AudioAnalysis, frame: number): boolean {
  return analysis.onsets.includes(frame);
}

/**
 * Check if a frame is a peak
 */
export function isPeakAtFrame(peaks: PeakData, frame: number): boolean {
  return peaks.indices.includes(frame);
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
  getSmoothedFeature,
  normalizeFeature,
  applyFeatureCurve,
  detectPeaks,
  generatePeakGraph,
  isBeatAtFrame,
  isPeakAtFrame
};
