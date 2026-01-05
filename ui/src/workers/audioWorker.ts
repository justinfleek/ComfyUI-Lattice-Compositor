/**
 * Audio Analysis Web Worker
 *
 * Performs audio analysis in a background thread to avoid blocking the main thread.
 * Uses Cooley-Tukey FFT (O(n log n)) instead of naive DFT (O(n²)).
 */

// ============================================================================
// Types (duplicated from audioFeatures.ts to avoid import issues in worker)
// ============================================================================

interface AudioAnalysis {
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
  // New spectral features
  spectralFlux: number[];
  zeroCrossingRate: number[];
  spectralRolloff: number[];
  spectralFlatness: number[];
  chromaFeatures: {
    chroma: number[][]; // [frameIndex][pitchClass] 12 values per frame
    chromaEnergy: number[]; // Total chroma energy per frame
    estimatedKey: string; // Best guess at musical key
    keyConfidence: number; // 0-1 confidence in key estimation
  };
}

interface FrequencyBandRanges {
  sub: [number, number];
  bass: [number, number];
  lowMid: [number, number];
  mid: [number, number];
  highMid: [number, number];
  high: [number, number];
}

// Message types
interface AnalyzeMessage {
  type: "analyze";
  payload: {
    channelData: Float32Array;
    sampleRate: number;
    fps: number;
  };
}

interface CancelMessage {
  type: "cancel";
}

type WorkerMessage = AnalyzeMessage | CancelMessage;

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

let cancelled = false;

// ============================================================================
// Progress Reporting
// ============================================================================

function reportProgress(phase: string, progress: number, message: string) {
  self.postMessage({
    type: "progress",
    payload: { phase, progress, message },
  });
}

function reportComplete(analysis: AudioAnalysis) {
  self.postMessage({
    type: "complete",
    payload: analysis,
  });
}

function reportError(message: string) {
  self.postMessage({
    type: "error",
    payload: { message },
  });
}

// ============================================================================
// Cooley-Tukey FFT (O(n log n))
// ============================================================================

/**
 * Radix-2 Cooley-Tukey FFT
 * Much faster than naive DFT for power-of-2 sizes
 */
function fft(real: Float32Array, imag: Float32Array): void {
  const n = real.length;

  // Bit-reversal permutation
  for (let i = 0, j = 0; i < n; i++) {
    if (i < j) {
      [real[i], real[j]] = [real[j], real[i]];
      [imag[i], imag[j]] = [imag[j], imag[i]];
    }
    let m = n >> 1;
    while (m >= 1 && j >= m) {
      j -= m;
      m >>= 1;
    }
    j += m;
  }

  // Cooley-Tukey iterative FFT
  for (let size = 2; size <= n; size *= 2) {
    const halfSize = size / 2;
    const tableStep = n / size;

    for (let i = 0; i < n; i += size) {
      for (let j = i, k = 0; j < i + halfSize; j++, k += tableStep) {
        const angle = (-2 * Math.PI * k) / n;
        const tpRe = Math.cos(angle);
        const tpIm = Math.sin(angle);

        const l = j + halfSize;
        const tRe = real[l] * tpRe - imag[l] * tpIm;
        const tIm = real[l] * tpIm + imag[l] * tpRe;

        real[l] = real[j] - tRe;
        imag[l] = imag[j] - tIm;
        real[j] += tRe;
        imag[j] += tIm;
      }
    }
  }
}

/**
 * Compute magnitude spectrum using FFT
 */
function computeMagnitudeSpectrum(
  samples: Float32Array,
  fftSize: number,
): Float32Array {
  // Ensure power of 2
  const n = fftSize;

  // Create arrays with proper size
  const real = new Float32Array(n);
  const imag = new Float32Array(n);

  // Apply Hanning window and copy samples
  for (let i = 0; i < n; i++) {
    const windowValue = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (n - 1)));
    real[i] = (samples[i] || 0) * windowValue;
    imag[i] = 0;
  }

  // Perform FFT
  fft(real, imag);

  // Compute magnitudes (only need first half due to symmetry)
  const halfN = n >> 1;
  const magnitudes = new Float32Array(halfN);
  for (let i = 0; i < halfN; i++) {
    magnitudes[i] = Math.sqrt(real[i] * real[i] + imag[i] * imag[i]) / n;
  }

  return magnitudes;
}

// ============================================================================
// Validation Helpers (duplicated to avoid import issues in worker)
// ============================================================================

const DEFAULT_FPS = 16;

/**
 * Validates fps to prevent division by zero.
 * Returns validated fps or default if invalid.
 */
function validateFps(fps: number): number {
  if (!Number.isFinite(fps) || fps <= 0) {
    return DEFAULT_FPS;
  }
  return Math.max(1, Math.min(120, fps));
}

// ============================================================================
// Analysis Functions
// ============================================================================

function extractAmplitudeEnvelope(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const envelope: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return envelope;

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

  // Normalize
  const maxValue = Math.max(...envelope, 0.0001);
  return envelope.map((v) => v / maxValue);
}

function extractRMSEnergy(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const rmsValues: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return rmsValues;

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

  // Normalize
  const maxValue = Math.max(...rmsValues, 0.0001);
  return rmsValues.map((v) => v / maxValue);
}

function extractFrequencyBands(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): AudioAnalysis["frequencyBands"] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;

  const bands: AudioAnalysis["frequencyBands"] = {
    sub: [],
    bass: [],
    lowMid: [],
    mid: [],
    highMid: [],
    high: [],
  };

  // Calculate bin ranges for each band
  const bandBins: Record<string, { start: number; end: number }> = {};
  for (const [band, [low, high]] of Object.entries(FREQUENCY_BANDS)) {
    bandBins[band] = {
      start: Math.floor(low / binFrequency),
      end: Math.ceil(high / binFrequency),
    };
  }

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return bands;

    // Report progress every 10 frames
    if (frame % 10 === 0) {
      reportProgress(
        "frequency",
        frame / frameCount,
        `Analyzing frequency bands: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      // Not enough samples, use previous values
      for (const band of Object.keys(bands) as (keyof typeof bands)[]) {
        bands[band].push(
          bands[band].length > 0 ? bands[band][bands[band].length - 1] : 0,
        );
      }
      continue;
    }

    // Get spectrum using fast FFT
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    // Extract band energies
    for (const [band, { start, end }] of Object.entries(bandBins)) {
      let energy = 0;
      let count = 0;
      for (let i = start; i < Math.min(end, spectrum.length); i++) {
        energy += spectrum[i];
        count++;
      }
      bands[band as keyof typeof bands].push(count > 0 ? energy / count : 0);
    }
  }

  // Normalize each band
  for (const band of Object.keys(bands) as (keyof typeof bands)[]) {
    const maxValue = Math.max(...bands[band], 0.0001);
    bands[band] = bands[band].map((v) => v / maxValue);
  }

  return bands;
}

function extractSpectralCentroid(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const centroids: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return centroids;

    // Report progress every 10 frames
    if (frame % 10 === 0) {
      reportProgress(
        "spectral",
        frame / frameCount,
        `Computing spectral centroid: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      centroids.push(
        centroids.length > 0 ? centroids[centroids.length - 1] : 0,
      );
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    let weightedSum = 0;
    let totalMagnitude = 0;

    for (let i = 0; i < spectrum.length; i++) {
      const frequency = i * binFrequency;
      weightedSum += frequency * spectrum[i];
      totalMagnitude += spectrum[i];
    }

    const centroid = totalMagnitude > 0 ? weightedSum / totalMagnitude : 0;
    centroids.push(centroid);
  }

  // Normalize
  const maxValue = Math.max(...centroids, 0.0001);
  return centroids.map((v) => v / maxValue);
}

/**
 * Extract Zero Crossing Rate per frame
 * Measures how often the signal crosses zero - higher values indicate noisier/rougher sounds
 */
function extractZeroCrossingRate(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const zcrValues: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return zcrValues;

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

    // Normalize by window length
    const windowLength = endSample - startSample;
    zcrValues.push(windowLength > 1 ? crossings / (windowLength - 1) : 0);
  }

  // Normalize to 0-1
  const maxValue = Math.max(...zcrValues, 0.0001);
  return zcrValues.map((v) => v / maxValue);
}

/**
 * Extract Spectral Flux per frame
 * Measures how much the spectrum changes from frame to frame - good for onset detection
 */
function extractSpectralFlux(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const fluxValues: number[] = [];
  let prevSpectrum: Float32Array | null = null;

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return fluxValues;

    if (frame % 20 === 0) {
      reportProgress(
        "spectralFlux",
        frame / frameCount,
        `Computing spectral flux: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      fluxValues.push(
        fluxValues.length > 0 ? fluxValues[fluxValues.length - 1] : 0,
      );
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    if (prevSpectrum) {
      let flux = 0;
      for (let i = 0; i < spectrum.length; i++) {
        const diff = spectrum[i] - prevSpectrum[i];
        // Half-wave rectification - only positive changes
        if (diff > 0) flux += diff;
      }
      fluxValues.push(flux);
    } else {
      fluxValues.push(0);
    }

    prevSpectrum = spectrum;
  }

  // Normalize
  const maxValue = Math.max(...fluxValues, 0.0001);
  return fluxValues.map((v) => v / maxValue);
}

/**
 * Extract Spectral Rolloff per frame
 * Frequency below which 85% of the spectral energy is contained
 * Lower rolloff = more energy in lower frequencies
 */
function extractSpectralRolloff(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
  rolloffPercent: number = 0.85,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const rolloffValues: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return rolloffValues;

    if (frame % 20 === 0) {
      reportProgress(
        "spectralRolloff",
        frame / frameCount,
        `Computing spectral rolloff: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      rolloffValues.push(
        rolloffValues.length > 0 ? rolloffValues[rolloffValues.length - 1] : 0,
      );
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    // Total energy
    let totalEnergy = 0;
    for (let i = 0; i < spectrum.length; i++) {
      totalEnergy += spectrum[i] * spectrum[i];
    }

    // Find rolloff frequency
    const threshold = totalEnergy * rolloffPercent;
    let cumulativeEnergy = 0;
    let rolloffBin = 0;

    for (let i = 0; i < spectrum.length; i++) {
      cumulativeEnergy += spectrum[i] * spectrum[i];
      if (cumulativeEnergy >= threshold) {
        rolloffBin = i;
        break;
      }
    }

    rolloffValues.push(rolloffBin * binFrequency);
  }

  // Normalize by Nyquist frequency
  const nyquist = sampleRate / 2;
  return rolloffValues.map((v) => v / nyquist);
}

/**
 * Extract Spectral Flatness per frame
 * Ratio of geometric mean to arithmetic mean of spectrum
 * Values close to 1 = noise-like, close to 0 = tonal
 */
function extractSpectralFlatness(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const flatnessValues: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return flatnessValues;

    if (frame % 20 === 0) {
      reportProgress(
        "spectralFlatness",
        frame / frameCount,
        `Computing spectral flatness: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      flatnessValues.push(
        flatnessValues.length > 0
          ? flatnessValues[flatnessValues.length - 1]
          : 0,
      );
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    // Filter out zero or very small values for log computation
    const nonZeroSpectrum = spectrum.filter((v) => v > 1e-10);

    if (nonZeroSpectrum.length === 0) {
      flatnessValues.push(0);
      continue;
    }

    // Geometric mean (use log for numerical stability)
    let logSum = 0;
    for (const v of nonZeroSpectrum) {
      logSum += Math.log(v);
    }
    const geometricMean = Math.exp(logSum / nonZeroSpectrum.length);

    // Arithmetic mean
    let sum = 0;
    for (const v of nonZeroSpectrum) {
      sum += v;
    }
    const arithmeticMean = sum / nonZeroSpectrum.length;

    // Flatness is ratio
    const flatness = arithmeticMean > 0 ? geometricMean / arithmeticMean : 0;
    flatnessValues.push(flatness);
  }

  // Already normalized between 0 and 1
  return flatnessValues;
}

/**
 * Extract Chroma Features per frame
 * 12-bin pitch class representation (C, C#, D, D#, E, F, F#, G, G#, A, A#, B)
 * Used for pitch/harmony detection
 */
function extractChromaFeatures(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): AudioAnalysis["chromaFeatures"] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const chromaFrames: number[][] = [];
  const chromaEnergy: number[] = [];

  // Reference frequency for A4
  const A4 = 440;

  // Key names for estimation
  const KEY_NAMES = [
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

  // Major and minor key profiles (Krumhansl-Schmuckler)
  const MAJOR_PROFILE = [
    6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88,
  ];
  const MINOR_PROFILE = [
    6.33, 2.68, 3.52, 5.38, 2.6, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17,
  ];

  // Accumulator for key estimation
  const avgChroma = new Array(12).fill(0);
  let totalFrames = 0;

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled)
      return {
        chroma: chromaFrames,
        chromaEnergy,
        estimatedKey: "C major",
        keyConfidence: 0,
      };

    if (frame % 20 === 0) {
      reportProgress(
        "chroma",
        frame / frameCount,
        `Computing chroma features: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      chromaFrames.push(
        chromaFrames.length > 0
          ? [...chromaFrames[chromaFrames.length - 1]]
          : new Array(12).fill(0),
      );
      chromaEnergy.push(
        chromaEnergy.length > 0 ? chromaEnergy[chromaEnergy.length - 1] : 0,
      );
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    // Initialize 12 chroma bins
    const chroma = new Array(12).fill(0);

    // Map each FFT bin to a chroma bin
    for (let i = 1; i < spectrum.length; i++) {
      const frequency = i * binFrequency;

      // Skip frequencies outside musical range (20Hz - 5kHz)
      if (frequency < 20 || frequency > 5000) continue;

      // Calculate pitch class (0-11, where 0 = C)
      // MIDI note number = 69 + 12 * log2(f/440)
      const midiNote = 69 + 12 * Math.log2(frequency / A4);
      const pitchClass = Math.round(midiNote) % 12;
      const normalizedPitchClass =
        pitchClass < 0 ? pitchClass + 12 : pitchClass;

      // Accumulate energy into chroma bin
      chroma[normalizedPitchClass] += spectrum[i] * spectrum[i];
    }

    // Calculate total energy for this frame
    const frameEnergy = chroma.reduce((a, b) => a + b, 0);
    chromaEnergy.push(frameEnergy);

    // Normalize chroma vector
    const chromaMax = Math.max(...chroma, 0.0001);
    const normalizedChroma = chroma.map((v) => v / chromaMax);

    // Accumulate for key estimation
    for (let i = 0; i < 12; i++) {
      avgChroma[i] += normalizedChroma[i];
    }
    totalFrames++;

    chromaFrames.push(normalizedChroma);
  }

  // Estimate key using Krumhansl-Schmuckler algorithm
  // Normalize average chroma
  if (totalFrames > 0) {
    for (let i = 0; i < 12; i++) {
      avgChroma[i] /= totalFrames;
    }
  }

  // Correlate with all 24 key profiles (12 major + 12 minor)
  let bestKey = "C major";
  let bestCorrelation = -Infinity;

  for (let root = 0; root < 12; root++) {
    // Rotate profile to start at this root
    const rotatedMajor: number[] = [];
    const rotatedMinor: number[] = [];
    for (let i = 0; i < 12; i++) {
      rotatedMajor.push(MAJOR_PROFILE[(i + 12 - root) % 12]);
      rotatedMinor.push(MINOR_PROFILE[(i + 12 - root) % 12]);
    }

    // Calculate Pearson correlation
    const majorCorr = pearsonCorrelation(avgChroma, rotatedMajor);
    const minorCorr = pearsonCorrelation(avgChroma, rotatedMinor);

    if (majorCorr > bestCorrelation) {
      bestCorrelation = majorCorr;
      bestKey = `${KEY_NAMES[root]} major`;
    }
    if (minorCorr > bestCorrelation) {
      bestCorrelation = minorCorr;
      bestKey = `${KEY_NAMES[root]} minor`;
    }
  }

  // Normalize correlation to confidence (0-1)
  const keyConfidence = Math.max(0, Math.min(1, (bestCorrelation + 1) / 2));

  // Normalize chroma energy
  const maxEnergy = Math.max(...chromaEnergy, 0.0001);
  const normalizedEnergy = chromaEnergy.map((v) => v / maxEnergy);

  return {
    chroma: chromaFrames,
    chromaEnergy: normalizedEnergy,
    estimatedKey: bestKey,
    keyConfidence,
  };
}

/**
 * Calculate Pearson correlation coefficient between two arrays
 */
function pearsonCorrelation(x: number[], y: number[]): number {
  const n = x.length;
  if (n !== y.length || n === 0) return 0;

  let sumX = 0,
    sumY = 0,
    sumXY = 0,
    sumX2 = 0,
    sumY2 = 0;

  for (let i = 0; i < n; i++) {
    sumX += x[i];
    sumY += y[i];
    sumXY += x[i] * y[i];
    sumX2 += x[i] * x[i];
    sumY2 += y[i] * y[i];
  }

  const numerator = n * sumXY - sumX * sumY;
  const denominator = Math.sqrt(
    (n * sumX2 - sumX * sumX) * (n * sumY2 - sumY * sumY),
  );

  return denominator === 0 ? 0 : numerator / denominator;
}

function detectOnsets(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
  sensitivity: number = 0.5,
): number[] {
  const samplesPerFrame = Math.floor(sampleRate / validateFps(fps));
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);

  // Calculate spectral flux
  const spectralFlux: number[] = [];
  let prevSpectrum: Float32Array | null = null;

  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return [];

    // Report progress every 10 frames
    if (frame % 10 === 0) {
      reportProgress(
        "onsets",
        frame / frameCount,
        `Detecting onsets: ${Math.round((frame / frameCount) * 100)}%`,
      );
    }

    const startSample = frame * samplesPerFrame;

    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      spectralFlux.push(0);
      continue;
    }

    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE,
    );

    if (prevSpectrum) {
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
    threshold.push(mean + (1 - sensitivity) * 2 * std);
  }

  return threshold;
}

function detectBPM(channelData: Float32Array, sampleRate: number): number {
  reportProgress("bpm", 0, "Detecting BPM...");

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

  const analysisLength = Math.min(envelope.length, downsampledRate * 10);
  const signal = envelope.slice(0, analysisLength);

  for (let lag = minLag; lag <= maxLag; lag++) {
    if (cancelled) return 120;

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

  const bpm = (60 * downsampledRate) / bestLag;
  reportProgress("bpm", 1, "BPM detection complete");

  return Math.round(Math.max(minBPM, Math.min(maxBPM, bpm)));
}

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
// Main Analysis Entry Point
// ============================================================================

async function analyzeAudio(
  channelData: Float32Array,
  sampleRate: number,
  fps: number,
): Promise<AudioAnalysis> {
  cancelled = false;

  const duration = channelData.length / sampleRate;
  const frameCount = Math.ceil(duration * fps);

  // Phase 1: Amplitude
  reportProgress("amplitude", 0, "Extracting amplitude envelope...");
  const amplitudeEnvelope = extractAmplitudeEnvelope(
    channelData,
    sampleRate,
    fps,
  );
  if (cancelled) throw new Error("Cancelled");
  reportProgress("amplitude", 1, "Amplitude envelope complete");

  // Phase 2: RMS
  reportProgress("rms", 0, "Calculating RMS energy...");
  const rmsEnergy = extractRMSEnergy(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("rms", 1, "RMS energy complete");

  // Phase 3: Frequency bands (slowest)
  reportProgress("frequency", 0, "Analyzing frequency bands...");
  const frequencyBands = extractFrequencyBands(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("frequency", 1, "Frequency bands complete");

  // Phase 4: Spectral centroid
  reportProgress("spectral", 0, "Computing spectral centroid...");
  const spectralCentroid = extractSpectralCentroid(
    channelData,
    sampleRate,
    fps,
  );
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectral", 1, "Spectral centroid complete");

  // Phase 5: Zero Crossing Rate
  reportProgress("zcr", 0, "Computing zero crossing rate...");
  const zeroCrossingRate = extractZeroCrossingRate(
    channelData,
    sampleRate,
    fps,
  );
  if (cancelled) throw new Error("Cancelled");
  reportProgress("zcr", 1, "Zero crossing rate complete");

  // Phase 6: Spectral Flux
  reportProgress("spectralFlux", 0, "Computing spectral flux...");
  const spectralFlux = extractSpectralFlux(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralFlux", 1, "Spectral flux complete");

  // Phase 7: Spectral Rolloff
  reportProgress("spectralRolloff", 0, "Computing spectral rolloff...");
  const spectralRolloff = extractSpectralRolloff(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralRolloff", 1, "Spectral rolloff complete");

  // Phase 8: Spectral Flatness
  reportProgress("spectralFlatness", 0, "Computing spectral flatness...");
  const spectralFlatness = extractSpectralFlatness(
    channelData,
    sampleRate,
    fps,
  );
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralFlatness", 1, "Spectral flatness complete");

  // Phase 9: Chroma Features
  reportProgress("chroma", 0, "Computing chroma features...");
  const chromaFeatures = extractChromaFeatures(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("chroma", 1, "Chroma features complete");

  // Phase 10: Onset detection
  reportProgress("onsets", 0, "Detecting onsets...");
  const onsets = detectOnsets(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("onsets", 1, "Onset detection complete");

  // Phase 11: BPM
  reportProgress("bpm", 0, "Detecting BPM...");
  const bpm = detectBPM(channelData, sampleRate);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("bpm", 1, "BPM detection complete");

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
    spectralFlux,
    zeroCrossingRate,
    spectralRolloff,
    spectralFlatness,
    chromaFeatures,
  };
}

// ============================================================================
// Worker Message Handler
// ============================================================================

self.onmessage = async (event: MessageEvent<WorkerMessage>) => {
  const message = event.data;

  switch (message.type) {
    case "analyze":
      try {
        const { channelData, sampleRate, fps } = message.payload;
        const analysis = await analyzeAudio(channelData, sampleRate, fps);
        reportComplete(analysis);
      } catch (error) {
        if ((error as Error).message === "Cancelled") {
          reportError("Analysis cancelled");
        } else {
          reportError(`Analysis failed: ${(error as Error).message}`);
        }
      }
      break;

    case "cancel":
      cancelled = true;
      break;
  }
};

// Export for TypeScript module resolution
export {};
