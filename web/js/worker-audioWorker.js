const DEFAULT_FFT_SIZE = 2048;
const FREQUENCY_BANDS = {
  sub: [20, 60],
  bass: [60, 250],
  lowMid: [250, 500],
  mid: [500, 2e3],
  highMid: [2e3, 4e3],
  high: [4e3, 2e4]
};
let cancelled = false;
function reportProgress(phase, progress, message) {
  self.postMessage({
    type: "progress",
    payload: { phase, progress, message }
  });
}
function reportComplete(analysis) {
  self.postMessage({
    type: "complete",
    payload: analysis
  });
}
function reportError(message) {
  self.postMessage({
    type: "error",
    payload: { message }
  });
}
function fft(real, imag) {
  const n = real.length;
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
  for (let size = 2; size <= n; size *= 2) {
    const halfSize = size / 2;
    const tableStep = n / size;
    for (let i = 0; i < n; i += size) {
      for (let j = i, k = 0; j < i + halfSize; j++, k += tableStep) {
        const angle = -2 * Math.PI * k / n;
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
function computeMagnitudeSpectrum(samples, fftSize) {
  const n = fftSize;
  const real = new Float32Array(n);
  const imag = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const windowValue = 0.5 * (1 - Math.cos(2 * Math.PI * i / (n - 1)));
    real[i] = (samples[i] || 0) * windowValue;
    imag[i] = 0;
  }
  fft(real, imag);
  const halfN = n >> 1;
  const magnitudes = new Float32Array(halfN);
  for (let i = 0; i < halfN; i++) {
    magnitudes[i] = Math.sqrt(real[i] * real[i] + imag[i] * imag[i]) / n;
  }
  return magnitudes;
}
function extractAmplitudeEnvelope(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const envelope = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return envelope;
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + samplesPerFrame, channelData.length);
    let maxAmp = 0;
    for (let i = startSample; i < endSample; i++) {
      const amp = Math.abs(channelData[i]);
      if (amp > maxAmp) maxAmp = amp;
    }
    envelope.push(maxAmp);
  }
  const maxValue = Math.max(...envelope, 1e-4);
  return envelope.map((v) => v / maxValue);
}
function extractRMSEnergy(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const rmsValues = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return rmsValues;
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
  const maxValue = Math.max(...rmsValues, 1e-4);
  return rmsValues.map((v) => v / maxValue);
}
function extractFrequencyBands(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const bands = {
    sub: [],
    bass: [],
    lowMid: [],
    mid: [],
    highMid: [],
    high: []
  };
  const bandBins = {};
  for (const [band, [low, high]] of Object.entries(FREQUENCY_BANDS)) {
    bandBins[band] = {
      start: Math.floor(low / binFrequency),
      end: Math.ceil(high / binFrequency)
    };
  }
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return bands;
    if (frame % 10 === 0) {
      reportProgress("frequency", frame / frameCount, `Analyzing frequency bands: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      for (const band of Object.keys(bands)) {
        bands[band].push(bands[band].length > 0 ? bands[band][bands[band].length - 1] : 0);
      }
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
    );
    for (const [band, { start, end }] of Object.entries(bandBins)) {
      let energy = 0;
      let count = 0;
      for (let i = start; i < Math.min(end, spectrum.length); i++) {
        energy += spectrum[i];
        count++;
      }
      bands[band].push(count > 0 ? energy / count : 0);
    }
  }
  for (const band of Object.keys(bands)) {
    const maxValue = Math.max(...bands[band], 1e-4);
    bands[band] = bands[band].map((v) => v / maxValue);
  }
  return bands;
}
function extractSpectralCentroid(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const centroids = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return centroids;
    if (frame % 10 === 0) {
      reportProgress("spectral", frame / frameCount, `Computing spectral centroid: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      centroids.push(centroids.length > 0 ? centroids[centroids.length - 1] : 0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
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
  const maxValue = Math.max(...centroids, 1e-4);
  return centroids.map((v) => v / maxValue);
}
function extractZeroCrossingRate(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const zcrValues = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return zcrValues;
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + samplesPerFrame, channelData.length);
    let crossings = 0;
    for (let i = startSample + 1; i < endSample; i++) {
      if (channelData[i] >= 0 && channelData[i - 1] < 0 || channelData[i] < 0 && channelData[i - 1] >= 0) {
        crossings++;
      }
    }
    const windowLength = endSample - startSample;
    zcrValues.push(windowLength > 1 ? crossings / (windowLength - 1) : 0);
  }
  const maxValue = Math.max(...zcrValues, 1e-4);
  return zcrValues.map((v) => v / maxValue);
}
function extractSpectralFlux(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const fluxValues = [];
  let prevSpectrum = null;
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return fluxValues;
    if (frame % 20 === 0) {
      reportProgress("spectralFlux", frame / frameCount, `Computing spectral flux: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      fluxValues.push(fluxValues.length > 0 ? fluxValues[fluxValues.length - 1] : 0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
    );
    if (prevSpectrum) {
      let flux = 0;
      for (let i = 0; i < spectrum.length; i++) {
        const diff = spectrum[i] - prevSpectrum[i];
        if (diff > 0) flux += diff;
      }
      fluxValues.push(flux);
    } else {
      fluxValues.push(0);
    }
    prevSpectrum = spectrum;
  }
  const maxValue = Math.max(...fluxValues, 1e-4);
  return fluxValues.map((v) => v / maxValue);
}
function extractSpectralRolloff(channelData, sampleRate, fps, rolloffPercent = 0.85) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const rolloffValues = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return rolloffValues;
    if (frame % 20 === 0) {
      reportProgress("spectralRolloff", frame / frameCount, `Computing spectral rolloff: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      rolloffValues.push(rolloffValues.length > 0 ? rolloffValues[rolloffValues.length - 1] : 0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
    );
    let totalEnergy = 0;
    for (let i = 0; i < spectrum.length; i++) {
      totalEnergy += spectrum[i] * spectrum[i];
    }
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
  const nyquist = sampleRate / 2;
  return rolloffValues.map((v) => v / nyquist);
}
function extractSpectralFlatness(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const flatnessValues = [];
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return flatnessValues;
    if (frame % 20 === 0) {
      reportProgress("spectralFlatness", frame / frameCount, `Computing spectral flatness: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      flatnessValues.push(flatnessValues.length > 0 ? flatnessValues[flatnessValues.length - 1] : 0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
    );
    const nonZeroSpectrum = spectrum.filter((v) => v > 1e-10);
    if (nonZeroSpectrum.length === 0) {
      flatnessValues.push(0);
      continue;
    }
    let logSum = 0;
    for (const v of nonZeroSpectrum) {
      logSum += Math.log(v);
    }
    const geometricMean = Math.exp(logSum / nonZeroSpectrum.length);
    let sum = 0;
    for (const v of nonZeroSpectrum) {
      sum += v;
    }
    const arithmeticMean = sum / nonZeroSpectrum.length;
    const flatness = arithmeticMean > 0 ? geometricMean / arithmeticMean : 0;
    flatnessValues.push(flatness);
  }
  return flatnessValues;
}
function extractChromaFeatures(channelData, sampleRate, fps) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const binFrequency = sampleRate / DEFAULT_FFT_SIZE;
  const chromaFrames = [];
  const chromaEnergy = [];
  const A4 = 440;
  const KEY_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
  const MAJOR_PROFILE = [6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88];
  const MINOR_PROFILE = [6.33, 2.68, 3.52, 5.38, 2.6, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17];
  const avgChroma = new Array(12).fill(0);
  let totalFrames = 0;
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return { chroma: chromaFrames, chromaEnergy, estimatedKey: "C major", keyConfidence: 0 };
    if (frame % 20 === 0) {
      reportProgress("chroma", frame / frameCount, `Computing chroma features: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      chromaFrames.push(chromaFrames.length > 0 ? [...chromaFrames[chromaFrames.length - 1]] : new Array(12).fill(0));
      chromaEnergy.push(chromaEnergy.length > 0 ? chromaEnergy[chromaEnergy.length - 1] : 0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
    );
    const chroma = new Array(12).fill(0);
    for (let i = 1; i < spectrum.length; i++) {
      const frequency = i * binFrequency;
      if (frequency < 20 || frequency > 5e3) continue;
      const midiNote = 69 + 12 * Math.log2(frequency / A4);
      const pitchClass = Math.round(midiNote) % 12;
      const normalizedPitchClass = pitchClass < 0 ? pitchClass + 12 : pitchClass;
      chroma[normalizedPitchClass] += spectrum[i] * spectrum[i];
    }
    const frameEnergy = chroma.reduce((a, b) => a + b, 0);
    chromaEnergy.push(frameEnergy);
    const chromaMax = Math.max(...chroma, 1e-4);
    const normalizedChroma = chroma.map((v) => v / chromaMax);
    for (let i = 0; i < 12; i++) {
      avgChroma[i] += normalizedChroma[i];
    }
    totalFrames++;
    chromaFrames.push(normalizedChroma);
  }
  if (totalFrames > 0) {
    for (let i = 0; i < 12; i++) {
      avgChroma[i] /= totalFrames;
    }
  }
  let bestKey = "C major";
  let bestCorrelation = -Infinity;
  for (let root = 0; root < 12; root++) {
    const rotatedMajor = [];
    const rotatedMinor = [];
    for (let i = 0; i < 12; i++) {
      rotatedMajor.push(MAJOR_PROFILE[(i + 12 - root) % 12]);
      rotatedMinor.push(MINOR_PROFILE[(i + 12 - root) % 12]);
    }
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
  const keyConfidence = Math.max(0, Math.min(1, (bestCorrelation + 1) / 2));
  const maxEnergy = Math.max(...chromaEnergy, 1e-4);
  const normalizedEnergy = chromaEnergy.map((v) => v / maxEnergy);
  return {
    chroma: chromaFrames,
    chromaEnergy: normalizedEnergy,
    estimatedKey: bestKey,
    keyConfidence
  };
}
function pearsonCorrelation(x, y) {
  const n = x.length;
  if (n !== y.length || n === 0) return 0;
  let sumX = 0, sumY = 0, sumXY = 0, sumX2 = 0, sumY2 = 0;
  for (let i = 0; i < n; i++) {
    sumX += x[i];
    sumY += y[i];
    sumXY += x[i] * y[i];
    sumX2 += x[i] * x[i];
    sumY2 += y[i] * y[i];
  }
  const numerator = n * sumXY - sumX * sumY;
  const denominator = Math.sqrt((n * sumX2 - sumX * sumX) * (n * sumY2 - sumY * sumY));
  return denominator === 0 ? 0 : numerator / denominator;
}
function detectOnsets(channelData, sampleRate, fps, sensitivity = 0.5) {
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const frameCount = Math.ceil(channelData.length / samplesPerFrame);
  const spectralFlux = [];
  let prevSpectrum = null;
  for (let frame = 0; frame < frameCount; frame++) {
    if (cancelled) return [];
    if (frame % 10 === 0) {
      reportProgress("onsets", frame / frameCount, `Detecting onsets: ${Math.round(frame / frameCount * 100)}%`);
    }
    const startSample = frame * samplesPerFrame;
    if (startSample + DEFAULT_FFT_SIZE > channelData.length) {
      spectralFlux.push(0);
      continue;
    }
    const spectrum = computeMagnitudeSpectrum(
      channelData.slice(startSample, startSample + DEFAULT_FFT_SIZE),
      DEFAULT_FFT_SIZE
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
  const onsets = [];
  const threshold = calculateAdaptiveThreshold(spectralFlux, sensitivity);
  for (let i = 1; i < spectralFlux.length - 1; i++) {
    if (spectralFlux[i] > spectralFlux[i - 1] && spectralFlux[i] > spectralFlux[i + 1] && spectralFlux[i] > threshold[i]) {
      onsets.push(i);
    }
  }
  return onsets;
}
function calculateAdaptiveThreshold(flux, sensitivity) {
  const windowSize = 10;
  const threshold = [];
  for (let i = 0; i < flux.length; i++) {
    const start = Math.max(0, i - windowSize);
    const end = Math.min(flux.length, i + windowSize + 1);
    const window = flux.slice(start, end);
    const mean = window.reduce((a, b) => a + b, 0) / window.length;
    const std = Math.sqrt(
      window.reduce((a, b) => a + (b - mean) ** 2, 0) / window.length
    );
    threshold.push(mean + (1 - sensitivity) * 2 * std);
  }
  return threshold;
}
function detectBPM(channelData, sampleRate) {
  reportProgress("bpm", 0, "Detecting BPM...");
  const downsampleFactor = 4;
  const downsampled = [];
  for (let i = 0; i < channelData.length; i += downsampleFactor) {
    downsampled.push(Math.abs(channelData[i]));
  }
  const envelope = applyEnvelopeFollower(downsampled, 0.1);
  const minBPM = 60;
  const maxBPM = 200;
  const downsampledRate = sampleRate / downsampleFactor;
  const minLag = Math.floor(60 / maxBPM * downsampledRate);
  const maxLag = Math.floor(60 / minBPM * downsampledRate);
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
  const bpm = 60 * downsampledRate / bestLag;
  reportProgress("bpm", 1, "BPM detection complete");
  return Math.round(Math.max(minBPM, Math.min(maxBPM, bpm)));
}
function applyEnvelopeFollower(signal, smoothing) {
  const envelope = [];
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
async function analyzeAudio(channelData, sampleRate, fps) {
  cancelled = false;
  const duration = channelData.length / sampleRate;
  const frameCount = Math.ceil(duration * fps);
  reportProgress("amplitude", 0, "Extracting amplitude envelope...");
  const amplitudeEnvelope = extractAmplitudeEnvelope(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("amplitude", 1, "Amplitude envelope complete");
  reportProgress("rms", 0, "Calculating RMS energy...");
  const rmsEnergy = extractRMSEnergy(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("rms", 1, "RMS energy complete");
  reportProgress("frequency", 0, "Analyzing frequency bands...");
  const frequencyBands = extractFrequencyBands(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("frequency", 1, "Frequency bands complete");
  reportProgress("spectral", 0, "Computing spectral centroid...");
  const spectralCentroid = extractSpectralCentroid(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectral", 1, "Spectral centroid complete");
  reportProgress("zcr", 0, "Computing zero crossing rate...");
  const zeroCrossingRate = extractZeroCrossingRate(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("zcr", 1, "Zero crossing rate complete");
  reportProgress("spectralFlux", 0, "Computing spectral flux...");
  const spectralFlux = extractSpectralFlux(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralFlux", 1, "Spectral flux complete");
  reportProgress("spectralRolloff", 0, "Computing spectral rolloff...");
  const spectralRolloff = extractSpectralRolloff(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralRolloff", 1, "Spectral rolloff complete");
  reportProgress("spectralFlatness", 0, "Computing spectral flatness...");
  const spectralFlatness = extractSpectralFlatness(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("spectralFlatness", 1, "Spectral flatness complete");
  reportProgress("chroma", 0, "Computing chroma features...");
  const chromaFeatures = extractChromaFeatures(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("chroma", 1, "Chroma features complete");
  reportProgress("onsets", 0, "Detecting onsets...");
  const onsets = detectOnsets(channelData, sampleRate, fps);
  if (cancelled) throw new Error("Cancelled");
  reportProgress("onsets", 1, "Onset detection complete");
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
    chromaFeatures
  };
}
self.onmessage = async (event) => {
  const message = event.data;
  switch (message.type) {
    case "analyze":
      try {
        const { channelData, sampleRate, fps } = message.payload;
        const analysis = await analyzeAudio(channelData, sampleRate, fps);
        reportComplete(analysis);
      } catch (error) {
        if (error.message === "Cancelled") {
          reportError("Analysis cancelled");
        } else {
          reportError(`Analysis failed: ${error.message}`);
        }
      }
      break;
    case "cancel":
      cancelled = true;
      break;
  }
};
