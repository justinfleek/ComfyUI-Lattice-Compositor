# WEYL COMPOSITOR — AUDIO ANALYSIS & REACTIVITY

**Document ID**: 10_AUDIO_REACTIVITY  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md), [09_PICKWHIP_DEPENDENCIES.md](./09_PICKWHIP_DEPENDENCIES.md)

> Audio analysis happens **once** at import time.
> Features are stored as **frame-indexed arrays**.
> No live audio contexts exist during evaluation.

---

## 1. CORE PRINCIPLE

```
Audio File Import
       ↓
Decode to PCM (offline)
       ↓
Compute Features (per-frame)
       ↓
Store AudioAnalysis (immutable)
       ↓
Sample at frame N during evaluation (O(1) lookup)
```

**Audio reactivity is pre-computed lookup, not real-time analysis.**

This approach guarantees:
- ✅ Deterministic evaluation
- ✅ Frame-accurate synchronization
- ✅ Scrub-order independence
- ✅ Reproducible exports

---

## 2. AUDIO ANALYSIS STRUCTURE

### 2.1 AudioAnalysis Interface

```typescript
interface AudioAnalysis {
  readonly id: string
  readonly assetId: string        // Reference to audio asset
  readonly sampleRate: number     // Original audio sample rate
  readonly frameRate: number      // Project frame rate
  readonly frameCount: number     // Total frames
  readonly duration: number       // Duration in seconds
  readonly features: AudioFeatures
}
```

### 2.2 AudioFeatures Interface

```typescript
interface AudioFeatures {
  // Time-domain features
  readonly amplitude: Float32Array      // Peak amplitude per frame [0-1]
  readonly rms: Float32Array            // RMS energy per frame [0-1]
  readonly zeroCrossings: Float32Array  // Zero crossing rate per frame
  
  // Frequency-domain features
  readonly spectrum: readonly Float32Array[]  // FFT bins per frame
  readonly spectralCentroid: Float32Array     // Brightness indicator
  readonly spectralRolloff: Float32Array      // High-frequency content
  readonly spectralFlux: Float32Array         // Rate of spectral change
  
  // Rhythm features
  readonly beats: Uint8Array            // 1 = beat detected at frame
  readonly onsets: Uint8Array           // 1 = onset detected at frame
  readonly tempo: number                // Estimated BPM
  
  // Pitch features
  readonly chromagram: readonly Float32Array[]  // 12 pitch classes per frame
  readonly pitchConfidence: Float32Array        // How tonal vs noisy
}
```

---

## 3. ANALYSIS PIPELINE

### 3.1 Full Implementation

```typescript
async function analyzeAudio(
  asset: AudioAsset,
  frameRate: number,
  options: AnalysisOptions = {}
): Promise<AudioAnalysis> {
  // 1. Decode audio to PCM (offline)
  const audioBuffer = await decodeAudioFile(asset.sourcePath)
  
  // 2. Mix to mono for analysis
  const samples = mixToMono(audioBuffer)
  
  // 3. Calculate frame boundaries
  const samplesPerFrame = Math.floor(audioBuffer.sampleRate / frameRate)
  const frameCount = Math.ceil(samples.length / samplesPerFrame)
  
  // 4. Initialize feature arrays
  const features: AudioFeatures = {
    amplitude: new Float32Array(frameCount),
    rms: new Float32Array(frameCount),
    zeroCrossings: new Float32Array(frameCount),
    spectrum: [],
    spectralCentroid: new Float32Array(frameCount),
    spectralRolloff: new Float32Array(frameCount),
    spectralFlux: new Float32Array(frameCount),
    beats: new Uint8Array(frameCount),
    onsets: new Uint8Array(frameCount),
    tempo: 0,
    chromagram: [],
    pitchConfidence: new Float32Array(frameCount)
  }
  
  // 5. Analyze each frame
  const fftSize = options.fftSize ?? 2048
  const hopSize = samplesPerFrame
  
  let prevSpectrum: Float32Array | null = null
  
  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame
    const endSample = Math.min(startSample + samplesPerFrame, samples.length)
    const frameSamples = samples.slice(startSample, endSample)
    
    // Time-domain features
    features.amplitude[frame] = computePeakAmplitude(frameSamples)
    features.rms[frame] = computeRMS(frameSamples)
    features.zeroCrossings[frame] = computeZeroCrossings(frameSamples)
    
    // Frequency-domain features
    const paddedSamples = padToLength(frameSamples, fftSize)
    const windowed = applyHannWindow(paddedSamples)
    const spectrum = computeFFT(windowed)
    
    features.spectrum.push(spectrum)
    features.spectralCentroid[frame] = computeSpectralCentroid(spectrum, audioBuffer.sampleRate)
    features.spectralRolloff[frame] = computeSpectralRolloff(spectrum, 0.85)
    
    if (prevSpectrum) {
      features.spectralFlux[frame] = computeSpectralFlux(spectrum, prevSpectrum)
    }
    prevSpectrum = spectrum
    
    // Pitch features
    const chroma = computeChromagram(spectrum, audioBuffer.sampleRate)
    features.chromagram.push(chroma)
    features.pitchConfidence[frame] = computePitchConfidence(chroma)
  }
  
  // 6. Detect beats and onsets
  detectBeats(features)
  detectOnsets(features)
  features.tempo = estimateTempo(features, frameRate)
  
  return Object.freeze({
    id: generateId(),
    assetId: asset.id,
    sampleRate: audioBuffer.sampleRate,
    frameRate,
    frameCount,
    duration: samples.length / audioBuffer.sampleRate,
    features: Object.freeze(features)
  })
}
```

### 3.2 Feature Computation Functions

```typescript
function computePeakAmplitude(samples: Float32Array): number {
  let max = 0
  for (let i = 0; i < samples.length; i++) {
    const abs = Math.abs(samples[i])
    if (abs > max) max = abs
  }
  return max
}

function computeRMS(samples: Float32Array): number {
  let sum = 0
  for (let i = 0; i < samples.length; i++) {
    sum += samples[i] * samples[i]
  }
  return Math.sqrt(sum / samples.length)
}

function computeZeroCrossings(samples: Float32Array): number {
  let count = 0
  for (let i = 1; i < samples.length; i++) {
    if ((samples[i] >= 0) !== (samples[i - 1] >= 0)) {
      count++
    }
  }
  return count / samples.length
}

function computeSpectralCentroid(spectrum: Float32Array, sampleRate: number): number {
  let weightedSum = 0
  let sum = 0
  const binWidth = sampleRate / (spectrum.length * 2)
  
  for (let i = 0; i < spectrum.length; i++) {
    const frequency = i * binWidth
    weightedSum += frequency * spectrum[i]
    sum += spectrum[i]
  }
  
  return sum > 0 ? weightedSum / sum : 0
}

function computeSpectralRolloff(spectrum: Float32Array, threshold: number): number {
  let total = 0
  for (let i = 0; i < spectrum.length; i++) {
    total += spectrum[i]
  }
  
  const target = total * threshold
  let cumulative = 0
  
  for (let i = 0; i < spectrum.length; i++) {
    cumulative += spectrum[i]
    if (cumulative >= target) {
      return i / spectrum.length
    }
  }
  
  return 1
}

function computeSpectralFlux(current: Float32Array, previous: Float32Array): number {
  let flux = 0
  for (let i = 0; i < current.length; i++) {
    const diff = current[i] - previous[i]
    if (diff > 0) flux += diff  // Half-wave rectification
  }
  return flux
}

function computeChromagram(spectrum: Float32Array, sampleRate: number): Float32Array {
  const chroma = new Float32Array(12)
  const binWidth = sampleRate / (spectrum.length * 2)
  
  for (let i = 1; i < spectrum.length; i++) {
    const frequency = i * binWidth
    if (frequency < 20 || frequency > 8000) continue
    
    const pitch = 12 * Math.log2(frequency / 440) + 69
    const pitchClass = Math.round(pitch) % 12
    chroma[pitchClass] += spectrum[i]
  }
  
  // Normalize
  const max = Math.max(...chroma)
  if (max > 0) {
    for (let i = 0; i < 12; i++) {
      chroma[i] /= max
    }
  }
  
  return chroma
}
```

### 3.3 Beat Detection

```typescript
function detectBeats(features: AudioFeatures): void {
  // Use spectral flux for onset detection
  const flux = features.spectralFlux
  const threshold = computeAdaptiveThreshold(flux, 8)  // 8-frame window
  
  for (let i = 1; i < flux.length - 1; i++) {
    // Peak picking with adaptive threshold
    if (flux[i] > flux[i - 1] && 
        flux[i] > flux[i + 1] && 
        flux[i] > threshold[i]) {
      features.beats[i] = 1
    }
  }
}

function detectOnsets(features: AudioFeatures): void {
  // Onsets are more sensitive than beats
  const flux = features.spectralFlux
  const threshold = computeAdaptiveThreshold(flux, 4)  // 4-frame window
  
  for (let i = 1; i < flux.length; i++) {
    if (flux[i] > threshold[i] && flux[i] > flux[i - 1]) {
      features.onsets[i] = 1
    }
  }
}

function computeAdaptiveThreshold(
  signal: Float32Array, 
  windowSize: number
): Float32Array {
  const threshold = new Float32Array(signal.length)
  const halfWindow = Math.floor(windowSize / 2)
  
  for (let i = 0; i < signal.length; i++) {
    const start = Math.max(0, i - halfWindow)
    const end = Math.min(signal.length, i + halfWindow + 1)
    
    let sum = 0
    for (let j = start; j < end; j++) {
      sum += signal[j]
    }
    
    const mean = sum / (end - start)
    threshold[i] = mean * 1.5  // 150% of local mean
  }
  
  return threshold
}

function estimateTempo(features: AudioFeatures, frameRate: number): number {
  // Count beats and calculate BPM
  let beatCount = 0
  for (let i = 0; i < features.beats.length; i++) {
    beatCount += features.beats[i]
  }
  
  if (beatCount < 2) return 0
  
  const durationSeconds = features.beats.length / frameRate
  const bpm = (beatCount / durationSeconds) * 60
  
  // Constrain to reasonable range
  return Math.max(60, Math.min(200, bpm))
}
```

---

## 4. FEATURE ACCESS AT EVALUATION

### 4.1 Direct Frame Lookup

```typescript
function getAudioFeature(
  analysis: AudioAnalysis,
  feature: AudioFeatureName,
  frame: number,
  band?: number
): number {
  // Clamp frame to valid range
  const clampedFrame = Math.max(0, Math.min(frame, analysis.frameCount - 1))
  
  switch (feature) {
    case 'amplitude':
      return analysis.features.amplitude[clampedFrame]
    
    case 'rms':
      return analysis.features.rms[clampedFrame]
    
    case 'spectrum':
      const spectrum = analysis.features.spectrum[clampedFrame]
      return spectrum?.[band ?? 0] ?? 0
    
    case 'spectralCentroid':
      return analysis.features.spectralCentroid[clampedFrame]
    
    case 'beat':
      return analysis.features.beats[clampedFrame]
    
    case 'onset':
      return analysis.features.onsets[clampedFrame]
    
    case 'chroma':
      const chroma = analysis.features.chromagram[clampedFrame]
      return chroma?.[band ?? 0] ?? 0
    
    default:
      return 0
  }
}

type AudioFeatureName = 
  | 'amplitude' 
  | 'rms' 
  | 'spectrum' 
  | 'spectralCentroid'
  | 'spectralRolloff'
  | 'beat' 
  | 'onset'
  | 'chroma'
```

### 4.2 Smoothed Feature Access

```typescript
function getSmoothedFeature(
  analysis: AudioAnalysis,
  feature: AudioFeatureName,
  frame: number,
  windowSize: number = 3
): number {
  const features = getFeatureArray(analysis, feature)
  if (!features) return 0
  
  let sum = 0
  let count = 0
  
  const halfWindow = Math.floor(windowSize / 2)
  const start = Math.max(0, frame - halfWindow)
  const end = Math.min(analysis.frameCount - 1, frame + halfWindow)
  
  for (let i = start; i <= end; i++) {
    sum += features[i]
    count++
  }
  
  return count > 0 ? sum / count : 0
}

function getFeatureArray(
  analysis: AudioAnalysis,
  feature: AudioFeatureName
): Float32Array | Uint8Array | null {
  switch (feature) {
    case 'amplitude': return analysis.features.amplitude
    case 'rms': return analysis.features.rms
    case 'spectralCentroid': return analysis.features.spectralCentroid
    case 'beat': return analysis.features.beats
    case 'onset': return analysis.features.onsets
    default: return null
  }
}
```

---

## 5. AUDIO PROPERTY MAPPING

### 5.1 Mapping Interface

```typescript
interface AudioPropertyMapping {
  readonly targetProperty: PropertyPath
  readonly audioFeature: AudioSourcePath
  readonly transform?: MappingFunction
  readonly smoothing?: number  // Frames to smooth over
}

interface AudioSourcePath {
  readonly type: 'audio'
  readonly feature: AudioFeatureName
  readonly band?: number  // For spectrum/chroma
}
```

### 5.2 Common Mappings

```typescript
// Scale by amplitude
const scaleByAmplitude: AudioPropertyMapping = {
  targetProperty: { layerId: 'layer-1', property: 'transform.scale.x' },
  audioFeature: { type: 'audio', feature: 'amplitude' },
  transform: (v, f) => 1 + v * 0.5,  // 1.0 to 1.5
  smoothing: 2
}

// Rotate by spectral centroid
const rotateByBrightness: AudioPropertyMapping = {
  targetProperty: { layerId: 'layer-1', property: 'transform.rotation.z' },
  audioFeature: { type: 'audio', feature: 'spectralCentroid' },
  transform: (v, f) => v * 360  // Map to degrees
}

// Opacity pulse on beats
const opacityOnBeat: AudioPropertyMapping = {
  targetProperty: { layerId: 'layer-1', property: 'opacity' },
  audioFeature: { type: 'audio', feature: 'beat' },
  transform: (v, f) => v === 1 ? 1 : 0.3  // Flash on beat
}

// Color by bass frequencies
const colorByBass: AudioPropertyMapping = {
  targetProperty: { layerId: 'layer-1', property: 'fill.color.r' },
  audioFeature: { type: 'audio', feature: 'spectrum', band: 2 },
  transform: (v, f) => Math.min(1, v * 3)
}
```

---

## 6. INTEGRATION WITH MOTIONENGINE

### 6.1 Passing AudioAnalysis

```typescript
function evaluate(
  frame: number,
  project: WeylProject,
  audioAnalysis?: AudioAnalysis
): FrameState {
  // Audio analysis is passed through to all evaluations
  const propertyValues = evaluateProperties(
    project.composition,
    frame,
    audioAnalysis  // Used for audio-driven properties
  )
  
  // ... rest of evaluation
}
```

### 6.2 Resolving Audio Sources

```typescript
function resolveSource(
  source: PropertyPath | AudioSourcePath,
  values: Map<string, unknown>,
  frame: number,
  audioAnalysis?: AudioAnalysis
): number {
  if ('type' in source && source.type === 'audio') {
    // Audio source
    if (!audioAnalysis) {
      console.warn('Audio source requested but no analysis provided')
      return 0
    }
    return getAudioFeature(audioAnalysis, source.feature, frame, source.band)
  }
  
  // Property source
  const key = pathToKey(source as PropertyPath)
  return values.get(key) as number ?? 0
}
```

---

## 7. AUDIO EXPORT FOR COMFYUI

### 7.1 Export Format

```typescript
interface AudioConditioningExport {
  readonly version: string
  readonly frameRate: number
  readonly frameCount: number
  
  // Primary features for diffusion models
  readonly amplitude: Float32Array
  readonly rms: Float32Array
  readonly beats: Uint8Array
  
  // Flattened spectrum [frames × bins]
  readonly spectrum: Float32Array
  readonly spectrumBins: number
  
  // Metadata
  readonly tempo: number
  readonly duration: number
}
```

### 7.2 Export Function

```typescript
function exportAudioConditioning(
  analysis: AudioAnalysis,
  outputPath: string
): void {
  const spectrumBins = analysis.features.spectrum[0]?.length ?? 0
  const flatSpectrum = new Float32Array(analysis.frameCount * spectrumBins)
  
  for (let f = 0; f < analysis.frameCount; f++) {
    flatSpectrum.set(analysis.features.spectrum[f], f * spectrumBins)
  }
  
  const export_: AudioConditioningExport = {
    version: '1.0.0',
    frameRate: analysis.frameRate,
    frameCount: analysis.frameCount,
    amplitude: analysis.features.amplitude,
    rms: analysis.features.rms,
    beats: analysis.features.beats,
    spectrum: flatSpectrum,
    spectrumBins,
    tempo: analysis.features.tempo,
    duration: analysis.duration
  }
  
  // Save as .npz for Python/ComfyUI compatibility
  saveAsNumpy(export_, outputPath)
}
```

### 7.3 Compatible Models

Audio conditioning works with:

| Model | Feature Used |
|-------|--------------|
| **ATI** (Audio-to-Image) | Spectrum, amplitude |
| **AudioReactive ControlNet** | Beat, amplitude |
| **Wan Audio** extensions | All features |
| **RyanOnTheInside** | Amplitude, spectrum, beats |

---

## 8. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Live audio context during evaluation
const audioContext = new AudioContext()
const analyser = audioContext.createAnalyser()
analyser.getFloatTimeDomainData(buffer)

// ❌ FORBIDDEN: Real-time FFT
function onAudioProcess(event) {
  const spectrum = computeFFT(event.inputBuffer)  // NO!
}

// ❌ FORBIDDEN: Audio playback affecting evaluation
audio.play()
const time = audio.currentTime  // Don't use for frame sync

// ❌ FORBIDDEN: Web Audio API during evaluation
navigator.mediaDevices.getUserMedia()
ScriptProcessorNode, AudioWorkletNode

// ❌ FORBIDDEN: Time-dependent audio access
const amplitude = getCurrentAmplitude()  // "Current" implies real-time

// ✅ REQUIRED: Pre-computed lookup
const amplitude = analysis.features.amplitude[frame]
const spectrum = analysis.features.spectrum[frame]
const beat = analysis.features.beats[frame]
```

---

## 9. TESTING REQUIREMENTS

```typescript
describe('Audio Analysis', () => {
  it('produces identical features for same audio', async () => {
    const a = await analyzeAudio(asset, 30)
    const b = await analyzeAudio(asset, 30)
    
    expect(a.features.amplitude).toEqual(b.features.amplitude)
    expect(a.features.spectrum).toEqual(b.features.spectrum)
    expect(a.features.beats).toEqual(b.features.beats)
  })

  it('frame lookup is O(1)', () => {
    const analysis = createMockAnalysis(10000)  // 10k frames
    
    const start = performance.now()
    for (let i = 0; i < 10000; i++) {
      getAudioFeature(analysis, 'amplitude', i)
    }
    const elapsed = performance.now() - start
    
    expect(elapsed).toBeLessThan(10)  // Should be very fast
  })

  it('features are immutable', () => {
    const analysis = await analyzeAudio(asset, 30)
    
    expect(Object.isFrozen(analysis)).toBe(true)
    expect(Object.isFrozen(analysis.features)).toBe(true)
    
    expect(() => {
      analysis.features.amplitude[0] = 999
    }).toThrow()
  })

  it('beat detection is deterministic', async () => {
    const a = await analyzeAudio(asset, 30)
    const b = await analyzeAudio(asset, 30)
    
    expect(a.features.beats).toEqual(b.features.beats)
  })
})

describe('Audio Property Mapping', () => {
  it('audio-driven properties are deterministic', () => {
    const analysis = createMockAnalysis(100)
    analysis.features.amplitude[50] = 0.8
    
    const a = motionEngine.evaluate(50, project, analysis)
    const b = motionEngine.evaluate(50, project, analysis)
    
    expect(a.layers[0].transform.scale.x).toEqual(b.layers[0].transform.scale.x)
  })

  it('missing audio returns fallback', () => {
    const result = motionEngine.evaluate(50, project, undefined)
    
    // Should use default value, not crash
    expect(result.layers[0].transform.scale.x).toBe(1)
  })
})
```

---

## 10. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Audio analysis happens at import time, not evaluation time
- [ ] No `AudioContext` usage during evaluation
- [ ] No real-time FFT computation
- [ ] All audio features are frame-indexed arrays
- [ ] Feature lookup is O(1) array access
- [ ] Analysis results are immutable (frozen)
- [ ] Beat detection is deterministic
- [ ] Audio export format is ComfyUI-compatible
- [ ] Missing audio gracefully returns fallback values
- [ ] Scrubbing with audio produces identical results

**Any real-time audio processing during evaluation is a critical violation.**

---

**Previous**: [09_PICKWHIP_DEPENDENCIES.md](./09_PICKWHIP_DEPENDENCIES.md)  
**Next**: [11_PRECOMPOSITION.md](./11_PRECOMPOSITION.md)
