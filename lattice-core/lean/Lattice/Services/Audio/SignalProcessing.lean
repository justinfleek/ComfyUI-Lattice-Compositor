/-
  Lattice.Services.Audio.SignalProcessing - Audio Signal Processing Math

  Pure mathematical functions for audio feature extraction:
  - DFT (Discrete Fourier Transform) with windowing
  - Spectral features (centroid, flux, rolloff, flatness)
  - Mel scale conversions
  - DCT (Discrete Cosine Transform)
  - Feature curves and normalization
  - Peak detection algorithms
  - Envelope following

  Features:
  - All computations are pure (no AudioContext dependency)
  - Suitable for deterministic audio-reactive animations
  - Operates on pre-extracted sample arrays

  Source: ui/src/services/audioFeatures.ts
-/

namespace Lattice.Services.Audio.SignalProcessing

--------------------------------------------------------------------------------
-- Window Functions
--------------------------------------------------------------------------------

/-- Hanning window coefficient for sample i of window size n.

    w(i) = 0.5 * (1 - cos(2πi / (n-1))) -/
def hanningCoeff (i n : Nat) : Float :=
  if n <= 1 then 1.0
  else
    let denominator := (n - 1).toFloat
    0.5 * (1.0 - Float.cos (2.0 * Float.pi * i.toFloat / denominator))

/-- Apply Hanning window to array of samples. -/
def applyHanningWindow (samples : Array Float) : Array Float :=
  let n := samples.size
  samples.mapIdx fun i sample => sample * hanningCoeff i.val n

--------------------------------------------------------------------------------
-- DFT (Discrete Fourier Transform)
--------------------------------------------------------------------------------

/-- Compute magnitude at frequency bin k using DFT.

    X(k) = Σ x(n) * e^(-j2πkn/N)
    |X(k)| = sqrt(real² + imag²) / N -/
def dftBinMagnitude (samples : Array Float) (k : Nat) : Float :=
  let n := samples.size
  if n == 0 then 0.0
  else
    let angleCoeff := 2.0 * Float.pi * k.toFloat / n.toFloat
    let (real, imag) := samples.foldl (init := (0.0, 0.0)) fun (r, i) (idx, sample) =>
      let angle := angleCoeff * idx.toFloat
      (r + sample * Float.cos angle, i - sample * Float.sin angle)
    Float.sqrt (real * real + imag * imag) / n.toFloat
  where
    foldWithIndex (samples : Array Float) : (Float × Float) :=
      let n := samples.size
      samples.foldl (init := (0.0, 0.0, 0)) fun (r, i, idx) sample =>
        let angle := 2.0 * Float.pi * k.toFloat * idx.toFloat / n.toFloat
        (r + sample * Float.cos angle, i - sample * Float.sin angle, idx + 1)
      |>.fst

/-- Compute magnitude spectrum using simple DFT (first half). -/
def simpleDFT (samples : Array Float) : Array Float :=
  let n := samples.size
  let halfN := n / 2
  let windowed := applyHanningWindow samples
  Array.range halfN |>.map fun k =>
    let angleCoeff := 2.0 * Float.pi * k.toFloat / n.toFloat
    let (real, imag) := windowed.foldl (init := (0.0, 0.0)) fun (acc : Float × Float) sample =>
      -- Note: We need index tracking
      (acc.1, acc.2)  -- Placeholder
    -- Proper implementation with index
    computeBinMagnitude windowed k
  where
    computeBinMagnitude (samples : Array Float) (k : Nat) : Float :=
      let n := samples.size
      if n == 0 then 0.0
      else
        let result := Array.range n |>.foldl (init := (0.0, 0.0)) fun (r, i) t =>
          let sample := samples[t]!
          let angle := 2.0 * Float.pi * k.toFloat * t.toFloat / n.toFloat
          (r + sample * Float.cos angle, i - sample * Float.sin angle)
        Float.sqrt (result.1 * result.1 + result.2 * result.2) / n.toFloat

--------------------------------------------------------------------------------
-- Spectral Features
--------------------------------------------------------------------------------

/-- Spectral centroid: frequency-weighted mean of spectrum.

    centroid = Σ(f_k * |X(k)|) / Σ|X(k)|

    Returns centroid in Hz given bin frequency spacing. -/
def spectralCentroid (magnitudes : Array Float) (binFrequency : Float) : Float :=
  let (weightedSum, totalMag) := magnitudes.foldl (init := (0.0, 0.0, 0)) fun (ws, tm, idx) mag =>
    let freq := idx.toFloat * binFrequency
    (ws + freq * mag, tm + mag, idx + 1)
  |> fun (ws, tm, _) => (ws, tm)
  if totalMag > 0.0 then weightedSum / totalMag else 0.0

/-- Spectral flux: rate of spectral change between frames.

    flux = Σ max(0, |X_t(k)| - |X_{t-1}(k)|)

    Only counts positive differences (energy increases). -/
def spectralFlux (currentSpectrum prevSpectrum : Array Float) : Float :=
  let minLen := min currentSpectrum.size prevSpectrum.size
  Array.range minLen |>.foldl (init := 0.0) fun acc k =>
    let curr := currentSpectrum[k]!
    let prev := prevSpectrum[k]!
    let diff := curr - prev
    if diff > 0.0 then acc + diff else acc

/-- Spectral rolloff: frequency below which rolloffPercent of energy lies.

    Finds k where Σ_{i=0}^{k} |X(i)|² >= rolloffPercent * Σ|X|² -/
def spectralRolloff (magnitudes : Array Float) (rolloffPercent : Float) (binFrequency : Float) : Float :=
  let totalEnergy := magnitudes.foldl (init := 0.0) fun acc m => acc + m
  let threshold := totalEnergy * rolloffPercent
  let (_, rolloffBin) := magnitudes.foldl (init := (0.0, 0)) fun (cumulative, bin) mag =>
    if cumulative >= threshold then (cumulative, bin)
    else (cumulative + mag, bin + 1)
  rolloffBin.toFloat * binFrequency

/-- Spectral flatness: ratio of geometric to arithmetic mean.

    flatness = (Π|X(k)|)^(1/N) / (Σ|X(k)|/N)

    0 = tonal (clear pitch), 1 = noise-like -/
def spectralFlatness (magnitudes : Array Float) : Float :=
  -- Filter out near-zero values to avoid log(0)
  let nonZero := magnitudes.filter (· > 1e-10)
  if nonZero.size == 0 then 0.0
  else
    let n := nonZero.size.toFloat
    -- Geometric mean = exp(mean(log))
    let logSum := nonZero.foldl (init := 0.0) fun acc m => acc + Float.log m
    let geometricMean := Float.exp (logSum / n)
    -- Arithmetic mean
    let sum := nonZero.foldl (init := 0.0) fun acc m => acc + m
    let arithmeticMean := sum / n
    if arithmeticMean > 0.0 then geometricMean / arithmeticMean else 0.0

--------------------------------------------------------------------------------
-- Zero Crossing Rate
--------------------------------------------------------------------------------

/-- Zero crossing rate: number of sign changes per sample.

    Indicates percussiveness/noisiness of signal. -/
def zeroCrossingRate (samples : Array Float) : Float :=
  if samples.size <= 1 then 0.0
  else
    let crossings := Array.range (samples.size - 1) |>.foldl (init := 0) fun count i =>
      let curr := samples[i + 1]!
      let prev := samples[i]!
      if (curr >= 0.0 && prev < 0.0) || (curr < 0.0 && prev >= 0.0)
      then count + 1
      else count
    crossings.toFloat / (samples.size - 1).toFloat

--------------------------------------------------------------------------------
-- Mel Scale Conversion
--------------------------------------------------------------------------------

/-- Convert frequency in Hz to Mel scale.

    mel = 2595 * log10(1 + hz/700) -/
def hzToMel (hz : Float) : Float :=
  2595.0 * Float.log (1.0 + hz / 700.0) / Float.log 10.0

/-- Convert Mel scale to frequency in Hz.

    hz = 700 * (10^(mel/2595) - 1) -/
def melToHz (mel : Float) : Float :=
  700.0 * (Float.exp (mel / 2595.0 * Float.log 10.0) - 1.0)

/-- Convert MIDI note number to frequency in Hz.

    f = 440 * 2^((midi - 69) / 12) -/
def midiToHz (midi : Float) : Float :=
  440.0 * Float.exp ((midi - 69.0) / 12.0 * Float.log 2.0)

/-- Convert frequency in Hz to MIDI note number.

    midi = 69 + 12 * log2(f / 440) -/
def hzToMidi (hz : Float) : Float :=
  if hz <= 0.0 then 0.0
  else 69.0 + 12.0 * Float.log (hz / 440.0) / Float.log 2.0

/-- Get pitch class (0-11) from frequency.

    C=0, C#=1, D=2, ..., B=11 -/
def hzToPitchClass (hz : Float) : Nat :=
  let midi := hzToMidi hz
  let rounded := midi.toUInt32.toNat
  rounded % 12

--------------------------------------------------------------------------------
-- DCT (Discrete Cosine Transform)
--------------------------------------------------------------------------------

/-- DCT-II coefficient at index c for input of length N.

    X(c) = Σ x(m) * cos(π * c * (m + 0.5) / N)

    Used for computing MFCCs from log mel energies. -/
def dctCoeff (logMelEnergies : Array Float) (c : Nat) : Float :=
  let n := logMelEnergies.size
  if n == 0 then 0.0
  else
    Array.range n |>.foldl (init := 0.0) fun acc m =>
      let energy := logMelEnergies[m]!
      let angle := Float.pi * c.toFloat * (m.toFloat + 0.5) / n.toFloat
      acc + energy * Float.cos angle

/-- Compute MFCC coefficients from log mel energies. -/
def computeMFCC (logMelEnergies : Array Float) (numCoeffs : Nat) : Array Float :=
  Array.range numCoeffs |>.map fun c => dctCoeff logMelEnergies c

--------------------------------------------------------------------------------
-- Feature Curves
--------------------------------------------------------------------------------

/-- Curve type for feature transformation. -/
inductive FeatureCurve
  | linear      -- f(x) = x
  | exponential -- f(x) = x²
  | logarithmic -- f(x) = √x
  | smoothstep  -- f(x) = x²(3 - 2x)
  deriving Repr, Inhabited, BEq

/-- Apply feature curve to value in [0, 1].

    Transforms dynamic range for more dramatic or subtle responses. -/
def applyFeatureCurve (value : Float) (curve : FeatureCurve) : Float :=
  let clamped := Float.max 0.0 (Float.min 1.0 value)
  match curve with
  | .linear => clamped
  | .exponential => clamped * clamped
  | .logarithmic => Float.sqrt clamped
  | .smoothstep => clamped * clamped * (3.0 - 2.0 * clamped)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

/-- Normalize array to [minOut, maxOut] range. -/
def normalizeArray (values : Array Float) (minOut maxOut : Float) : Array Float :=
  if values.isEmpty then #[]
  else
    let minVal := values.foldl (init := values[0]!) fun acc v => Float.min acc v
    let maxVal := values.foldl (init := values[0]!) fun acc v => Float.max acc v
    let range := if maxVal == minVal then 1.0 else maxVal - minVal
    let outRange := maxOut - minOut
    values.map fun v => minOut + ((v - minVal) / range) * outRange

/-- Normalize array to [0, 1] range. -/
def normalize01 (values : Array Float) : Array Float :=
  normalizeArray values 0.0 1.0

--------------------------------------------------------------------------------
-- Envelope Follower
--------------------------------------------------------------------------------

/-- Apply envelope follower (attack/release smoothing).

    If sample > envelope: envelope = sample (instant attack)
    Else: envelope = envelope * (1 - smoothing) + sample * smoothing -/
def applyEnvelopeFollower (samples : Array Float) (smoothing : Float) : Array Float :=
  if samples.isEmpty then #[]
  else
    let s := Float.max 0.0 (Float.min 1.0 smoothing)
    samples.foldl (init := (#[], 0.0)) fun (result, env) sample =>
      let newEnv := if sample > env then sample
                    else env * (1.0 - s) + sample * s
      (result.push newEnv, newEnv)
    |>.1

--------------------------------------------------------------------------------
-- Adaptive Threshold
--------------------------------------------------------------------------------

/-- Calculate adaptive threshold using local statistics.

    threshold[i] = mean(window) + sensitivity_factor * std(window)

    @param flux Signal values
    @param windowSize Half-window size for local statistics
    @param sensitivityFactor Multiplier for standard deviation (higher = stricter)
    @return Threshold array same length as input -/
def calculateAdaptiveThreshold (flux : Array Float) (windowSize : Nat) (sensitivityFactor : Float) : Array Float :=
  flux.mapIdx fun i _ =>
    let start := if i.val >= windowSize then i.val - windowSize else 0
    let endIdx := min flux.size (i.val + windowSize + 1)
    -- Extract window
    let window := Array.range (endIdx - start) |>.map fun j => flux[start + j]!
    if window.isEmpty then 0.0
    else
      -- Mean
      let sum := window.foldl (init := 0.0) fun acc v => acc + v
      let mean := sum / window.size.toFloat
      -- Standard deviation
      let sqDiffSum := window.foldl (init := 0.0) fun acc v =>
        let diff := v - mean
        acc + diff * diff
      let std := Float.sqrt (sqDiffSum / window.size.toFloat)
      mean + sensitivityFactor * std

--------------------------------------------------------------------------------
-- Peak Detection
--------------------------------------------------------------------------------

/-- Detect local maxima above threshold.

    Returns array of (index, value) pairs for peaks. -/
def detectLocalMaxima (values : Array Float) (threshold : Float) : Array (Nat × Float) :=
  if values.size <= 2 then #[]
  else
    Array.range (values.size - 2) |>.filterMap fun i =>
      let idx := i + 1
      let prev := values[i]!
      let curr := values[idx]!
      let next := values[idx + 1]!
      if curr > prev && curr > next && curr >= threshold
      then some (idx, curr)
      else none

/-- Filter peaks to enforce minimum distance.

    When peaks are too close, keep the one with higher value. -/
def enforceMinPeakDistance (peaks : Array (Nat × Float)) (minDistance : Nat) : Array (Nat × Float) :=
  peaks.foldl (init := #[]) fun filtered (idx, val) =>
    -- Check if there's a recent peak within minDistance
    let conflict := filtered.find? fun (prevIdx, _) =>
      let diff := if idx >= prevIdx then idx - prevIdx else prevIdx - idx
      diff < minDistance
    match conflict with
    | none => filtered.push (idx, val)
    | some (prevIdx, prevVal) =>
      if val > prevVal then
        -- Replace previous peak with this one
        filtered.filter (fun (pi, _) => pi != prevIdx) |>.push (idx, val)
      else
        -- Keep previous peak
        filtered

--------------------------------------------------------------------------------
-- Chroma Features
--------------------------------------------------------------------------------

/-- Pitch class names for display. -/
def pitchClassNames : Array String :=
  #["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

/-- Accumulate spectrum magnitudes into 12 pitch classes (chroma). -/
def computeChroma (magnitudes : Array Float) (binFrequency : Float) : Array Float :=
  let minFreq := 27.5   -- A0
  let maxFreq := 4186.0 -- C8 (piano range)
  let chroma := Array.mkArray 12 0.0
  magnitudes.foldl (init := (chroma, 1)) fun (acc, bin) mag =>
    let freq := bin.toFloat * binFrequency
    if freq < minFreq || freq > maxFreq then (acc, bin + 1)
    else
      let pitchClass := hzToPitchClass freq
      let updated := acc.set! pitchClass (acc[pitchClass]! + mag)
      (updated, bin + 1)
  |>.1

end Lattice.Services.Audio.SignalProcessing
