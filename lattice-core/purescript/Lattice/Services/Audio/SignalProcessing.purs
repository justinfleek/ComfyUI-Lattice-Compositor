-- | Lattice.Services.Audio.SignalProcessing - Audio Signal Processing Math
-- |
-- | Pure mathematical functions for audio feature extraction:
-- | - DFT (Discrete Fourier Transform) with windowing
-- | - Spectral features (centroid, flux, rolloff, flatness)
-- | - Mel scale conversions
-- | - DCT (Discrete Cosine Transform)
-- | - Feature curves and normalization
-- | - Peak detection algorithms
-- | - Envelope following
-- |
-- | Features:
-- | - All computations are pure (no AudioContext dependency)
-- | - Suitable for deterministic audio-reactive animations
-- | - Operates on pre-extracted sample arrays
-- |
-- | Source: ui/src/services/audioFeatures.ts

module Lattice.Services.Audio.SignalProcessing
  ( FeatureCurve(..)
  , hanningCoeff
  , applyHanningWindow
  , computeBinMagnitude
  , simpleDFT
  , spectralCentroid
  , spectralFlux
  , spectralRolloff
  , spectralFlatness
  , zeroCrossingRate
  , hzToMel
  , melToHz
  , midiToHz
  , hzToMidi
  , hzToPitchClass
  , dctCoeff
  , computeMFCC
  , applyFeatureCurve
  , normalizeArray
  , normalize01
  , applyEnvelopeFollower
  , calculateAdaptiveThreshold
  , detectLocalMaxima
  , enforceMinPeakDistance
  , pitchClassNames
  , computeChroma
  ) where

import Prelude

import Data.Array (filter, foldl, length, mapWithIndex, range, sortBy, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (abs) as Ord
import Data.Tuple (Tuple(..))
import Math (cos, exp, log, pi, sin, sqrt) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Window Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Hanning window coefficient for sample i of window size n.
-- |
-- | w(i) = 0.5 * (1 - cos(2πi / (n-1)))
hanningCoeff :: Int -> Int -> Number
hanningCoeff i n
  | n <= 1 = 1.0
  | otherwise = 0.5 * (1.0 - Math.cos (2.0 * Math.pi * toNumber i / toNumber (n - 1)))

-- | Apply Hanning window to array of samples.
applyHanningWindow :: Array Number -> Array Number
applyHanningWindow samples =
  let n = length samples
  in mapWithIndex (\i s -> s * hanningCoeff i n) samples

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // dft
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute magnitude at frequency bin k using DFT.
-- |
-- | X(k) = Σ x(n) * e^(-j2πkn/N)
-- | |X(k)| = sqrt(real² + imag²) / N
computeBinMagnitude :: Array Number -> Int -> Number
computeBinMagnitude samples k =
  let n = length samples
  in if n == 0 then 0.0
     else
      let angleCoeff = 2.0 * Math.pi * toNumber k / toNumber n
          result = foldlWithIndex (\acc t sample ->
            let angle = angleCoeff * toNumber t
                r = acc.real + sample * Math.cos angle
                i = acc.imag - sample * Math.sin angle
            in { real: r, imag: i }
          ) { real: 0.0, imag: 0.0 } samples
      in Math.sqrt (result.real * result.real + result.imag * result.imag) / toNumber n

-- | Compute magnitude spectrum using simple DFT (first half).
simpleDFT :: Array Number -> Array Number
simpleDFT samples =
  let n = length samples
      halfN = n / 2
      windowed = applyHanningWindow samples
  in map (computeBinMagnitude windowed) (range 0 (halfN - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Spectral Features
-- ────────────────────────────────────────────────────────────────────────────

-- | Spectral centroid: frequency-weighted mean of spectrum.
-- |
-- | centroid = Σ(f_k * |X(k)|) / Σ|X(k)|
spectralCentroid :: Array Number -> Number -> Number
spectralCentroid magnitudes binFrequency =
  let result = foldlWithIndex (\acc idx mag ->
        let freq = toNumber idx * binFrequency
        in { ws: acc.ws + freq * mag, tm: acc.tm + mag }
      ) { ws: 0.0, tm: 0.0 } magnitudes
  in if result.tm > 0.0 then result.ws / result.tm else 0.0

-- | Spectral flux: rate of spectral change between frames.
-- |
-- | flux = Σ max(0, |X_t(k)| - |X_{t-1}(k)|)
spectralFlux :: Array Number -> Array Number -> Number
spectralFlux currentSpectrum prevSpectrum =
  let minLen = min (length currentSpectrum) (length prevSpectrum)
  in foldl (\acc k ->
       let curr = fromMaybe 0.0 (currentSpectrum !! k)
           prev = fromMaybe 0.0 (prevSpectrum !! k)
           diff = curr - prev
       in if diff > 0.0 then acc + diff else acc
     ) 0.0 (range 0 (minLen - 1))

-- | Spectral rolloff: frequency below which rolloffPercent of energy lies.
spectralRolloff :: Array Number -> Number -> Number -> Number
spectralRolloff magnitudes rolloffPercent binFrequency =
  let totalEnergy = foldl (+) 0.0 magnitudes
      threshold = totalEnergy * rolloffPercent
      result = foldl (\acc mag ->
        if acc.cumulative >= threshold then acc
        else { cumulative: acc.cumulative + mag, bin: acc.bin + 1 }
      ) { cumulative: 0.0, bin: 0 } magnitudes
  in toNumber result.bin * binFrequency

-- | Spectral flatness: ratio of geometric to arithmetic mean.
-- |
-- | 0 = tonal (clear pitch), 1 = noise-like
spectralFlatness :: Array Number -> Number
spectralFlatness magnitudes =
  let nonZero = filter (_ > 1.0e-10) magnitudes
      n = length nonZero
  in if n == 0 then 0.0
     else
       let nf = toNumber n
           logSum = foldl (\acc m -> acc + Math.log m) 0.0 nonZero
           geometricMean = Math.exp (logSum / nf)
           arithmeticMean = foldl (+) 0.0 nonZero / nf
       in if arithmeticMean > 0.0 then geometricMean / arithmeticMean else 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Zero Crossing Rate
-- ────────────────────────────────────────────────────────────────────────────

-- | Zero crossing rate: number of sign changes per sample.
zeroCrossingRate :: Array Number -> Number
zeroCrossingRate samples
  | length samples <= 1 = 0.0
  | otherwise =
      let n = length samples
          crossings = foldl (\acc i ->
            let curr = fromMaybe 0.0 (samples !! (i + 1))
                prev = fromMaybe 0.0 (samples !! i)
            in if (curr >= 0.0 && prev < 0.0) || (curr < 0.0 && prev >= 0.0)
               then acc + 1.0 else acc
          ) 0.0 (range 0 (n - 2))
      in crossings / toNumber (n - 1)

-- ────────────────────────────────────────────────────────────────────────────
-- Mel Scale Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert frequency in Hz to Mel scale.
-- |
-- | mel = 2595 * log10(1 + hz/700)
hzToMel :: Number -> Number
hzToMel hz = 2595.0 * Math.log (1.0 + hz / 700.0) / Math.log 10.0

-- | Convert Mel scale to frequency in Hz.
-- |
-- | hz = 700 * (10^(mel/2595) - 1)
melToHz :: Number -> Number
melToHz mel = 700.0 * (Math.exp (mel / 2595.0 * Math.log 10.0) - 1.0)

-- | Convert MIDI note number to frequency in Hz.
-- |
-- | f = 440 * 2^((midi - 69) / 12)
midiToHz :: Number -> Number
midiToHz midi = 440.0 * Math.exp ((midi - 69.0) / 12.0 * Math.log 2.0)

-- | Convert frequency in Hz to MIDI note number.
-- |
-- | midi = 69 + 12 * log2(f / 440)
hzToMidi :: Number -> Number
hzToMidi hz
  | hz <= 0.0 = 0.0
  | otherwise = 69.0 + 12.0 * Math.log (hz / 440.0) / Math.log 2.0

-- | Get pitch class (0-11) from frequency.
-- |
-- | C=0, C#=1, D=2, ..., B=11
hzToPitchClass :: Number -> Int
hzToPitchClass hz =
  let midi = hzToMidi hz
      rounded = toInt midi
  in rounded `mod` 12

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // dct
-- ────────────────────────────────────────────────────────────────────────────

-- | DCT-II coefficient at index c for input of length N.
-- |
-- | X(c) = Σ x(m) * cos(π * c * (m + 0.5) / N)
dctCoeff :: Array Number -> Int -> Number
dctCoeff logMelEnergies c
  | length logMelEnergies == 0 = 0.0
  | otherwise =
      let n = length logMelEnergies
          nf = toNumber n
      in foldlWithIndex (\acc m energy ->
           let angle = Math.pi * toNumber c * (toNumber m + 0.5) / nf
           in acc + energy * Math.cos angle
         ) 0.0 logMelEnergies

-- | Compute MFCC coefficients from log mel energies.
computeMFCC :: Array Number -> Int -> Array Number
computeMFCC logMelEnergies numCoeffs =
  map (dctCoeff logMelEnergies) (range 0 (numCoeffs - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Feature Curves
-- ────────────────────────────────────────────────────────────────────────────

-- | Curve type for feature transformation.
data FeatureCurve
  = CurveLinear      -- ^ f(x) = x
  | CurveExponential -- ^ f(x) = x²
  | CurveLogarithmic -- ^ f(x) = √x
  | CurveSmoothstep  -- ^ f(x) = x²(3 - 2x)

derive instance eqFeatureCurve :: Eq FeatureCurve

-- | Apply feature curve to value in [0, 1].
applyFeatureCurve :: Number -> FeatureCurve -> Number
applyFeatureCurve value curve =
  let clamped = max 0.0 (min 1.0 value)
  in case curve of
       CurveLinear      -> clamped
       CurveExponential -> clamped * clamped
       CurveLogarithmic -> Math.sqrt clamped
       CurveSmoothstep  -> clamped * clamped * (3.0 - 2.0 * clamped)

-- ────────────────────────────────────────────────────────────────────────────
-- Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Normalize array to [minOut, maxOut] range.
normalizeArray :: Array Number -> Number -> Number -> Array Number
normalizeArray values minOut maxOut
  | length values == 0 = []
  | otherwise =
      let minVal = foldl min (fromMaybe 0.0 (values !! 0)) values
          maxVal = foldl max (fromMaybe 0.0 (values !! 0)) values
          rangeVal = if maxVal == minVal then 1.0 else maxVal - minVal
          outRange = maxOut - minOut
      in map (\v -> minOut + ((v - minVal) / rangeVal) * outRange) values

-- | Normalize array to [0, 1] range.
normalize01 :: Array Number -> Array Number
normalize01 values = normalizeArray values 0.0 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Envelope Follower
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply envelope follower (attack/release smoothing).
applyEnvelopeFollower :: Array Number -> Number -> Array Number
applyEnvelopeFollower samples smoothing
  | length samples == 0 = []
  | otherwise =
      let s = max 0.0 (min 1.0 smoothing)
          step env sample =
            if sample > env then sample
            else env * (1.0 - s) + sample * s
          result = foldl (\acc sample ->
            let newEnv = step acc.env sample
            in { result: acc.result <> [newEnv], env: newEnv }
          ) { result: [], env: 0.0 } samples
      in result.result

-- ────────────────────────────────────────────────────────────────────────────
-- Adaptive Threshold
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate adaptive threshold using local statistics.
calculateAdaptiveThreshold :: Array Number -> Int -> Number -> Array Number
calculateAdaptiveThreshold flux windowSize sensitivityFactor =
  mapWithIndex computeThreshold flux
  where
    computeThreshold i _ =
      let start = max 0 (i - windowSize)
          endIdx = min (length flux) (i + windowSize + 1)
          window = map (\j -> fromMaybe 0.0 (flux !! j)) (range start (endIdx - 1))
          n = length window
      in if n == 0 then 0.0
         else
           let nf = toNumber n
               sumVal = foldl (+) 0.0 window
               mean = sumVal / nf
               sqDiffSum = foldl (\acc v -> acc + (v - mean) * (v - mean)) 0.0 window
               std = Math.sqrt (sqDiffSum / nf)
           in mean + sensitivityFactor * std

-- ────────────────────────────────────────────────────────────────────────────
-- Peak Detection
-- ────────────────────────────────────────────────────────────────────────────

-- | Detect local maxima above threshold.
detectLocalMaxima :: Array Number -> Number -> Array (Tuple Int Number)
detectLocalMaxima values threshold
  | length values <= 2 = []
  | otherwise =
      foldl (\acc i ->
        let prev = fromMaybe 0.0 (values !! i)
            curr = fromMaybe 0.0 (values !! (i + 1))
            next = fromMaybe 0.0 (values !! (i + 2))
        in if curr > prev && curr > next && curr >= threshold
           then acc <> [Tuple (i + 1) curr]
           else acc
      ) [] (range 0 (length values - 3))

-- | Filter peaks to enforce minimum distance.
enforceMinPeakDistance :: Array (Tuple Int Number) -> Int -> Array (Tuple Int Number)
enforceMinPeakDistance peaks minDistance =
  let sorted = sortBy (\(Tuple i1 _) (Tuple i2 _) -> compare i1 i2) peaks
  in foldl addPeak [] sorted
  where
    addPeak filtered (Tuple idx val) =
      let conflict = filter (\(Tuple pi _) -> Ord.abs (pi - idx) < minDistance) filtered
      in case conflict of
           [] -> filtered <> [Tuple idx val]
           _ ->
             case conflict !! 0 of
               Just (Tuple prevIdx prevVal) ->
                 if val > prevVal
                 then filter (\(Tuple pi _) -> pi /= prevIdx) filtered <> [Tuple idx val]
                 else filtered
               Nothing -> filtered

-- ────────────────────────────────────────────────────────────────────────────
-- Chroma Features
-- ────────────────────────────────────────────────────────────────────────────

-- | Pitch class names for display.
pitchClassNames :: Array String
pitchClassNames = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

-- | Accumulate spectrum magnitudes into 12 pitch classes (chroma).
computeChroma :: Array Number -> Number -> Array Number
computeChroma magnitudes binFrequency =
  let minFreq = 27.5   -- A0
      maxFreq = 4186.0 -- C8 (piano range)
      initChroma = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
      result = foldlWithIndex (\acc bin mag ->
        let freq = toNumber bin * binFrequency
        in if freq < minFreq || freq > maxFreq then acc
           else
             let pc = hzToPitchClass freq
                 current = fromMaybe 0.0 (acc !! pc)
             in updateAt pc (current + mag) acc
      ) initChroma magnitudes
  in result

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert Int to Number (pure implementation)
toNumber :: Int -> Number
toNumber n = if n < 0 then negate (toNumberPos (negate n)) else toNumberPos n
  where
    toNumberPos :: Int -> Number
    toNumberPos 0 = 0.0
    toNumberPos i = 1.0 + toNumberPos (i - 1)

-- | Convert Number to Int (floor)
toInt :: Number -> Int
toInt n = toIntImpl n 0
  where
    toIntImpl :: Number -> Int -> Int
    toIntImpl x acc
      | x < 1.0 = acc
      | otherwise = toIntImpl (x - 1.0) (acc + 1)

-- | Fold with index
foldlWithIndex :: forall a b. (b -> Int -> a -> b) -> b -> Array a -> b
foldlWithIndex f init arr =
  let result = foldl (\acc x -> { val: f acc.val acc.idx x, idx: acc.idx + 1 }) { val: init, idx: 0 } arr
  in result.val

-- | Update array at index (pure, returns new array)
updateAt :: forall a. Int -> a -> Array a -> Array a
updateAt idx val arr =
  mapWithIndex (\i x -> if i == idx then val else x) arr
