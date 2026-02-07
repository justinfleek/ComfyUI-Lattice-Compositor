{-|
Module      : Lattice.Services.Audio.SignalProcessing
Description : Audio Signal Processing Math
Copyright   : (c) Lattice Team, 2026
License     : MIT

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
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Audio.SignalProcessing
  ( -- * Window Functions
    hanningCoeff
  , applyHanningWindow
    -- * DFT
  , computeBinMagnitude
  , simpleDFT
    -- * Spectral Features
  , spectralCentroid
  , spectralFlux
  , spectralRolloff
  , spectralFlatness
  , zeroCrossingRate
    -- * Mel Scale
  , hzToMel
  , melToHz
  , midiToHz
  , hzToMidi
  , hzToPitchClass
    -- * DCT
  , dctCoeff
  , computeMFCC
    -- * Feature Curves
  , FeatureCurve(..)
  , applyFeatureCurve
    -- * Normalization
  , normalizeArray
  , normalize01
    -- * Envelope
  , applyEnvelopeFollower
    -- * Threshold
  , calculateAdaptiveThreshold
    -- * Peak Detection
  , detectLocalMaxima
  , enforceMinPeakDistance
    -- * Chroma
  , pitchClassNames
  , computeChroma
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.List (sortBy)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- Window Functions
--------------------------------------------------------------------------------

-- | Hanning window coefficient for sample i of window size n.
--
-- w(i) = 0.5 * (1 - cos(2πi / (n-1)))
hanningCoeff :: Int -> Int -> Double
hanningCoeff i n
  | n <= 1    = 1
  | otherwise = 0.5 * (1 - cos (2 * pi * fromIntegral i / fromIntegral (n - 1)))

-- | Apply Hanning window to array of samples.
applyHanningWindow :: Vector Double -> Vector Double
applyHanningWindow samples =
  let n = V.length samples
  in V.imap (\i s -> s * hanningCoeff i n) samples

--------------------------------------------------------------------------------
-- DFT (Discrete Fourier Transform)
--------------------------------------------------------------------------------

-- | Compute magnitude at frequency bin k using DFT.
--
-- X(k) = Σ x(n) * e^(-j2πkn/N)
-- |X(k)| = sqrt(real² + imag²) / N
computeBinMagnitude :: Vector Double -> Int -> Double
computeBinMagnitude samples k
  | n == 0    = 0
  | otherwise =
      let angleCoeff = 2 * pi * fromIntegral k / fromIntegral n
          (real, imag) = V.ifoldl' accum (0, 0) samples
          accum (r, i) t sample =
            let angle = angleCoeff * fromIntegral t
            in (r + sample * cos angle, i - sample * sin angle)
      in sqrt (real * real + imag * imag) / fromIntegral n
  where
    n = V.length samples

-- | Compute magnitude spectrum using simple DFT (first half).
simpleDFT :: Vector Double -> Vector Double
simpleDFT samples =
  let n = V.length samples
      halfN = n `div` 2
      windowed = applyHanningWindow samples
  in V.generate halfN (computeBinMagnitude windowed)

--------------------------------------------------------------------------------
-- Spectral Features
--------------------------------------------------------------------------------

-- | Spectral centroid: frequency-weighted mean of spectrum.
--
-- centroid = Σ(f_k * |X(k)|) / Σ|X(k)|
--
-- Returns centroid in Hz given bin frequency spacing.
spectralCentroid :: Vector Double -> Double -> Double
spectralCentroid magnitudes binFrequency =
  let (weightedSum, totalMag) = V.ifoldl' accum (0, 0) magnitudes
      accum (ws, tm) idx mag =
        let freq = fromIntegral idx * binFrequency
        in (ws + freq * mag, tm + mag)
  in if totalMag > 0 then weightedSum / totalMag else 0

-- | Spectral flux: rate of spectral change between frames.
--
-- flux = Σ max(0, |X_t(k)| - |X_{t-1}(k)|)
--
-- Only counts positive differences (energy increases).
spectralFlux :: Vector Double -> Vector Double -> Double
spectralFlux currentSpectrum prevSpectrum =
  let minLen = min (V.length currentSpectrum) (V.length prevSpectrum)
  in V.sum $ V.generate minLen $ \k ->
       let curr = currentSpectrum V.! k
           prev = prevSpectrum V.! k
           diff = curr - prev
       in if diff > 0 then diff else 0

-- | Spectral rolloff: frequency below which rolloffPercent of energy lies.
--
-- Finds k where Σ_{i=0}^{k} |X(i)| >= rolloffPercent * Σ|X|
spectralRolloff :: Vector Double -> Double -> Double -> Double
spectralRolloff magnitudes rolloffPercent binFrequency =
  let totalEnergy = V.sum magnitudes
      threshold = totalEnergy * rolloffPercent
      (_, rolloffBin) = V.foldl' step (0, 0) magnitudes
      step (cumulative, bin) mag
        | cumulative >= threshold = (cumulative, bin)
        | otherwise = (cumulative + mag, bin + 1)
  in fromIntegral rolloffBin * binFrequency

-- | Spectral flatness: ratio of geometric to arithmetic mean.
--
-- flatness = (Π|X(k)|)^(1/N) / (Σ|X(k)|/N)
--
-- 0 = tonal (clear pitch), 1 = noise-like
spectralFlatness :: Vector Double -> Double
spectralFlatness magnitudes =
  let nonZero = V.filter (> 1e-10) magnitudes
      n = V.length nonZero
  in if n == 0 then 0
     else
       let nf = fromIntegral n
           logSum = V.sum $ V.map log nonZero
           geometricMean = exp (logSum / nf)
           arithmeticMean = V.sum nonZero / nf
       in if arithmeticMean > 0 then geometricMean / arithmeticMean else 0

--------------------------------------------------------------------------------
-- Zero Crossing Rate
--------------------------------------------------------------------------------

-- | Zero crossing rate: number of sign changes per sample.
--
-- Indicates percussiveness/noisiness of signal.
zeroCrossingRate :: Vector Double -> Double
zeroCrossingRate samples
  | V.length samples <= 1 = 0
  | otherwise =
      let crossings = V.sum $ V.generate (V.length samples - 1) $ \i ->
            let curr = samples V.! (i + 1)
                prev = samples V.! i
            in if (curr >= 0 && prev < 0) || (curr < 0 && prev >= 0)
               then 1 else 0
      in crossings / fromIntegral (V.length samples - 1)

--------------------------------------------------------------------------------
-- Mel Scale Conversion
--------------------------------------------------------------------------------

-- | Convert frequency in Hz to Mel scale.
--
-- mel = 2595 * log10(1 + hz/700)
hzToMel :: Double -> Double
hzToMel hz = 2595 * log (1 + hz / 700) / log 10

-- | Convert Mel scale to frequency in Hz.
--
-- hz = 700 * (10^(mel/2595) - 1)
melToHz :: Double -> Double
melToHz mel = 700 * (exp (mel / 2595 * log 10) - 1)

-- | Convert MIDI note number to frequency in Hz.
--
-- f = 440 * 2^((midi - 69) / 12)
midiToHz :: Double -> Double
midiToHz midi = 440 * exp ((midi - 69) / 12 * log 2)

-- | Convert frequency in Hz to MIDI note number.
--
-- midi = 69 + 12 * log2(f / 440)
hzToMidi :: Double -> Double
hzToMidi hz
  | hz <= 0   = 0
  | otherwise = 69 + 12 * log (hz / 440) / log 2

-- | Get pitch class (0-11) from frequency.
--
-- C=0, C#=1, D=2, ..., B=11
hzToPitchClass :: Double -> Int
hzToPitchClass hz =
  let midi = hzToMidi hz
      rounded = round midi :: Int
  in rounded `mod` 12

--------------------------------------------------------------------------------
-- DCT (Discrete Cosine Transform)
--------------------------------------------------------------------------------

-- | DCT-II coefficient at index c for input of length N.
--
-- X(c) = Σ x(m) * cos(π * c * (m + 0.5) / N)
--
-- Used for computing MFCCs from log mel energies.
dctCoeff :: Vector Double -> Int -> Double
dctCoeff logMelEnergies c
  | V.null logMelEnergies = 0
  | otherwise =
      let n = V.length logMelEnergies
          nf = fromIntegral n
      in V.sum $ V.imap (\m energy ->
           let angle = pi * fromIntegral c * (fromIntegral m + 0.5) / nf
           in energy * cos angle) logMelEnergies

-- | Compute MFCC coefficients from log mel energies.
computeMFCC :: Vector Double -> Int -> Vector Double
computeMFCC logMelEnergies numCoeffs =
  V.generate numCoeffs (dctCoeff logMelEnergies)

--------------------------------------------------------------------------------
-- Feature Curves
--------------------------------------------------------------------------------

-- | Curve type for feature transformation.
data FeatureCurve
  = CurveLinear      -- ^ f(x) = x
  | CurveExponential -- ^ f(x) = x²
  | CurveLogarithmic -- ^ f(x) = √x
  | CurveSmoothstep  -- ^ f(x) = x²(3 - 2x)
  deriving (Show, Eq)

-- | Apply feature curve to value in [0, 1].
--
-- Transforms dynamic range for more dramatic or subtle responses.
applyFeatureCurve :: Double -> FeatureCurve -> Double
applyFeatureCurve value curve =
  let clamped = max 0 (min 1 value)
  in case curve of
       CurveLinear      -> clamped
       CurveExponential -> clamped * clamped
       CurveLogarithmic -> sqrt clamped
       CurveSmoothstep  -> clamped * clamped * (3 - 2 * clamped)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Normalize array to [minOut, maxOut] range.
normalizeArray :: Vector Double -> Double -> Double -> Vector Double
normalizeArray values minOut maxOut
  | V.null values = V.empty
  | otherwise =
      let minVal = V.minimum values
          maxVal = V.maximum values
          range = if maxVal == minVal then 1 else maxVal - minVal
          outRange = maxOut - minOut
      in V.map (\v -> minOut + ((v - minVal) / range) * outRange) values

-- | Normalize array to [0, 1] range.
normalize01 :: Vector Double -> Vector Double
normalize01 values = normalizeArray values 0 1

--------------------------------------------------------------------------------
-- Envelope Follower
--------------------------------------------------------------------------------

-- | Apply envelope follower (attack/release smoothing).
--
-- If sample > envelope: envelope = sample (instant attack)
-- Else: envelope = envelope * (1 - smoothing) + sample * smoothing
applyEnvelopeFollower :: Vector Double -> Double -> Vector Double
applyEnvelopeFollower samples smoothing
  | V.null samples = V.empty
  | otherwise =
      let s = max 0 (min 1 smoothing)
          step env sample =
            if sample > env then sample
            else env * (1 - s) + sample * s
      in V.postscanl' step 0 samples

--------------------------------------------------------------------------------
-- Adaptive Threshold
--------------------------------------------------------------------------------

-- | Calculate adaptive threshold using local statistics.
--
-- threshold[i] = mean(window) + sensitivity_factor * std(window)
calculateAdaptiveThreshold :: Vector Double -> Int -> Double -> Vector Double
calculateAdaptiveThreshold flux windowSize sensitivityFactor =
  V.imap computeThreshold flux
  where
    computeThreshold i _ =
      let start = max 0 (i - windowSize)
          endIdx = min (V.length flux) (i + windowSize + 1)
          window = V.slice start (endIdx - start) flux
      in if V.null window then 0
         else
           let n = fromIntegral (V.length window)
               mean = V.sum window / n
               sqDiffSum = V.sum $ V.map (\v -> (v - mean) * (v - mean)) window
               std = sqrt (sqDiffSum / n)
           in mean + sensitivityFactor * std

--------------------------------------------------------------------------------
-- Peak Detection
--------------------------------------------------------------------------------

-- | Detect local maxima above threshold.
--
-- Returns list of (index, value) pairs for peaks.
detectLocalMaxima :: Vector Double -> Double -> [(Int, Double)]
detectLocalMaxima values threshold
  | V.length values <= 2 = []
  | otherwise =
      [(i + 1, curr) |
        i <- [0 .. V.length values - 3],
        let prev = values V.! i,
        let curr = values V.! (i + 1),
        let next = values V.! (i + 2),
        curr > prev,
        curr > next,
        curr >= threshold]

-- | Filter peaks to enforce minimum distance.
--
-- When peaks are too close, keep the one with higher value.
enforceMinPeakDistance :: [(Int, Double)] -> Int -> [(Int, Double)]
enforceMinPeakDistance peaks minDistance =
  foldl addPeak [] (sortBy (comparing fst) peaks)
  where
    addPeak filtered (idx, val) =
      case filter (\(pi, _) -> abs (pi - idx) < minDistance) filtered of
        [] -> filtered ++ [(idx, val)]
        (prevIdx, prevVal):_ ->
          if val > prevVal
          then filter (\(pi, _) -> pi /= prevIdx) filtered ++ [(idx, val)]
          else filtered

--------------------------------------------------------------------------------
-- Chroma Features
--------------------------------------------------------------------------------

-- | Pitch class names for display.
pitchClassNames :: [String]
pitchClassNames = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

-- | Accumulate spectrum magnitudes into 12 pitch classes (chroma).
computeChroma :: Vector Double -> Double -> Vector Double
computeChroma magnitudes binFrequency =
  let minFreq = 27.5   -- A0
      maxFreq = 4186.0 -- C8 (piano range)
      initChroma = V.replicate 12 0
      (chroma, _) = V.ifoldl' accum (initChroma, 1) magnitudes
      accum (acc, bin) _ mag =
        let freq = fromIntegral bin * binFrequency
        in if freq < minFreq || freq > maxFreq
           then (acc, bin + 1)
           else
             let pc = hzToPitchClass freq
                 updated = acc V.// [(pc, acc V.! pc + mag)]
             in (updated, bin + 1)
  in chroma
