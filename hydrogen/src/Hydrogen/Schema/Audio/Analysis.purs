-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // audio // analysis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio analysis atoms for metering, FFT, and signal analysis.
-- |
-- | ## Level Metering
-- | RMS (Root Mean Square) gives perceived loudness.
-- | Peak shows maximum amplitude (for clipping detection).
-- | Crest Factor is the ratio of Peak to RMS (dynamic range indicator).
-- |
-- | ## Spectral Analysis
-- | FFT bins represent frequency content.
-- | Spectral Centroid indicates "brightness" of sound.
-- | Zero Crossings can indicate noisiness or pitch.
-- |
-- | ## Pitch Detection
-- | Detected frequency, MIDI note, and confidence level.

module Hydrogen.Schema.Audio.Analysis
  ( -- * Level Atoms
    RMSLevel(..)
  , PeakLevel(..)
  , CrestFactor(..)
  
  -- * Spectral Atoms
  , FFTBin(..)
  , SpectralCentroid(..)
  , ZeroCrossing(..)
  
  -- * Constructors
  , rmsLevel
  , peakLevel
  , crestFactor
  , fftBin
  , spectralCentroid
  , zeroCrossing
  
  -- * Accessors
  , unwrapRMSLevel
  , unwrapPeakLevel
  , unwrapCrestFactor
  , unwrapFFTBin
  , unwrapSpectralCentroid
  , unwrapZeroCrossing
  
  -- * Metering Molecule
  , Metering
  , metering
  
  -- * Pitch Detection Molecule
  , PitchDetection
  , pitchDetection
  
  -- * Metering Standards
  , MeteringStandard(..)
  , meteringStandardName
  
  -- * Bounds
  , rmsLevelBounds
  , peakLevelBounds
  , crestFactorBounds
  , fftBinBounds
  , spectralCentroidBounds
  , zeroCrossingBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rms level
-- ═════════════════════════════════════════════════════════════════════════════

-- | RMSLevel - Root Mean Square amplitude level.
-- | Represents perceived loudness (0.0 to 1.0).
-- | More representative of loudness than peak.
newtype RMSLevel = RMSLevel Number

derive instance eqRMSLevel :: Eq RMSLevel
derive instance ordRMSLevel :: Ord RMSLevel

instance showRMSLevel :: Show RMSLevel where
  show (RMSLevel n) = show n <> " RMS"

-- | Create an RMSLevel value (clamped to 0.0-1.0)
rmsLevel :: Number -> RMSLevel
rmsLevel n
  | n < 0.0 = RMSLevel 0.0
  | n > 1.0 = RMSLevel 1.0
  | otherwise = RMSLevel n

unwrapRMSLevel :: RMSLevel -> Number
unwrapRMSLevel (RMSLevel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // peak level
-- ═════════════════════════════════════════════════════════════════════════════

-- | PeakLevel - Peak amplitude level.
-- | Maximum amplitude in the analysis window (0.0 to 1.0).
-- | Used for clipping detection.
newtype PeakLevel = PeakLevel Number

derive instance eqPeakLevel :: Eq PeakLevel
derive instance ordPeakLevel :: Ord PeakLevel

instance showPeakLevel :: Show PeakLevel where
  show (PeakLevel n) = show n <> " peak"

-- | Create a PeakLevel value (clamped to 0.0-1.0)
peakLevel :: Number -> PeakLevel
peakLevel n
  | n < 0.0 = PeakLevel 0.0
  | n > 1.0 = PeakLevel 1.0
  | otherwise = PeakLevel n

unwrapPeakLevel :: PeakLevel -> Number
unwrapPeakLevel (PeakLevel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // crest factor
-- ═════════════════════════════════════════════════════════════════════════════

-- | CrestFactor - Peak to RMS ratio in dB.
-- | Indicates dynamic range of the signal.
-- | Sine wave = 3dB, square wave = 0dB, highly dynamic = 15-20dB.
newtype CrestFactor = CrestFactor Number

derive instance eqCrestFactor :: Eq CrestFactor
derive instance ordCrestFactor :: Ord CrestFactor

instance showCrestFactor :: Show CrestFactor where
  show (CrestFactor n) = show n <> " dB crest"

-- | Create a CrestFactor value (clamped to 0-40)
crestFactor :: Number -> CrestFactor
crestFactor n
  | n < 0.0 = CrestFactor 0.0
  | n > 40.0 = CrestFactor 40.0
  | otherwise = CrestFactor n

unwrapCrestFactor :: CrestFactor -> Number
unwrapCrestFactor (CrestFactor n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // fft bin
-- ═════════════════════════════════════════════════════════════════════════════

-- | FFTBin - Normalized FFT bin magnitude.
-- | Represents amplitude at a specific frequency band (0.0 to 1.0).
-- | Used for spectrum analyzers and visualizers.
newtype FFTBin = FFTBin Number

derive instance eqFFTBin :: Eq FFTBin
derive instance ordFFTBin :: Ord FFTBin

instance showFFTBin :: Show FFTBin where
  show (FFTBin n) = show n <> " bin"

-- | Create an FFTBin value (clamped to 0.0-1.0)
fftBin :: Number -> FFTBin
fftBin n
  | n < 0.0 = FFTBin 0.0
  | n > 1.0 = FFTBin 1.0
  | otherwise = FFTBin n

unwrapFFTBin :: FFTBin -> Number
unwrapFFTBin (FFTBin n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // spectral centroid
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpectralCentroid - "Center of mass" of the spectrum in Hz.
-- | Indicates perceived brightness of the sound.
-- | Higher values = brighter sound.
newtype SpectralCentroid = SpectralCentroid Number

derive instance eqSpectralCentroid :: Eq SpectralCentroid
derive instance ordSpectralCentroid :: Ord SpectralCentroid

instance showSpectralCentroid :: Show SpectralCentroid where
  show (SpectralCentroid n) = show n <> " Hz centroid"

-- | Create a SpectralCentroid value (clamped to 0-22050)
spectralCentroid :: Number -> SpectralCentroid
spectralCentroid n
  | n < 0.0 = SpectralCentroid 0.0
  | n > 22050.0 = SpectralCentroid 22050.0
  | otherwise = SpectralCentroid n

unwrapSpectralCentroid :: SpectralCentroid -> Number
unwrapSpectralCentroid (SpectralCentroid n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // zero crossing
-- ═════════════════════════════════════════════════════════════════════════════

-- | ZeroCrossing - Count of zero crossings in the signal.
-- | High zero-crossing rate indicates noisiness or high frequency content.
-- | Low rate indicates fundamental-heavy signals.
newtype ZeroCrossing = ZeroCrossing Int

derive instance eqZeroCrossing :: Eq ZeroCrossing
derive instance ordZeroCrossing :: Ord ZeroCrossing

instance showZeroCrossing :: Show ZeroCrossing where
  show (ZeroCrossing n) = show n <> " crossings"

-- | Create a ZeroCrossing value (clamped to non-negative)
zeroCrossing :: Int -> ZeroCrossing
zeroCrossing n
  | n < 0 = ZeroCrossing 0
  | otherwise = ZeroCrossing n

unwrapZeroCrossing :: ZeroCrossing -> Int
unwrapZeroCrossing (ZeroCrossing n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // metering molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metering - Combined level metering data.
-- | Includes RMS, Peak, Crest Factor, and clip count.
type Metering =
  { rms :: RMSLevel
  , peak :: PeakLevel
  , crest :: CrestFactor
  , clipCount :: Int
  }

-- | Create a Metering record with specified values.
metering :: Number -> Number -> Number -> Int -> Metering
metering r p c clips =
  { rms: rmsLevel r
  , peak: peakLevel p
  , crest: crestFactor c
  , clipCount: clampClips clips
  }
  where
    clampClips n
      | n < 0 = 0
      | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pitch detection molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | PitchDetection - Detected pitch information.
-- | Includes frequency, MIDI note approximation, cent offset, and confidence.
type PitchDetection =
  { frequency :: Number       -- ^ Detected frequency in Hz
  , midiNote :: Int           -- ^ Nearest MIDI note number
  , centOffset :: Number      -- ^ Offset from MIDI note in cents (-50 to 50)
  , confidence :: Number      -- ^ Detection confidence (0.0 to 1.0)
  }

-- | Create a PitchDetection record.
pitchDetection :: Number -> Int -> Number -> Number -> PitchDetection
pitchDetection freq note cents conf =
  { frequency: clampFreq freq
  , midiNote: clampNote note
  , centOffset: clampCents cents
  , confidence: clampConf conf
  }
  where
    clampFreq f
      | f < 0.0 = 0.0
      | otherwise = f
    clampNote n
      | n < 0 = 0
      | n > 127 = 127
      | otherwise = n
    clampCents c
      | c < (-50.0) = (-50.0)
      | c > 50.0 = 50.0
      | otherwise = c
    clampConf c
      | c < 0.0 = 0.0
      | c > 1.0 = 1.0
      | otherwise = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // metering standards
-- ═════════════════════════════════════════════════════════════════════════════

-- | MeteringStandard - Standard metering scales.
-- | Different standards for different applications.
data MeteringStandard
  = VUMeter          -- ^ VU meter (-20 to +3 dBu reference)
  | PeakMeter        -- ^ Peak meter (dBFS)
  | RMSMeter         -- ^ RMS meter (dBFS)
  | LoudnessMeter    -- ^ LUFS/LKFS loudness
  | TruePeak         -- ^ Inter-sample true peak
  | PhaseMeter       -- ^ Phase correlation (-1 to +1)

derive instance eqMeteringStandard :: Eq MeteringStandard
derive instance ordMeteringStandard :: Ord MeteringStandard

instance showMeteringStandard :: Show MeteringStandard where
  show = meteringStandardName

-- | Get the display name for a metering standard
meteringStandardName :: MeteringStandard -> String
meteringStandardName VUMeter = "VU"
meteringStandardName PeakMeter = "Peak"
meteringStandardName RMSMeter = "RMS"
meteringStandardName LoudnessMeter = "Loudness"
meteringStandardName TruePeak = "True Peak"
meteringStandardName PhaseMeter = "Phase"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for RMSLevel
-- |
-- | Min: 0.0 (silence)
-- | Max: 1.0 (full scale)
rmsLevelBounds :: Bounded.NumberBounds
rmsLevelBounds = Bounded.numberBounds 0.0 1.0 "rmsLevel" "RMS amplitude (0-1)"

-- | Bounds for PeakLevel
-- |
-- | Min: 0.0 (silence)
-- | Max: 1.0 (full scale)
peakLevelBounds :: Bounded.NumberBounds
peakLevelBounds = Bounded.numberBounds 0.0 1.0 "peakLevel" "Peak amplitude (0-1)"

-- | Bounds for CrestFactor
-- |
-- | Min: 0.0 dB (square wave)
-- | Max: 40.0 dB (very dynamic)
crestFactorBounds :: Bounded.NumberBounds
crestFactorBounds = Bounded.numberBounds 0.0 40.0 "crestFactor" "Peak/RMS ratio in dB (0-40)"

-- | Bounds for FFTBin
-- |
-- | Min: 0.0 (no energy)
-- | Max: 1.0 (normalized max)
fftBinBounds :: Bounded.NumberBounds
fftBinBounds = Bounded.numberBounds 0.0 1.0 "fftBin" "Normalized FFT bin magnitude (0-1)"

-- | Bounds for SpectralCentroid
-- |
-- | Min: 0.0 Hz
-- | Max: 22050.0 Hz (Nyquist at 44.1kHz)
spectralCentroidBounds :: Bounded.NumberBounds
spectralCentroidBounds = Bounded.numberBounds 0.0 22050.0 "spectralCentroid" "Spectral centroid in Hz (0-22050)"

-- | Bounds for ZeroCrossing
-- |
-- | Min: 0
-- | Max: unbounded (finite)
zeroCrossingBounds :: Bounded.IntBounds
zeroCrossingBounds = Bounded.intBounds 0 1000000 "zeroCrossing" "Zero crossing count (0+)"
