-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // level
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Level and amplitude atoms for audio processing.
-- |
-- | ## Decibel Scale
-- | Audio amplitude is typically measured in decibels (dB), a logarithmic
-- | scale where -6dB is half amplitude and -∞dB is silence.
-- |
-- | ## dBFS (Full Scale)
-- | Digital audio uses dBFS where 0dBFS is the maximum possible level.
-- | Values above 0dBFS cause clipping.
-- |
-- | ## Linear Gain
-- | For actual signal multiplication, linear gain (0.0 to 1.0) is used.
-- | Many synthesis operations require linear values.

module Hydrogen.Schema.Audio.Level
  ( -- * Types
    Decibel(..)
  , DecibelFS(..)
  , LinearGain(..)
  , Percent(..)
  
  -- * Constructors
  , decibel
  , decibelFS
  , linearGain
  , percent
  
  -- * Predefined Values
  , unity
  , silence
  , minus3dB
  , minus6dB
  , minus12dB
  , minus20dB
  
  -- * Accessors
  , unwrapDecibel
  , unwrapDecibelFS
  , unwrapLinearGain
  , unwrapPercent
  
  -- * Conversions
  , decibelToLinear
  , linearToDecibel
  , percentToLinear
  , linearToPercent
  
  -- * Operations
  , addDb
  , multiplyGain
  
  -- * Bounds
  , decibelBounds
  , decibelFSBounds
  , linearGainBounds
  , percentBounds
  ) where

import Prelude

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // decibel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decibel - relative logarithmic amplitude scale.
-- | Clamped to [-120, 0] for practical digital audio.
-- | -120dB is effectively silence (10^-6 linear).
newtype Decibel = Decibel Number

derive instance eqDecibel :: Eq Decibel
derive instance ordDecibel :: Ord Decibel

instance showDecibel :: Show Decibel where
  show (Decibel n) = show n <> " dB"

-- | Create a Decibel value (clamped to -120 to 0)
decibel :: Number -> Decibel
decibel n
  | n < (-120.0) = Decibel (-120.0)
  | n > 0.0 = Decibel 0.0
  | otherwise = Decibel n

unwrapDecibel :: Decibel -> Number
unwrapDecibel (Decibel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // decibel fs
-- ═════════════════════════════════════════════════════════════════════════════

-- | DecibelFS - decibels relative to digital full scale.
-- | 0dBFS is maximum, negative values are below full scale.
-- | Clamped to [-60, 0] for metering purposes.
newtype DecibelFS = DecibelFS Number

derive instance eqDecibelFS :: Eq DecibelFS
derive instance ordDecibelFS :: Ord DecibelFS

instance showDecibelFS :: Show DecibelFS where
  show (DecibelFS n) = show n <> " dBFS"

-- | Create a DecibelFS value (clamped to -60 to 0)
decibelFS :: Number -> DecibelFS
decibelFS n
  | n < (-60.0) = DecibelFS (-60.0)
  | n > 0.0 = DecibelFS 0.0
  | otherwise = DecibelFS n

unwrapDecibelFS :: DecibelFS -> Number
unwrapDecibelFS (DecibelFS n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // linear gain
-- ═════════════════════════════════════════════════════════════════════════════

-- | LinearGain - linear amplitude multiplier.
-- | 0.0 = silence, 1.0 = unity gain.
-- | Clamped to [0, 1] for standard gain.
newtype LinearGain = LinearGain Number

derive instance eqLinearGain :: Eq LinearGain
derive instance ordLinearGain :: Ord LinearGain

instance showLinearGain :: Show LinearGain where
  show (LinearGain n) = show n

-- | Create a LinearGain value (clamped to 0-1)
linearGain :: Number -> LinearGain
linearGain n
  | n < 0.0 = LinearGain 0.0
  | n > 1.0 = LinearGain 1.0
  | otherwise = LinearGain n

unwrapLinearGain :: LinearGain -> Number
unwrapLinearGain (LinearGain n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // percent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Percent - percentage value for user-facing controls.
-- | Clamped to [0, 100].
newtype Percent = Percent Number

derive instance eqPercent :: Eq Percent
derive instance ordPercent :: Ord Percent

instance showPercent :: Show Percent where
  show (Percent n) = show n <> "%"

-- | Create a Percent value (clamped to 0-100)
percent :: Number -> Percent
percent n
  | n < 0.0 = Percent 0.0
  | n > 100.0 = Percent 100.0
  | otherwise = Percent n

unwrapPercent :: Percent -> Number
unwrapPercent (Percent n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unity gain (0dB, 1.0 linear)
unity :: LinearGain
unity = LinearGain 1.0

-- | Silence (0.0 linear)
silence :: LinearGain
silence = LinearGain 0.0

-- | -3dB (approximately 0.707 linear, half power)
minus3dB :: Decibel
minus3dB = Decibel (-3.0)

-- | -6dB (approximately 0.5 linear, half amplitude)
minus6dB :: Decibel
minus6dB = Decibel (-6.0)

-- | -12dB (approximately 0.25 linear)
minus12dB :: Decibel
minus12dB = Decibel (-12.0)

-- | -20dB (0.1 linear, common reference)
minus20dB :: Decibel
minus20dB = Decibel (-20.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert decibels to linear gain
-- | Formula: 10^(dB/20)
decibelToLinear :: Decibel -> LinearGain
decibelToLinear (Decibel db) =
  linearGain (Math.pow 10.0 (db / 20.0))

-- | Convert linear gain to decibels
-- | Formula: 20 * log10(linear)
linearToDecibel :: LinearGain -> Decibel
linearToDecibel (LinearGain lin)
  | lin <= 0.0 = Decibel (-120.0)  -- Effective silence
  | otherwise = decibel (20.0 * Math.log10 lin)

-- | Convert percent to linear gain
percentToLinear :: Percent -> LinearGain
percentToLinear (Percent p) = linearGain (p / 100.0)

-- | Convert linear gain to percent
linearToPercent :: LinearGain -> Percent
linearToPercent (LinearGain lin) = percent (lin * 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two decibel values (this is multiplication in linear domain)
addDb :: Decibel -> Decibel -> Decibel
addDb (Decibel a) (Decibel b) = decibel (a + b)

-- | Multiply two linear gains
multiplyGain :: LinearGain -> LinearGain -> LinearGain
multiplyGain (LinearGain a) (LinearGain b) = linearGain (a * b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Decibel
-- |
-- | Min: -120.0 (effective silence)
-- | Max: 0.0 (unity)
decibelBounds :: Bounded.NumberBounds
decibelBounds = Bounded.numberBounds (-120.0) 0.0 "decibel" "Relative amplitude in dB (-120 to 0)"

-- | Bounds for DecibelFS
-- |
-- | Min: -60.0
-- | Max: 0.0 (digital full scale)
decibelFSBounds :: Bounded.NumberBounds
decibelFSBounds = Bounded.numberBounds (-60.0) 0.0 "decibelFS" "Amplitude relative to full scale (-60 to 0)"

-- | Bounds for LinearGain
-- |
-- | Min: 0.0 (silence)
-- | Max: 1.0 (unity)
linearGainBounds :: Bounded.NumberBounds
linearGainBounds = Bounded.numberBounds 0.0 1.0 "linearGain" "Linear amplitude multiplier (0-1)"

-- | Bounds for Percent
-- |
-- | Min: 0.0
-- | Max: 100.0
percentBounds :: Bounded.NumberBounds
percentBounds = Bounded.numberBounds 0.0 100.0 "percent" "Percentage value (0-100)"
