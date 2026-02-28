-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // audio // filter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Filter types and configuration for audio synthesis.
-- |
-- | ## Filter Types
-- | Classic subtractive synthesis filters:
-- | - Low-pass: attenuates frequencies above cutoff
-- | - High-pass: attenuates frequencies below cutoff
-- | - Band-pass: passes frequencies within a band
-- | - Notch: attenuates frequencies within a narrow band
-- |
-- | ## Resonance
-- | Controls the peak at the cutoff frequency.
-- | High resonance creates the classic "synth filter" sound.
-- |
-- | ## Key Tracking
-- | Optionally modulates cutoff by MIDI note number.

module Hydrogen.Schema.Audio.Filter
  ( -- * Filter Type (Compound)
    FilterType(..)
  , filterTypeName
  
  -- * Filter Molecule
  , Filter
  , filter
  , lowPassFilter
  , highPassFilter
  , bandPassFilter
  
  -- * Filter Slopes
  , FilterSlope(..)
  , filterSlopeDb
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Audio.Synthesis as Synth
import Hydrogen.Schema.Audio.Envelope as Env

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // filter types
-- ═════════════════════════════════════════════════════════════════════════════

-- | FilterType - frequency filter type.
-- | Determines which frequencies are passed or attenuated.
data FilterType
  = LowPass       -- ^ Passes frequencies below cutoff
  | HighPass      -- ^ Passes frequencies above cutoff
  | BandPass      -- ^ Passes frequencies within a band around cutoff
  | BandStop      -- ^ Attenuates frequencies within a band (notch)
  | Notch         -- ^ Narrow bandstop filter
  | AllPass       -- ^ Phase shift only, no amplitude change
  | Peak          -- ^ Parametric EQ boost/cut at frequency
  | LowShelf      -- ^ Boost/cut below frequency
  | HighShelf     -- ^ Boost/cut above frequency
  | Resonant      -- ^ Resonant low-pass (classic synth filter)

derive instance eqFilterType :: Eq FilterType
derive instance ordFilterType :: Ord FilterType

instance showFilterType :: Show FilterType where
  show = filterTypeName

-- | Get display name for filter type
filterTypeName :: FilterType -> String
filterTypeName LowPass = "Low Pass"
filterTypeName HighPass = "High Pass"
filterTypeName BandPass = "Band Pass"
filterTypeName BandStop = "Band Stop"
filterTypeName Notch = "Notch"
filterTypeName AllPass = "All Pass"
filterTypeName Peak = "Peak"
filterTypeName LowShelf = "Low Shelf"
filterTypeName HighShelf = "High Shelf"
filterTypeName Resonant = "Resonant"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // filter slopes
-- ═════════════════════════════════════════════════════════════════════════════

-- | FilterSlope - steepness of filter rolloff.
-- | Measured in dB per octave.
data FilterSlope
  = Slope6dB      -- ^ 1-pole, 6dB/octave (gentle)
  | Slope12dB     -- ^ 2-pole, 12dB/octave (common)
  | Slope18dB     -- ^ 3-pole, 18dB/octave
  | Slope24dB     -- ^ 4-pole, 24dB/octave (steep, classic Moog)
  | Slope36dB     -- ^ 6-pole, 36dB/octave (very steep)
  | Slope48dB     -- ^ 8-pole, 48dB/octave (extreme)

derive instance eqFilterSlope :: Eq FilterSlope
derive instance ordFilterSlope :: Ord FilterSlope

instance showFilterSlope :: Show FilterSlope where
  show slope = filterSlopeDb slope

-- | Get dB/octave string for filter slope
filterSlopeDb :: FilterSlope -> String
filterSlopeDb Slope6dB = "6dB/oct"
filterSlopeDb Slope12dB = "12dB/oct"
filterSlopeDb Slope18dB = "18dB/oct"
filterSlopeDb Slope24dB = "24dB/oct"
filterSlopeDb Slope36dB = "36dB/oct"
filterSlopeDb Slope48dB = "48dB/oct"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // filter molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter configuration.
-- | Complete filter setup for synthesis.
type Filter =
  { filterType :: FilterType
  , cutoff :: Synth.CutoffFreq
  , resonance :: Synth.Resonance
  , slope :: FilterSlope
  , envelope :: Env.ADSR          -- ^ Filter envelope (modulates cutoff)
  , envelopeAmount :: Number      -- ^ How much envelope affects cutoff (-1 to 1)
  , keyTrack :: Number            -- ^ Cutoff tracks keyboard (0 = none, 1 = full)
  }

-- | Create a filter with specified parameters.
-- |
-- | ## Parameters
-- | - `fType`: Filter type
-- | - `cutoffHz`: Cutoff frequency in Hz
-- | - `res`: Resonance (0.0-1.0)
-- | - `slope`: Filter steepness
filter :: FilterType -> Number -> Number -> FilterSlope -> Filter
filter fType cutoffHz res slope' =
  { filterType: fType
  , cutoff: Synth.cutoffFreq cutoffHz
  , resonance: Synth.resonance res
  , slope: slope'
  , envelope: Env.adsrDefault
  , envelopeAmount: 0.0  -- No envelope modulation by default
  , keyTrack: 0.0        -- No key tracking by default
  }

-- | Create a low-pass filter with common settings.
lowPassFilter :: Number -> Number -> Filter
lowPassFilter cutoffHz res =
  { filterType: LowPass
  , cutoff: Synth.cutoffFreq cutoffHz
  , resonance: Synth.resonance res
  , slope: Slope24dB
  , envelope: Env.adsrDefault
  , envelopeAmount: 0.0
  , keyTrack: 0.0
  }

-- | Create a high-pass filter with common settings.
highPassFilter :: Number -> Number -> Filter
highPassFilter cutoffHz res =
  { filterType: HighPass
  , cutoff: Synth.cutoffFreq cutoffHz
  , resonance: Synth.resonance res
  , slope: Slope12dB
  , envelope: Env.adsrDefault
  , envelopeAmount: 0.0
  , keyTrack: 0.0
  }

-- | Create a band-pass filter with common settings.
bandPassFilter :: Number -> Number -> Filter
bandPassFilter cutoffHz res =
  { filterType: BandPass
  , cutoff: Synth.cutoffFreq cutoffHz
  , resonance: Synth.resonance res
  , slope: Slope12dB
  , envelope: Env.adsrDefault
  , envelopeAmount: 0.0
  , keyTrack: 0.0
  }
