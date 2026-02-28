-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio effects molecules - reverb, delay, compressor, EQ.
-- |
-- | ## Reverb
-- | Simulates acoustic space reflections.
-- | Parameters: room size, damping, wet/dry mix, pre-delay.
-- |
-- | ## Delay
-- | Echo effect with adjustable time and feedback.
-- | Can be tempo-synced.
-- |
-- | ## Compressor
-- | Dynamic range control.
-- | Parameters: threshold, ratio, attack, release, makeup gain.
-- |
-- | ## EQ
-- | Parametric equalizer with multiple bands.

module Hydrogen.Schema.Audio.Effects
  ( -- * Reverb
    ReverbAlgorithm(..)
  , Reverb
  , reverb
  , reverbHall
  , reverbRoom
  , reverbPlate
  , reverbAmbient
  
  -- * Delay
  , Delay
  , delay
  , delayQuarter
  , delayEighth
  
  -- * Compressor
  , Compressor
  , compressor
  , compressorGentle
  , compressorHard
  , compressorVocal
  , compressorDrums
  , compressorMaster
  
  -- * EQ
  , EQBand
  , EQ
  , eqBand
  , eq3Band
  , eqPresence
  , eqDrumBus
  , eqMaster
  , eqTelephone
  
  -- * Distortion
  , DistortionType(..)
  , Distortion
  , distortion
  , distortionSubtle
  
  -- * Gate
  , Gate
  , gate
  , gateDefault
  
  -- * Limiter
  , Limiter
  , limiter
  , limiterDefault
  , limiterMaster
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , negate
  , (<)
  , (>)
  )

import Hydrogen.Schema.Audio.Synthesis as Synth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // reverb algorithms
-- ═════════════════════════════════════════════════════════════════════════════

-- | ReverbAlgorithm - type of reverb simulation.
data ReverbAlgorithm
  = Hall          -- ^ Large concert hall
  | Room          -- ^ Medium room
  | Chamber       -- ^ Small chamber
  | Plate         -- ^ Plate reverb (metallic)
  | Spring        -- ^ Spring reverb (vintage)
  | Convolution   -- ^ Impulse response based
  | Algorithmic   -- ^ Digital algorithm (Schroeder, etc.)

derive instance eqReverbAlgorithm :: Eq ReverbAlgorithm
derive instance ordReverbAlgorithm :: Ord ReverbAlgorithm

instance showReverbAlgorithm :: Show ReverbAlgorithm where
  show Hall = "Hall"
  show Room = "Room"
  show Chamber = "Chamber"
  show Plate = "Plate"
  show Spring = "Spring"
  show Convolution = "Convolution"
  show Algorithmic = "Algorithmic"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // reverb molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverb effect configuration.
type Reverb =
  { algorithm :: ReverbAlgorithm
  , roomSize :: Number          -- ^ 0.0 = small, 1.0 = large
  , damping :: Number           -- ^ 0.0 = bright, 1.0 = dark
  , mix :: Synth.Mix
  , preDelayMs :: Number        -- ^ Pre-delay in milliseconds
  , diffusion :: Number         -- ^ 0.0 = sparse, 1.0 = dense
  }

-- | Create a reverb effect.
reverb :: ReverbAlgorithm -> Number -> Number -> Number -> Reverb
reverb algo size damp mixAmount =
  { algorithm: algo
  , roomSize: clamp01 size
  , damping: clamp01 damp
  , mix: Synth.mix mixAmount
  , preDelayMs: 0.0
  , diffusion: 0.7
  }
  where
    clamp01 n
      | n < 0.0 = 0.0
      | n > 1.0 = 1.0
      | otherwise = n

-- | Hall reverb preset
reverbHall :: Reverb
reverbHall =
  { algorithm: Hall
  , roomSize: 0.9
  , damping: 0.4
  , mix: Synth.mix 0.3
  , preDelayMs: 20.0
  , diffusion: 0.8
  }

-- | Room reverb preset
reverbRoom :: Reverb
reverbRoom =
  { algorithm: Room
  , roomSize: 0.5
  , damping: 0.5
  , mix: Synth.mix 0.25
  , preDelayMs: 5.0
  , diffusion: 0.6
  }

-- | Plate reverb preset
reverbPlate :: Reverb
reverbPlate =
  { algorithm: Plate
  , roomSize: 0.7
  , damping: 0.3
  , mix: Synth.mix 0.35
  , preDelayMs: 0.0
  , diffusion: 0.9
  }

-- | Ambient reverb preset — spacious, atmospheric.
-- | Long decay, high diffusion for pads and cinematic textures.
reverbAmbient :: Reverb
reverbAmbient =
  { algorithm: Hall
  , roomSize: 1.0
  , damping: 0.6
  , mix: Synth.mix 0.5
  , preDelayMs: 50.0
  , diffusion: 0.95
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // delay molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Delay effect configuration.
type Delay =
  { timeMs :: Number            -- ^ Delay time in milliseconds
  , feedback :: Synth.Feedback
  , mix :: Synth.Mix
  , filterCutoff :: Synth.CutoffFreq  -- ^ High-cut filter on feedback
  , pingPong :: Boolean         -- ^ Alternating L/R delay
  }

-- | Create a delay effect.
delay :: Number -> Number -> Number -> Delay
delay timeMs' fb mixAmount =
  { timeMs: clampTime timeMs'
  , feedback: Synth.feedback fb
  , mix: Synth.mix mixAmount
  , filterCutoff: Synth.cutoff20k  -- No filtering by default
  , pingPong: false
  }
  where
    clampTime t
      | t < 0.0 = 0.0
      | t > 5000.0 = 5000.0  -- 5 second max
      | otherwise = t

-- | Quarter note delay at 120 BPM (500ms)
delayQuarter :: Delay
delayQuarter =
  { timeMs: 500.0
  , feedback: Synth.feedback 0.4
  , mix: Synth.mix 0.3
  , filterCutoff: Synth.cutoff5k
  , pingPong: false
  }

-- | Eighth note delay at 120 BPM (250ms)
delayEighth :: Delay
delayEighth =
  { timeMs: 250.0
  , feedback: Synth.feedback 0.5
  , mix: Synth.mix 0.25
  , filterCutoff: Synth.cutoff10k
  , pingPong: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // compressor molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compressor effect configuration.
type Compressor =
  { thresholdDb :: Number       -- ^ Threshold in dB (-60 to 0)
  , ratio :: Number             -- ^ Compression ratio (1:1 to 20:1)
  , attackMs :: Number          -- ^ Attack time in ms
  , releaseMs :: Number         -- ^ Release time in ms
  , kneeDb :: Number            -- ^ Soft knee width in dB
  , makeupDb :: Number          -- ^ Makeup gain in dB
  }

-- | Create a compressor.
compressor :: Number -> Number -> Number -> Number -> Compressor
compressor threshold ratio' attack release =
  { thresholdDb: clampThreshold threshold
  , ratio: clampRatio ratio'
  , attackMs: clampAttack attack
  , releaseMs: clampRelease release
  , kneeDb: 6.0  -- Moderate soft knee
  , makeupDb: 0.0
  }
  where
    clampThreshold t
      | t < (-60.0) = (-60.0)
      | t > 0.0 = 0.0
      | otherwise = t
    clampRatio r
      | r < 1.0 = 1.0
      | r > 20.0 = 20.0
      | otherwise = r
    clampAttack a
      | a < 0.1 = 0.1
      | a > 500.0 = 500.0
      | otherwise = a
    clampRelease r
      | r < 10.0 = 10.0
      | r > 2000.0 = 2000.0
      | otherwise = r

-- | Gentle compression preset
compressorGentle :: Compressor
compressorGentle =
  { thresholdDb: (-12.0)
  , ratio: 2.0
  , attackMs: 30.0
  , releaseMs: 200.0
  , kneeDb: 10.0
  , makeupDb: 3.0
  }

-- | Hard compression preset
compressorHard :: Compressor
compressorHard =
  { thresholdDb: (-20.0)
  , ratio: 8.0
  , attackMs: 5.0
  , releaseMs: 100.0
  , kneeDb: 3.0
  , makeupDb: 6.0
  }

-- | Vocal compressor preset — smooth, controlled dynamics.
-- | Medium attack preserves transients, gentle ratio for transparency.
compressorVocal :: Compressor
compressorVocal =
  { thresholdDb: (-18.0)
  , ratio: 3.0
  , attackMs: 15.0
  , releaseMs: 150.0
  , kneeDb: 8.0
  , makeupDb: 4.0
  }

-- | Drum compressor preset — punchy, aggressive.
-- | Fast attack catches transients, high ratio for punch.
compressorDrums :: Compressor
compressorDrums =
  { thresholdDb: (-15.0)
  , ratio: 6.0
  , attackMs: 3.0
  , releaseMs: 80.0
  , kneeDb: 4.0
  , makeupDb: 5.0
  }

-- | Master compressor preset — glue compression.
-- | Very gentle, transparent bus compression.
compressorMaster :: Compressor
compressorMaster =
  { thresholdDb: (-8.0)
  , ratio: 1.5
  , attackMs: 30.0
  , releaseMs: 300.0
  , kneeDb: 12.0
  , makeupDb: 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // eq molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | EQ band configuration.
type EQBand =
  { frequency :: Synth.CutoffFreq
  , gainDb :: Number            -- ^ Boost/cut in dB (-15 to +15)
  , q :: Synth.Resonance        -- ^ Bandwidth (higher = narrower)
  }

-- | Create an EQ band.
eqBand :: Number -> Number -> Number -> EQBand
eqBand freq gain q' =
  { frequency: Synth.cutoffFreq freq
  , gainDb: clampGain gain
  , q: Synth.resonance q'
  }
  where
    clampGain g
      | g < (-15.0) = (-15.0)
      | g > 15.0 = 15.0
      | otherwise = g

-- | EQ with multiple bands.
type EQ =
  { bands :: Array EQBand
  , outputGainDb :: Number
  }

-- | Create a simple 3-band EQ (low, mid, high).
eq3Band :: Number -> Number -> Number -> EQ
eq3Band lowGain midGain highGain =
  { bands:
      [ eqBand 100.0 lowGain 0.7    -- Low shelf at 100Hz
      , eqBand 1000.0 midGain 0.5   -- Mid peak at 1kHz
      , eqBand 8000.0 highGain 0.7  -- High shelf at 8kHz
      ]
  , outputGainDb: 0.0
  }

-- | Presence EQ preset — adds clarity and presence to vocals.
-- | Boosts upper mids for intelligibility, slight air boost.
eqPresence :: EQ
eqPresence =
  { bands:
      [ eqBand 200.0 (-2.0) 0.8     -- Cut mud
      , eqBand 3000.0 3.0 0.6       -- Presence boost
      , eqBand 12000.0 2.0 0.5      -- Air/sparkle
      ]
  , outputGainDb: 0.0
  }

-- | Drum bus EQ preset — punchy low-end, controlled highs.
eqDrumBus :: EQ
eqDrumBus =
  { bands:
      [ eqBand 60.0 3.0 0.7         -- Sub weight
      , eqBand 100.0 2.0 0.6        -- Punch
      , eqBand 400.0 (-2.0) 0.5     -- Cut boxiness
      , eqBand 4000.0 1.5 0.7       -- Attack definition
      ]
  , outputGainDb: 0.0
  }

-- | Master EQ preset — gentle final curve.
-- | Subtle adjustments for cohesion.
eqMaster :: EQ
eqMaster =
  { bands:
      [ eqBand 30.0 1.0 0.5         -- Sub presence
      , eqBand 250.0 (-1.0) 0.4     -- Clean up mud
      , eqBand 3500.0 0.5 0.4       -- Slight presence
      , eqBand 14000.0 1.0 0.5      -- Air
      ]
  , outputGainDb: 0.0
  }

-- | Telephone EQ preset — lo-fi bandpass filter.
-- | Simulates narrow-band telephone/radio transmission.
eqTelephone :: EQ
eqTelephone =
  { bands:
      [ eqBand 80.0 (-15.0) 1.0     -- Cut lows
      , eqBand 300.0 3.0 0.8        -- Boost low-mids
      , eqBand 2500.0 4.0 0.6       -- Nasal presence
      , eqBand 4000.0 (-12.0) 0.8   -- Cut highs
      ]
  , outputGainDb: (-3.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // distortion molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | DistortionType - type of harmonic distortion.
data DistortionType
  = Overdrive     -- ^ Soft clipping (tube-like)
  | Distort       -- ^ Hard clipping
  | Fuzz          -- ^ Extreme clipping (transistor-like)
  | BitCrush      -- ^ Bit depth reduction
  | WaveShaper    -- ^ Custom waveshaping curve

derive instance eqDistortionType :: Eq DistortionType
derive instance ordDistortionType :: Ord DistortionType

instance showDistortionType :: Show DistortionType where
  show Overdrive = "Overdrive"
  show Distort = "Distortion"
  show Fuzz = "Fuzz"
  show BitCrush = "Bit Crush"
  show WaveShaper = "Wave Shaper"

-- | Distortion effect configuration.
type Distortion =
  { distType :: DistortionType
  , drive :: Synth.Drive
  , tone :: Synth.CutoffFreq    -- ^ Post-distortion tone control
  , mix :: Synth.Mix
  }

-- | Create a distortion effect.
distortion :: DistortionType -> Number -> Number -> Distortion
distortion dType drv mixAmount =
  { distType: dType
  , drive: Synth.drive drv
  , tone: Synth.cutoff5k
  , mix: Synth.mix mixAmount
  }

-- | Subtle distortion preset — light saturation/warmth.
-- | Adds harmonics without obvious distortion artifacts.
distortionSubtle :: Distortion
distortionSubtle =
  { distType: Overdrive
  , drive: Synth.drive 0.2
  , tone: Synth.cutoff10k
  , mix: Synth.mix 0.3
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // gate molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gate effect configuration.
-- | Cuts signal below threshold.
type Gate =
  { thresholdDb :: Number       -- ^ Open threshold in dB
  , attackMs :: Number          -- ^ Time to open
  , holdMs :: Number            -- ^ Minimum open time
  , releaseMs :: Number         -- ^ Time to close
  , rangeDb :: Number           -- ^ Attenuation when closed (0 = full cut)
  }

-- | Create a gate effect.
gate :: Number -> Number -> Number -> Number -> Gate
gate threshold attack hold release =
  { thresholdDb: clampThreshold threshold
  , attackMs: clampTime attack
  , holdMs: clampTime hold
  , releaseMs: clampTime release
  , rangeDb: (-80.0)  -- Full cut
  }
  where
    clampThreshold t
      | t < (-60.0) = (-60.0)
      | t > 0.0 = 0.0
      | otherwise = t
    clampTime ms
      | ms < 0.0 = 0.0
      | ms > 1000.0 = 1000.0
      | otherwise = ms

-- | Default gate preset — general purpose noise gate.
gateDefault :: Gate
gateDefault =
  { thresholdDb: (-40.0)
  , attackMs: 1.0
  , holdMs: 50.0
  , releaseMs: 100.0
  , rangeDb: (-80.0)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // limiter molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Limiter effect configuration.
-- | Prevents signal from exceeding ceiling.
type Limiter =
  { thresholdDb :: Number       -- ^ Limiting threshold
  , releaseMs :: Number         -- ^ Release time
  , ceilingDb :: Number         -- ^ Maximum output level
  , lookaheadMs :: Number       -- ^ Look-ahead for true peak limiting
  }

-- | Create a limiter.
limiter :: Number -> Number -> Number -> Limiter
limiter threshold release ceiling =
  { thresholdDb: clampThreshold threshold
  , releaseMs: clampRelease release
  , ceilingDb: clampCeiling ceiling
  , lookaheadMs: 1.0  -- 1ms lookahead
  }
  where
    clampThreshold t
      | t < (-30.0) = (-30.0)
      | t > 0.0 = 0.0
      | otherwise = t
    clampRelease r
      | r < 1.0 = 1.0
      | r > 500.0 = 500.0
      | otherwise = r
    clampCeiling c
      | c < (-6.0) = (-6.0)
      | c > 0.0 = 0.0
      | otherwise = c

-- | Default limiter preset — transparent limiting.
limiterDefault :: Limiter
limiterDefault =
  { thresholdDb: (-1.0)
  , releaseMs: 100.0
  , ceilingDb: (-0.3)
  , lookaheadMs: 1.0
  }

-- | Master limiter preset — for final mix stage.
-- | More aggressive with true peak limiting.
limiterMaster :: Limiter
limiterMaster =
  { thresholdDb: (-3.0)
  , releaseMs: 50.0
  , ceilingDb: (-0.1)
  , lookaheadMs: 3.0
  }


