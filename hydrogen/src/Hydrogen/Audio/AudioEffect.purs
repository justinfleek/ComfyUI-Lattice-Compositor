-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // audio // audio-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AudioEffect — Composable Audio Effect Pipeline
-- |
-- | Parallel to RenderEffect for visual, AudioEffect provides a composable
-- | ADT for audio processing. Effects are pure data describing audio
-- | transformations. The audio runtime interprets them.
-- |
-- | ## Architecture
-- |
-- | ```
-- | AudioEffect
-- |     ↓ interpreted by
-- | AudioRuntime (Web Audio API, native, etc.)
-- |     ↓ produces
-- | Processed Audio
-- | ```
-- |
-- | ## Composition
-- |
-- | Effects compose via:
-- | - `EffectSequence` — Apply in series (input → effect1 → effect2 → output)
-- | - `EffectParallel` — Apply in parallel and mix
-- | - `EffectConditional` — Apply based on condition
-- | - `EffectAnimated` — Crossfade between effect states
-- |
-- | ## Reference
-- | Council gap: COUNCIL_REVIEW.md §3.6 "RenderEffect.purs is visual-only"
module Hydrogen.Audio.AudioEffect
  ( -- * Core Effect Type
    AudioEffect(..)
    -- * Spatial Effect
  , SpatialEffect
    -- * Conditions
  , AudioCondition(..)
    -- * Effect Pass
  , AudioPass
  , AudioInput(..)
  , AudioOutput(..)
    -- * Composition
  , effectSequence
  , effectParallel
  , effectConditional
  , effectWhen
  , effectAnimated
    -- * Presets
  , vocalChain
  , drumBus
  , masterChain
  , ambientReverb
  , radioVoice
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Audio.Effects as FX
import Hydrogen.Schema.Audio.Spatial as Spatial

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | An audio effect — composable audio processing operation.
-- |
-- | Effects are pure data describing audio transformations.
-- | The interpreter converts them to audio processing nodes.
data AudioEffect
  = EffectReverb FX.Reverb
  | EffectDelay FX.Delay
  | EffectCompressor FX.Compressor
  | EffectEQ FX.EQ
  | EffectDistortion FX.Distortion
  | EffectGate FX.Gate
  | EffectLimiter FX.Limiter
  | EffectSpatialize SpatialEffect
  | EffectSequence (Array AudioEffect)      -- Apply in series
  | EffectParallel (Array AudioEffect)      -- Apply in parallel (mix)
  | EffectConditional                       -- Apply based on condition
      { condition :: AudioCondition
      , thenEffect :: AudioEffect
      , elseEffect :: Maybe AudioEffect
      }
  | EffectAnimated                          -- Crossfade between states
      { from :: AudioEffect
      , to :: AudioEffect
      , progress :: Number                  -- 0.0-1.0
      }
  | EffectNone                              -- Identity (no effect)

derive instance eqAudioEffect :: Eq AudioEffect

instance showAudioEffect :: Show AudioEffect where
  show (EffectReverb _) = "(EffectReverb ...)"
  show (EffectDelay _) = "(EffectDelay ...)"
  show (EffectCompressor _) = "(EffectCompressor ...)"
  show (EffectEQ _) = "(EffectEQ ...)"
  show (EffectDistortion _) = "(EffectDistortion ...)"
  show (EffectGate _) = "(EffectGate ...)"
  show (EffectLimiter _) = "(EffectLimiter ...)"
  show (EffectSpatialize _) = "(EffectSpatialize ...)"
  show (EffectSequence _) = "(EffectSequence [...])"
  show (EffectParallel _) = "(EffectParallel [...])"
  show (EffectConditional _) = "(EffectConditional ...)"
  show (EffectAnimated _) = "(EffectAnimated ...)"
  show EffectNone = "EffectNone"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // spatial effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial audio effect configuration.
-- |
-- | Uses azimuth/elevation/distance model for 3D positioning.
type SpatialEffect =
  { azimuth :: Spatial.Azimuth           -- Horizontal angle (-180 to 180)
  , elevation :: Spatial.Elevation       -- Vertical angle (-90 to 90)
  , distance :: Spatial.AudioDistance    -- Distance from listener
  , pan :: Spatial.Pan                   -- Stereo pan (-1 to 1)
  , width :: Spatial.StereoWidth         -- Stereo width (0 to 2)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conditions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Condition for conditional audio effects.
data AudioCondition
  = ConditionPlaying              -- Audio is currently playing
  | ConditionMuted                -- Audio is muted
  | ConditionVolumeAbove Number   -- Volume exceeds threshold (0-1)
  | ConditionVolumeBelow Number   -- Volume below threshold (0-1)
  | ConditionFrequencyAbove Number -- Dominant frequency above Hz
  | ConditionFrequencyBelow Number -- Dominant frequency below Hz
  | ConditionBeatDetected         -- Beat/transient detected
  | ConditionSilence              -- Signal is silent
  | ConditionAlways               -- Always true

derive instance eqAudioCondition :: Eq AudioCondition

instance showAudioCondition :: Show AudioCondition where
  show ConditionPlaying = "ConditionPlaying"
  show ConditionMuted = "ConditionMuted"
  show (ConditionVolumeAbove v) = "(ConditionVolumeAbove " <> show v <> ")"
  show (ConditionVolumeBelow v) = "(ConditionVolumeBelow " <> show v <> ")"
  show (ConditionFrequencyAbove f) = "(ConditionFrequencyAbove " <> show f <> ")"
  show (ConditionFrequencyBelow f) = "(ConditionFrequencyBelow " <> show f <> ")"
  show ConditionBeatDetected = "ConditionBeatDetected"
  show ConditionSilence = "ConditionSilence"
  show ConditionAlways = "ConditionAlways"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // effect pass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio effect pass specification.
type AudioPass =
  { input :: AudioInput
  , output :: AudioOutput
  , effect :: AudioEffect
  , wetDry :: Number              -- 0.0 = dry, 1.0 = wet
  }

-- | Input source for audio pass.
data AudioInput
  = InputSource String            -- Named audio source
  | InputPrevious                 -- Output of previous pass
  | InputMix (Array String)       -- Mix of named sources

derive instance eqAudioInput :: Eq AudioInput

-- | Output destination for audio pass.
data AudioOutput
  = OutputDestination             -- Final output (speakers)
  | OutputBus String              -- Named bus for routing
  | OutputAnalyzer                -- For visualization/analysis

derive instance eqAudioOutput :: Eq AudioOutput

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence effects (apply in order).
effectSequence :: Array AudioEffect -> AudioEffect
effectSequence effects = EffectSequence effects

-- | Parallel effects (apply simultaneously and mix).
effectParallel :: Array AudioEffect -> AudioEffect
effectParallel effects = EffectParallel effects

-- | Conditional effect with else branch.
effectConditional :: AudioCondition -> AudioEffect -> Maybe AudioEffect -> AudioEffect
effectConditional cond thenE elseE = EffectConditional
  { condition: cond
  , thenEffect: thenE
  , elseEffect: elseE
  }

-- | Conditional effect without else branch.
effectWhen :: AudioCondition -> AudioEffect -> AudioEffect
effectWhen cond effect = effectConditional cond effect Nothing

-- | Animated crossfade between effects.
effectAnimated :: AudioEffect -> AudioEffect -> Number -> AudioEffect
effectAnimated from to progress = EffectAnimated
  { from: from
  , to: to
  , progress: progress
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vocal chain preset — standard voice processing.
-- |
-- | Signal flow: Gate → EQ (presence boost) → Compressor → Limiter
-- | Suitable for podcasts, voiceovers, vocal recordings.
vocalChain :: AudioEffect
vocalChain = effectSequence
  [ EffectGate FX.gateDefault
  , EffectEQ FX.eqPresence
  , EffectCompressor FX.compressorVocal
  , EffectLimiter FX.limiterDefault
  ]

-- | Drum bus preset — punchy drum processing.
-- |
-- | Signal flow: EQ (low-end boost) → Compressor (punchy attack) → Limiter
-- | Designed for drum groups and percussive elements.
drumBus :: AudioEffect
drumBus = effectSequence
  [ EffectEQ FX.eqDrumBus
  , EffectCompressor FX.compressorDrums
  , EffectLimiter FX.limiterDefault
  ]

-- | Master chain preset — final output processing.
-- |
-- | Signal flow: EQ (gentle curve) → Compressor (glue) → Limiter (ceiling)
-- | For master bus / final mix stage.
masterChain :: AudioEffect
masterChain = effectSequence
  [ EffectEQ FX.eqMaster
  , EffectCompressor FX.compressorMaster
  , EffectLimiter FX.limiterMaster
  ]

-- | Ambient reverb preset — spacious, atmospheric reverb.
-- |
-- | Long decay, diffuse, subtle modulation.
-- | Ideal for pads, ambient textures, cinematic soundscapes.
ambientReverb :: AudioEffect
ambientReverb = EffectReverb FX.reverbAmbient

-- | Radio voice preset — lo-fi vocal effect.
-- |
-- | Signal flow: EQ (telephone band) → Distortion (subtle saturation)
-- | Creates walkie-talkie / radio transmission effect.
radioVoice :: AudioEffect
radioVoice = effectSequence
  [ EffectEQ FX.eqTelephone
  , EffectDistortion FX.distortionSubtle
  ]
