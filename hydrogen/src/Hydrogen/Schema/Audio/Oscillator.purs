-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // audio // oscillator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Oscillator types and configuration for audio synthesis.
-- |
-- | ## Oscillator Types
-- | Classic waveforms: sine, square, sawtooth, triangle.
-- | Noise types: white, pink, brown (red), blue, violet.
-- |
-- | ## Molecule Structure
-- | An Oscillator combines:
-- | - Waveform type
-- | - Frequency (or MIDI note)
-- | - Phase offset
-- | - Gain level
-- | - Sync mode (optional hard sync to another oscillator)

module Hydrogen.Schema.Audio.Oscillator
  ( -- * Oscillator Type (Compound)
    OscillatorType(..)
  , oscillatorTypeName
  , isNoiseType
  
  -- * Oscillator Molecule
  , Oscillator
  , oscillator
  , oscillatorFromMidi
  
  -- * Presets
  , sineOsc
  , squareOsc
  , sawOsc
  , triangleOsc
  , whiteNoiseOsc
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , (<)
  , (>)
  )

import Hydrogen.Schema.Audio.Frequency as Freq
import Hydrogen.Schema.Audio.Level as Level

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // oscillator types
-- ═════════════════════════════════════════════════════════════════════════════

-- | OscillatorType - waveform type for synthesis.
-- | Classic analog waveforms plus noise generators.
data OscillatorType
  = Sine          -- ^ Pure sine wave (fundamental only)
  | Cosine        -- ^ Pure cosine wave (90° phase shifted sine)
  | Square        -- ^ 50% duty cycle square wave (odd harmonics)
  | Pulse         -- ^ Variable duty cycle square (for PWM)
  | Sawtooth      -- ^ Rising sawtooth (all harmonics)
  | ReverseSaw    -- ^ Falling sawtooth
  | Triangle      -- ^ Triangle wave (odd harmonics, 12dB/oct rolloff)
  | NoiseWhite    -- ^ White noise (equal energy per frequency)
  | NoisePink     -- ^ Pink noise (-3dB/octave, equal energy per octave)
  | NoiseBrown    -- ^ Brown/red noise (-6dB/octave, Brownian motion)
  | NoiseBlue     -- ^ Blue noise (+3dB/octave)
  | NoiseViolet   -- ^ Violet noise (+6dB/octave)
  | Sample        -- ^ Audio file playback as oscillator

derive instance eqOscillatorType :: Eq OscillatorType
derive instance ordOscillatorType :: Ord OscillatorType

instance showOscillatorType :: Show OscillatorType where
  show = oscillatorTypeName

-- | Get display name for oscillator type
oscillatorTypeName :: OscillatorType -> String
oscillatorTypeName Sine = "Sine"
oscillatorTypeName Cosine = "Cosine"
oscillatorTypeName Square = "Square"
oscillatorTypeName Pulse = "Pulse"
oscillatorTypeName Sawtooth = "Sawtooth"
oscillatorTypeName ReverseSaw = "Reverse Saw"
oscillatorTypeName Triangle = "Triangle"
oscillatorTypeName NoiseWhite = "White Noise"
oscillatorTypeName NoisePink = "Pink Noise"
oscillatorTypeName NoiseBrown = "Brown Noise"
oscillatorTypeName NoiseBlue = "Blue Noise"
oscillatorTypeName NoiseViolet = "Violet Noise"
oscillatorTypeName Sample = "Sample"

-- | Check if oscillator type is a noise generator
isNoiseType :: OscillatorType -> Boolean
isNoiseType NoiseWhite = true
isNoiseType NoisePink = true
isNoiseType NoiseBrown = true
isNoiseType NoiseBlue = true
isNoiseType NoiseViolet = true
isNoiseType _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // oscillator molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oscillator configuration.
-- | Complete oscillator setup for synthesis.
type Oscillator =
  { oscType :: OscillatorType
  , frequency :: Freq.Hertz
  , phase :: Number              -- ^ Phase offset in degrees (0-360)
  , gain :: Level.LinearGain
  , pulseWidth :: Number         -- ^ Duty cycle for Pulse type (0.0-1.0)
  , sync :: Boolean              -- ^ Hard sync to another oscillator
  }

-- | Create an oscillator with specified parameters.
-- |
-- | ## Parameters
-- | - `oscType`: Waveform type
-- | - `freqHz`: Frequency in Hz
-- | - `phaseOffset`: Phase offset in degrees (0-360)
-- | - `gainLevel`: Amplitude (0.0-1.0)
oscillator :: OscillatorType -> Number -> Number -> Number -> Oscillator
oscillator oscType freqHz phaseOffset gainLevel =
  { oscType: oscType
  , frequency: Freq.hertz freqHz
  , phase: clampPhase phaseOffset
  , gain: Level.linearGain gainLevel
  , pulseWidth: 0.5  -- Default 50% duty cycle
  , sync: false
  }
  where
    clampPhase p
      | p < 0.0 = 0.0
      | p > 360.0 = 360.0
      | otherwise = p

-- | Create an oscillator from MIDI note number.
oscillatorFromMidi :: OscillatorType -> Int -> Number -> Oscillator
oscillatorFromMidi oscType midiNote gainLevel =
  let noteFreq = Freq.midiToHertz (Freq.midiNote midiNote)
  in { oscType: oscType
     , frequency: noteFreq
     , phase: 0.0
     , gain: Level.linearGain gainLevel
     , pulseWidth: 0.5
     , sync: false
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple sine oscillator at A4 (440Hz)
sineOsc :: Oscillator
sineOsc =
  { oscType: Sine
  , frequency: Freq.a4
  , phase: 0.0
  , gain: Level.unity
  , pulseWidth: 0.5
  , sync: false
  }

-- | Simple square oscillator at A4
squareOsc :: Oscillator
squareOsc =
  { oscType: Square
  , frequency: Freq.a4
  , phase: 0.0
  , gain: Level.unity
  , pulseWidth: 0.5
  , sync: false
  }

-- | Simple sawtooth oscillator at A4
sawOsc :: Oscillator
sawOsc =
  { oscType: Sawtooth
  , frequency: Freq.a4
  , phase: 0.0
  , gain: Level.unity
  , pulseWidth: 0.5
  , sync: false
  }

-- | Simple triangle oscillator at A4
triangleOsc :: Oscillator
triangleOsc =
  { oscType: Triangle
  , frequency: Freq.a4
  , phase: 0.0
  , gain: Level.unity
  , pulseWidth: 0.5
  , sync: false
  }

-- | White noise generator
whiteNoiseOsc :: Oscillator
whiteNoiseOsc =
  { oscType: NoiseWhite
  , frequency: Freq.hertz 0.0  -- Not applicable for noise
  , phase: 0.0
  , gain: Level.unity
  , pulseWidth: 0.5
  , sync: false
  }


