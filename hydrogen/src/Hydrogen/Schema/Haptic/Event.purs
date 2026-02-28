-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // haptic // event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Haptic Event Molecules - composed haptic feedback primitives.
-- |
-- | These molecules compose the haptic atoms into meaningful events
-- | that can be triggered during UI interactions.
-- |
-- | ## SCHEMA.md Reference (Molecules)
-- | ```
-- | | HapticEvent   | Intensity + Sharpness + Duration         |
-- | | VibrationStep | Intensity + Duration                     |
-- | | AudioCue      | SoundID + Volume + Pitch + Pan           |
-- | | HapticPattern | Array of HapticEvent + timing            |
-- | ```
-- |
-- | ## Dependencies
-- | - Haptic/Vibration.purs (Intensity, Sharpness, HapticDuration, Attack, Decay)
-- | - Haptic/Audio.purs (Volume, Pitch, Pan, SoundId)
-- | - Prelude
-- |
-- | ## Dependents
-- | - Haptic/Feedback.purs (uses events in compounds)
-- | - Component.* (triggers haptic feedback)

module Hydrogen.Schema.Haptic.Event
  ( -- * HapticEvent Molecule
    HapticEvent
  , hapticEvent
  , eventIntensity
  , eventSharpness
  , eventDuration
  , eventAttack
  , eventDecay
  , quickTapEvent
  , softPressEvent
  , sharpClickEvent
  , sustainedPressEvent
  , longHoldEvent
    -- * VibrationStep Molecule
  , VibrationStep
  , vibrationStep
  , stepIntensity
  , stepDuration
  , shortStep
  , mediumStep
  , longStep
    -- * AudioCue Molecule
  , AudioCue
  , audioCue
  , cueSound
  , cueVolume
  , cuePitch
  , cuePan
  , defaultAudioCue
  , quietAudioCue
  , loudAudioCue
    -- * HapticPattern Molecule
  , HapticPattern
  , hapticPattern
  , patternEvents
  , patternLoop
  , singleEventPattern
  , doubleEventPattern
  , tripleEventPattern
  ) where

import Prelude

import Hydrogen.Schema.Haptic.Audio
  ( Pan
  , Pitch
  , SoundId
  , Volume
  , mkPan
  , mkPitch
  , mkSoundId
  , mkVolume
  , normalPitch
  , normalVolume
  , panCenter
  , quietVolume
  , loudVolume
  , unwrapPan
  , unwrapPitch
  , unwrapSoundId
  , unwrapVolume
  )
import Hydrogen.Schema.Haptic.Vibration
  ( Attack
  , Decay
  , HapticDuration
  , Intensity
  , Sharpness
  , lightIntensity
  , mediumIntensity
  , heavyIntensity
  , mediumSharpness
  , sharpSharpness
  , softSharpness
  , shortDuration
  , mediumDuration
  , longDuration
  , instantDuration
  , mkAttack
  , mkDecay
  , mkHapticDuration
  , mkIntensity
  , mkSharpness
  , noAttack
  , noDecay
  , quickAttack
  , quickDecay
  , unwrapAttack
  , unwrapDecay
  , unwrapHapticDuration
  , unwrapIntensity
  , unwrapSharpness
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // haptic // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | HapticEvent molecule: Intensity + Sharpness + Duration + Attack + Decay
-- |
-- | A single haptic feedback event with full envelope control.
type HapticEvent =
  { intensity :: Intensity        -- ^ Vibration strength
  , sharpness :: Sharpness        -- ^ Feel quality (soft to sharp)
  , duration :: HapticDuration    -- ^ How long the event lasts
  , attack :: Attack              -- ^ Ramp up time
  , decay :: Decay                -- ^ Ramp down time
  }

-- | Create a haptic event
hapticEvent :: Number -> Number -> Number -> Number -> Number -> HapticEvent
hapticEvent intensityVal sharpnessVal durationMs attackMs decayMs =
  { intensity: mkIntensity intensityVal
  , sharpness: mkSharpness sharpnessVal
  , duration: mkHapticDuration durationMs
  , attack: mkAttack attackMs
  , decay: mkDecay decayMs
  }

-- | Get event intensity
eventIntensity :: HapticEvent -> Number
eventIntensity he = unwrapIntensity he.intensity

-- | Get event sharpness
eventSharpness :: HapticEvent -> Number
eventSharpness he = unwrapSharpness he.sharpness

-- | Get event duration
eventDuration :: HapticEvent -> Number
eventDuration he = unwrapHapticDuration he.duration

-- | Get event attack time
eventAttack :: HapticEvent -> Number
eventAttack he = unwrapAttack he.attack

-- | Get event decay time
eventDecay :: HapticEvent -> Number
eventDecay he = unwrapDecay he.decay

-- | Quick tap event (light, sharp, instant)
quickTapEvent :: HapticEvent
quickTapEvent =
  { intensity: lightIntensity
  , sharpness: sharpSharpness
  , duration: instantDuration
  , attack: noAttack
  , decay: quickDecay
  }

-- | Soft press event (medium, soft, short)
softPressEvent :: HapticEvent
softPressEvent =
  { intensity: mediumIntensity
  , sharpness: softSharpness
  , duration: shortDuration
  , attack: quickAttack
  , decay: quickDecay
  }

-- | Sharp click event (heavy, sharp, short)
sharpClickEvent :: HapticEvent
sharpClickEvent =
  { intensity: heavyIntensity
  , sharpness: sharpSharpness
  , duration: shortDuration
  , attack: noAttack
  , decay: noDecay
  }

-- | Sustained press event (medium intensity, medium duration)
sustainedPressEvent :: HapticEvent
sustainedPressEvent =
  { intensity: mediumIntensity
  , sharpness: mediumSharpness
  , duration: mediumDuration
  , attack: quickAttack
  , decay: quickDecay
  }

-- | Long hold event (heavy, long duration)
longHoldEvent :: HapticEvent
longHoldEvent =
  { intensity: heavyIntensity
  , sharpness: softSharpness
  , duration: longDuration
  , attack: quickAttack
  , decay: quickDecay
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vibration // step
-- ═════════════════════════════════════════════════════════════════════════════

-- | VibrationStep molecule: Intensity + Duration
-- |
-- | A simpler haptic primitive without envelope control, for
-- | building vibration patterns.
type VibrationStep =
  { intensity :: Intensity        -- ^ Vibration strength
  , duration :: HapticDuration    -- ^ Step duration
  }

-- | Create a vibration step
vibrationStep :: Number -> Number -> VibrationStep
vibrationStep intensityVal durationMs =
  { intensity: mkIntensity intensityVal
  , duration: mkHapticDuration durationMs
  }

-- | Get step intensity
stepIntensity :: VibrationStep -> Number
stepIntensity vs = unwrapIntensity vs.intensity

-- | Get step duration
stepDuration :: VibrationStep -> Number
stepDuration vs = unwrapHapticDuration vs.duration

-- | Short vibration step (light, 30ms)
shortStep :: VibrationStep
shortStep =
  { intensity: lightIntensity
  , duration: mkHapticDuration 30.0
  }

-- | Medium vibration step (medium, 100ms)
mediumStep :: VibrationStep
mediumStep =
  { intensity: mediumIntensity
  , duration: mkHapticDuration 100.0
  }

-- | Long vibration step (heavy, 250ms)
longStep :: VibrationStep
longStep =
  { intensity: heavyIntensity
  , duration: mkHapticDuration 250.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio // cue
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioCue molecule: SoundID + Volume + Pitch + Pan
-- |
-- | An audio feedback event with playback parameters.
type AudioCue =
  { sound :: SoundId              -- ^ Sound asset identifier
  , volume :: Volume              -- ^ Playback volume
  , pitch :: Pitch                -- ^ Playback pitch
  , pan :: Pan                    -- ^ Stereo position
  }

-- | Create an audio cue
audioCue :: String -> Number -> Number -> Number -> AudioCue
audioCue soundName volumeVal pitchVal panVal =
  { sound: mkSoundId soundName
  , volume: mkVolume volumeVal
  , pitch: mkPitch pitchVal
  , pan: mkPan panVal
  }

-- | Get cue sound ID
cueSound :: AudioCue -> String
cueSound ac = unwrapSoundId ac.sound

-- | Get cue volume
cueVolume :: AudioCue -> Number
cueVolume ac = unwrapVolume ac.volume

-- | Get cue pitch
cuePitch :: AudioCue -> Number
cuePitch ac = unwrapPitch ac.pitch

-- | Get cue pan
cuePan :: AudioCue -> Number
cuePan ac = unwrapPan ac.pan

-- | Default audio cue (normal volume, normal pitch, center pan)
defaultAudioCue :: String -> AudioCue
defaultAudioCue soundName =
  { sound: mkSoundId soundName
  , volume: normalVolume
  , pitch: normalPitch
  , pan: panCenter
  }

-- | Quiet audio cue (25% volume)
quietAudioCue :: String -> AudioCue
quietAudioCue soundName =
  { sound: mkSoundId soundName
  , volume: quietVolume
  , pitch: normalPitch
  , pan: panCenter
  }

-- | Loud audio cue (75% volume)
loudAudioCue :: String -> AudioCue
loudAudioCue soundName =
  { sound: mkSoundId soundName
  , volume: loudVolume
  , pitch: normalPitch
  , pan: panCenter
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // haptic // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | HapticPattern molecule: Array of HapticEvent + loop flag
-- |
-- | A sequence of haptic events that can be played together.
type HapticPattern =
  { events :: Array HapticEvent   -- ^ Sequence of events
  , loop :: Boolean               -- ^ Should the pattern repeat?
  }

-- | Create a haptic pattern
hapticPattern :: Array HapticEvent -> Boolean -> HapticPattern
hapticPattern events loop = { events, loop }

-- | Get pattern events
patternEvents :: HapticPattern -> Array HapticEvent
patternEvents hp = hp.events

-- | Get pattern loop flag
patternLoop :: HapticPattern -> Boolean
patternLoop hp = hp.loop

-- | Single event pattern (no loop)
singleEventPattern :: HapticEvent -> HapticPattern
singleEventPattern event = { events: [event], loop: false }

-- | Double event pattern (two quick taps)
doubleEventPattern :: HapticEvent -> HapticPattern
doubleEventPattern event = { events: [event, event], loop: false }

-- | Triple event pattern (three quick taps)
tripleEventPattern :: HapticEvent -> HapticPattern
tripleEventPattern event = { events: [event, event, event], loop: false }
