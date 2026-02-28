-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // schema // haptic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Haptic - Pillar 10 of the Hydrogen Schema.
-- |
-- | Multi-sensory feedback atoms for tactile and auditory response.
-- | Covers vibration parameters (intensity, sharpness, duration),
-- | audio feedback (volume, pitch, pan), and composed feedback patterns.
-- |
-- | ## Sub-modules
-- | - Vibration: Intensity, sharpness, frequency, duration, attack, decay
-- | - Audio: Volume, pitch, pan, sound identifiers
-- | - Event: HapticEvent, VibrationStep, AudioCue, HapticPattern molecules
-- | - Feedback: Impact, notification, selection, continuous, system patterns
-- |
-- | ## Atomic Vocabulary
-- | ```
-- | Vibration Atoms:
-- | | Intensity     | Number | 0.0  | 1.0   | clamps | Vibration strength       |
-- | | Sharpness     | Number | 0.0  | 1.0   | clamps | Haptic sharpness (iOS)   |
-- | | Frequency     | Number | 0    | 500   | clamps | Vibration frequency (Hz) |
-- | | Duration      | Number | 0    | 10000 | clamps | Haptic duration (ms)     |
-- | | Attack        | Number | 0    | none  | finite | Ramp up time (ms)        |
-- | | Decay         | Number | 0    | none  | finite | Ramp down time (ms)      |
-- |
-- | Audio Atoms:
-- | | Volume        | Number | 0.0  | 1.0   | clamps | Sound volume             |
-- | | Pitch         | Number | 0.1  | 4.0   | clamps | Pitch multiplier         |
-- | | Pan           | Number | -1.0 | 1.0   | clamps | Stereo pan               |
-- | | SoundId       | String | -    | -     | -      | Sound asset identifier   |
-- | ```
-- |
-- | ## Dependents
-- | - Component.* (haptic feedback for interactions)
-- | - Button.* (tactile response on press/release)
-- | - Interaction.* (gesture feedback patterns)

module Hydrogen.Schema.Haptic
  ( -- * Re-exports from Vibration
    module Hydrogen.Schema.Haptic.Vibration
    -- * Re-exports from Audio
  , module Hydrogen.Schema.Haptic.Audio
    -- * Re-exports from Event
  , module Hydrogen.Schema.Haptic.Event
    -- * Re-exports from Feedback
  , module Hydrogen.Schema.Haptic.Feedback
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // vibration // re-exports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Haptic.Vibration
  ( -- Intensity (0.0-1.0, clamps)
    Intensity
  , mkIntensity
  , unwrapIntensity
  , minIntensity
  , maxIntensity
  , noIntensity
  , lightIntensity
  , mediumIntensity
  , heavyIntensity
  , fullIntensity
    -- Sharpness (0.0-1.0, clamps)
  , Sharpness
  , mkSharpness
  , unwrapSharpness
  , minSharpness
  , maxSharpness
  , softSharpness
  , mediumSharpness
  , sharpSharpness
    -- Frequency (0-500 Hz, clamps)
  , HapticFrequency
  , mkHapticFrequency
  , unwrapHapticFrequency
  , minHapticFrequency
  , maxHapticFrequency
  , lowFrequency
  , midFrequency
  , highFrequency
    -- Duration (0-10000 ms, clamps)
  , HapticDuration
  , mkHapticDuration
  , unwrapHapticDuration
  , minHapticDuration
  , maxHapticDuration
  , instantDuration
  , shortDuration
  , mediumDuration
  , longDuration
    -- Attack (0+ ms, finite)
  , Attack
  , mkAttack
  , unwrapAttack
  , noAttack
  , quickAttack
  , slowAttack
    -- Decay (0+ ms, finite)
  , Decay
  , mkDecay
  , unwrapDecay
  , noDecay
  , quickDecay
  , slowDecay
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // audio // re-exports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Haptic.Audio
  ( -- Volume (0.0-1.0, clamps)
    Volume
  , mkVolume
  , unwrapVolume
  , minVolume
  , maxVolume
  , muteVolume
  , quietVolume
  , normalVolume
  , loudVolume
  , maxedVolume
    -- Pitch (0.1-4.0, clamps)
  , Pitch
  , mkPitch
  , unwrapPitch
  , minPitch
  , maxPitch
  , veryLowPitch
  , lowPitch
  , normalPitch
  , highPitch
  , veryHighPitch
    -- Pan (-1.0 to 1.0, clamps)
  , Pan
  , mkPan
  , unwrapPan
  , minPan
  , maxPan
  , panLeft
  , panCenter
  , panRight
  , panHardLeft
  , panHardRight
    -- SoundId (identifier)
  , SoundId
  , mkSoundId
  , unwrapSoundId
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // event // re-exports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Haptic.Event
  ( -- HapticEvent Molecule
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
    -- VibrationStep Molecule
  , VibrationStep
  , vibrationStep
  , stepIntensity
  , stepDuration
  , shortStep
  , mediumStep
  , longStep
    -- AudioCue Molecule
  , AudioCue
  , audioCue
  , cueSound
  , cueVolume
  , cuePitch
  , cuePan
  , defaultAudioCue
  , quietAudioCue
  , loudAudioCue
    -- HapticPattern Molecule
  , HapticPattern
  , hapticPattern
  , patternEvents
  , patternLoop
  , singleEventPattern
  , doubleEventPattern
  , tripleEventPattern
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // feedback // re-exports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Haptic.Feedback
  ( -- Impact Feedback
    ImpactFeedback(ImpactLight, ImpactMedium, ImpactHeavy, ImpactSoft, ImpactRigid)
  , impactToEvent
  , impactIntensity
  , maxImpactIntensity
    -- Notification Feedback
  , NotificationFeedback(NotifySuccess, NotifyWarning, NotifyError)
  , notificationToPattern
  , notificationSeverity
    -- Selection Feedback
  , SelectionFeedback(SelectionTick, SelectionStart, SelectionEnd)
  , selectionToEvent
    -- Continuous Feedback
  , ContinuousFeedback
  , ContinuousType(TextureType, SliderType, RampType)
  , textureFeedback
  , sliderFeedback
  , rampFeedback
  , continuousIntensityAt
    -- System Patterns (iOS)
  , SystemPattern(Peek, Pop, AlignmentGuide, LevelChange)
  , systemPatternToEvents
    -- Audio Feedback
  , AudioFeedback
      ( ClickSound
      , KeySound
      , LockSound
      , PaymentSound
      , CameraSound
      , AmbientLoop
      )
  , audioFeedbackToCue
  , audioFeedbackSoundId
  )
