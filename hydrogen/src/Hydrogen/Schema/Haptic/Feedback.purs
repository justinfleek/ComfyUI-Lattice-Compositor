-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // haptic // feedback
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Haptic Feedback Compounds - complete haptic feedback patterns.
-- |
-- | These compounds compose haptic events into semantic feedback types
-- | for common UI interactions: impacts, notifications, selections,
-- | continuous feedback, and system patterns.
-- |
-- | ## SCHEMA.md Reference (Compounds)
-- | ```
-- | Impact Feedback: ImpactLight, ImpactMedium, ImpactHeavy, ImpactSoft, ImpactRigid
-- | Notification: NotifySuccess, NotifyWarning, NotifyError
-- | Selection: SelectionTick, SelectionStart, SelectionEnd
-- | Continuous: Texture, Slider, Ramp
-- | System (iOS): Peek, Pop, AlignmentGuide, LevelChange
-- | Audio: ClickSound, KeySound, LockSound, PaymentSound, CameraSound, AmbientLoop
-- | ```
-- |
-- | ## Dependencies
-- | - Haptic/Event.purs (HapticEvent, HapticPattern, AudioCue)
-- | - Haptic/Vibration.purs (atoms)
-- | - Prelude
-- |
-- | ## Dependents
-- | - Component.* (triggers haptic feedback on interactions)
-- | - Runtime.* (executes haptic patterns)

module Hydrogen.Schema.Haptic.Feedback
  ( -- * Impact Feedback
    ImpactFeedback(ImpactLight, ImpactMedium, ImpactHeavy, ImpactSoft, ImpactRigid)
  , impactToEvent
  , impactIntensity
  , maxImpactIntensity
    -- * Notification Feedback
  , NotificationFeedback(NotifySuccess, NotifyWarning, NotifyError)
  , notificationToPattern
  , notificationSeverity
    -- * Selection Feedback
  , SelectionFeedback(SelectionTick, SelectionStart, SelectionEnd)
  , selectionToEvent
    -- * Continuous Feedback
  , ContinuousFeedback
  , ContinuousType(TextureType, SliderType, RampType)
  , textureFeedback
  , sliderFeedback
  , rampFeedback
  , continuousIntensityAt
    -- * System Patterns (iOS)
  , SystemPattern(Peek, Pop, AlignmentGuide, LevelChange)
  , systemPatternToEvents
    -- * Audio Feedback
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
  ) where

import Prelude

import Data.Int (floor, toNumber)

import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , HapticEvent
  , HapticPattern
  , audioCue
  , hapticEvent
  , hapticPattern
  , quickTapEvent
  , sharpClickEvent
  , softPressEvent
  , sustainedPressEvent
  )
import Hydrogen.Schema.Haptic.Vibration
  ( fullIntensity
  , heavyIntensity
  , lightIntensity
  , mediumIntensity
  , unwrapIntensity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // impact // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Impact feedback types for tap/press interactions.
-- |
-- | These correspond to UIImpactFeedbackGenerator styles on iOS
-- | and similar haptic APIs on Android.
data ImpactFeedback
  = ImpactLight                   -- ^ Subtle tap
  | ImpactMedium                  -- ^ Standard tap
  | ImpactHeavy                   -- ^ Strong tap
  | ImpactSoft                    -- ^ Muted, soft tap
  | ImpactRigid                   -- ^ Sharp, rigid tap

derive instance eqImpactFeedback :: Eq ImpactFeedback

instance showImpactFeedback :: Show ImpactFeedback where
  show ImpactLight = "ImpactLight"
  show ImpactMedium = "ImpactMedium"
  show ImpactHeavy = "ImpactHeavy"
  show ImpactSoft = "ImpactSoft"
  show ImpactRigid = "ImpactRigid"

-- | Convert impact feedback to a haptic event
impactToEvent :: ImpactFeedback -> HapticEvent
impactToEvent ImpactLight = quickTapEvent
impactToEvent ImpactMedium = softPressEvent
impactToEvent ImpactHeavy = sharpClickEvent
impactToEvent ImpactSoft = hapticEvent 0.3 0.2 30.0 10.0 20.0
impactToEvent ImpactRigid = hapticEvent 0.8 0.95 20.0 0.0 0.0

-- | Get the intensity level of an impact
impactIntensity :: ImpactFeedback -> Number
impactIntensity ImpactLight = unwrapIntensity lightIntensity
impactIntensity ImpactMedium = unwrapIntensity mediumIntensity
impactIntensity ImpactHeavy = unwrapIntensity heavyIntensity
impactIntensity ImpactSoft = 0.3
impactIntensity ImpactRigid = 0.8

-- | Get the maximum possible impact intensity
maxImpactIntensity :: Number
maxImpactIntensity = unwrapIntensity fullIntensity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // notification // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Notification feedback types for system events.
-- |
-- | These correspond to UINotificationFeedbackGenerator types on iOS.
data NotificationFeedback
  = NotifySuccess                 -- ^ Positive acknowledgment
  | NotifyWarning                 -- ^ Attention needed
  | NotifyError                   -- ^ Something went wrong

derive instance eqNotificationFeedback :: Eq NotificationFeedback

instance showNotificationFeedback :: Show NotificationFeedback where
  show NotifySuccess = "NotifySuccess"
  show NotifyWarning = "NotifyWarning"
  show NotifyError = "NotifyError"

-- | Convert notification feedback to a haptic pattern
-- | Notifications often use multiple pulses to convey meaning.
notificationToPattern :: NotificationFeedback -> HapticPattern
notificationToPattern NotifySuccess =
  -- Two quick ascending pulses
  hapticPattern
    [ hapticEvent 0.4 0.6 30.0 0.0 10.0
    , hapticEvent 0.6 0.7 40.0 0.0 15.0
    ]
    false
notificationToPattern NotifyWarning =
  -- Three medium pulses
  hapticPattern
    [ hapticEvent 0.5 0.5 35.0 5.0 10.0
    , hapticEvent 0.5 0.5 35.0 5.0 10.0
    , hapticEvent 0.5 0.5 35.0 5.0 10.0
    ]
    false
notificationToPattern NotifyError =
  -- Two heavy pulses
  hapticPattern
    [ hapticEvent 0.8 0.8 50.0 0.0 20.0
    , hapticEvent 0.9 0.9 60.0 0.0 30.0
    ]
    false

-- | Get severity level of notification (0-1)
notificationSeverity :: NotificationFeedback -> Number
notificationSeverity NotifySuccess = 0.3
notificationSeverity NotifyWarning = 0.6
notificationSeverity NotifyError = 0.9

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // selection // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection feedback types for picker/list interactions.
-- |
-- | These correspond to UISelectionFeedbackGenerator on iOS.
data SelectionFeedback
  = SelectionTick                 -- ^ Single selection change
  | SelectionStart                -- ^ Begin selection
  | SelectionEnd                  -- ^ End selection

derive instance eqSelectionFeedback :: Eq SelectionFeedback

instance showSelectionFeedback :: Show SelectionFeedback where
  show SelectionTick = "SelectionTick"
  show SelectionStart = "SelectionStart"
  show SelectionEnd = "SelectionEnd"

-- | Convert selection feedback to a haptic event
selectionToEvent :: SelectionFeedback -> HapticEvent
selectionToEvent SelectionTick =
  -- Very light, quick tick
  hapticEvent 0.15 0.8 10.0 0.0 5.0
selectionToEvent SelectionStart =
  -- Slightly stronger start indicator
  hapticEvent 0.25 0.6 20.0 0.0 10.0
selectionToEvent SelectionEnd =
  -- Confirmation feel
  hapticEvent 0.3 0.7 25.0 5.0 15.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // continuous // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Continuous feedback configuration for ongoing interactions.
-- |
-- | Used for sliders, scroll positions, and textured surfaces.
type ContinuousFeedback =
  { feedbackType :: ContinuousType
  , baseIntensity :: Number       -- ^ Base intensity (0-1)
  , modulation :: Number          -- ^ Intensity variation (0-1)
  , frequency :: Number           -- ^ Update frequency (Hz)
  }

-- | Types of continuous feedback
data ContinuousType
  = TextureType                   -- ^ Textured surface feel
  | SliderType                    -- ^ Position-dependent intensity
  | RampType                      -- ^ Increasing/decreasing over time

derive instance eqContinuousType :: Eq ContinuousType

instance showContinuousType :: Show ContinuousType where
  show TextureType = "Texture"
  show SliderType = "Slider"
  show RampType = "Ramp"

-- | Create a texture feedback (simulates textured surface)
textureFeedback :: Number -> Number -> ContinuousFeedback
textureFeedback intensity modulation =
  { feedbackType: TextureType
  , baseIntensity: clamp 0.0 1.0 intensity
  , modulation: clamp 0.0 1.0 modulation
  , frequency: 60.0  -- 60 Hz update rate
  }

-- | Create a slider feedback (intensity varies with position)
sliderFeedback :: Number -> ContinuousFeedback
sliderFeedback baseIntensity =
  { feedbackType: SliderType
  , baseIntensity: clamp 0.0 1.0 baseIntensity
  , modulation: 0.5  -- Position modulates by 50%
  , frequency: 30.0
  }

-- | Create a ramp feedback (intensity changes over time)
rampFeedback :: Number -> Number -> ContinuousFeedback
rampFeedback startIntensity endIntensity =
  { feedbackType: RampType
  , baseIntensity: clamp 0.0 1.0 startIntensity
  , modulation: clamp 0.0 1.0 (endIntensity - startIntensity)
  , frequency: 60.0
  }

-- | Get intensity at a given position (0-1) for continuous feedback
continuousIntensityAt :: Number -> ContinuousFeedback -> Number
continuousIntensityAt position cf =
  let pos = clamp 0.0 1.0 position
  in case cf.feedbackType of
    TextureType ->
      -- Oscillating intensity based on position
      cf.baseIntensity + cf.modulation * sinApprox (pos * 6.28318 * 10.0)
    SliderType ->
      -- Linear interpolation based on position
      cf.baseIntensity * (1.0 - cf.modulation) + cf.baseIntensity * cf.modulation * pos
    RampType ->
      -- Smooth ramp from base to base + modulation
      cf.baseIntensity + cf.modulation * pos

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // system // patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | iOS system haptic patterns.
-- |
-- | These correspond to specific system interactions on iOS.
data SystemPattern
  = Peek                          -- ^ Preview content (3D Touch peek)
  | Pop                           -- ^ Confirm selection (3D Touch pop)
  | AlignmentGuide                -- ^ Snap to guide (design tools)
  | LevelChange                   -- ^ Undo/redo level marker

derive instance eqSystemPattern :: Eq SystemPattern

instance showSystemPattern :: Show SystemPattern where
  show Peek = "Peek"
  show Pop = "Pop"
  show AlignmentGuide = "AlignmentGuide"
  show LevelChange = "LevelChange"

-- | Convert system pattern to haptic events
systemPatternToEvents :: SystemPattern -> Array HapticEvent
systemPatternToEvents Peek =
  -- Gentle preview indication
  [ hapticEvent 0.3 0.5 40.0 10.0 20.0 ]
systemPatternToEvents Pop =
  -- Stronger confirmation
  [ sustainedPressEvent ]
systemPatternToEvents AlignmentGuide =
  -- Quick snap feedback
  [ hapticEvent 0.4 0.9 15.0 0.0 5.0 ]
systemPatternToEvents LevelChange =
  -- Distinct level marker
  [ hapticEvent 0.5 0.6 30.0 5.0 10.0
  , hapticEvent 0.3 0.4 20.0 5.0 15.0
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // audio // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio feedback types for UI sounds.
data AudioFeedback
  = ClickSound                    -- ^ UI click
  | KeySound                      -- ^ Keyboard key press
  | LockSound                     -- ^ Lock screen
  | PaymentSound                  -- ^ Transaction complete
  | CameraSound                   -- ^ Shutter sound
  | AmbientLoop                   -- ^ Background audio (name parameter)

derive instance eqAudioFeedback :: Eq AudioFeedback

instance showAudioFeedback :: Show AudioFeedback where
  show ClickSound = "ClickSound"
  show KeySound = "KeySound"
  show LockSound = "LockSound"
  show PaymentSound = "PaymentSound"
  show CameraSound = "CameraSound"
  show AmbientLoop = "AmbientLoop"

-- | Convert audio feedback to an audio cue
audioFeedbackToCue :: AudioFeedback -> AudioCue
audioFeedbackToCue ClickSound =
  audioCue "ui_click" 0.4 1.0 0.0
audioFeedbackToCue KeySound =
  audioCue "keyboard_tap" 0.3 1.1 0.0
audioFeedbackToCue LockSound =
  audioCue "lock_screen" 0.5 1.0 0.0
audioFeedbackToCue PaymentSound =
  audioCue "payment_success" 0.6 1.0 0.0
audioFeedbackToCue CameraSound =
  audioCue "camera_shutter" 0.7 1.0 0.0
audioFeedbackToCue AmbientLoop =
  audioCue "ambient_loop" 0.2 1.0 0.0

-- | Get the sound ID for an audio feedback type
audioFeedbackSoundId :: AudioFeedback -> String
audioFeedbackSoundId ClickSound = "ui_click"
audioFeedbackSoundId KeySound = "keyboard_tap"
audioFeedbackSoundId LockSound = "lock_screen"
audioFeedbackSoundId PaymentSound = "payment_success"
audioFeedbackSoundId CameraSound = "camera_shutter"
audioFeedbackSoundId AmbientLoop = "ambient_loop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sine function approximation (for texture modulation)
-- | Using Taylor series: sin(x) ≈ x - x³/6 + x⁵/120
sinApprox :: Number -> Number
sinApprox x =
  let x' = x - (toNumber (floor (x / 6.28318))) * 6.28318  -- Normalize to 0-2π
      x2 = x' * x'
      x3 = x2 * x'
      x5 = x3 * x2
  in x' - x3 / 6.0 + x5 / 120.0
