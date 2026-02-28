-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // element // button // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonBehavior — interaction atoms for button response.
-- |
-- | ## Atoms Included
-- |
-- | - Haptic feedback (vibration on press/release)
-- | - Audio cues (click sounds)
-- | - Keyboard shortcuts
-- | - Long press threshold

module Hydrogen.Schema.Element.Button.Behavior
  ( -- * Button Behavior Record
    ButtonBehavior
  , defaultBehavior
    -- * Accessors
  , behHapticPress
  , behHapticRelease
  , behAudioClick
  , behLongPressMs
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback(ImpactLight, ImpactMedium)
  ) as Haptic

import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  ) as Haptic

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // button behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Behavior atoms for button interaction.
-- |
-- | Haptic, audio, and timing properties.
type ButtonBehavior =
  { -- Haptic
    hapticOnPress :: Maybe Haptic.ImpactFeedback    -- ^ Vibration on press
  , hapticOnRelease :: Maybe Haptic.ImpactFeedback  -- ^ Vibration on release
    -- Audio
  , audioOnClick :: Maybe Haptic.AudioCue           -- ^ Sound on click
    -- Timing
  , longPressThresholdMs :: Number                  -- ^ Long press threshold (ms)
  , debounceMs :: Number                            -- ^ Click debounce (ms)
  }

-- | Default button behavior.
-- |
-- | Light haptic on press, no audio, 500ms long press threshold.
defaultBehavior :: ButtonBehavior
defaultBehavior =
  { hapticOnPress: Just Haptic.ImpactLight
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for press.
behHapticPress :: ButtonBehavior -> Maybe Haptic.ImpactFeedback
behHapticPress b = b.hapticOnPress

-- | Get haptic feedback for release.
behHapticRelease :: ButtonBehavior -> Maybe Haptic.ImpactFeedback
behHapticRelease b = b.hapticOnRelease

-- | Get audio cue for click.
behAudioClick :: ButtonBehavior -> Maybe Haptic.AudioCue
behAudioClick b = b.audioOnClick

-- | Get long press threshold in milliseconds.
behLongPressMs :: ButtonBehavior -> Number
behLongPressMs b = b.longPressThresholdMs
