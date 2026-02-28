-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio Trigger — Event-based audio playback for UI feedback.
-- |
-- | ## Design Philosophy
-- |
-- | Audio triggers are declarative descriptions of when and how to play
-- | sounds in response to UI events. The runtime handles actual playback.
-- |
-- | ## Use Cases
-- |
-- | - Hover sounds (dog bark on hover over dog card)
-- | - Click feedback (button press sounds)
-- | - Enter/exit sounds (slide transitions)
-- | - Achievement sounds (gamification)
-- | - Error/success feedback
-- |
-- | ## Audio Behavior
-- |
-- | - Play once vs loop
-- | - Fade in/out
-- | - Volume control
-- | - Delay before playing
-- |
-- | ## Dependencies
-- |
-- | - Schema.Audio.Level (volume)
-- | - Schema.Dimension.Temporal (delay, fade duration)

module Hydrogen.Schema.Audio.Trigger
  ( -- * Audio Source
    AudioSource
      ( AudioUrl
      , AudioInline
      )
  , audioUrl
  , audioInline
  
  -- * Trigger Events
  , TriggerEvent
      ( OnHoverEnter
      , OnHoverLeave
      , OnClick
      , OnFocus
      , OnBlur
      , OnEnter
      , OnExit
      , OnLoad
      )
  
  -- * Audio Behavior
  , AudioBehavior
      ( PlayOnce
      , Loop
      , FadeIn
      , FadeOut
      , FadeInOut
      )
  
  -- * Audio Trigger
  , AudioTrigger
  , audioTrigger        -- :: AudioSource -> TriggerEvent -> AudioBehavior -> Number -> Number -> Number -> AudioTrigger
  , audioTriggerSimple  -- :: AudioSource -> TriggerEvent -> AudioTrigger
  
  -- * Presets
  , hoverSound          -- :: String -> Number -> AudioTrigger
  , clickSound          -- :: String -> Number -> AudioTrigger
  , transitionSound     -- :: String -> Number -> Number -> AudioTrigger
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of audio content
data AudioSource
  = AudioUrl String       -- ^ URL to audio file
  | AudioInline String    -- ^ Base64-encoded audio data

derive instance eqAudioSource :: Eq AudioSource
derive instance ordAudioSource :: Ord AudioSource

instance showAudioSource :: Show AudioSource where
  show (AudioUrl _) = "AudioUrl"
  show (AudioInline _) = "AudioInline"

-- | Create URL audio source
audioUrl :: String -> AudioSource
audioUrl = AudioUrl

-- | Create inline audio source
audioInline :: String -> AudioSource
audioInline = AudioInline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // trigger events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Events that can trigger audio playback
data TriggerEvent
  = OnHoverEnter    -- ^ Mouse enters element
  | OnHoverLeave    -- ^ Mouse leaves element
  | OnClick         -- ^ Element clicked
  | OnFocus         -- ^ Element receives focus
  | OnBlur          -- ^ Element loses focus
  | OnEnter         -- ^ Element enters viewport / becomes active
  | OnExit          -- ^ Element exits viewport / becomes inactive
  | OnLoad          -- ^ Element finished loading

derive instance eqTriggerEvent :: Eq TriggerEvent
derive instance ordTriggerEvent :: Ord TriggerEvent

instance showTriggerEvent :: Show TriggerEvent where
  show OnHoverEnter = "hover-enter"
  show OnHoverLeave = "hover-leave"
  show OnClick = "click"
  show OnFocus = "focus"
  show OnBlur = "blur"
  show OnEnter = "enter"
  show OnExit = "exit"
  show OnLoad = "load"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // audio behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How audio should be played
data AudioBehavior
  = PlayOnce      -- ^ Play once and stop
  | Loop          -- ^ Loop continuously
  | FadeIn        -- ^ Fade in from silence
  | FadeOut       -- ^ Fade out to silence
  | FadeInOut     -- ^ Fade in at start, fade out at end

derive instance eqAudioBehavior :: Eq AudioBehavior
derive instance ordAudioBehavior :: Ord AudioBehavior

instance showAudioBehavior :: Show AudioBehavior where
  show PlayOnce = "play-once"
  show Loop = "loop"
  show FadeIn = "fade-in"
  show FadeOut = "fade-out"
  show FadeInOut = "fade-in-out"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete audio trigger configuration.
-- | Combines source, event, behavior, volume, and timing.
type AudioTrigger =
  { source :: AudioSource
  , event :: TriggerEvent
  , behavior :: AudioBehavior
  , volume :: Number           -- ^ 0.0 to 1.0 linear gain
  , delayMs :: Number          -- ^ Delay before playing in ms
  , fadeDurationMs :: Number   -- ^ Fade duration in ms (for FadeIn/FadeOut)
  }

-- | Create a full audio trigger with all parameters.
-- |
-- | ## Parameters
-- | - `source`: Audio file URL or inline data
-- | - `event`: Which UI event triggers playback
-- | - `behavior`: How the audio plays (once, loop, fade)
-- | - `volume`: Playback volume (0.0 to 1.0)
-- | - `delayMs`: Delay before playing (milliseconds)
-- | - `fadeDurationMs`: Duration of fade in/out (milliseconds)
audioTrigger
  :: AudioSource
  -> TriggerEvent
  -> AudioBehavior
  -> Number
  -> Number
  -> Number
  -> AudioTrigger
audioTrigger src evt bhv vol delay fade =
  { source: src
  , event: evt
  , behavior: bhv
  , volume: clampVolume vol
  , delayMs: clampDelay delay
  , fadeDurationMs: clampFade fade
  }
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampDelay d
      | d < 0.0 = 0.0
      | otherwise = d
    clampFade f
      | f < 0.0 = 0.0
      | otherwise = f

-- | Create a simple audio trigger with sensible defaults.
-- | Uses PlayOnce behavior, full volume, no delay, no fade.
audioTriggerSimple :: AudioSource -> TriggerEvent -> AudioTrigger
audioTriggerSimple src evt =
  { source: src
  , event: evt
  , behavior: PlayOnce
  , volume: 1.0
  , delayMs: 0.0
  , fadeDurationMs: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a hover sound preset.
-- | Plays on hover enter with slight fade-in for smoothness.
-- |
-- | ## Parameters
-- | - `url`: URL to the audio file
-- | - `volume`: Playback volume (0.0 to 1.0)
hoverSound :: String -> Number -> AudioTrigger
hoverSound url vol =
  { source: AudioUrl url
  , event: OnHoverEnter
  , behavior: FadeIn
  , volume: clampVol vol
  , delayMs: 0.0
  , fadeDurationMs: 50.0
  }
  where
    clampVol v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Create a click sound preset.
-- | Immediate playback on click, no fade.
-- |
-- | ## Parameters
-- | - `url`: URL to the audio file
-- | - `volume`: Playback volume (0.0 to 1.0)
clickSound :: String -> Number -> AudioTrigger
clickSound url vol =
  { source: AudioUrl url
  , event: OnClick
  , behavior: PlayOnce
  , volume: clampVol vol
  , delayMs: 0.0
  , fadeDurationMs: 0.0
  }
  where
    clampVol v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Create a transition sound preset.
-- | Plays on element enter with fade-in-out for smooth transitions.
-- |
-- | ## Parameters
-- | - `url`: URL to the audio file
-- | - `volume`: Playback volume (0.0 to 1.0)
-- | - `fadeDurationMs`: Duration of fade in/out
transitionSound :: String -> Number -> Number -> AudioTrigger
transitionSound url vol fade =
  { source: AudioUrl url
  , event: OnEnter
  , behavior: FadeInOut
  , volume: clampVol vol
  , delayMs: 0.0
  , fadeDurationMs: clampFade fade
  }
  where
    clampVol v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampFade f
      | f < 0.0 = 0.0
      | otherwise = f
