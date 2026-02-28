-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // audio // av-sync
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AVSync — Audio-Visual Synchronization Primitives
-- |
-- | ## Purpose
-- |
-- | Provides types for synchronized audio-visual elements. Critical for:
-- | - AI avatar lip-sync
-- | - Medical device audio-visual alerts
-- | - Video editing / motion graphics
-- | - Accessibility (audio descriptions synced to visual state)
-- |
-- | ## Architecture
-- |
-- | ```
-- | AVElement
-- |   ├── visual :: Element        -- What to render
-- |   ├── audio :: AudioCue        -- What to play
-- |   └── sync :: SyncMode         -- How they relate
-- |
-- | VoiceElement
-- |   ├── text :: String           -- What to say
-- |   ├── voice :: VoiceProfile    -- How to say it
-- |   └── emotion :: EmotionTag    -- Emotional coloring
-- | ```
-- |
-- | ## Sync Modes
-- |
-- | - `SyncImmediate` — Play audio when visual appears
-- | - `SyncOnVisible` — Play when element enters viewport
-- | - `SyncOnProgress` — Scrub audio with animation progress
-- | - `SyncOnMarker` — Play at specific timeline markers
-- |
-- | ## Reference
-- | Council gap: COUNCIL_REVIEW.md §3.6 "MISSING: Audio-visual sync"
module Hydrogen.Audio.AVSync
  ( -- * Sync Mode
    SyncMode(..)
    -- * Audio Cue
  , AudioCue
  , audioCue
  , audioCueSimple
    -- * AV Element
  , AVElement
  , avElement
  , avElementSimple
    -- * Voice Element  
  , VoiceElement
  , voiceElement
  , voiceElementSimple
    -- * Emotion Tags
  , EmotionTag(..)
  , emotionIntensity
    -- * Timeline Marker
  , TimelineMarker
  , marker
    -- * Lip Sync
  , LipSyncMode(..)
  , LipSyncData
  , VisemeFrame
  , lipSyncData
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Audio.Voice as Voice
import Hydrogen.Schema.Audio.Trigger as Trigger

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sync mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How audio and visual elements are synchronized.
data SyncMode
  = SyncImmediate              -- ^ Audio plays when visual renders
  | SyncOnVisible              -- ^ Audio plays when element enters viewport
  | SyncOnProgress Number      -- ^ Audio position tied to animation progress (0-1)
  | SyncOnMarker TimelineMarker -- ^ Audio plays at specific marker
  | SyncManual                 -- ^ Sync controlled externally (programmatic)
  | SyncNone                   -- ^ No synchronization (independent)

derive instance eqSyncMode :: Eq SyncMode

instance showSyncMode :: Show SyncMode where
  show SyncImmediate = "SyncImmediate"
  show SyncOnVisible = "SyncOnVisible"
  show (SyncOnProgress p) = "(SyncOnProgress " <> show p <> ")"
  show (SyncOnMarker m) = "(SyncOnMarker " <> show m.id <> ")"
  show SyncManual = "SyncManual"
  show SyncNone = "SyncNone"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // timeline marker
-- ═════════════════════════════════════════════════════════════════════════════

-- | A named point in a timeline for synchronization.
type TimelineMarker =
  { id :: String                -- ^ Unique marker identifier
  , timeMs :: Number            -- ^ Position in milliseconds
  , label :: Maybe String       -- ^ Human-readable label
  }

-- | Create a timeline marker.
marker :: String -> Number -> TimelineMarker
marker markerId time =
  { id: markerId
  , timeMs: clampTime time
  , label: Nothing
  }
  where
    clampTime t
      | t < 0.0 = 0.0
      | otherwise = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // audio cue
-- ═════════════════════════════════════════════════════════════════════════════

-- | An audio event to be triggered in sync with visuals.
-- |
-- | Builds on AudioTrigger but adds timing and priority for AV sync.
type AudioCue =
  { trigger :: Trigger.AudioTrigger   -- ^ The audio trigger configuration
  , priority :: Int                   -- ^ Priority for overlapping cues (higher wins)
  , offsetMs :: Number                -- ^ Offset from sync point in ms
  , durationMs :: Maybe Number        -- ^ Optional duration limit
  , interruptible :: Boolean          -- ^ Can be interrupted by higher priority cue
  }

-- | Create an audio cue with full configuration.
audioCue 
  :: Trigger.AudioTrigger 
  -> Int 
  -> Number 
  -> Maybe Number 
  -> Boolean 
  -> AudioCue
audioCue trig prio offset dur interrupt =
  { trigger: trig
  , priority: prio
  , offsetMs: offset
  , durationMs: dur
  , interruptible: interrupt
  }

-- | Create a simple audio cue with sensible defaults.
-- | Priority 0, no offset, no duration limit, interruptible.
audioCueSimple :: Trigger.AudioTrigger -> AudioCue
audioCueSimple trig =
  { trigger: trig
  , priority: 0
  , offsetMs: 0.0
  , durationMs: Nothing
  , interruptible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // av element
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined audio-visual element.
-- |
-- | The `visual` field is a String identifier referencing an Element.
-- | This avoids circular dependency with Element module while enabling
-- | runtime to resolve the actual Element for rendering.
-- |
-- | For full type safety, wrap this in your app's Element type:
-- | ```purescript
-- | data MyElement
-- |   = Pure Element
-- |   | WithAudio AVElement Element
-- | ```
type AVElement =
  { visualId :: String          -- ^ Reference to visual Element
  , audio :: AudioCue           -- ^ Audio to play
  , sync :: SyncMode            -- ^ How they synchronize
  , fallbackText :: Maybe String -- ^ Accessibility fallback
  }

-- | Create an AV element with full configuration.
avElement :: String -> AudioCue -> SyncMode -> Maybe String -> AVElement
avElement vid aud syncMode fallback =
  { visualId: vid
  , audio: aud
  , sync: syncMode
  , fallbackText: fallback
  }

-- | Create a simple AV element with immediate sync and no fallback.
avElementSimple :: String -> AudioCue -> AVElement
avElementSimple vid aud =
  { visualId: vid
  , audio: aud
  , sync: SyncImmediate
  , fallbackText: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // emotion tag
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emotional coloring for synthesized speech.
-- |
-- | These map to voice parameter adjustments:
-- | - Happy → higher pitch, faster rate, more variation
-- | - Sad → lower pitch, slower rate, less energy
-- | - Angry → higher intensity, faster rate, more strain
-- | - etc.
data EmotionTag
  = EmotionNeutral              -- ^ No emotional coloring
  | EmotionHappy Number         -- ^ Joy/happiness (0-1 intensity)
  | EmotionSad Number           -- ^ Sadness/melancholy
  | EmotionAngry Number         -- ^ Anger/frustration
  | EmotionFear Number          -- ^ Fear/anxiety
  | EmotionSurprise Number      -- ^ Surprise/astonishment
  | EmotionDisgust Number       -- ^ Disgust/revulsion
  | EmotionContempt Number      -- ^ Contempt/disdain
  | EmotionExcitement Number    -- ^ Excitement/enthusiasm
  | EmotionCalm Number          -- ^ Calm/serenity
  | EmotionConcern Number       -- ^ Concern/worry
  | EmotionConfidence Number    -- ^ Confidence/assurance

derive instance eqEmotionTag :: Eq EmotionTag
derive instance ordEmotionTag :: Ord EmotionTag

instance showEmotionTag :: Show EmotionTag where
  show EmotionNeutral = "Neutral"
  show (EmotionHappy i) = "Happy(" <> show i <> ")"
  show (EmotionSad i) = "Sad(" <> show i <> ")"
  show (EmotionAngry i) = "Angry(" <> show i <> ")"
  show (EmotionFear i) = "Fear(" <> show i <> ")"
  show (EmotionSurprise i) = "Surprise(" <> show i <> ")"
  show (EmotionDisgust i) = "Disgust(" <> show i <> ")"
  show (EmotionContempt i) = "Contempt(" <> show i <> ")"
  show (EmotionExcitement i) = "Excitement(" <> show i <> ")"
  show (EmotionCalm i) = "Calm(" <> show i <> ")"
  show (EmotionConcern i) = "Concern(" <> show i <> ")"
  show (EmotionConfidence i) = "Confidence(" <> show i <> ")"

-- | Extract intensity from emotion tag (0-1).
emotionIntensity :: EmotionTag -> Number
emotionIntensity EmotionNeutral = 0.0
emotionIntensity (EmotionHappy i) = clamp01 i
emotionIntensity (EmotionSad i) = clamp01 i
emotionIntensity (EmotionAngry i) = clamp01 i
emotionIntensity (EmotionFear i) = clamp01 i
emotionIntensity (EmotionSurprise i) = clamp01 i
emotionIntensity (EmotionDisgust i) = clamp01 i
emotionIntensity (EmotionContempt i) = clamp01 i
emotionIntensity (EmotionExcitement i) = clamp01 i
emotionIntensity (EmotionCalm i) = clamp01 i
emotionIntensity (EmotionConcern i) = clamp01 i
emotionIntensity (EmotionConfidence i) = clamp01 i

-- | Clamp to 0-1 range
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // voice element
-- ═════════════════════════════════════════════════════════════════════════════

-- | AI voice rendering element.
-- |
-- | Combines text content with voice profile and emotional expression.
-- | The runtime synthesizes speech using TTS (text-to-speech) or
-- | neural voice synthesis based on these parameters.
type VoiceElement =
  { text :: String                    -- ^ Text to speak
  , voice :: Voice.VoiceProfile       -- ^ Voice characteristics
  , emotion :: EmotionTag             -- ^ Emotional coloring
  , ssml :: Maybe String              -- ^ Optional SSML markup for fine control
  , language :: String                -- ^ BCP 47 language tag (e.g., "en-US")
  , lipSync :: Maybe LipSyncMode      -- ^ Optional lip sync configuration
  }

-- | Create a voice element with full configuration.
voiceElement 
  :: String 
  -> Voice.VoiceProfile 
  -> EmotionTag 
  -> Maybe String 
  -> String 
  -> Maybe LipSyncMode 
  -> VoiceElement
voiceElement txt vp emo ssmlMarkup lang lip =
  { text: txt
  , voice: vp
  , emotion: emo
  , ssml: ssmlMarkup
  , language: lang
  , lipSync: lip
  }

-- | Create a simple voice element with defaults.
-- | Uses default voice profile, neutral emotion, English, no lip sync.
voiceElementSimple :: String -> VoiceElement
voiceElementSimple txt =
  { text: txt
  , voice: Voice.voiceProfileDefault
  , emotion: EmotionNeutral
  , ssml: Nothing
  , language: "en-US"
  , lipSync: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // lip sync
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lip synchronization mode for AI avatars.
data LipSyncMode
  = LipSyncNone                 -- ^ No lip sync
  | LipSyncViseme               -- ^ Viseme-based (mouth shapes)
  | LipSyncBlendShape           -- ^ Blend shape animation
  | LipSyncPhoneme              -- ^ Phoneme-to-shape mapping

derive instance eqLipSyncMode :: Eq LipSyncMode
derive instance ordLipSyncMode :: Ord LipSyncMode

instance showLipSyncMode :: Show LipSyncMode where
  show LipSyncNone = "None"
  show LipSyncViseme = "Viseme"
  show LipSyncBlendShape = "BlendShape"
  show LipSyncPhoneme = "Phoneme"

-- | Lip sync data for a voice element.
-- |
-- | Contains timing information for animating mouth shapes
-- | in sync with synthesized speech.
type LipSyncData =
  { mode :: LipSyncMode
  , framerate :: Number           -- ^ Frames per second for sync data
  , visemes :: Array VisemeFrame  -- ^ Sequence of mouth shapes with timing
  }

-- | A single frame of lip sync data.
type VisemeFrame =
  { timeMs :: Number              -- ^ Time offset in milliseconds
  , viseme :: String              -- ^ Viseme identifier (e.g., "AA", "EE", "OO")
  , weight :: Number              -- ^ Blend weight 0-1
  }

-- | Create lip sync data configuration.
lipSyncData :: LipSyncMode -> Number -> Array VisemeFrame -> LipSyncData
lipSyncData mode fps frames =
  { mode: mode
  , framerate: clampFps fps
  , visemes: frames
  }
  where
    clampFps f
      | f < 1.0 = 1.0
      | f > 120.0 = 120.0
      | otherwise = f
