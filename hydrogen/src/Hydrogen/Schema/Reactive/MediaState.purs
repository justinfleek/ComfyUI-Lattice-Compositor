-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // reactive // media-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MediaState - audio/video playback state atoms.
-- |
-- | Models the complete playback lifecycle for Frame.io-level
-- | video interfaces. Includes buffering, seeking, and error states.

module Hydrogen.Schema.Reactive.MediaState
  ( -- * Playback Status
    PlaybackStatus(..)
  , isPlaying
  , isPaused
  , isStopped
  , isBuffering
  , isSeeking
  , isEnded
  , hasError
  -- * Ready State (HTMLMediaElement.readyState)
  , ReadyState(..)
  , isHaveNothing
  , isHaveMetadata
  , isHaveCurrentData
  , isHaveFutureData
  , isHaveEnoughData
  , canPlay
  , canPlayThrough
  -- * Network State (HTMLMediaElement.networkState)
  , NetworkLoadState(..)
  , isNetworkEmpty
  , isNetworkIdle
  , isNetworkLoading
  , isNetworkNoSource
  -- * Playback Rate
  , PlaybackRate(..)
  , playbackRate
  , normalSpeed
  , halfSpeed
  , doubleSpeed
  , unwrapRate
  , isNormalSpeed
  , isSlowMotion
  , isFastForward
  -- * Volume Level
  , VolumeLevel(..)
  , volumeLevel
  , fullVolume
  , halfVolume
  , muted
  , unwrapVolume
  , isMuted
  , isAudible
  -- * Time Position
  , TimePosition(..)
  , timePosition
  , startPosition
  , unwrapTime
  -- * Duration
  , Duration(..)
  , duration
  , unknownDuration
  , unwrapDuration
  , hasDuration
  -- * Buffered Range
  , BufferedRange
  , bufferedRange
  , rangeStartTime
  , rangeEndTime
  , rangeLength
  -- * Media Progress (Molecule)
  , MediaProgress
  , mediaProgress
  , initialProgress
  , progressPercent
  , bufferedPercent
  , remainingTime
  -- * Media State (Compound)
  , MediaState
  , mediaState
  , initialMediaState
  , playingState
  , pausedState
  , endedState
  -- * State Transitions
  , play
  , pause
  , stop
  , seek
  , setVolume
  , toggleMute
  , setPlaybackRate
  -- * Computed Properties
  , shouldShowControls
  , shouldShowBuffering
  , canSeek
  , formattedCurrentTime
  , formattedDuration
  -- * Bounds
  , playbackRateBounds
  , volumeLevelBounds
  , timePositionBounds
  ) where

import Prelude

import Data.Array (last, length)
import Data.Int (floor)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // playback status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media playback status
data PlaybackStatus
  = Playing      -- ^ Actively playing
  | Paused       -- ^ Paused by user
  | Stopped      -- ^ Stopped (at beginning)
  | Buffering    -- ^ Waiting for data
  | Seeking      -- ^ Seeking to new position
  | Ended        -- ^ Reached end of media
  | Error String -- ^ Playback error

derive instance eqPlaybackStatus :: Eq PlaybackStatus

instance showPlaybackStatus :: Show PlaybackStatus where
  show Playing = "playing"
  show Paused = "paused"
  show Stopped = "stopped"
  show Buffering = "buffering"
  show Seeking = "seeking"
  show Ended = "ended"
  show (Error msg) = "error: " <> msg

isPlaying :: PlaybackStatus -> Boolean
isPlaying Playing = true
isPlaying _ = false

isPaused :: PlaybackStatus -> Boolean
isPaused Paused = true
isPaused _ = false

isStopped :: PlaybackStatus -> Boolean
isStopped Stopped = true
isStopped _ = false

isBuffering :: PlaybackStatus -> Boolean
isBuffering Buffering = true
isBuffering _ = false

isSeeking :: PlaybackStatus -> Boolean
isSeeking Seeking = true
isSeeking _ = false

isEnded :: PlaybackStatus -> Boolean
isEnded Ended = true
isEnded _ = false

hasError :: PlaybackStatus -> Boolean
hasError (Error _) = true
hasError _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ready state
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTMLMediaElement.readyState values
data ReadyState
  = HaveNothing      -- ^ 0: No information about media
  | HaveMetadata     -- ^ 1: Metadata loaded (duration, dimensions)
  | HaveCurrentData  -- ^ 2: Current playback position data available
  | HaveFutureData   -- ^ 3: Enough data for current + some future frames
  | HaveEnoughData   -- ^ 4: Enough data to play through without buffering

derive instance eqReadyState :: Eq ReadyState
derive instance ordReadyState :: Ord ReadyState

instance showReadyState :: Show ReadyState where
  show HaveNothing = "have-nothing"
  show HaveMetadata = "have-metadata"
  show HaveCurrentData = "have-current-data"
  show HaveFutureData = "have-future-data"
  show HaveEnoughData = "have-enough-data"

isHaveNothing :: ReadyState -> Boolean
isHaveNothing HaveNothing = true
isHaveNothing _ = false

isHaveMetadata :: ReadyState -> Boolean
isHaveMetadata HaveMetadata = true
isHaveMetadata _ = false

isHaveCurrentData :: ReadyState -> Boolean
isHaveCurrentData HaveCurrentData = true
isHaveCurrentData _ = false

isHaveFutureData :: ReadyState -> Boolean
isHaveFutureData HaveFutureData = true
isHaveFutureData _ = false

isHaveEnoughData :: ReadyState -> Boolean
isHaveEnoughData HaveEnoughData = true
isHaveEnoughData _ = false

-- | Can start playback?
canPlay :: ReadyState -> Boolean
canPlay rs = rs >= HaveFutureData

-- | Can play through without buffering?
canPlayThrough :: ReadyState -> Boolean
canPlayThrough HaveEnoughData = true
canPlayThrough _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // network load state
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTMLMediaElement.networkState values
data NetworkLoadState
  = NetworkEmpty     -- ^ 0: No source set
  | NetworkIdle      -- ^ 1: Not currently downloading
  | NetworkLoading   -- ^ 2: Downloading data
  | NetworkNoSource  -- ^ 3: No supported source found

derive instance eqNetworkLoadState :: Eq NetworkLoadState
derive instance ordNetworkLoadState :: Ord NetworkLoadState

instance showNetworkLoadState :: Show NetworkLoadState where
  show NetworkEmpty = "empty"
  show NetworkIdle = "idle"
  show NetworkLoading = "loading"
  show NetworkNoSource = "no-source"

isNetworkEmpty :: NetworkLoadState -> Boolean
isNetworkEmpty NetworkEmpty = true
isNetworkEmpty _ = false

isNetworkIdle :: NetworkLoadState -> Boolean
isNetworkIdle NetworkIdle = true
isNetworkIdle _ = false

isNetworkLoading :: NetworkLoadState -> Boolean
isNetworkLoading NetworkLoading = true
isNetworkLoading _ = false

isNetworkNoSource :: NetworkLoadState -> Boolean
isNetworkNoSource NetworkNoSource = true
isNetworkNoSource _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // playback rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playback speed multiplier (0.25 - 4.0 typical range)
newtype PlaybackRate = PlaybackRate Number

derive instance eqPlaybackRate :: Eq PlaybackRate
derive instance ordPlaybackRate :: Ord PlaybackRate

instance showPlaybackRate :: Show PlaybackRate where
  show (PlaybackRate r) = show r <> "x"

-- | Create playback rate (clamps to valid range)
playbackRate :: Number -> PlaybackRate
playbackRate r = PlaybackRate (max 0.25 (min 4.0 r))

-- | Normal speed (1.0x)
normalSpeed :: PlaybackRate
normalSpeed = PlaybackRate 1.0

-- | Half speed (0.5x)
halfSpeed :: PlaybackRate
halfSpeed = PlaybackRate 0.5

-- | Double speed (2.0x)
doubleSpeed :: PlaybackRate
doubleSpeed = PlaybackRate 2.0

-- | Extract rate value
unwrapRate :: PlaybackRate -> Number
unwrapRate (PlaybackRate r) = r

-- | Is playing at normal speed?
isNormalSpeed :: PlaybackRate -> Boolean
isNormalSpeed (PlaybackRate r) = r == 1.0

-- | Is playing in slow motion?
isSlowMotion :: PlaybackRate -> Boolean
isSlowMotion (PlaybackRate r) = r < 1.0

-- | Is playing in fast forward?
isFastForward :: PlaybackRate -> Boolean
isFastForward (PlaybackRate r) = r > 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // volume level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Volume level (0.0 - 1.0)
newtype VolumeLevel = VolumeLevel Number

derive instance eqVolumeLevel :: Eq VolumeLevel
derive instance ordVolumeLevel :: Ord VolumeLevel

instance showVolumeLevel :: Show VolumeLevel where
  show (VolumeLevel v) = show (floor (v * 100.0)) <> "%"

-- | Create volume level (clamps to 0-1)
volumeLevel :: Number -> VolumeLevel
volumeLevel v = VolumeLevel (max 0.0 (min 1.0 v))

-- | Full volume
fullVolume :: VolumeLevel
fullVolume = VolumeLevel 1.0

-- | Half volume
halfVolume :: VolumeLevel
halfVolume = VolumeLevel 0.5

-- | Muted (0 volume)
muted :: VolumeLevel
muted = VolumeLevel 0.0

-- | Extract volume value
unwrapVolume :: VolumeLevel -> Number
unwrapVolume (VolumeLevel v) = v

-- | Is volume at zero?
isMuted :: VolumeLevel -> Boolean
isMuted (VolumeLevel v) = v == 0.0

-- | Is volume above zero?
isAudible :: VolumeLevel -> Boolean
isAudible (VolumeLevel v) = v > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // time position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current time position in seconds
newtype TimePosition = TimePosition Number

derive instance eqTimePosition :: Eq TimePosition
derive instance ordTimePosition :: Ord TimePosition

instance showTimePosition :: Show TimePosition where
  show (TimePosition t) = formatTime t

-- | Create time position (clamps to [0, 604800] seconds)
-- |
-- | Maximum is 7 days (604800 seconds) — practical upper limit for any media.
timePosition :: Number -> TimePosition
timePosition t = TimePosition (Bounded.clampNumber 0.0 604800.0 t)

-- | Start of media
startPosition :: TimePosition
startPosition = TimePosition 0.0

-- | Extract time value
unwrapTime :: TimePosition -> Number
unwrapTime (TimePosition t) = t

-- | Format time as MM:SS or HH:MM:SS
formatTime :: Number -> String
formatTime seconds =
  let totalSeconds = floor seconds
      h = totalSeconds / 3600
      m = (totalSeconds `mod` 3600) / 60
      s = totalSeconds `mod` 60
      pad n = if n < 10 then "0" <> show n else show n
  in if h > 0
       then show h <> ":" <> pad m <> ":" <> pad s
       else pad m <> ":" <> pad s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media duration in seconds (Maybe because unknown until loaded)
newtype Duration = Duration (Maybe Number)

derive instance eqDuration :: Eq Duration

instance showDuration :: Show Duration where
  show (Duration Nothing) = "--:--"
  show (Duration (Just d)) = formatTime d

-- | Create duration
duration :: Number -> Duration
duration d = Duration (Just (max 0.0 d))

-- | Unknown duration (not yet loaded)
unknownDuration :: Duration
unknownDuration = Duration Nothing

-- | Extract duration value
unwrapDuration :: Duration -> Maybe Number
unwrapDuration (Duration d) = d

-- | Is duration known?
hasDuration :: Duration -> Boolean
hasDuration (Duration d) = isJust d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // buffered range
-- ═════════════════════════════════════════════════════════════════════════════

-- | A buffered time range
type BufferedRange =
  { start :: Number  -- ^ Start time in seconds
  , end :: Number    -- ^ End time in seconds
  }

-- | Create buffered range
bufferedRange :: Number -> Number -> BufferedRange
bufferedRange start end =
  { start: max 0.0 start
  , end: max start end
  }

-- | Get range start
rangeStartTime :: BufferedRange -> Number
rangeStartTime r = r.start

-- | Get range end
rangeEndTime :: BufferedRange -> Number
rangeEndTime r = r.end

-- | Get range length
rangeLength :: BufferedRange -> Number
rangeLength r = r.end - r.start

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // media progress molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playback and buffering progress
type MediaProgress =
  { currentTime :: TimePosition
  , duration :: Duration
  , buffered :: Array BufferedRange
  }

-- | Create media progress
mediaProgress :: TimePosition -> Duration -> Array BufferedRange -> MediaProgress
mediaProgress currentTime dur buffered =
  { currentTime, duration: dur, buffered }

-- | Initial progress (start, unknown duration)
initialProgress :: MediaProgress
initialProgress = mediaProgress startPosition unknownDuration []

-- | Get progress as percentage (0-100)
progressPercent :: MediaProgress -> Number
progressPercent mp = case unwrapDuration mp.duration of
  Nothing -> 0.0
  Just dur -> 
    if dur <= 0.0 
      then 0.0 
      else (unwrapTime mp.currentTime / dur) * 100.0

-- | Get buffered percentage (furthest buffered point)
bufferedPercent :: MediaProgress -> Number
bufferedPercent mp = case unwrapDuration mp.duration of
  Nothing -> 0.0
  Just dur ->
    if dur <= 0.0 
      then 0.0
      else case last mp.buffered of
        Nothing -> 0.0
        Just r -> (r.end / dur) * 100.0

-- | Get remaining time in seconds
remainingTime :: MediaProgress -> Maybe Number
remainingTime mp = case unwrapDuration mp.duration of
  Nothing -> Nothing
  Just dur -> Just (dur - unwrapTime mp.currentTime)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // media state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete media playback state
type MediaState =
  { status :: PlaybackStatus
  , readyState :: ReadyState
  , networkState :: NetworkLoadState
  , progress :: MediaProgress
  , volume :: VolumeLevel
  , isMuted :: Boolean           -- ^ Separate from volume (can be muted at full volume)
  , playbackRate :: PlaybackRate
  , isFullscreen :: Boolean
  , isPictureInPicture :: Boolean
  , loop :: Boolean
  , autoplay :: Boolean
  }

-- | Create media state
mediaState :: PlaybackStatus -> MediaProgress -> MediaState
mediaState status progress =
  { status
  , readyState: HaveNothing
  , networkState: NetworkEmpty
  , progress
  , volume: fullVolume
  , isMuted: false
  , playbackRate: normalSpeed
  , isFullscreen: false
  , isPictureInPicture: false
  , loop: false
  , autoplay: false
  }

-- | Initial media state (stopped, nothing loaded)
initialMediaState :: MediaState
initialMediaState = mediaState Stopped initialProgress

-- | Playing state
playingState :: MediaProgress -> MediaState
playingState = mediaState Playing

-- | Paused state
pausedState :: MediaProgress -> MediaState
pausedState = mediaState Paused

-- | Ended state
endedState :: MediaProgress -> MediaState
endedState = mediaState Ended

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start playback
play :: MediaState -> MediaState
play ms = ms { status = Playing }

-- | Pause playback
pause :: MediaState -> MediaState
pause ms = ms { status = Paused }

-- | Stop playback (reset to beginning)
stop :: MediaState -> MediaState
stop ms = ms 
  { status = Stopped
  , progress = ms.progress { currentTime = startPosition }
  }

-- | Seek to position
seek :: TimePosition -> MediaState -> MediaState
seek pos ms = ms
  { status = Seeking
  , progress = ms.progress { currentTime = pos }
  }

-- | Set volume level
setVolume :: VolumeLevel -> MediaState -> MediaState
setVolume vol ms = ms { volume = vol }

-- | Toggle mute state
toggleMute :: MediaState -> MediaState
toggleMute ms = ms { isMuted = not ms.isMuted }

-- | Set playback rate
setPlaybackRate :: PlaybackRate -> MediaState -> MediaState
setPlaybackRate rate ms = ms { playbackRate = rate }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should show playback controls?
shouldShowControls :: MediaState -> Boolean
shouldShowControls ms = 
  isPaused ms.status || 
  isStopped ms.status || 
  isEnded ms.status

-- | Should show buffering indicator?
shouldShowBuffering :: MediaState -> Boolean
shouldShowBuffering ms =
  isBuffering ms.status ||
  (isPlaying ms.status && not (canPlayThrough ms.readyState))

-- | Can seek in media?
canSeek :: MediaState -> Boolean
canSeek ms = 
  hasDuration ms.progress.duration &&
  length ms.progress.buffered > 0

-- | Get formatted current time string
formattedCurrentTime :: MediaState -> String
formattedCurrentTime ms = show ms.progress.currentTime

-- | Get formatted duration string
formattedDuration :: MediaState -> String
formattedDuration ms = show ms.progress.duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for PlaybackRate [0.25, 4.0]
-- |
-- | - 0.25x: Quarter speed (slowest practical slow-motion)
-- | - 4.0x: Quadruple speed (fastest practical fast-forward)
playbackRateBounds :: Bounded.NumberBounds
playbackRateBounds = Bounded.numberBounds 0.25 4.0 "PlaybackRate"
  "Playback speed multiplier (0.25x slow-motion to 4.0x fast-forward)"

-- | Bounds for VolumeLevel [0.0, 1.0]
-- |
-- | - 0.0: Muted (silent)
-- | - 1.0: Full volume
volumeLevelBounds :: Bounded.NumberBounds
volumeLevelBounds = Bounded.numberBounds 0.0 1.0 "VolumeLevel"
  "Audio volume level as unit interval (0=muted, 1=full)"

-- | Bounds for TimePosition [0.0, 604800.0] seconds
-- |
-- | - 0.0: Start of media
-- | - 604800.0: 7 days (maximum practical media duration)
timePositionBounds :: Bounded.NumberBounds
timePositionBounds = Bounded.numberBounds 0.0 604800.0 "TimePosition"
  "Playback position in seconds (0 to 7 days maximum)"
