-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // motion // lottie
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lottie — Animation data and playback configuration.
-- |
-- | ## Design Philosophy
-- |
-- | Lottie animations are JSON-based vector animations exported from
-- | After Effects via Bodymovin. This module provides:
-- | - Source management (URL or inline JSON)
-- | - Playback control (autoplay, loop, direction, speed)
-- | - Event-triggered playback
-- | - Segment playback (specific frame ranges)
-- |
-- | ## Use Cases
-- |
-- | - Loading spinners
-- | - Hover animations (dog starts playing when hovered)
-- | - Success/error feedback animations
-- | - Decorative illustrations
-- | - Icon animations
-- |
-- | ## Runtime Interpretation
-- |
-- | The runtime uses lottie-web or similar library to render.
-- | This module is pure data describing WHAT to animate.

module Hydrogen.Schema.Motion.Lottie
  ( -- * Lottie Source
    LottieSource
      ( LottieUrl
      , LottieInline
      )
  , lottieUrl
  , lottieInline
  
  -- * Playback Direction
  , PlaybackDirection
      ( Forward
      , Reverse
      , Alternate
      )
  
  -- * Loop Mode
  , LoopMode
      ( LoopInfinite
      , LoopCount
      )
  
  -- * Playback Config
  , LottiePlayback(..)
  , lottiePlayback
  , defaultPlayback
  , autoplayLoop
  , playOnce
  , playAlternate
  , manualPlayback
  , slowMotion
  , fastPlayback
  
  -- * Segment
  , LottieSegment
      ( SegmentFull
      , SegmentFrames
      , SegmentMarker
      , SegmentMarkerRange
      )
  , lottieSegment
  , fullAnimation
  , frameRange
  , markerSegment
  , markerRange
  , firstHalf
  , secondHalf
  , singleFrame
  
  -- * Trigger Config
  , LottieTrigger
      ( TriggerOnLoad
      , TriggerOnHover
      , TriggerOnClick
      , TriggerOnEnter
      , TriggerManual
      )
  
  -- * Renderer
  , LottieRenderer
      ( RendererSvg
      , RendererCanvas
      , RendererHtml
      )
  
  -- * Lottie Animation
  , LottieAnimation(..)
  , lottieAnimation
  , defaultLottie
  , fromUrl
  , fromInline
  , loadingSpinner
  , hoverAnimation
  , clickAnimation
  , scrollAnimation
  , successAnimation
  , errorAnimation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  , (<=)
  , (/)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // lottie source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of Lottie animation data
data LottieSource
  = LottieUrl String      -- ^ URL to .json animation file
  | LottieInline String   -- ^ Inline JSON animation data

derive instance eqLottieSource :: Eq LottieSource
derive instance ordLottieSource :: Ord LottieSource

instance showLottieSource :: Show LottieSource where
  show (LottieUrl _) = "LottieUrl"
  show (LottieInline _) = "LottieInline"

-- | Create URL lottie source
lottieUrl :: String -> LottieSource
lottieUrl = LottieUrl

-- | Create inline lottie source
lottieInline :: String -> LottieSource
lottieInline = LottieInline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // playback direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation playback direction
data PlaybackDirection
  = Forward     -- ^ Play from start to end
  | Reverse     -- ^ Play from end to start
  | Alternate   -- ^ Alternate between forward and reverse

derive instance eqPlaybackDirection :: Eq PlaybackDirection
derive instance ordPlaybackDirection :: Ord PlaybackDirection

instance showPlaybackDirection :: Show PlaybackDirection where
  show Forward = "forward"
  show Reverse = "reverse"
  show Alternate = "alternate"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // playback config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lottie playback configuration.
-- |
-- | Controls how the animation plays:
-- | - Autoplay on load or wait for trigger
-- | - Loop count (finite or infinite)
-- | - Playback speed (1.0 = normal, 0.5 = half speed, 2.0 = double)
-- | - Direction (forward, reverse, alternate ping-pong)
-- | - Initial delay before starting
-- |
-- | ## Speed Bounds
-- |
-- | Speed is clamped to 0.1 to 10.0:
-- | - Below 0.1 is effectively paused
-- | - Above 10.0 is too fast to perceive
-- |
-- | ## Loop Behavior
-- |
-- | - `LoopInfinite`: Loop forever until stopped
-- | - `LoopCount n`: Play n times then stop
-- | - `LoopCount 1`: Play once (same as playOnce)
newtype LottiePlayback = LottiePlayback
  { autoplay :: Boolean            -- ^ Start playing on load
  , loop :: LoopMode               -- ^ Loop behavior
  , speed :: Number                -- ^ Playback speed (0.1 to 10.0)
  , direction :: PlaybackDirection -- ^ Playback direction
  , delayMs :: Number              -- ^ Delay before starting (milliseconds)
  , pauseOnHoverExit :: Boolean    -- ^ Pause when mouse leaves (for hover triggers)
  , resetOnComplete :: Boolean     -- ^ Reset to first frame when done
  }

-- | Loop mode for animation
data LoopMode
  = LoopInfinite                   -- ^ Loop forever
  | LoopCount Int                  -- ^ Loop n times (1 = play once)

derive instance eqLoopMode :: Eq LoopMode

instance showLoopMode :: Show LoopMode where
  show LoopInfinite = "infinite"
  show (LoopCount n) = "loop:" <> show n

derive instance eqLottiePlayback :: Eq LottiePlayback

instance showLottiePlayback :: Show LottiePlayback where
  show (LottiePlayback p) = 
    "LottiePlayback(speed:" <> show p.speed <> 
    ", " <> show p.loop <> ")"

-- | Create playback config with full options
lottiePlayback
  :: { autoplay :: Boolean
     , loop :: LoopMode
     , speed :: Number
     , direction :: PlaybackDirection
     , delayMs :: Number
     , pauseOnHoverExit :: Boolean
     , resetOnComplete :: Boolean
     }
  -> LottiePlayback
lottiePlayback cfg = LottiePlayback
  { autoplay: cfg.autoplay
  , loop: cfg.loop
  , speed: clampSpeed cfg.speed
  , direction: cfg.direction
  , delayMs: clampMs cfg.delayMs
  , pauseOnHoverExit: cfg.pauseOnHoverExit
  , resetOnComplete: cfg.resetOnComplete
  }
  where
    clampSpeed s
      | s < 0.1 = 0.1
      | s > 10.0 = 10.0
      | otherwise = s
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | Default playback (autoplay, loop forever, 1x speed, forward)
defaultPlayback :: LottiePlayback
defaultPlayback = LottiePlayback
  { autoplay: true
  , loop: LoopInfinite
  , speed: 1.0
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: false
  }

-- | Autoplay with infinite loop
autoplayLoop :: LottiePlayback
autoplayLoop = LottiePlayback
  { autoplay: true
  , loop: LoopInfinite
  , speed: 1.0
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: false
  }

-- | Play once and stop
playOnce :: LottiePlayback
playOnce = LottiePlayback
  { autoplay: true
  , loop: LoopCount 1
  , speed: 1.0
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: true
  }

-- | Play forward then reverse (ping-pong)
playAlternate :: LottiePlayback
playAlternate = LottiePlayback
  { autoplay: true
  , loop: LoopInfinite
  , speed: 1.0
  , direction: Alternate
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: false
  }

-- | Manual control (no autoplay, for programmatic triggers)
manualPlayback :: LottiePlayback
manualPlayback = LottiePlayback
  { autoplay: false
  , loop: LoopCount 1
  , speed: 1.0
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: true
  , resetOnComplete: true
  }

-- | Slow motion playback (0.5x speed)
slowMotion :: LottiePlayback
slowMotion = LottiePlayback
  { autoplay: true
  , loop: LoopInfinite
  , speed: 0.5
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: false
  }

-- | Fast playback (2x speed)
fastPlayback :: LottiePlayback
fastPlayback = LottiePlayback
  { autoplay: true
  , loop: LoopInfinite
  , speed: 2.0
  , direction: Forward
  , delayMs: 0.0
  , pauseOnHoverExit: false
  , resetOnComplete: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // segment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Segment of animation (frame range).
-- |
-- | Lottie animations can be played in segments:
-- | - Full animation (all frames)
-- | - Specific frame range (startFrame to endFrame)
-- | - Named markers (if defined in After Effects)
-- |
-- | ## Frame Numbers
-- |
-- | Frames are 0-indexed integers. A typical 2-second animation at 30fps
-- | has frames 0-59.
-- |
-- | ## Markers
-- |
-- | After Effects allows naming frames with markers. These can be referenced
-- | by name rather than frame number, making animations more maintainable.
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Play frames 0-30 only
-- | introSegment = frameRange 0 30
-- |
-- | -- Play from marker "hover_start" to "hover_end"
-- | hoverSegment = markerRange "hover_start" "hover_end"
-- | ```
data LottieSegment
  = SegmentFull                        -- ^ Play entire animation
  | SegmentFrames Int Int              -- ^ Play from startFrame to endFrame (inclusive)
  | SegmentMarker String               -- ^ Play segment defined by single marker
  | SegmentMarkerRange String String   -- ^ Play from startMarker to endMarker

derive instance eqLottieSegment :: Eq LottieSegment

instance showLottieSegment :: Show LottieSegment where
  show SegmentFull = "full"
  show (SegmentFrames start end) = 
    "frames:" <> show start <> "-" <> show end
  show (SegmentMarker name) = 
    "marker:" <> name
  show (SegmentMarkerRange start end) = 
    "markers:" <> start <> "-" <> end

-- | Create segment from frame range
-- |
-- | Clamps negative frames to 0. Swaps start/end if start > end.
lottieSegment :: Int -> Int -> LottieSegment
lottieSegment startFrame endFrame = 
  let
    s = clampFrame startFrame
    e = clampFrame endFrame
  in
    if s <= e
      then SegmentFrames s e
      else SegmentFrames e s
  where
    clampFrame f
      | f < 0 = 0
      | otherwise = f

-- | Full animation (all frames from start to end)
fullAnimation :: LottieSegment
fullAnimation = SegmentFull

-- | Specific frame range
frameRange :: Int -> Int -> LottieSegment
frameRange = lottieSegment

-- | Single marker segment
markerSegment :: String -> LottieSegment
markerSegment = SegmentMarker

-- | Range between two markers
markerRange :: String -> String -> LottieSegment
markerRange = SegmentMarkerRange

-- | First half of animation (useful for hover-in)
firstHalf :: Int -> LottieSegment
firstHalf totalFrames = SegmentFrames 0 (totalFrames / 2)

-- | Second half of animation (useful for hover-out)
secondHalf :: Int -> LottieSegment
secondHalf totalFrames = SegmentFrames (totalFrames / 2) totalFrames

-- | Single frame (for paused states)
singleFrame :: Int -> LottieSegment
singleFrame frame = SegmentFrames frame frame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lottie trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | When to start playing the animation
data LottieTrigger
  = TriggerOnLoad     -- ^ Play when element loads
  | TriggerOnHover    -- ^ Play when hovered
  | TriggerOnClick    -- ^ Play when clicked
  | TriggerOnEnter    -- ^ Play when element enters viewport
  | TriggerManual     -- ^ Don't auto-play, control programmatically

derive instance eqLottieTrigger :: Eq LottieTrigger
derive instance ordLottieTrigger :: Ord LottieTrigger

instance showLottieTrigger :: Show LottieTrigger where
  show TriggerOnLoad = "on-load"
  show TriggerOnHover = "on-hover"
  show TriggerOnClick = "on-click"
  show TriggerOnEnter = "on-enter"
  show TriggerManual = "manual"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // lottie animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Lottie animation configuration.
-- |
-- | Composes all Lottie configuration into a single type:
-- | - Source (URL or inline JSON)
-- | - Playback settings (speed, loop, direction)
-- | - Segment (which frames to play)
-- | - Trigger (when to start playing)
-- | - Renderer settings (SVG vs Canvas vs HTML)
-- |
-- | ## Renderer Options
-- |
-- | - `RendererSvg`: Best quality, most compatible
-- | - `RendererCanvas`: Better performance for complex animations
-- | - `RendererHtml`: Renders as DOM elements (limited support)
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple loading spinner
-- | spinner = lottieAnimation
-- |   { source: LottieUrl "/animations/spinner.json"
-- |   , playback: autoplayLoop
-- |   , segment: fullAnimation
-- |   , trigger: TriggerOnLoad
-- |   , renderer: RendererSvg
-- |   , preserveAspectRatio: "xMidYMid slice"
-- |   }
-- |
-- | -- Hover-triggered icon
-- | hoverIcon = fromUrl "/animations/menu-icon.json" TriggerOnHover
-- | ```
newtype LottieAnimation = LottieAnimation
  { source :: LottieSource             -- ^ Animation data source
  , playback :: LottiePlayback         -- ^ Playback configuration
  , segment :: LottieSegment           -- ^ Which segment to play
  , trigger :: LottieTrigger           -- ^ When to start playing
  , renderer :: LottieRenderer         -- ^ How to render
  , preserveAspectRatio :: String      -- ^ SVG preserveAspectRatio attribute
  , className :: String                -- ^ CSS class for container
  , ariaLabel :: String                -- ^ Accessibility label
  }

-- | Lottie renderer backend
data LottieRenderer
  = RendererSvg      -- ^ SVG renderer (default, best quality)
  | RendererCanvas   -- ^ Canvas 2D renderer (better performance)
  | RendererHtml     -- ^ HTML/DOM renderer (limited support)

derive instance eqLottieRenderer :: Eq LottieRenderer

instance showLottieRenderer :: Show LottieRenderer where
  show RendererSvg = "svg"
  show RendererCanvas = "canvas"
  show RendererHtml = "html"

derive instance eqLottieAnimation :: Eq LottieAnimation

instance showLottieAnimation :: Show LottieAnimation where
  show (LottieAnimation a) = 
    "LottieAnimation(" <> show a.source <> 
    ", " <> show a.trigger <> ")"

-- | Create Lottie animation with full configuration
lottieAnimation
  :: { source :: LottieSource
     , playback :: LottiePlayback
     , segment :: LottieSegment
     , trigger :: LottieTrigger
     , renderer :: LottieRenderer
     , preserveAspectRatio :: String
     , className :: String
     , ariaLabel :: String
     }
  -> LottieAnimation
lottieAnimation cfg = LottieAnimation
  { source: cfg.source
  , playback: cfg.playback
  , segment: cfg.segment
  , trigger: cfg.trigger
  , renderer: cfg.renderer
  , preserveAspectRatio: cfg.preserveAspectRatio
  , className: cfg.className
  , ariaLabel: cfg.ariaLabel
  }

-- | Default Lottie animation configuration
-- |
-- | Requires a source to be provided. Uses sensible defaults for everything else.
defaultLottie :: LottieSource -> LottieAnimation
defaultLottie src = LottieAnimation
  { source: src
  , playback: defaultPlayback
  , segment: fullAnimation
  , trigger: TriggerOnLoad
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Animation"
  }

-- | Create Lottie from URL with trigger
fromUrl :: String -> LottieTrigger -> LottieAnimation
fromUrl url trigger = LottieAnimation
  { source: LottieUrl url
  , playback: defaultPlayback
  , segment: fullAnimation
  , trigger: trigger
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Animation"
  }

-- | Create Lottie from inline JSON
fromInline :: String -> LottieAnimation
fromInline json = LottieAnimation
  { source: LottieInline json
  , playback: defaultPlayback
  , segment: fullAnimation
  , trigger: TriggerOnLoad
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Animation"
  }

-- | Loading spinner preset
loadingSpinner :: String -> LottieAnimation
loadingSpinner url = LottieAnimation
  { source: LottieUrl url
  , playback: autoplayLoop
  , segment: fullAnimation
  , trigger: TriggerOnLoad
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: "loading-spinner"
  , ariaLabel: "Loading"
  }

-- | Hover animation preset
hoverAnimation :: String -> LottieAnimation
hoverAnimation url = LottieAnimation
  { source: LottieUrl url
  , playback: manualPlayback
  , segment: fullAnimation
  , trigger: TriggerOnHover
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Interactive animation"
  }

-- | Click animation preset (plays once on click)
clickAnimation :: String -> LottieAnimation
clickAnimation url = LottieAnimation
  { source: LottieUrl url
  , playback: playOnce
  , segment: fullAnimation
  , trigger: TriggerOnClick
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Animation"
  }

-- | Scroll-triggered animation (plays when enters viewport)
scrollAnimation :: String -> LottieAnimation
scrollAnimation url = LottieAnimation
  { source: LottieUrl url
  , playback: playOnce
  , segment: fullAnimation
  , trigger: TriggerOnEnter
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: ""
  , ariaLabel: "Animation"
  }

-- | Success feedback animation
successAnimation :: String -> LottieAnimation
successAnimation url = LottieAnimation
  { source: LottieUrl url
  , playback: playOnce
  , segment: fullAnimation
  , trigger: TriggerManual
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: "success-animation"
  , ariaLabel: "Success"
  }

-- | Error feedback animation
errorAnimation :: String -> LottieAnimation
errorAnimation url = LottieAnimation
  { source: LottieUrl url
  , playback: playOnce
  , segment: fullAnimation
  , trigger: TriggerManual
  , renderer: RendererSvg
  , preserveAspectRatio: "xMidYMid meet"
  , className: "error-animation"
  , ariaLabel: "Error"
  }
