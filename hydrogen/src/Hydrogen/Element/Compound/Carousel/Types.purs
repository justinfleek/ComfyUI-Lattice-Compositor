-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // carousel // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Types — Core type definitions for the carousel compound.
-- |
-- | ## Architecture
-- |
-- | This module defines the atomic and molecular types that compose into
-- | carousel state and configuration. No rendering logic — pure types.
-- |
-- | ## Type Hierarchy
-- |
-- | **Atoms** (bounded primitives):
-- | - SlideIndex, TransitionKind, LayoutPath, ContentKind
-- |
-- | **Molecules** (composed atoms):
-- | - SlideConfig, TransitionConfig, LayoutConfig
-- |
-- | **Compounds** (full configurations):
-- | - CarouselConfig (assembled from molecules)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Schema atoms (referenced, not imported here)

module Hydrogen.Element.Compound.Carousel.Types
  ( -- * Slide Index
    SlideIndex
  , slideIndex
  , unwrapSlideIndex
  , firstSlide
  , nextIndex
  , prevIndex
  
  -- * Transition Kinds
  , TransitionKind
      ( TransitionNone
      , TransitionSlide
      , TransitionSlideVertical
      , TransitionFade
      , TransitionZoom
      , TransitionFlip
      , TransitionFlipVertical
      , TransitionCube
      , TransitionCoverflow
      , TransitionCards
      , TransitionWheel
      , TransitionSpiral
      , TransitionParallax
      , TransitionMorph
      , TransitionDissolve
      , TransitionBlur
      , TransitionWipe
      , TransitionReveal
      )
  
  -- * Layout Paths
  , LayoutPath
      ( PathLinear
      , PathLinearVertical
      , PathGrid
      , PathMasonry
      , PathStack
      , PathCircular
      , PathArc
      , PathHelix
      , PathSphere
      , PathCylinder
      , PathMobius
      , PathCustom
      )
  
  -- * Content Kinds
  , ContentKind
      ( ContentImage
      , ContentVideo
      , ContentAudio
      , ContentEmbed
      , ContentText
      , ContentCard
      , ContentHTML
      , ContentCanvas
      , ContentWebGL
      , ContentGame
      , ContentLiveData
      , ContentInteractive
      )
  
  -- * Slide Position
  , SlidePosition
      ( PositionActive
      , PositionPrev
      , PositionNext
      , PositionNearby
      , PositionOffscreen
      )
  
  -- * Navigation Mode
  , NavigationMode
      ( NavArrows
      , NavDots
      , NavThumbnails
      , NavProgress
      , NavKeyboard
      , NavSwipe
      , NavDrag
      , NavScroll
      , NavPinch
      , NavVoice
      , NavRetinal
      , NavBrainwave
      )
  
  -- * Autoplay Mode
  , AutoplayMode
      ( AutoplayOff
      , AutoplayTimed
      , AutoplayContentAware
      , AutoplayAdaptive
      , AutoplayOnVisible
      , AutoplayOnFocus
      , AutoplayOnRetinalFocus
      )
  
  -- * Focus Mode (for accessibility/retinal)
  , FocusMode
      ( FocusKeyboard
      , FocusMouse
      , FocusTouch
      , FocusProximity
      , FocusRetinal
      , FocusRetinalDwell
      , FocusRetinalSaccade
      , FocusAttention
      )
  
  -- * Carousel Messages
  , CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      , StartAutoplay
      , StopAutoplay
      , ToggleAutoplay
      )
  
  -- * Transition Bounds
  , firstTransition
  , lastTransition
  
  -- * Slide Index Validation
  , isValidSlide
  , slideIndexEq
  , minSlideIndex
  , slideIndexInBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , show
  , top
  , bottom
  , (+)
  , (-)
  , (>=)
  , (<=)
  , (==)
  , (<>)
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // slide index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded slide index (0 to maxSlides-1)
-- |
-- | Always valid — construction clamps to bounds.
-- | Navigation functions handle wrapping based on carousel config.
newtype SlideIndex = SlideIndex Int

derive instance eqSlideIndex :: Eq SlideIndex
derive instance ordSlideIndex :: Ord SlideIndex

instance showSlideIndex :: Show SlideIndex where
  show (SlideIndex i) = "Slide[" <> show i <> "]"

-- | Create slide index, clamped to non-negative
slideIndex :: Int -> SlideIndex
slideIndex i = SlideIndex (max 0 i)

-- | Extract index value
unwrapSlideIndex :: SlideIndex -> Int
unwrapSlideIndex (SlideIndex i) = i

-- | First slide (index 0)
firstSlide :: SlideIndex
firstSlide = SlideIndex 0

-- | Next index (caller must handle bounds/wrapping)
nextIndex :: SlideIndex -> SlideIndex
nextIndex (SlideIndex i) = SlideIndex (i + 1)

-- | Previous index (floors at 0)
prevIndex :: SlideIndex -> SlideIndex
prevIndex (SlideIndex i) = SlideIndex (max 0 (i - 1))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transition kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition animation type between slides
-- |
-- | Each transition can be configured with duration and easing separately.
-- | 3D transitions require perspective to be set on container.
data TransitionKind
  = TransitionNone        -- ^ Instant switch, no animation
  | TransitionSlide       -- ^ Horizontal slide (default)
  | TransitionSlideVertical -- ^ Vertical slide
  | TransitionFade        -- ^ Crossfade opacity
  | TransitionZoom        -- ^ Scale in/out
  | TransitionFlip        -- ^ 3D flip on Y axis
  | TransitionFlipVertical -- ^ 3D flip on X axis
  | TransitionCube        -- ^ 3D cube rotation
  | TransitionCoverflow   -- ^ 3D coverflow (iTunes style)
  | TransitionCards       -- ^ Stacked cards effect
  | TransitionWheel       -- ^ Ferris wheel rotation
  | TransitionSpiral      -- ^ 3D spiral path
  | TransitionParallax    -- ^ Multi-layer parallax
  | TransitionMorph       -- ^ Shape morphing between slides
  | TransitionDissolve    -- ^ Pixel dissolve effect
  | TransitionBlur        -- ^ Blur transition
  | TransitionWipe        -- ^ Directional wipe
  | TransitionReveal      -- ^ Reveal underneath

derive instance eqTransitionKind :: Eq TransitionKind
derive instance ordTransitionKind :: Ord TransitionKind

instance showTransitionKind :: Show TransitionKind where
  show TransitionNone = "none"
  show TransitionSlide = "slide"
  show TransitionSlideVertical = "slide-vertical"
  show TransitionFade = "fade"
  show TransitionZoom = "zoom"
  show TransitionFlip = "flip"
  show TransitionFlipVertical = "flip-vertical"
  show TransitionCube = "cube"
  show TransitionCoverflow = "coverflow"
  show TransitionCards = "cards"
  show TransitionWheel = "wheel"
  show TransitionSpiral = "spiral"
  show TransitionParallax = "parallax"
  show TransitionMorph = "morph"
  show TransitionDissolve = "dissolve"
  show TransitionBlur = "blur"
  show TransitionWipe = "wipe"
  show TransitionReveal = "reveal"

instance boundedTransitionKind :: Bounded TransitionKind where
  top = TransitionReveal
  bottom = TransitionNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // layout path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometric path slides follow
-- |
-- | Defines the spatial arrangement of slides in 2D or 3D space.
-- | Linear is the traditional carousel; others create immersive experiences.
data LayoutPath
  = PathLinear          -- ^ Horizontal line (traditional)
  | PathLinearVertical  -- ^ Vertical line
  | PathGrid            -- ^ 2D grid arrangement
  | PathMasonry         -- ^ Pinterest-style masonry
  | PathStack           -- ^ Stacked cards (Tinder style)
  | PathCircular        -- ^ Circle in XY plane
  | PathArc             -- ^ Partial arc
  | PathHelix           -- ^ 3D helix/spiral
  | PathSphere          -- ^ Points on sphere surface
  | PathCylinder        -- ^ Wrapped around cylinder
  | PathMobius          -- ^ Möbius strip (continuous loop)
  | PathCustom          -- ^ Custom path (defined by points)

derive instance eqLayoutPath :: Eq LayoutPath
derive instance ordLayoutPath :: Ord LayoutPath

instance showLayoutPath :: Show LayoutPath where
  show PathLinear = "linear"
  show PathLinearVertical = "linear-vertical"
  show PathGrid = "grid"
  show PathMasonry = "masonry"
  show PathStack = "stack"
  show PathCircular = "circular"
  show PathArc = "arc"
  show PathHelix = "helix"
  show PathSphere = "sphere"
  show PathCylinder = "cylinder"
  show PathMobius = "mobius"
  show PathCustom = "custom"

instance boundedLayoutPath :: Bounded LayoutPath where
  top = PathCustom
  bottom = PathLinear

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // content kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of content a slide contains
-- |
-- | Content-aware rendering enables:
-- | - Appropriate loading states per type
-- | - Media controls for video/audio
-- | - Lazy loading strategies
-- | - Accessibility announcements
data ContentKind
  = ContentImage        -- ^ Static image (jpg, png, webp, svg)
  | ContentVideo        -- ^ Video content (mp4, webm)
  | ContentAudio        -- ^ Audio with visualization
  | ContentEmbed        -- ^ External embed (YouTube, Vimeo, etc.)
  | ContentText         -- ^ Rich text block
  | ContentCard         -- ^ Structured card component
  | ContentHTML         -- ^ Arbitrary HTML/Element
  | ContentCanvas       -- ^ Canvas 2D rendering
  | ContentWebGL        -- ^ WebGL 3D scene
  | ContentGame         -- ^ Interactive game/simulation
  | ContentLiveData     -- ^ Live updating data feed
  | ContentInteractive  -- ^ Full interactive component

derive instance eqContentKind :: Eq ContentKind
derive instance ordContentKind :: Ord ContentKind

instance showContentKind :: Show ContentKind where
  show ContentImage = "image"
  show ContentVideo = "video"
  show ContentAudio = "audio"
  show ContentEmbed = "embed"
  show ContentText = "text"
  show ContentCard = "card"
  show ContentHTML = "html"
  show ContentCanvas = "canvas"
  show ContentWebGL = "webgl"
  show ContentGame = "game"
  show ContentLiveData = "live-data"
  show ContentInteractive = "interactive"

instance boundedContentKind :: Bounded ContentKind where
  top = ContentInteractive
  bottom = ContentImage

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // slide position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Relative position of a slide to the active slide
-- |
-- | Used for applying position-aware effects (blur inactive, scale active, etc.)
data SlidePosition
  = PositionActive      -- ^ Currently focused/active slide
  | PositionPrev        -- ^ Immediately before active
  | PositionNext        -- ^ Immediately after active
  | PositionNearby Int  -- ^ N positions from active (signed)
  | PositionOffscreen   -- ^ Not visible, can be virtualized

derive instance eqSlidePosition :: Eq SlidePosition

instance showSlidePosition :: Show SlidePosition where
  show PositionActive = "active"
  show PositionPrev = "prev"
  show PositionNext = "next"
  show (PositionNearby n) = "nearby[" <> show n <> "]"
  show PositionOffscreen = "offscreen"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // navigation mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How users can navigate the carousel
-- |
-- | Multiple modes can be enabled simultaneously.
data NavigationMode
  = NavArrows           -- ^ Prev/Next arrow buttons
  | NavDots             -- ^ Dot indicators (click to jump)
  | NavThumbnails       -- ^ Thumbnail strip
  | NavProgress         -- ^ Progress bar (click to seek)
  | NavKeyboard         -- ^ Arrow keys, Home/End
  | NavSwipe            -- ^ Touch swipe gestures
  | NavDrag             -- ^ Mouse drag
  | NavScroll           -- ^ Scroll wheel
  | NavPinch            -- ^ Pinch to zoom/navigate
  | NavVoice            -- ^ Voice commands
  | NavRetinal          -- ^ Eye/gaze tracking
  | NavBrainwave        -- ^ BCI input (future)

derive instance eqNavigationMode :: Eq NavigationMode
derive instance ordNavigationMode :: Ord NavigationMode

instance showNavigationMode :: Show NavigationMode where
  show NavArrows = "arrows"
  show NavDots = "dots"
  show NavThumbnails = "thumbnails"
  show NavProgress = "progress"
  show NavKeyboard = "keyboard"
  show NavSwipe = "swipe"
  show NavDrag = "drag"
  show NavScroll = "scroll"
  show NavPinch = "pinch"
  show NavVoice = "voice"
  show NavRetinal = "retinal"
  show NavBrainwave = "brainwave"

instance boundedNavigationMode :: Bounded NavigationMode where
  top = NavBrainwave
  bottom = NavArrows

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // autoplay mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Autoplay behavior configuration
-- |
-- | Defines how automatic slide advancement works.
data AutoplayMode
  = AutoplayOff              -- ^ No autoplay
  | AutoplayTimed            -- ^ Fixed interval per slide
  | AutoplayContentAware     -- ^ Duration based on content (video length, reading time)
  | AutoplayAdaptive         -- ^ Learns from user engagement
  | AutoplayOnVisible        -- ^ Only when carousel is in viewport
  | AutoplayOnFocus          -- ^ Only when carousel has focus
  | AutoplayOnRetinalFocus   -- ^ Only when user is looking at carousel

derive instance eqAutoplayMode :: Eq AutoplayMode
derive instance ordAutoplayMode :: Ord AutoplayMode

instance showAutoplayMode :: Show AutoplayMode where
  show AutoplayOff = "off"
  show AutoplayTimed = "timed"
  show AutoplayContentAware = "content-aware"
  show AutoplayAdaptive = "adaptive"
  show AutoplayOnVisible = "on-visible"
  show AutoplayOnFocus = "on-focus"
  show AutoplayOnRetinalFocus = "on-retinal-focus"

instance boundedAutoplayMode :: Bounded AutoplayMode where
  top = AutoplayOnRetinalFocus
  bottom = AutoplayOff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // focus mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus detection mode for accessibility and advanced input
-- |
-- | Determines how the carousel detects user attention.
data FocusMode
  = FocusKeyboard          -- ^ Standard keyboard focus (tab navigation)
  | FocusMouse             -- ^ Mouse hover
  | FocusTouch             -- ^ Touch/tap
  | FocusProximity         -- ^ Device proximity sensors
  | FocusRetinal           -- ^ Eye tracking (WebGazer, Tobii, etc.)
  | FocusRetinalDwell      -- ^ Eye tracking with dwell time
  | FocusRetinalSaccade    -- ^ Eye tracking detecting saccades
  | FocusAttention         -- ^ Combined signals (ML model)

derive instance eqFocusMode :: Eq FocusMode
derive instance ordFocusMode :: Ord FocusMode

instance showFocusMode :: Show FocusMode where
  show FocusKeyboard = "keyboard"
  show FocusMouse = "mouse"
  show FocusTouch = "touch"
  show FocusProximity = "proximity"
  show FocusRetinal = "retinal"
  show FocusRetinalDwell = "retinal-dwell"
  show FocusRetinalSaccade = "retinal-saccade"
  show FocusAttention = "attention"

instance boundedFocusMode :: Bounded FocusMode where
  top = FocusAttention
  bottom = FocusKeyboard

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // carousel messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the carousel can produce
-- |
-- | These are the only ways to interact with carousel state.
-- | The update function in the application handles these messages.
data CarouselMsg
  = GoToSlide SlideIndex     -- ^ Navigate to specific slide
  | NextSlide                -- ^ Go to next slide
  | PrevSlide                -- ^ Go to previous slide
  | StartAutoplay            -- ^ Start autoplay
  | StopAutoplay             -- ^ Stop autoplay
  | ToggleAutoplay           -- ^ Toggle autoplay state

derive instance eqCarouselMsg :: Eq CarouselMsg

instance showCarouselMsg :: Show CarouselMsg where
  show (GoToSlide idx) = "GoToSlide(" <> show idx <> ")"
  show NextSlide = "NextSlide"
  show PrevSlide = "PrevSlide"
  show StartAutoplay = "StartAutoplay"
  show StopAutoplay = "StopAutoplay"
  show ToggleAutoplay = "ToggleAutoplay"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // utility functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the first (simplest) transition kind
-- | Useful for defaulting when no transition is desired
firstTransition :: TransitionKind
firstTransition = bottom

-- | Get the last (most complex) transition kind
-- | Useful for getting the bounds of transition options
lastTransition :: TransitionKind
lastTransition = top

-- | Check if a slide index is valid (>= 0) for navigation
-- | Returns true if the raw index is non-negative
isValidSlide :: SlideIndex -> Boolean
isValidSlide idx = unwrapSlideIndex idx >= 0

-- | Check if two slide indices point to the same slide
slideIndexEq :: SlideIndex -> SlideIndex -> Boolean
slideIndexEq a b = unwrapSlideIndex a == unwrapSlideIndex b

-- | Get the lesser of two slide indices
-- | Useful for determining which slide comes first
minSlideIndex :: SlideIndex -> SlideIndex -> SlideIndex
minSlideIndex a b = slideIndex (min (unwrapSlideIndex a) (unwrapSlideIndex b))

-- | Check if a slide index is within a maximum bound
-- | Useful for capping navigation to valid ranges
slideIndexInBounds :: SlideIndex -> Int -> Boolean
slideIndexInBounds idx maxIdx = unwrapSlideIndex idx <= maxIdx
