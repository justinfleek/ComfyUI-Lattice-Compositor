-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // carousel // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel State — The complete runtime state of a carousel.
-- |
-- | ## Design Philosophy
-- |
-- | State is pure data describing the carousel at a point in time.
-- | State transitions are pure functions: State -> Msg -> State.
-- | The runtime renders state to DOM; no mutation here.
-- |
-- | ## State Components
-- |
-- | - Current slide index
-- | - Transition progress (0.0-1.0 during transitions)
-- | - Gesture state (swipe, drag, pinch, etc.)
-- | - Autoplay state (playing/paused, timer)
-- | - Focus state (keyboard, mouse, retinal)
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (SlideIndex, AutoplayMode, etc.)
-- | - Carousel.Gestures (GestureState)
-- | - Carousel.Transitions (TransitionConfig)

module Hydrogen.Element.Compound.Carousel.State
  ( -- * Transition State
    TransitionState
  , transitionState
  , noTransition
  , isTransitioning
  , transitionProgress
  
  -- * Autoplay State
  , AutoplayState
  , autoplayState
  , autoplaying
  , paused
  , isAutoplaying
  
  -- * Carousel State
  , CarouselState
  , initialState
  , currentIndex
  , totalSlides
  , isFirstSlide
  , isLastSlide
  
  -- * Autoplay Mode Queries
  , isContentAwareAutoplay
  , isAdaptiveAutoplay
  , isVisibilityBasedAutoplay
  , isFocusBasedAutoplay
  , isRetinalFocusAutoplay
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( max
  , min
  , (-)
  , (==)
  )

import Hydrogen.Element.Compound.Carousel.Types 
  ( SlideIndex
  , unwrapSlideIndex
  , firstSlide
  , AutoplayMode
      ( AutoplayOff
      , AutoplayTimed
      , AutoplayContentAware
      , AutoplayAdaptive
      , AutoplayOnVisible
      , AutoplayOnFocus
      , AutoplayOnRetinalFocus
      )
  )
import Hydrogen.Element.Compound.Carousel.Gestures (GestureState, initialGestureState)
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transition state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of an ongoing transition between slides
-- |
-- | Progress goes from 0.0 (at source) to 1.0 (at destination).
type TransitionState =
  { active :: Boolean
  , fromIndex :: SlideIndex
  , toIndex :: SlideIndex
  , progress :: Number    -- 0.0 to 1.0
  }

-- | Create a transition state
transitionState :: SlideIndex -> SlideIndex -> Number -> TransitionState
transitionState fromIdx toIdx prog =
  { active: true
  , fromIndex: fromIdx
  , toIndex: toIdx
  , progress: clampProgress prog
  }

-- | No active transition
noTransition :: TransitionState
noTransition =
  { active: false
  , fromIndex: firstSlide
  , toIndex: firstSlide
  , progress: 0.0
  }

-- | Check if transition is in progress
isTransitioning :: TransitionState -> Boolean
isTransitioning t = t.active

-- | Get transition progress (0.0 to 1.0)
transitionProgress :: TransitionState -> Number
transitionProgress t = t.progress

-- | Clamp progress to [0.0, 1.0]
clampProgress :: Number -> Number
clampProgress n = max 0.0 (min 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // autoplay state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Autoplay timer state
-- |
-- | Tracks whether autoplay is active and time until next slide.
type AutoplayState =
  { playing :: Boolean
  , mode :: AutoplayMode
  , interval :: Temporal.Milliseconds
  , remaining :: Temporal.Milliseconds
  }

-- | Create autoplay state
autoplayState :: AutoplayMode -> Temporal.Milliseconds -> AutoplayState
autoplayState mode interval =
  { playing: true
  , mode: mode
  , interval: interval
  , remaining: interval
  }

-- | Autoplay active state
autoplaying :: Temporal.Milliseconds -> AutoplayState
autoplaying interval = autoplayState AutoplayTimed interval

-- | Autoplay paused state
paused :: AutoplayState
paused =
  { playing: false
  , mode: AutoplayOff
  , interval: Temporal.milliseconds 0.0
  , remaining: Temporal.milliseconds 0.0
  }

-- | Check if autoplay is active
isAutoplaying :: AutoplayState -> Boolean
isAutoplaying s = s.playing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // carousel state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete carousel runtime state
-- |
-- | This compound aggregates all state needed to render the carousel.
type CarouselState =
  { current :: SlideIndex
  , total :: Int
  , transition :: TransitionState
  , gesture :: GestureState
  , autoplay :: AutoplayState
  , loop :: Boolean            -- Whether to loop at boundaries
  }

-- | Create initial carousel state
initialState :: Int -> CarouselState
initialState slideCount =
  { current: firstSlide
  , total: max 1 slideCount
  , transition: noTransition
  , gesture: initialGestureState
  , autoplay: paused
  , loop: true
  }

-- | Get current slide index
currentIndex :: CarouselState -> SlideIndex
currentIndex s = s.current

-- | Get total number of slides
totalSlides :: CarouselState -> Int
totalSlides s = s.total

-- | Check if on first slide
isFirstSlide :: CarouselState -> Boolean
isFirstSlide s = unwrapSlideIndex s.current == 0

-- | Check if on last slide
isLastSlide :: CarouselState -> Boolean
isLastSlide s = unwrapSlideIndex s.current == s.total - 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // autoplay mode queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if autoplay is content-aware mode
-- | Content-aware autoplay adjusts timing based on content type (video vs image)
isContentAwareAutoplay :: AutoplayState -> Boolean
isContentAwareAutoplay s = case s.mode of
  AutoplayContentAware -> true
  _ -> false

-- | Check if autoplay is adaptive mode
-- | Adaptive autoplay learns from user behavior
isAdaptiveAutoplay :: AutoplayState -> Boolean
isAdaptiveAutoplay s = case s.mode of
  AutoplayAdaptive -> true
  _ -> false

-- | Check if autoplay is visibility-based
-- | Visibility-based autoplay only plays when carousel is visible
isVisibilityBasedAutoplay :: AutoplayState -> Boolean
isVisibilityBasedAutoplay s = case s.mode of
  AutoplayOnVisible -> true
  _ -> false

-- | Check if autoplay is focus-based
-- | Focus-based autoplay only plays when carousel has focus
isFocusBasedAutoplay :: AutoplayState -> Boolean
isFocusBasedAutoplay s = case s.mode of
  AutoplayOnFocus -> true
  _ -> false

-- | Check if autoplay is retinal-focus based
-- | Retinal-focus autoplay uses gaze detection for optimal timing
isRetinalFocusAutoplay :: AutoplayState -> Boolean
isRetinalFocusAutoplay s = case s.mode of
  AutoplayOnRetinalFocus -> true
  _ -> false
