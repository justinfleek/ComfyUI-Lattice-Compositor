-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // motion // scroll-animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scroll-triggered animations — Pure Data
-- |
-- | Scroll state and viewport intersection are modeled as **pure data**.
-- | The runtime provides scroll position updates; animation logic is computed
-- | from pure functions.
-- |
-- | ## Pure Data Model
-- |
-- | Instead of subscribing to scroll events imperatively, you define:
-- |
-- | 1. **ScrollState** — Pure data representing scroll position and direction
-- | 2. **ViewportState** — Pure data representing element visibility
-- | 3. **ScrollAnimationConfig** — Pure data describing animation triggers
-- |
-- | The runtime observes scroll events and updates state. Your view function
-- | receives current state and returns elements with computed properties.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.ScrollAnimation as SA
-- |
-- | -- Define scroll animation as pure data
-- | scrollFadeIn :: SA.ScrollAnimationConfig
-- | scrollFadeIn =
-- |   { preset: SA.FadeInUp
-- |   , threshold: 0.2        -- 20% visible
-- |   , once: true            -- Only animate once
-- |   , delay: Milliseconds 0.0
-- |   }
-- |
-- | -- Compute animation state from viewport intersection
-- | animationState :: SA.ViewportState -> SA.AnimationClasses
-- | animationState vs =
-- |   if vs.isIntersecting && vs.ratio >= 0.2
-- |     then SA.presetToClasses SA.FadeInUp
-- |     else SA.initialClasses SA.FadeInUp
-- |
-- | -- Progress-based parallax (pure computation)
-- | parallaxOffset :: SA.ScrollState -> Number
-- | parallaxOffset ss = ss.progress * 50.0  -- 50px parallax
-- | ```
module Hydrogen.Motion.ScrollAnimation
  ( -- * Animation Presets (Pure Data)
    AnimationPreset(..)
  , AnimationClasses
  , presetToClasses
  , initialClasses
    -- * Scroll State (Pure Data)
  , ScrollState
  , defaultScrollState
  , ScrollDirection(..)
  , scrollDirection
  , scrollProgress
  , scrollVelocity
    -- * Viewport State (Pure Data)
  , ViewportState
  , defaultViewportState
  , isInViewport
  , viewportRatio
    -- * Scroll Animation Config (Pure Data)
  , ScrollAnimationConfig
  , defaultScrollAnimationConfig
  , ViewportConfig
  , defaultViewportConfig
  , ProgressConfig
  , defaultProgressConfig
    -- * Animation Computation (Pure Functions)
  , computeAnimationState
  , computeProgress
  , computeParallaxOffset
  , computeOpacityFromProgress
  , computeTransformFromProgress
    -- * Scroll Behavior (Pure Data)
  , ScrollBehavior(..)
  , ScrollBlock(..)
  , ScrollInline(..)
  , ScrollTarget
  , scrollToTop
  , scrollToPosition
  , scrollToElement
    -- * Direction Detection (Pure Functions)
  , detectDirection
  , directionChanged
  ) where

import Prelude

import Data.Time.Duration (Milliseconds(Milliseconds))
import Data.Number (abs) as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // animation presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined animation presets — pure enum
data AnimationPreset
  = FadeIn           -- ^ Fade in from transparent
  | FadeInUp         -- ^ Fade in while sliding up
  | FadeInDown       -- ^ Fade in while sliding down
  | FadeInLeft       -- ^ Fade in while sliding from left
  | FadeInRight      -- ^ Fade in while sliding from right
  | SlideUp          -- ^ Slide up into view
  | SlideDown        -- ^ Slide down into view
  | SlideLeft        -- ^ Slide in from right
  | SlideRight       -- ^ Slide in from left
  | ScaleIn          -- ^ Scale up from small
  | ScaleInUp        -- ^ Scale and slide up
  | ZoomIn           -- ^ Zoom in effect
  | FlipIn           -- ^ 3D flip effect
  | RotateIn         -- ^ Rotate into view
  | Bounce           -- ^ Bounce effect
  | Custom String    -- ^ Custom CSS class

derive instance eqAnimationPreset :: Eq AnimationPreset

instance showAnimationPreset :: Show AnimationPreset where
  show FadeIn = "FadeIn"
  show FadeInUp = "FadeInUp"
  show FadeInDown = "FadeInDown"
  show FadeInLeft = "FadeInLeft"
  show FadeInRight = "FadeInRight"
  show SlideUp = "SlideUp"
  show SlideDown = "SlideDown"
  show SlideLeft = "SlideLeft"
  show SlideRight = "SlideRight"
  show ScaleIn = "ScaleIn"
  show ScaleInUp = "ScaleInUp"
  show ZoomIn = "ZoomIn"
  show FlipIn = "FlipIn"
  show RotateIn = "RotateIn"
  show Bounce = "Bounce"
  show (Custom c) = "Custom " <> c

-- | Animation CSS classes — pure data
type AnimationClasses =
  { initial :: String
  , animate :: String
  }

-- | Convert preset to animation classes
presetToClasses :: AnimationPreset -> AnimationClasses
presetToClasses = case _ of
  FadeIn ->
    { initial: "opacity-0"
    , animate: "opacity-100 transition-opacity duration-500"
    }
  FadeInUp ->
    { initial: "opacity-0 translate-y-8"
    , animate: "opacity-100 translate-y-0 transition-all duration-500"
    }
  FadeInDown ->
    { initial: "opacity-0 -translate-y-8"
    , animate: "opacity-100 translate-y-0 transition-all duration-500"
    }
  FadeInLeft ->
    { initial: "opacity-0 -translate-x-8"
    , animate: "opacity-100 translate-x-0 transition-all duration-500"
    }
  FadeInRight ->
    { initial: "opacity-0 translate-x-8"
    , animate: "opacity-100 translate-x-0 transition-all duration-500"
    }
  SlideUp ->
    { initial: "translate-y-full"
    , animate: "translate-y-0 transition-transform duration-500"
    }
  SlideDown ->
    { initial: "-translate-y-full"
    , animate: "translate-y-0 transition-transform duration-500"
    }
  SlideLeft ->
    { initial: "translate-x-full"
    , animate: "translate-x-0 transition-transform duration-500"
    }
  SlideRight ->
    { initial: "-translate-x-full"
    , animate: "translate-x-0 transition-transform duration-500"
    }
  ScaleIn ->
    { initial: "scale-0 opacity-0"
    , animate: "scale-100 opacity-100 transition-all duration-500"
    }
  ScaleInUp ->
    { initial: "scale-75 opacity-0 translate-y-4"
    , animate: "scale-100 opacity-100 translate-y-0 transition-all duration-500"
    }
  ZoomIn ->
    { initial: "scale-50 opacity-0"
    , animate: "scale-100 opacity-100 transition-all duration-700 ease-out"
    }
  FlipIn ->
    { initial: "opacity-0 rotateX-90"
    , animate: "opacity-100 rotateX-0 transition-all duration-500"
    }
  RotateIn ->
    { initial: "opacity-0 rotate-180 scale-50"
    , animate: "opacity-100 rotate-0 scale-100 transition-all duration-500"
    }
  Bounce ->
    { initial: "opacity-0 translate-y-8"
    , animate: "opacity-100 translate-y-0 animate-bounce transition-all duration-500"
    }
  Custom cls ->
    { initial: ""
    , animate: cls
    }

-- | Get initial classes for a preset
initialClasses :: AnimationPreset -> String
initialClasses preset = (presetToClasses preset).initial

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scroll state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll direction — pure enum
data ScrollDirection
  = ScrollingUp
  | ScrollingDown
  | NotScrolling

derive instance eqScrollDirection :: Eq ScrollDirection

instance showScrollDirection :: Show ScrollDirection where
  show ScrollingUp = "ScrollingUp"
  show ScrollingDown = "ScrollingDown"
  show NotScrolling = "NotScrolling"

-- | Scroll state — pure data representing current scroll position
-- |
-- | This is provided by the runtime and passed to your view functions.
type ScrollState =
  { scrollY :: Number            -- ^ Current vertical scroll position (pixels)
  , scrollX :: Number            -- ^ Current horizontal scroll position (pixels)
  , maxScrollY :: Number         -- ^ Maximum vertical scroll (document height - viewport height)
  , maxScrollX :: Number         -- ^ Maximum horizontal scroll
  , previousY :: Number          -- ^ Previous scroll Y (for direction detection)
  , previousX :: Number          -- ^ Previous scroll X
  , viewportHeight :: Number     -- ^ Viewport height in pixels
  , viewportWidth :: Number      -- ^ Viewport width in pixels
  , timestamp :: Number          -- ^ Timestamp of last scroll event (ms)
  }

-- | Default scroll state
defaultScrollState :: ScrollState
defaultScrollState =
  { scrollY: 0.0
  , scrollX: 0.0
  , maxScrollY: 0.0
  , maxScrollX: 0.0
  , previousY: 0.0
  , previousX: 0.0
  , viewportHeight: 0.0
  , viewportWidth: 0.0
  , timestamp: 0.0
  }

-- | Compute scroll direction from state — pure function
scrollDirection :: ScrollState -> ScrollDirection
scrollDirection state
  | state.scrollY > state.previousY = ScrollingDown
  | state.scrollY < state.previousY = ScrollingUp
  | otherwise = NotScrolling

-- | Compute overall scroll progress (0.0 to 1.0) — pure function
scrollProgress :: ScrollState -> Number
scrollProgress state
  | state.maxScrollY <= 0.0 = 0.0
  | otherwise = clampNumber 0.0 1.0 (state.scrollY / state.maxScrollY)

-- | Compute scroll velocity (pixels per ms) — pure function
scrollVelocity :: ScrollState -> Number -> Number
scrollVelocity state deltaTime
  | deltaTime <= 0.0 = 0.0
  | otherwise = Math.abs (state.scrollY - state.previousY) / deltaTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport state for an element — pure data
-- |
-- | Describes how an element intersects with the viewport.
type ViewportState =
  { isIntersecting :: Boolean    -- ^ Element is at least partially visible
  , ratio :: Number              -- ^ Intersection ratio (0.0 to 1.0)
  , boundingTop :: Number        -- ^ Top edge relative to viewport
  , boundingBottom :: Number     -- ^ Bottom edge relative to viewport
  , boundingLeft :: Number       -- ^ Left edge relative to viewport
  , boundingRight :: Number      -- ^ Right edge relative to viewport
  , isFullyVisible :: Boolean    -- ^ Element is completely visible
  , hasTriggered :: Boolean      -- ^ Animation has already triggered (for once mode)
  }

-- | Default viewport state
defaultViewportState :: ViewportState
defaultViewportState =
  { isIntersecting: false
  , ratio: 0.0
  , boundingTop: 0.0
  , boundingBottom: 0.0
  , boundingLeft: 0.0
  , boundingRight: 0.0
  , isFullyVisible: false
  , hasTriggered: false
  }

-- | Check if element is in viewport — pure function
isInViewport :: ViewportState -> Boolean
isInViewport = _.isIntersecting

-- | Get viewport intersection ratio — pure function
viewportRatio :: ViewportState -> Number
viewportRatio = _.ratio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // animation configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll animation configuration — pure data
type ScrollAnimationConfig =
  { preset :: AnimationPreset
  , threshold :: Number          -- ^ Visibility threshold (0.0 to 1.0)
  , once :: Boolean              -- ^ Only animate once
  , delay :: Milliseconds        -- ^ Delay before animation
  }

-- | Default scroll animation config
defaultScrollAnimationConfig :: ScrollAnimationConfig
defaultScrollAnimationConfig =
  { preset: FadeInUp
  , threshold: 0.1
  , once: true
  , delay: Milliseconds 0.0
  }

-- | Viewport trigger configuration — pure data
type ViewportConfig =
  { animation :: AnimationPreset
  , threshold :: Number
  , rootMargin :: String
  , once :: Boolean
  , delay :: Milliseconds
  }

-- | Default viewport configuration
defaultViewportConfig :: ViewportConfig
defaultViewportConfig =
  { animation: FadeInUp
  , threshold: 0.1
  , rootMargin: "0px"
  , once: true
  , delay: Milliseconds 0.0
  }

-- | Progress-based animation configuration — pure data
type ProgressConfig =
  { start :: Number              -- ^ Progress start (0.0 to 1.0)
  , end :: Number                -- ^ Progress end (0.0 to 1.0)
  , clampOutput :: Boolean       -- ^ Clamp output to 0-1 range
  }

-- | Default progress configuration
defaultProgressConfig :: ProgressConfig
defaultProgressConfig =
  { start: 0.0
  , end: 1.0
  , clampOutput: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animation computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute animation state from viewport state — pure function
-- |
-- | Returns the CSS classes to apply based on visibility.
computeAnimationState 
  :: ScrollAnimationConfig 
  -> ViewportState 
  -> AnimationClasses
computeAnimationState config vs =
  let
    shouldAnimate = vs.isIntersecting 
                 && vs.ratio >= config.threshold
                 && (not config.once || not vs.hasTriggered)
    classes = presetToClasses config.preset
  in
    if shouldAnimate
      then classes
      else { initial: classes.initial, animate: classes.initial }

-- | Compute progress value from scroll state — pure function
-- |
-- | Maps scroll progress to output range based on config.
computeProgress :: ProgressConfig -> ScrollState -> Number
computeProgress config state =
  let
    rawProgress = scrollProgress state
    -- Map from [start, end] to [0, 1]
    normalizedProgress = (rawProgress - config.start) / (config.end - config.start)
    output = if config.clampOutput
               then clampNumber 0.0 1.0 normalizedProgress
               else normalizedProgress
  in
    output

-- | Compute parallax offset from progress — pure function
computeParallaxOffset :: Number -> Number -> Number
computeParallaxOffset progress maxOffset = progress * maxOffset

-- | Compute opacity from progress — pure function
computeOpacityFromProgress :: Number -> Number
computeOpacityFromProgress = clampNumber 0.0 1.0

-- | Compute transform string from progress — pure function
computeTransformFromProgress 
  :: { translateY :: Number, scale :: Number } 
  -> Number 
  -> String
computeTransformFromProgress config progress =
  "translateY(" <> show (config.translateY * (1.0 - progress)) <> "px) " <>
  "scale(" <> show (1.0 - (1.0 - config.scale) * (1.0 - progress)) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // direction helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detect direction from two scroll positions — pure function
detectDirection :: Number -> Number -> ScrollDirection
detectDirection previousY currentY
  | currentY > previousY = ScrollingDown
  | currentY < previousY = ScrollingUp
  | otherwise = NotScrolling

-- | Check if direction changed — pure function
directionChanged :: ScrollDirection -> ScrollDirection -> Boolean
directionChanged prev curr = prev /= curr && curr /= NotScrolling

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // scroll targets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll behavior — pure enum
data ScrollBehavior
  = Smooth
  | Instant
  | Auto

derive instance eqScrollBehavior :: Eq ScrollBehavior

instance showScrollBehavior :: Show ScrollBehavior where
  show Smooth = "smooth"
  show Instant = "instant"
  show Auto = "auto"

-- | Vertical alignment — pure enum
data ScrollBlock
  = BlockStart
  | BlockCenter
  | BlockEnd
  | BlockNearest

derive instance eqScrollBlock :: Eq ScrollBlock

instance showScrollBlock :: Show ScrollBlock where
  show BlockStart = "start"
  show BlockCenter = "center"
  show BlockEnd = "end"
  show BlockNearest = "nearest"

-- | Horizontal alignment — pure enum
data ScrollInline
  = InlineStart
  | InlineCenter
  | InlineEnd
  | InlineNearest

derive instance eqScrollInline :: Eq ScrollInline

instance showScrollInline :: Show ScrollInline where
  show InlineStart = "start"
  show InlineCenter = "center"
  show InlineEnd = "end"
  show InlineNearest = "nearest"

-- | Scroll target — pure data describing where to scroll
-- |
-- | The runtime interprets this and performs the scroll action.
type ScrollTarget =
  { x :: Number
  , y :: Number
  , behavior :: ScrollBehavior
  , block :: ScrollBlock
  , inline :: ScrollInline
  }

-- | Create scroll target for top of page
scrollToTop :: ScrollBehavior -> ScrollTarget
scrollToTop behavior =
  { x: 0.0
  , y: 0.0
  , behavior: behavior
  , block: BlockStart
  , inline: InlineStart
  }

-- | Create scroll target for specific position
scrollToPosition :: Number -> Number -> ScrollBehavior -> ScrollTarget
scrollToPosition x y behavior =
  { x: x
  , y: y
  , behavior: behavior
  , block: BlockStart
  , inline: InlineStart
  }

-- | Create scroll target for element (by ID)
-- |
-- | The runtime resolves the element ID to a position.
scrollToElement :: String -> ScrollBehavior -> ScrollBlock -> ScrollTarget
scrollToElement _elementId behavior block =
  { x: 0.0
  , y: 0.0
  , behavior: behavior
  , block: block
  , inline: InlineNearest
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range — pure function
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val
