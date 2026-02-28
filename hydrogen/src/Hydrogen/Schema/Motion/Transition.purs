-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // transition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transition - atoms for animated state changes.
-- |
-- | Defines how elements animate between states:
-- |
-- | ## Transition Type
-- | - Slide: Transform-based movement
-- | - Fade: Opacity change
-- | - Scale: Size change
-- | - None: Instant, no animation
-- |
-- | ## Transition Direction
-- | - For enter/exit animations
-- | - Which direction to slide from/to
-- |
-- | ## Transition Config
-- | - Combines type, duration, easing, delay
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)
-- | - Hydrogen.Schema.Motion.Easing (Easing)
-- | - Hydrogen.Schema.Geometry.Position (Edge, Axis)
-- |
-- | ## Dependents
-- | - Component.Carousel (slide transitions)
-- | - Component.Modal (enter/exit)
-- | - Component.Drawer (slide in/out)
-- | - Component.Toast (notification animations)
-- | - Component.Accordion (expand/collapse)

module Hydrogen.Schema.Motion.Transition
  ( -- * Transition Type
    TransitionType(Slide, Fade, Scale, Flip, None)
  , isAnimated
  , isInstant
  
  -- * Slide Direction
  , SlideDirection(SlideFromLeft, SlideFromRight, SlideFromTop, SlideFromBottom)
  , slideDirectionFromEdge
  , slideDirectionToEdge
  , reverseSlideDirection
  
  -- * Scale Origin
  , ScaleOrigin(ScaleFromCenter, ScaleFromEdge)
  
  -- * Flip Axis
  , FlipAxis(FlipHorizontal, FlipVertical)
  
  -- * Transition Config (Molecule)
  , TransitionConfig
  , transitionConfig
  , noTransition
  , slideTransition
  , fadeTransition
  , scaleTransition
  , transitionType
  , transitionDuration
  , transitionEasing
  , transitionDelay
  
  -- * Enter/Exit Transitions
  , EnterExitConfig
  , enterExitConfig
  , symmetricTransition
  , enterConfig
  , exitConfig
  
  -- * Common Presets
  , instantTransition
  , quickFade
  , smoothSlide
  , bouncyScale
  , gentleFade
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Dimension.Temporal 
  ( Milliseconds
  , ms
  )
import Hydrogen.Schema.Motion.Easing 
  ( Easing
  , linear
  , easeOut
  , easeInOut
  , easeOutBack
  )
import Hydrogen.Schema.Geometry.Position (Edge(Top, Bottom, Left, Right))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transition type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of visual transition between states
-- |
-- | Determines which CSS properties are animated:
-- | - Slide: transform (translateX/Y)
-- | - Fade: opacity
-- | - Scale: transform (scale)
-- | - Flip: transform (rotateX/Y)
-- | - None: no animation (instant change)
data TransitionType
  = Slide SlideDirection  -- ^ Sliding movement
  | Fade                  -- ^ Opacity transition
  | Scale ScaleOrigin     -- ^ Size change
  | Flip FlipAxis         -- ^ 3D flip
  | None                  -- ^ Instant, no animation

derive instance eqTransitionType :: Eq TransitionType

instance showTransitionType :: Show TransitionType where
  show (Slide dir) = "slide-" <> show dir
  show Fade = "fade"
  show (Scale origin) = "scale-" <> show origin
  show (Flip axis) = "flip-" <> show axis
  show None = "none"

-- | Is this an animated transition?
isAnimated :: TransitionType -> Boolean
isAnimated None = false
isAnimated _ = true

-- | Is this an instant (non-animated) transition?
isInstant :: TransitionType -> Boolean
isInstant None = true
isInstant _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // slide direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction for slide transitions
-- |
-- | Specifies which edge the element slides from (for enter)
-- | or slides to (for exit).
data SlideDirection
  = SlideFromLeft
  | SlideFromRight
  | SlideFromTop
  | SlideFromBottom

derive instance eqSlideDirection :: Eq SlideDirection
derive instance ordSlideDirection :: Ord SlideDirection

instance showSlideDirection :: Show SlideDirection where
  show SlideFromLeft = "left"
  show SlideFromRight = "right"
  show SlideFromTop = "top"
  show SlideFromBottom = "bottom"

-- | Convert edge to slide direction (entering from that edge)
slideDirectionFromEdge :: Edge -> SlideDirection
slideDirectionFromEdge Left = SlideFromLeft
slideDirectionFromEdge Right = SlideFromRight
slideDirectionFromEdge Top = SlideFromTop
slideDirectionFromEdge Bottom = SlideFromBottom

-- | Convert slide direction to corresponding edge
slideDirectionToEdge :: SlideDirection -> Edge
slideDirectionToEdge SlideFromLeft = Left
slideDirectionToEdge SlideFromRight = Right
slideDirectionToEdge SlideFromTop = Top
slideDirectionToEdge SlideFromBottom = Bottom

-- | Get opposite slide direction
reverseSlideDirection :: SlideDirection -> SlideDirection
reverseSlideDirection SlideFromLeft = SlideFromRight
reverseSlideDirection SlideFromRight = SlideFromLeft
reverseSlideDirection SlideFromTop = SlideFromBottom
reverseSlideDirection SlideFromBottom = SlideFromTop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scale origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin point for scale transitions
data ScaleOrigin
  = ScaleFromCenter  -- ^ Scale from center (default)
  | ScaleFromEdge Edge -- ^ Scale from specific edge

derive instance eqScaleOrigin :: Eq ScaleOrigin

instance showScaleOrigin :: Show ScaleOrigin where
  show ScaleFromCenter = "center"
  show (ScaleFromEdge e) = show e

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // flip axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis for 3D flip transitions
data FlipAxis
  = FlipHorizontal  -- ^ Flip around vertical axis (like turning a page)
  | FlipVertical    -- ^ Flip around horizontal axis (like flipping a card up)

derive instance eqFlipAxis :: Eq FlipAxis
derive instance ordFlipAxis :: Ord FlipAxis

instance showFlipAxis :: Show FlipAxis where
  show FlipHorizontal = "horizontal"
  show FlipVertical = "vertical"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transition config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete transition configuration
-- |
-- | Combines all parameters needed to define a transition:
-- | - Type: what kind of animation
-- | - Duration: how long
-- | - Easing: acceleration curve
-- | - Delay: wait before starting
type TransitionConfig =
  { transitionType :: TransitionType
  , duration :: Milliseconds
  , easing :: Easing
  , delay :: Milliseconds
  }

-- | Create a transition config
transitionConfig :: TransitionType -> Milliseconds -> Easing -> Milliseconds -> TransitionConfig
transitionConfig typ dur ease del =
  { transitionType: typ
  , duration: dur
  , easing: ease
  , delay: del
  }

-- | No transition (instant)
noTransition :: TransitionConfig
noTransition = transitionConfig None (ms 0.0) linear (ms 0.0)

-- | Create slide transition with direction
slideTransition :: SlideDirection -> Milliseconds -> Easing -> TransitionConfig
slideTransition dir dur ease = transitionConfig (Slide dir) dur ease (ms 0.0)

-- | Create fade transition
fadeTransition :: Milliseconds -> Easing -> TransitionConfig
fadeTransition dur ease = transitionConfig Fade dur ease (ms 0.0)

-- | Create scale transition
scaleTransition :: ScaleOrigin -> Milliseconds -> Easing -> TransitionConfig
scaleTransition origin dur ease = transitionConfig (Scale origin) dur ease (ms 0.0)

-- | Get transition type
transitionType :: TransitionConfig -> TransitionType
transitionType tc = tc.transitionType

-- | Get transition duration
transitionDuration :: TransitionConfig -> Milliseconds
transitionDuration tc = tc.duration

-- | Get transition easing
transitionEasing :: TransitionConfig -> Easing
transitionEasing tc = tc.easing

-- | Get transition delay
transitionDelay :: TransitionConfig -> Milliseconds
transitionDelay tc = tc.delay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // enter/exit transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paired enter and exit transitions
-- |
-- | For components that need different animations for appearing vs disappearing.
type EnterExitConfig =
  { enter :: TransitionConfig
  , exit :: TransitionConfig
  }

-- | Create enter/exit config with different transitions
enterExitConfig :: TransitionConfig -> TransitionConfig -> EnterExitConfig
enterExitConfig ent ext = { enter: ent, exit: ext }

-- | Create symmetric enter/exit (same transition for both)
symmetricTransition :: TransitionConfig -> EnterExitConfig
symmetricTransition tc = { enter: tc, exit: tc }

-- | Get enter transition
enterConfig :: EnterExitConfig -> TransitionConfig
enterConfig eec = eec.enter

-- | Get exit transition
exitConfig :: EnterExitConfig -> TransitionConfig
exitConfig eec = eec.exit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Instant transition (no animation)
instantTransition :: TransitionConfig
instantTransition = noTransition

-- | Quick fade (150ms)
quickFade :: TransitionConfig
quickFade = fadeTransition (ms 150.0) easeOut

-- | Smooth slide from right (300ms)
smoothSlide :: TransitionConfig
smoothSlide = slideTransition SlideFromRight (ms 300.0) easeInOut

-- | Bouncy scale from center (400ms with overshoot)
bouncyScale :: TransitionConfig
bouncyScale = scaleTransition ScaleFromCenter (ms 400.0) easeOutBack

-- | Gentle fade (250ms)
gentleFade :: TransitionConfig
gentleFade = fadeTransition (ms 250.0) easeInOut


