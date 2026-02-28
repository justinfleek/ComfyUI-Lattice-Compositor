-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // motion // presence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Enter/exit animations for components — Pure Data
-- |
-- | AnimatePresence enables animations when components mount and unmount,
-- | with support for exit animations and layout transitions.
-- |
-- | All presence state is **pure data**. No imperative mutations.
-- | Transitions happen via messages flowing through the update cycle.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Presence as P
-- |
-- | -- Define motion element as pure data
-- | myModal :: forall msg. Boolean -> P.MotionElement msg
-- | myModal isVisible =
-- |   { presence: if isVisible then P.Present else P.Exiting
-- |   , initial: P.variant { opacity: 0.0, scale: 0.9 }
-- |   , animate: P.variant { opacity: 1.0, scale: 1.0 }
-- |   , exit: P.variant { opacity: 0.0, scale: 0.9 }
-- |   , key: Just "modal"
-- |   , onStart: Nothing
-- |   , onComplete: Nothing
-- |   }
-- |
-- | -- Compute current variant based on presence state
-- | currentVariant :: P.MotionElement msg -> P.Variant
-- | currentVariant el = case el.presence of
-- |   P.Entering -> P.interpolate 0.0 el.initial el.animate
-- |   P.Present -> el.animate
-- |   P.Exiting -> el.exit
-- | ```
module Hydrogen.Motion.Presence
  ( -- * Presence State (Pure Data)
    PresenceState(..)
  , isVisible
  , isAnimating
    -- * Motion Element (Pure Data)
  , MotionElement
  , defaultMotionElement
    -- * Presence Mode
  , PresenceMode(..)
    -- * Variants (Pure Data)
  , Variant
  , variant
  , emptyVariant
  , variantWithOpacity
  , variantWithScale
  , variantWithTranslate
  , variantWithRotate
    -- * Preset Variants
  , fadeIn
  , fadeOut
  , Direction(..)
  , slideIn
  , slideOut
  , scaleIn
  , scaleOut
  , popIn
  , popOut
    -- * Variant Composition
  , combineVariants
  , withDuration
  , withDelay
  , withEasing
    -- * Variant Interpolation
  , interpolate
  , interpolateNumber
    -- * Presence Transitions (Pure Functions)
  , transitionTo
  , enter
  , present
  , exit
    -- * Serialization (for renderers)
  , variantToRecord
  , variantToLegacyCss
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (intercalate)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Time.Duration (Milliseconds(Milliseconds))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Presence state for a component — pure enum
-- |
-- | This is pure data representing where a component is in its lifecycle.
-- | State transitions are computed, not mutated.
data PresenceState
  = Entering    -- ^ Component is animating into view
  | Present     -- ^ Component is fully visible
  | Exiting     -- ^ Component is animating out of view
  | Absent      -- ^ Component is not rendered

derive instance eqPresenceState :: Eq PresenceState
derive instance ordPresenceState :: Ord PresenceState

instance showPresenceState :: Show PresenceState where
  show Entering = "Entering"
  show Present = "Present"
  show Exiting = "Exiting"
  show Absent = "Absent"

-- | Check if presence state is visible (should render)
isVisible :: PresenceState -> Boolean
isVisible Absent = false
isVisible _ = true

-- | Check if presence state is animating
isAnimating :: PresenceState -> Boolean
isAnimating Entering = true
isAnimating Exiting = true
isAnimating _ = false

-- | Animation presence mode — pure enum
data PresenceMode
  = Sync       -- ^ Enter and exit simultaneously
  | Wait       -- ^ Wait for exit before entering
  | PopLayout  -- ^ Pop exiting elements out of layout flow

derive instance eqPresenceMode :: Eq PresenceMode

instance showPresenceMode :: Show PresenceMode where
  show Sync = "Sync"
  show Wait = "Wait"
  show PopLayout = "PopLayout"

-- | Direction for slide animations — pure enum
data Direction
  = FromTop
  | FromBottom
  | FromLeft
  | FromRight
  | ToTop
  | ToBottom
  | ToLeft
  | ToRight

derive instance eqDirection :: Eq Direction

instance showDirection :: Show Direction where
  show FromTop = "FromTop"
  show FromBottom = "FromBottom"
  show FromLeft = "FromLeft"
  show FromRight = "FromRight"
  show ToTop = "ToTop"
  show ToBottom = "ToBottom"
  show ToLeft = "ToLeft"
  show ToRight = "ToRight"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation variant — pure data describing CSS transform properties
-- |
-- | All fields are optional. Only specified fields are applied.
type Variant =
  { opacity :: Maybe Number
  , scale :: Maybe Number
  , scaleX :: Maybe Number
  , scaleY :: Maybe Number
  , x :: Maybe Number          -- translateX in pixels
  , y :: Maybe Number          -- translateY in pixels
  , rotate :: Maybe Number     -- rotation in degrees
  , duration :: Maybe Number   -- milliseconds
  , delay :: Maybe Number      -- milliseconds
  , easing :: Maybe String     -- CSS easing function
  }

-- | Create a variant with opacity and scale
variant :: { opacity :: Number, scale :: Number } -> Variant
variant v =
  { opacity: Just v.opacity
  , scale: Just v.scale
  , scaleX: Nothing
  , scaleY: Nothing
  , x: Nothing
  , y: Nothing
  , rotate: Nothing
  , duration: Nothing
  , delay: Nothing
  , easing: Nothing
  }

-- | Empty variant (no changes)
emptyVariant :: Variant
emptyVariant =
  { opacity: Nothing
  , scale: Nothing
  , scaleX: Nothing
  , scaleY: Nothing
  , x: Nothing
  , y: Nothing
  , rotate: Nothing
  , duration: Nothing
  , delay: Nothing
  , easing: Nothing
  }

-- | Create variant with just opacity
variantWithOpacity :: Number -> Variant
variantWithOpacity o = emptyVariant { opacity = Just o }

-- | Create variant with just scale
variantWithScale :: Number -> Variant
variantWithScale s = emptyVariant { scale = Just s }

-- | Create variant with translation
variantWithTranslate :: Number -> Number -> Variant
variantWithTranslate tx ty = emptyVariant { x = Just tx, y = Just ty }

-- | Create variant with rotation (degrees)
variantWithRotate :: Number -> Variant
variantWithRotate r = emptyVariant { rotate = Just r }

-- | Fade in variant
fadeIn :: Variant
fadeIn = emptyVariant { opacity = Just 1.0 }

-- | Fade out variant
fadeOut :: Variant
fadeOut = emptyVariant { opacity = Just 0.0 }

-- | Slide in from direction
slideIn :: Direction -> Variant
slideIn dir = case dir of
  FromTop -> emptyVariant { y = Just 0.0, opacity = Just 1.0 }
  FromBottom -> emptyVariant { y = Just 0.0, opacity = Just 1.0 }
  FromLeft -> emptyVariant { x = Just 0.0, opacity = Just 1.0 }
  FromRight -> emptyVariant { x = Just 0.0, opacity = Just 1.0 }
  ToTop -> emptyVariant { y = Just (-20.0) }
  ToBottom -> emptyVariant { y = Just 20.0 }
  ToLeft -> emptyVariant { x = Just (-20.0) }
  ToRight -> emptyVariant { x = Just 20.0 }

-- | Slide out to direction
slideOut :: Direction -> Variant
slideOut dir = case dir of
  FromTop -> emptyVariant { y = Just (-20.0), opacity = Just 0.0 }
  FromBottom -> emptyVariant { y = Just 20.0, opacity = Just 0.0 }
  FromLeft -> emptyVariant { x = Just (-20.0), opacity = Just 0.0 }
  FromRight -> emptyVariant { x = Just 20.0, opacity = Just 0.0 }
  ToTop -> emptyVariant { y = Just (-20.0), opacity = Just 0.0 }
  ToBottom -> emptyVariant { y = Just 20.0, opacity = Just 0.0 }
  ToLeft -> emptyVariant { x = Just (-20.0), opacity = Just 0.0 }
  ToRight -> emptyVariant { x = Just 20.0, opacity = Just 0.0 }

-- | Scale in variant
scaleIn :: Variant
scaleIn = emptyVariant { scale = Just 1.0, opacity = Just 1.0 }

-- | Scale out variant
scaleOut :: Variant
scaleOut = emptyVariant { scale = Just 0.0, opacity = Just 0.0 }

-- | Pop in (scale with overshoot easing)
popIn :: Variant
popIn = emptyVariant
  { scale = Just 1.0
  , opacity = Just 1.0
  , easing = Just "cubic-bezier(0.34, 1.56, 0.64, 1)"
  }

-- | Pop out
popOut :: Variant
popOut = emptyVariant
  { scale = Just 0.8
  , opacity = Just 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // variant composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two variants (second takes precedence)
combineVariants :: Variant -> Variant -> Variant
combineVariants v1 v2 =
  { opacity: orElse v2.opacity v1.opacity
  , scale: orElse v2.scale v1.scale
  , scaleX: orElse v2.scaleX v1.scaleX
  , scaleY: orElse v2.scaleY v1.scaleY
  , x: orElse v2.x v1.x
  , y: orElse v2.y v1.y
  , rotate: orElse v2.rotate v1.rotate
  , duration: orElse v2.duration v1.duration
  , delay: orElse v2.delay v1.delay
  , easing: orElse v2.easing v1.easing
  }
  where
  orElse :: forall a. Maybe a -> Maybe a -> Maybe a
  orElse (Just x) _ = Just x
  orElse Nothing y = y

-- | Add duration to a variant
withDuration :: Milliseconds -> Variant -> Variant
withDuration (Milliseconds ms) v = v { duration = Just ms }

-- | Add delay to a variant
withDelay :: Milliseconds -> Variant -> Variant
withDelay (Milliseconds ms) v = v { delay = Just ms }

-- | Add easing to a variant
withEasing :: String -> Variant -> Variant
withEasing e v = v { easing = Just e }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // variant interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolate between two numbers
interpolateNumber :: Number -> Number -> Number -> Number
interpolateNumber t a b = a + (b - a) * t

-- | Interpolate between two variants
-- |
-- | `t` is progress from 0.0 to 1.0
interpolate :: Number -> Variant -> Variant -> Variant
interpolate t v1 v2 =
  { opacity: lerpMaybe v1.opacity v2.opacity
  , scale: lerpMaybe v1.scale v2.scale
  , scaleX: lerpMaybe v1.scaleX v2.scaleX
  , scaleY: lerpMaybe v1.scaleY v2.scaleY
  , x: lerpMaybe v1.x v2.x
  , y: lerpMaybe v1.y v2.y
  , rotate: lerpMaybe v1.rotate v2.rotate
  , duration: v2.duration   -- Use target duration
  , delay: v2.delay         -- Use target delay
  , easing: v2.easing       -- Use target easing
  }
  where
  lerpMaybe :: Maybe Number -> Maybe Number -> Maybe Number
  lerpMaybe (Just a) (Just b) = Just (interpolateNumber t a b)
  lerpMaybe Nothing (Just b) = Just b
  lerpMaybe (Just a) Nothing = Just a
  lerpMaybe Nothing Nothing = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // motion element
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion element — pure data describing an animated component
-- |
-- | The `msg` type parameter allows specifying callback messages.
-- | These are pure data — they get dispatched by the runtime, not executed here.
type MotionElement msg =
  { presence :: PresenceState       -- ^ Current presence state
  , initial :: Variant              -- ^ Initial state (before entering)
  , animate :: Variant              -- ^ Target animate state
  , exit :: Variant                 -- ^ Exit animation state
  , key :: Maybe String             -- ^ Unique key for presence tracking
  , onStart :: Maybe msg            -- ^ Message to dispatch on animation start
  , onComplete :: Maybe msg         -- ^ Message to dispatch on animation complete
  }

-- | Default motion element
defaultMotionElement :: forall msg. MotionElement msg
defaultMotionElement =
  { presence: Present
  , initial: emptyVariant
  , animate: emptyVariant
  , exit: emptyVariant
  , key: Nothing
  , onStart: Nothing
  , onComplete: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // presence transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition presence state — pure function
transitionTo :: forall msg. PresenceState -> MotionElement msg -> MotionElement msg
transitionTo newState el = el { presence = newState }

-- | Transition to entering state
enter :: forall msg. MotionElement msg -> MotionElement msg
enter = transitionTo Entering

-- | Transition to present state
present :: forall msg. MotionElement msg -> MotionElement msg
present = transitionTo Present

-- | Transition to exiting state
exit :: forall msg. MotionElement msg -> MotionElement msg
exit = transitionTo Exiting

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert variant to a record for renderer consumption
variantToRecord :: Variant -> 
  { opacity :: Number
  , scale :: Number
  , scaleX :: Number
  , scaleY :: Number
  , x :: Number
  , y :: Number
  , rotate :: Number
  , duration :: Number
  , delay :: Number
  , easing :: String
  }
variantToRecord v =
  { opacity: fromMaybe 1.0 v.opacity
  , scale: fromMaybe 1.0 v.scale
  , scaleX: fromMaybe 1.0 v.scaleX
  , scaleY: fromMaybe 1.0 v.scaleY
  , x: fromMaybe 0.0 v.x
  , y: fromMaybe 0.0 v.y
  , rotate: fromMaybe 0.0 v.rotate
  , duration: fromMaybe 300.0 v.duration
  , delay: fromMaybe 0.0 v.delay
  , easing: fromMaybe "ease" v.easing
  }

-- | Convert variant to CSS style string (for legacy renderers)
variantToLegacyCss :: Variant -> String
variantToLegacyCss v =
  intercalate "; " (Array.filter (\s -> s /= "")
    [ styleProp "opacity" v.opacity
    , transformProp v
    , transitionProp v
    ])
  where
  styleProp :: String -> Maybe Number -> String
  styleProp name (Just n) = name <> ": " <> show n
  styleProp _ Nothing = ""
  
  transformProp :: Variant -> String
  transformProp var =
    let
      parts = Array.filter (\s -> s /= "")
        [ case var.scale of
            Just s -> "scale(" <> show s <> ")"
            Nothing -> ""
        , case var.scaleX of
            Just s -> "scaleX(" <> show s <> ")"
            Nothing -> ""
        , case var.scaleY of
            Just s -> "scaleY(" <> show s <> ")"
            Nothing -> ""
        , case var.x of
            Just x -> "translateX(" <> show x <> "px)"
            Nothing -> ""
        , case var.y of
            Just y -> "translateY(" <> show y <> "px)"
            Nothing -> ""
        , case var.rotate of
            Just r -> "rotate(" <> show r <> "deg)"
            Nothing -> ""
        ]
    in
      if Array.null parts
        then ""
        else "transform: " <> intercalate " " parts
  
  transitionProp :: Variant -> String
  transitionProp var = case var.duration of
    Just d -> 
      let dur = show d <> "ms"
          ease = fromMaybe "ease" var.easing
          del = case var.delay of
            Just dl -> " " <> show dl <> "ms"
            Nothing -> ""
      in "transition: all " <> dur <> " " <> ease <> del
    Nothing -> ""
