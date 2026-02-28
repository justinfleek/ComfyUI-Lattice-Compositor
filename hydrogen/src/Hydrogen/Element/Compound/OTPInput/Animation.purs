-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // otpinput // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Animation — Pure data description of OTP digit animations.
-- |
-- | ## Animation Philosophy
-- |
-- | Animations are described as **pure data** using Schema atoms. The Target
-- | layer (DOM, WebGL, etc.) interprets this data to produce actual motion.
-- |
-- | 1. **Entry** — Scale pop when digit is typed
-- | 2. **Error** — Shake animation on validation failure
-- | 3. **Success** — Pulse animation on verification success
-- | 4. **Loading** — Subtle pulse during verification
-- |
-- | ## Architecture
-- |
-- | ```
-- | OTPAnimation (pure data)
-- |      ↓
-- | Element with animation data attributes
-- |      ↓
-- | Target interprets → actual motion
-- | ```
-- |
-- | NO CSS STRINGS. NO STYLE INJECTION. Pure data only.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Keyframe for keyframe data
-- | - Schema.Motion.Easing for timing functions
-- | - Schema.Dimension.Temporal for durations
-- | - Types module for DigitAnimationState, OTPState

module Hydrogen.Element.Compound.OTPInput.Animation
  ( -- * Animation Types
    OTPAnimation(OTPAnimation)
  , OTPAnimationProperty(TranslateX, TranslateY, Scale, ScaleX, ScaleY, Opacity, Rotate)
  , OTPKeyframe(OTPKeyframe)
  , OTPIterationCount(Once, Times, Infinite)
  , OTPFillMode(FillNone, FillForwards, FillBackwards, FillBoth)
  
  -- * Animation Definitions
  , shakeAnimation
  , pulseAnimation
  , entryAnimation
  , loadingAnimation
  
  -- * Animation Data Retrieval
  , getAnimation
  , getAnimationData
  , getAnimationDataAttrs
  
  -- * Animation State Computation
  , computeDigitAnimationState
  , shouldAnimate
  
  -- * Accessors
  , animationProperty
  , animationKeyframes
  , animationDuration
  , animationEasing
  , animationIterations
  , animationFillMode
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (*)
  , negate
  , not
  , map
  )

import Data.Array (concat)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Dimension.Temporal as Temporal

import Hydrogen.Element.Compound.OTPInput.Types
  ( DigitAnimationState(DigitIdle, DigitEntering, DigitFilled, DigitError, DigitSuccess)
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPDigit(OTPDigit)
  )

import Hydrogen.Element.Compound.OTPInput.Props
  ( OTPInputProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation property — what aspect of the element is animated.
-- |
-- | Each variant represents a CSS transform or style property.
-- | The Target layer interprets these to actual property changes.
data OTPAnimationProperty
  = TranslateX        -- Horizontal translation (px)
  | TranslateY        -- Vertical translation (px)
  | Scale             -- Uniform scale
  | ScaleX            -- Horizontal scale
  | ScaleY            -- Vertical scale
  | Opacity           -- Alpha channel [0.0, 1.0]
  | Rotate            -- Rotation (degrees)

derive instance eqOTPAnimationProperty :: Eq OTPAnimationProperty

instance showOTPAnimationProperty :: Show OTPAnimationProperty where
  show TranslateX = "translateX"
  show TranslateY = "translateY"
  show Scale = "scale"
  show ScaleX = "scaleX"
  show ScaleY = "scaleY"
  show Opacity = "opacity"
  show Rotate = "rotate"

-- | Keyframe — a value at a specific percentage of the animation.
-- |
-- | Percentage is normalized [0.0, 1.0] where 0.0 = 0% and 1.0 = 100%.
newtype OTPKeyframe = OTPKeyframe
  { percentage :: Number    -- [0.0, 1.0]
  , value :: Number         -- Property value at this point
  }

derive instance eqOTPKeyframe :: Eq OTPKeyframe

instance showOTPKeyframe :: Show OTPKeyframe where
  show (OTPKeyframe kf) = show (kf.percentage * 100.0) <> "% → " <> show kf.value

-- | Iteration count — how many times the animation plays.
data OTPIterationCount
  = Once                    -- Play exactly once
  | Times Int               -- Play n times
  | Infinite                -- Loop forever

derive instance eqOTPIterationCount :: Eq OTPIterationCount

instance showOTPIterationCount :: Show OTPIterationCount where
  show Once = "1"
  show (Times n) = show n
  show Infinite = "infinite"

-- | Fill mode — what state the element holds after animation.
data OTPFillMode
  = FillNone                -- Revert to pre-animation state
  | FillForwards            -- Hold final keyframe values
  | FillBackwards           -- Apply first keyframe before animation starts
  | FillBoth                -- Both forwards and backwards

derive instance eqOTPFillMode :: Eq OTPFillMode

instance showOTPFillMode :: Show OTPFillMode where
  show FillNone = "none"
  show FillForwards = "forwards"
  show FillBackwards = "backwards"
  show FillBoth = "both"

-- | Complete animation description — pure data.
-- |
-- | Describes a single-property animation with keyframes, timing, and behavior.
-- | For multi-property animations, compose multiple OTPAnimation values.
newtype OTPAnimation = OTPAnimation
  { property :: OTPAnimationProperty
  , keyframes :: Array OTPKeyframe
  , duration :: Temporal.Milliseconds
  , easing :: Easing.Easing
  , iterations :: OTPIterationCount
  , fillMode :: OTPFillMode
  }

derive instance eqOTPAnimation :: Eq OTPAnimation

instance showOTPAnimation :: Show OTPAnimation where
  show (OTPAnimation a) =
    show a.property <> " " <> show a.duration <> " " <> show a.easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animation definitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shake animation for error feedback.
-- |
-- | Horizontal oscillation: 0 → -4px → +4px → -4px → ... → 0
shakeAnimation :: Temporal.Milliseconds -> Array OTPAnimation
shakeAnimation duration =
  [ OTPAnimation
      { property: TranslateX
      , keyframes:
          [ OTPKeyframe { percentage: 0.0, value: 0.0 }
          , OTPKeyframe { percentage: 0.1, value: -4.0 }
          , OTPKeyframe { percentage: 0.2, value: 4.0 }
          , OTPKeyframe { percentage: 0.3, value: -4.0 }
          , OTPKeyframe { percentage: 0.4, value: 4.0 }
          , OTPKeyframe { percentage: 0.5, value: -4.0 }
          , OTPKeyframe { percentage: 0.6, value: 4.0 }
          , OTPKeyframe { percentage: 0.7, value: -4.0 }
          , OTPKeyframe { percentage: 0.8, value: 4.0 }
          , OTPKeyframe { percentage: 0.9, value: -4.0 }
          , OTPKeyframe { percentage: 1.0, value: 0.0 }
          ]
      , duration: duration
      , easing: Easing.easeOut
      , iterations: Once
      , fillMode: FillForwards
      }
  ]

-- | Pulse animation for success feedback.
-- |
-- | Scale oscillation: 1.0 → 1.05 → 1.0
pulseAnimation :: Temporal.Milliseconds -> Array OTPAnimation
pulseAnimation duration =
  [ OTPAnimation
      { property: Scale
      , keyframes:
          [ OTPKeyframe { percentage: 0.0, value: 1.0 }
          , OTPKeyframe { percentage: 0.5, value: 1.05 }
          , OTPKeyframe { percentage: 1.0, value: 1.0 }
          ]
      , duration: duration
      , easing: Easing.easeInOut
      , iterations: Once
      , fillMode: FillForwards
      }
  ]

-- | Entry animation for digit input.
-- |
-- | Scale + opacity: small/faded → normal
entryAnimation :: Temporal.Milliseconds -> Array OTPAnimation
entryAnimation duration =
  [ OTPAnimation
      { property: Scale
      , keyframes:
          [ OTPKeyframe { percentage: 0.0, value: 0.8 }
          , OTPKeyframe { percentage: 1.0, value: 1.0 }
          ]
      , duration: duration
      , easing: Easing.easeOut
      , iterations: Once
      , fillMode: FillForwards
      }
  , OTPAnimation
      { property: Opacity
      , keyframes:
          [ OTPKeyframe { percentage: 0.0, value: 0.5 }
          , OTPKeyframe { percentage: 1.0, value: 1.0 }
          ]
      , duration: duration
      , easing: Easing.easeOut
      , iterations: Once
      , fillMode: FillForwards
      }
  ]

-- | Loading animation for verification state.
-- |
-- | Opacity pulse: 1.0 → 0.6 → 1.0 (infinite)
loadingAnimation :: Array OTPAnimation
loadingAnimation =
  [ OTPAnimation
      { property: Opacity
      , keyframes:
          [ OTPKeyframe { percentage: 0.0, value: 1.0 }
          , OTPKeyframe { percentage: 0.5, value: 0.6 }
          , OTPKeyframe { percentage: 1.0, value: 1.0 }
          ]
      , duration: Temporal.ms 1000.0
      , easing: Easing.easeInOut
      , iterations: Infinite
      , fillMode: FillNone
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // animation data retrieval
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get animation data for a digit based on its state.
-- |
-- | Returns Nothing if no animation should play (idle, filled, or disabled).
getAnimation
  :: forall msg
   . OTPInputProps msg
  -> DigitAnimationState
  -> Maybe (Array OTPAnimation)
getAnimation props animState =
  if not props.animationEnabled
    then Nothing
    else case animState of
      DigitIdle -> Nothing
      DigitEntering -> Just (entryAnimation props.entryDuration)
      DigitFilled -> Nothing
      DigitError -> Just (shakeAnimation props.shakeDuration)
      DigitSuccess -> Just (pulseAnimation props.pulseDuration)

-- | Get animation data as a record for serialization/data-attribute encoding.
-- |
-- | Returns a record with animation parameters that can be attached to elements.
getAnimationData
  :: forall msg
   . OTPInputProps msg
  -> DigitAnimationState
  -> Maybe
       { animations :: Array OTPAnimation
       , reducedMotion :: Boolean
       }
getAnimationData props animState =
  case getAnimation props animState of
    Nothing -> Nothing
    Just anims -> Just
      { animations: anims
      , reducedMotion: props.reducedMotion
      }

-- | Convert animation data to Element data attributes.
-- |
-- | This encodes animation parameters as data-* attributes for the Target layer
-- | to interpret. Returns empty array if no animation is active.
-- |
-- | Data attributes encoded:
-- | - data-animation-property: The animated property (translateX, scale, etc.)
-- | - data-animation-duration: Duration in milliseconds
-- | - data-animation-iterations: Iteration count (1, infinite, etc.)
-- | - data-animation-fill-mode: Fill mode (none, forwards, backwards, both)
getAnimationDataAttrs
  :: forall msg
   . OTPInputProps msg
  -> DigitAnimationState
  -> Array (E.Attribute msg)
getAnimationDataAttrs props animState =
  case getAnimation props animState of
    Nothing -> []
    Just anims ->
      -- Encode each animation as data attributes
      -- For multiple animations, we use the primary (first) animation
      case anims of
        [] -> []
        _ ->
          let
            -- Collect all properties and encode them
            propAttrs = concat (map encodeAnimationAttrs anims)
          in
            propAttrs

-- | Encode a single animation as data attributes
encodeAnimationAttrs :: forall msg. OTPAnimation -> Array (E.Attribute msg)
encodeAnimationAttrs (OTPAnimation anim) =
  [ E.dataAttr "animation-property" (propertyToString anim.property)
  , E.dataAttr "animation-duration" (show (Temporal.unwrapMilliseconds anim.duration))
  , E.dataAttr "animation-iterations" (iterationsToString anim.iterations)
  , E.dataAttr "animation-fill-mode" (fillModeToString anim.fillMode)
  , E.dataAttr "animation-easing" (Easing.toLegacyCssString anim.easing)
  ]

-- | Convert animation property to string
propertyToString :: OTPAnimationProperty -> String
propertyToString TranslateX = "translateX"
propertyToString TranslateY = "translateY"
propertyToString Scale = "scale"
propertyToString ScaleX = "scaleX"
propertyToString ScaleY = "scaleY"
propertyToString Opacity = "opacity"
propertyToString Rotate = "rotate"

-- | Convert iteration count to string
iterationsToString :: OTPIterationCount -> String
iterationsToString Once = "1"
iterationsToString (Times n) = show n
iterationsToString Infinite = "infinite"

-- | Convert fill mode to string
fillModeToString :: OTPFillMode -> String
fillModeToString FillNone = "none"
fillModeToString FillForwards = "forwards"
fillModeToString FillBackwards = "backwards"
fillModeToString FillBoth = "both"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // animation state computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute the animation state for a digit based on component state.
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
computeDigitAnimationState
  :: OTPState
  -> OTPDigit
  -> Boolean  -- ^ Is this digit currently being entered?
  -> DigitAnimationState
computeDigitAnimationState state digit isEntering =
  case state of
    Idle ->
      case digit of
        OTPDigit Nothing -> DigitIdle
        OTPDigit (Just _) -> DigitFilled
    Entering ->
      if isEntering
        then DigitEntering
        else case digit of
          OTPDigit Nothing -> DigitIdle
          OTPDigit (Just _) -> DigitFilled
    Verifying ->
      case digit of
        OTPDigit Nothing -> DigitIdle
        OTPDigit (Just _) -> DigitFilled
    Success ->
      DigitSuccess
    Error ->
      DigitError

-- | Check if animations should run (respects animationEnabled prop)
shouldAnimate :: forall msg. OTPInputProps msg -> Boolean
shouldAnimate props = props.animationEnabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the property being animated
animationProperty :: OTPAnimation -> OTPAnimationProperty
animationProperty (OTPAnimation a) = a.property

-- | Get the keyframes
animationKeyframes :: OTPAnimation -> Array OTPKeyframe
animationKeyframes (OTPAnimation a) = a.keyframes

-- | Get the duration
animationDuration :: OTPAnimation -> Temporal.Milliseconds
animationDuration (OTPAnimation a) = a.duration

-- | Get the easing function
animationEasing :: OTPAnimation -> Easing.Easing
animationEasing (OTPAnimation a) = a.easing

-- | Get the iteration count
animationIterations :: OTPAnimation -> OTPIterationCount
animationIterations (OTPAnimation a) = a.iterations

-- | Get the fill mode
animationFillMode :: OTPAnimation -> OTPFillMode
animationFillMode (OTPAnimation a) = a.fillMode
