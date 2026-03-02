-- | Lattice.Services.Easing - Easing functions for animation
-- |
-- | Pure math functions for animation interpolation.
-- | All functions take normalized time t ∈ [0,1] and return eased value ∈ [0,1].
-- |
-- | Source: ui/src/services/easing.ts

module Lattice.Services.Easing
  ( -- * Easing Type
    EasingType(..)
  , easingTypeFromString
  , easingTypeToString
    -- * Core Functions
  , applyEasing
  , applyEasingType
  , interpolateWithEasing
    -- * Individual Easings
  , linear
  , easeInSine, easeOutSine, easeInOutSine
  , easeInQuad, easeOutQuad, easeInOutQuad
  , easeInCubic, easeOutCubic, easeInOutCubic
  , easeInQuart, easeOutQuart, easeInOutQuart
  , easeInQuint, easeOutQuint, easeInOutQuint
  , easeInExpo, easeOutExpo, easeInOutExpo
  , easeInCirc, easeOutCirc, easeInOutCirc
  , easeInBack, easeOutBack, easeInOutBack
  , easeInElastic, easeOutElastic, easeInOutElastic
  , easeInBounce, easeOutBounce, easeInOutBounce
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Math (cos, sin, sqrt, pow, pi)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

c1 :: Number
c1 = 1.70158

c2 :: Number
c2 = c1 * 1.525

c3 :: Number
c3 = c1 + 1.0

c4 :: Number
c4 = (2.0 * pi) / 3.0

c5 :: Number
c5 = (2.0 * pi) / 4.5

--------------------------------------------------------------------------------
-- Easing Type
--------------------------------------------------------------------------------

data EasingType
  = EaseLinear
  | EaseInSine | EaseOutSine | EaseInOutSine
  | EaseInQuad | EaseOutQuad | EaseInOutQuad
  | EaseInCubic | EaseOutCubic | EaseInOutCubic
  | EaseInQuart | EaseOutQuart | EaseInOutQuart
  | EaseInQuint | EaseOutQuint | EaseInOutQuint
  | EaseInExpo | EaseOutExpo | EaseInOutExpo
  | EaseInCirc | EaseOutCirc | EaseInOutCirc
  | EaseInBack | EaseOutBack | EaseInOutBack
  | EaseInElastic | EaseOutElastic | EaseInOutElastic
  | EaseInBounce | EaseOutBounce | EaseInOutBounce

derive instance Eq EasingType
derive instance Generic EasingType _
instance Show EasingType where show = genericShow

--------------------------------------------------------------------------------
-- Individual Easing Functions
--------------------------------------------------------------------------------

-- | Linear - no easing
linear :: Number -> Number
linear t = t

-- | Sine easing
easeInSine :: Number -> Number
easeInSine t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = 1.0 - cos ((t * pi) / 2.0)

easeOutSine :: Number -> Number
easeOutSine t = sin ((t * pi) / 2.0)

easeInOutSine :: Number -> Number
easeInOutSine t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = -(cos (pi * t) - 1.0) / 2.0

-- | Quadratic easing
easeInQuad :: Number -> Number
easeInQuad t = t * t

easeOutQuad :: Number -> Number
easeOutQuad t = let u = 1.0 - t in 1.0 - u * u

easeInOutQuad :: Number -> Number
easeInOutQuad t
  | t < 0.5 = 2.0 * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u) / 2.0

-- | Cubic easing
easeInCubic :: Number -> Number
easeInCubic t = t * t * t

easeOutCubic :: Number -> Number
easeOutCubic t = let u = 1.0 - t in 1.0 - u * u * u

easeInOutCubic :: Number -> Number
easeInOutCubic t
  | t < 0.5 = 4.0 * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u) / 2.0

-- | Quartic easing
easeInQuart :: Number -> Number
easeInQuart t = t * t * t * t

easeOutQuart :: Number -> Number
easeOutQuart t = let u = 1.0 - t in 1.0 - u * u * u * u

easeInOutQuart :: Number -> Number
easeInOutQuart t
  | t < 0.5 = 8.0 * t * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u * u) / 2.0

-- | Quintic easing
easeInQuint :: Number -> Number
easeInQuint t = t * t * t * t * t

easeOutQuint :: Number -> Number
easeOutQuint t = let u = 1.0 - t in 1.0 - u * u * u * u * u

easeInOutQuint :: Number -> Number
easeInOutQuint t
  | t < 0.5 = 16.0 * t * t * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u * u * u) / 2.0

-- | Exponential easing
easeInExpo :: Number -> Number
easeInExpo t
  | t == 0.0 = 0.0
  | otherwise = pow 2.0 (10.0 * t - 10.0)

easeOutExpo :: Number -> Number
easeOutExpo t
  | t == 1.0 = 1.0
  | otherwise = 1.0 - pow 2.0 (-10.0 * t)

easeInOutExpo :: Number -> Number
easeInOutExpo t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = pow 2.0 (20.0 * t - 10.0) / 2.0
  | otherwise = (2.0 - pow 2.0 (-20.0 * t + 10.0)) / 2.0

-- | Circular easing
easeInCirc :: Number -> Number
easeInCirc t = 1.0 - sqrt (1.0 - t * t)

easeOutCirc :: Number -> Number
easeOutCirc t = let u = t - 1.0 in sqrt (1.0 - u * u)

easeInOutCirc :: Number -> Number
easeInOutCirc t
  | t < 0.5 = let u = 2.0 * t in (1.0 - sqrt (1.0 - u * u)) / 2.0
  | otherwise = let u = -2.0 * t + 2.0 in (sqrt (1.0 - u * u) + 1.0) / 2.0

-- | Back easing (overshoot)
easeInBack :: Number -> Number
easeInBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = c3 * t * t * t - c1 * t * t

easeOutBack :: Number -> Number
easeOutBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let u = t - 1.0 in 1.0 + c3 * u * u * u + c1 * u * u

easeInOutBack :: Number -> Number
easeInOutBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = let u = 2.0 * t in (u * u * ((c2 + 1.0) * u - c2)) / 2.0
  | otherwise = let u = 2.0 * t - 2.0 in (u * u * ((c2 + 1.0) * u + c2) + 2.0) / 2.0

-- | Elastic easing
easeInElastic :: Number -> Number
easeInElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let p = pow 2.0 (10.0 * t - 10.0)
                in -p * sin ((t * 10.0 - 10.75) * c4)

easeOutElastic :: Number -> Number
easeOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let p = pow 2.0 (-10.0 * t)
                in p * sin ((t * 10.0 - 0.75) * c4) + 1.0

easeInOutElastic :: Number -> Number
easeInOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = let p = pow 2.0 (20.0 * t - 10.0)
              in -(p * sin ((20.0 * t - 11.125) * c5)) / 2.0
  | otherwise = let p = pow 2.0 (-20.0 * t + 10.0)
                in (p * sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0

-- | Bounce easing
easeOutBounce :: Number -> Number
easeOutBounce t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1.0 / d1 then n1 * t * t
     else if t < 2.0 / d1 then let t' = t - 1.5 / d1 in n1 * t' * t' + 0.75
     else if t < 2.5 / d1 then let t' = t - 2.25 / d1 in n1 * t' * t' + 0.9375
     else let t' = t - 2.625 / d1 in n1 * t' * t' + 0.984375

easeInBounce :: Number -> Number
easeInBounce t = 1.0 - easeOutBounce (1.0 - t)

easeInOutBounce :: Number -> Number
easeInOutBounce t
  | t < 0.5 = (1.0 - easeOutBounce (1.0 - 2.0 * t)) / 2.0
  | otherwise = (1.0 + easeOutBounce (2.0 * t - 1.0)) / 2.0

--------------------------------------------------------------------------------
-- Main Dispatch Function
--------------------------------------------------------------------------------

-- | Apply easing by type
applyEasingType :: EasingType -> Number -> Number
applyEasingType EaseLinear = linear
applyEasingType EaseInSine = easeInSine
applyEasingType EaseOutSine = easeOutSine
applyEasingType EaseInOutSine = easeInOutSine
applyEasingType EaseInQuad = easeInQuad
applyEasingType EaseOutQuad = easeOutQuad
applyEasingType EaseInOutQuad = easeInOutQuad
applyEasingType EaseInCubic = easeInCubic
applyEasingType EaseOutCubic = easeOutCubic
applyEasingType EaseInOutCubic = easeInOutCubic
applyEasingType EaseInQuart = easeInQuart
applyEasingType EaseOutQuart = easeOutQuart
applyEasingType EaseInOutQuart = easeInOutQuart
applyEasingType EaseInQuint = easeInQuint
applyEasingType EaseOutQuint = easeOutQuint
applyEasingType EaseInOutQuint = easeInOutQuint
applyEasingType EaseInExpo = easeInExpo
applyEasingType EaseOutExpo = easeOutExpo
applyEasingType EaseInOutExpo = easeInOutExpo
applyEasingType EaseInCirc = easeInCirc
applyEasingType EaseOutCirc = easeOutCirc
applyEasingType EaseInOutCirc = easeInOutCirc
applyEasingType EaseInBack = easeInBack
applyEasingType EaseOutBack = easeOutBack
applyEasingType EaseInOutBack = easeInOutBack
applyEasingType EaseInElastic = easeInElastic
applyEasingType EaseOutElastic = easeOutElastic
applyEasingType EaseInOutElastic = easeInOutElastic
applyEasingType EaseInBounce = easeInBounce
applyEasingType EaseOutBounce = easeOutBounce
applyEasingType EaseInOutBounce = easeInOutBounce

-- | Apply easing with clamped input
applyEasing :: EasingType -> Number -> Number
applyEasing easingType t = applyEasingType easingType (max 0.0 (min 1.0 t))

-- | Interpolate with easing
interpolateWithEasing :: Number -> Number -> Number -> EasingType -> Number
interpolateWithEasing start stop t easingType =
  let easedT = applyEasing easingType t
  in start + (stop - start) * easedT

--------------------------------------------------------------------------------
-- String Conversion
--------------------------------------------------------------------------------

easingTypeFromString :: String -> Maybe EasingType
easingTypeFromString = case _ of
  "linear" -> Just EaseLinear
  "easeInSine" -> Just EaseInSine
  "easeOutSine" -> Just EaseOutSine
  "easeInOutSine" -> Just EaseInOutSine
  "easeInQuad" -> Just EaseInQuad
  "easeOutQuad" -> Just EaseOutQuad
  "easeInOutQuad" -> Just EaseInOutQuad
  "easeInCubic" -> Just EaseInCubic
  "easeOutCubic" -> Just EaseOutCubic
  "easeInOutCubic" -> Just EaseInOutCubic
  "easeInQuart" -> Just EaseInQuart
  "easeOutQuart" -> Just EaseOutQuart
  "easeInOutQuart" -> Just EaseInOutQuart
  "easeInQuint" -> Just EaseInQuint
  "easeOutQuint" -> Just EaseOutQuint
  "easeInOutQuint" -> Just EaseInOutQuint
  "easeInExpo" -> Just EaseInExpo
  "easeOutExpo" -> Just EaseOutExpo
  "easeInOutExpo" -> Just EaseInOutExpo
  "easeInCirc" -> Just EaseInCirc
  "easeOutCirc" -> Just EaseOutCirc
  "easeInOutCirc" -> Just EaseInOutCirc
  "easeInBack" -> Just EaseInBack
  "easeOutBack" -> Just EaseOutBack
  "easeInOutBack" -> Just EaseInOutBack
  "easeInElastic" -> Just EaseInElastic
  "easeOutElastic" -> Just EaseOutElastic
  "easeInOutElastic" -> Just EaseInOutElastic
  "easeInBounce" -> Just EaseInBounce
  "easeOutBounce" -> Just EaseOutBounce
  "easeInOutBounce" -> Just EaseInOutBounce
  _ -> Nothing

easingTypeToString :: EasingType -> String
easingTypeToString = case _ of
  EaseLinear -> "linear"
  EaseInSine -> "easeInSine"
  EaseOutSine -> "easeOutSine"
  EaseInOutSine -> "easeInOutSine"
  EaseInQuad -> "easeInQuad"
  EaseOutQuad -> "easeOutQuad"
  EaseInOutQuad -> "easeInOutQuad"
  EaseInCubic -> "easeInCubic"
  EaseOutCubic -> "easeOutCubic"
  EaseInOutCubic -> "easeInOutCubic"
  EaseInQuart -> "easeInQuart"
  EaseOutQuart -> "easeOutQuart"
  EaseInOutQuart -> "easeInOutQuart"
  EaseInQuint -> "easeInQuint"
  EaseOutQuint -> "easeOutQuint"
  EaseInOutQuint -> "easeInOutQuint"
  EaseInExpo -> "easeInExpo"
  EaseOutExpo -> "easeOutExpo"
  EaseInOutExpo -> "easeInOutExpo"
  EaseInCirc -> "easeInCirc"
  EaseOutCirc -> "easeOutCirc"
  EaseInOutCirc -> "easeInOutCirc"
  EaseInBack -> "easeInBack"
  EaseOutBack -> "easeOutBack"
  EaseInOutBack -> "easeInOutBack"
  EaseInElastic -> "easeInElastic"
  EaseOutElastic -> "easeOutElastic"
  EaseInOutElastic -> "easeInOutElastic"
  EaseInBounce -> "easeInBounce"
  EaseOutBounce -> "easeOutBounce"
  EaseInOutBounce -> "easeInOutBounce"
