{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.Easing
Description : Easing functions for animation
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for animation interpolation.
All functions take normalized time t ∈ [0,1] and return eased value ∈ [0,1].

Source: ui/src/services/easing.ts
-}

module Lattice.Services.Easing
  ( -- * Easing Type
    EasingType(..)
  , easingTypeFromText
  , easingTypeToText
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

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

c1 :: Double
c1 = 1.70158

c2 :: Double
c2 = c1 * 1.525

c3 :: Double
c3 = c1 + 1.0

c4 :: Double
c4 = (2.0 * pi) / 3.0

c5 :: Double
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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

--------------------------------------------------------------------------------
-- Individual Easing Functions
--------------------------------------------------------------------------------

-- | Linear - no easing
linear :: Double -> Double
linear t = t

-- | Sine easing
easeInSine :: Double -> Double
easeInSine t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = 1.0 - cos ((t * pi) / 2.0)

easeOutSine :: Double -> Double
easeOutSine t = sin ((t * pi) / 2.0)

easeInOutSine :: Double -> Double
easeInOutSine t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = -(cos (pi * t) - 1.0) / 2.0

-- | Quadratic easing
easeInQuad :: Double -> Double
easeInQuad t = t * t

easeOutQuad :: Double -> Double
easeOutQuad t = let u = 1.0 - t in 1.0 - u * u

easeInOutQuad :: Double -> Double
easeInOutQuad t
  | t < 0.5 = 2.0 * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u) / 2.0

-- | Cubic easing
easeInCubic :: Double -> Double
easeInCubic t = t * t * t

easeOutCubic :: Double -> Double
easeOutCubic t = let u = 1.0 - t in 1.0 - u * u * u

easeInOutCubic :: Double -> Double
easeInOutCubic t
  | t < 0.5 = 4.0 * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u) / 2.0

-- | Quartic easing
easeInQuart :: Double -> Double
easeInQuart t = t * t * t * t

easeOutQuart :: Double -> Double
easeOutQuart t = let u = 1.0 - t in 1.0 - u * u * u * u

easeInOutQuart :: Double -> Double
easeInOutQuart t
  | t < 0.5 = 8.0 * t * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u * u) / 2.0

-- | Quintic easing
easeInQuint :: Double -> Double
easeInQuint t = t * t * t * t * t

easeOutQuint :: Double -> Double
easeOutQuint t = let u = 1.0 - t in 1.0 - u * u * u * u * u

easeInOutQuint :: Double -> Double
easeInOutQuint t
  | t < 0.5 = 16.0 * t * t * t * t * t
  | otherwise = let u = -2.0 * t + 2.0 in 1.0 - (u * u * u * u * u) / 2.0

-- | Exponential easing
easeInExpo :: Double -> Double
easeInExpo t
  | t == 0.0 = 0.0
  | otherwise = 2.0 ** (10.0 * t - 10.0)

easeOutExpo :: Double -> Double
easeOutExpo t
  | t == 1.0 = 1.0
  | otherwise = 1.0 - 2.0 ** (-10.0 * t)

easeInOutExpo :: Double -> Double
easeInOutExpo t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = (2.0 ** (20.0 * t - 10.0)) / 2.0
  | otherwise = (2.0 - 2.0 ** (-20.0 * t + 10.0)) / 2.0

-- | Circular easing
easeInCirc :: Double -> Double
easeInCirc t = 1.0 - sqrt (1.0 - t * t)

easeOutCirc :: Double -> Double
easeOutCirc t = let u = t - 1.0 in sqrt (1.0 - u * u)

easeInOutCirc :: Double -> Double
easeInOutCirc t
  | t < 0.5 = let u = 2.0 * t in (1.0 - sqrt (1.0 - u * u)) / 2.0
  | otherwise = let u = -2.0 * t + 2.0 in (sqrt (1.0 - u * u) + 1.0) / 2.0

-- | Back easing (overshoot)
easeInBack :: Double -> Double
easeInBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = c3 * t * t * t - c1 * t * t

easeOutBack :: Double -> Double
easeOutBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let u = t - 1.0 in 1.0 + c3 * u * u * u + c1 * u * u

easeInOutBack :: Double -> Double
easeInOutBack t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = let u = 2.0 * t in (u * u * ((c2 + 1.0) * u - c2)) / 2.0
  | otherwise = let u = 2.0 * t - 2.0 in (u * u * ((c2 + 1.0) * u + c2) + 2.0) / 2.0

-- | Elastic easing
easeInElastic :: Double -> Double
easeInElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let pow = 2.0 ** (10.0 * t - 10.0)
                in -pow * sin ((t * 10.0 - 10.75) * c4)

easeOutElastic :: Double -> Double
easeOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise = let pow = 2.0 ** (-10.0 * t)
                in pow * sin ((t * 10.0 - 0.75) * c4) + 1.0

easeInOutElastic :: Double -> Double
easeInOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = let pow = 2.0 ** (20.0 * t - 10.0)
              in -(pow * sin ((20.0 * t - 11.125) * c5)) / 2.0
  | otherwise = let pow = 2.0 ** (-20.0 * t + 10.0)
                in (pow * sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0

-- | Bounce easing
easeOutBounce :: Double -> Double
easeOutBounce t
  | t < 1.0 / d1 = n1 * t * t
  | t < 2.0 / d1 = let t' = t - 1.5 / d1 in n1 * t' * t' + 0.75
  | t < 2.5 / d1 = let t' = t - 2.25 / d1 in n1 * t' * t' + 0.9375
  | otherwise = let t' = t - 2.625 / d1 in n1 * t' * t' + 0.984375
  where
    n1 = 7.5625
    d1 = 2.75

easeInBounce :: Double -> Double
easeInBounce t = 1.0 - easeOutBounce (1.0 - t)

easeInOutBounce :: Double -> Double
easeInOutBounce t
  | t < 0.5 = (1.0 - easeOutBounce (1.0 - 2.0 * t)) / 2.0
  | otherwise = (1.0 + easeOutBounce (2.0 * t - 1.0)) / 2.0

--------------------------------------------------------------------------------
-- Main Dispatch Function
--------------------------------------------------------------------------------

-- | Apply easing by type
applyEasingType :: EasingType -> Double -> Double
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
applyEasing :: EasingType -> Double -> Double
applyEasing easingType t = applyEasingType easingType (max 0.0 (min 1.0 t))

-- | Interpolate with easing
interpolateWithEasing :: Double -> Double -> Double -> EasingType -> Double
interpolateWithEasing start stop t easingType =
  let easedT = applyEasing easingType t
  in start + (stop - start) * easedT

--------------------------------------------------------------------------------
-- String Conversion
--------------------------------------------------------------------------------

easingTypeFromText :: Text -> Maybe EasingType
easingTypeFromText "linear" = Just EaseLinear
easingTypeFromText "easeInSine" = Just EaseInSine
easingTypeFromText "easeOutSine" = Just EaseOutSine
easingTypeFromText "easeInOutSine" = Just EaseInOutSine
easingTypeFromText "easeInQuad" = Just EaseInQuad
easingTypeFromText "easeOutQuad" = Just EaseOutQuad
easingTypeFromText "easeInOutQuad" = Just EaseInOutQuad
easingTypeFromText "easeInCubic" = Just EaseInCubic
easingTypeFromText "easeOutCubic" = Just EaseOutCubic
easingTypeFromText "easeInOutCubic" = Just EaseInOutCubic
easingTypeFromText "easeInQuart" = Just EaseInQuart
easingTypeFromText "easeOutQuart" = Just EaseOutQuart
easingTypeFromText "easeInOutQuart" = Just EaseInOutQuart
easingTypeFromText "easeInQuint" = Just EaseInQuint
easingTypeFromText "easeOutQuint" = Just EaseOutQuint
easingTypeFromText "easeInOutQuint" = Just EaseInOutQuint
easingTypeFromText "easeInExpo" = Just EaseInExpo
easingTypeFromText "easeOutExpo" = Just EaseOutExpo
easingTypeFromText "easeInOutExpo" = Just EaseInOutExpo
easingTypeFromText "easeInCirc" = Just EaseInCirc
easingTypeFromText "easeOutCirc" = Just EaseOutCirc
easingTypeFromText "easeInOutCirc" = Just EaseInOutCirc
easingTypeFromText "easeInBack" = Just EaseInBack
easingTypeFromText "easeOutBack" = Just EaseOutBack
easingTypeFromText "easeInOutBack" = Just EaseInOutBack
easingTypeFromText "easeInElastic" = Just EaseInElastic
easingTypeFromText "easeOutElastic" = Just EaseOutElastic
easingTypeFromText "easeInOutElastic" = Just EaseInOutElastic
easingTypeFromText "easeInBounce" = Just EaseInBounce
easingTypeFromText "easeOutBounce" = Just EaseOutBounce
easingTypeFromText "easeInOutBounce" = Just EaseInOutBounce
easingTypeFromText _ = Nothing

easingTypeToText :: EasingType -> Text
easingTypeToText EaseLinear = "linear"
easingTypeToText EaseInSine = "easeInSine"
easingTypeToText EaseOutSine = "easeOutSine"
easingTypeToText EaseInOutSine = "easeInOutSine"
easingTypeToText EaseInQuad = "easeInQuad"
easingTypeToText EaseOutQuad = "easeOutQuad"
easingTypeToText EaseInOutQuad = "easeInOutQuad"
easingTypeToText EaseInCubic = "easeInCubic"
easingTypeToText EaseOutCubic = "easeOutCubic"
easingTypeToText EaseInOutCubic = "easeInOutCubic"
easingTypeToText EaseInQuart = "easeInQuart"
easingTypeToText EaseOutQuart = "easeOutQuart"
easingTypeToText EaseInOutQuart = "easeInOutQuart"
easingTypeToText EaseInQuint = "easeInQuint"
easingTypeToText EaseOutQuint = "easeOutQuint"
easingTypeToText EaseInOutQuint = "easeInOutQuint"
easingTypeToText EaseInExpo = "easeInExpo"
easingTypeToText EaseOutExpo = "easeOutExpo"
easingTypeToText EaseInOutExpo = "easeInOutExpo"
easingTypeToText EaseInCirc = "easeInCirc"
easingTypeToText EaseOutCirc = "easeOutCirc"
easingTypeToText EaseInOutCirc = "easeInOutCirc"
easingTypeToText EaseInBack = "easeInBack"
easingTypeToText EaseOutBack = "easeOutBack"
easingTypeToText EaseInOutBack = "easeInOutBack"
easingTypeToText EaseInElastic = "easeInElastic"
easingTypeToText EaseOutElastic = "easeOutElastic"
easingTypeToText EaseInOutElastic = "easeInOutElastic"
easingTypeToText EaseInBounce = "easeInBounce"
easingTypeToText EaseOutBounce = "easeOutBounce"
easingTypeToText EaseInOutBounce = "easeInOutBounce"
