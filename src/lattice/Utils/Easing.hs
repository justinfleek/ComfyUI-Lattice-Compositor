-- |
-- Module      : Lattice.Utils.Easing
-- Description : Easing functions for animation interpolation
-- 
-- Migrated from ui/src/services/easing.ts
-- Pure easing functions that take normalized time (0-1) and return eased value (0-1)
-- Ported from mojs easing library
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Easing
  ( -- Easing function type
    EasingFunction
  -- Linear
  , linear
  -- Sine
  , easeInSine
  , easeOutSine
  , easeInOutSine
  -- Quad (power of 2)
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  -- Cubic (power of 3)
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  -- Quart (power of 4)
  , easeInQuart
  , easeOutQuart
  , easeInOutQuart
  -- Quint (power of 5)
  , easeInQuint
  , easeOutQuint
  , easeInOutQuint
  -- Expo (exponential)
  , easeInExpo
  , easeOutExpo
  , easeInOutExpo
  -- Circ (circular)
  , easeInCirc
  , easeOutCirc
  , easeInOutCirc
  -- Back (overshoot)
  , easeInBack
  , easeOutBack
  , easeInOutBack
  -- Elastic
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  -- Bounce
  , easeInBounce
  , easeOutBounce
  , easeInOutBounce
  -- Helper functions
  , getEasing
  , applyEasing
  , interpolateWithEasing
  ) where

import Lattice.Utils.NumericSafety
  ( clamp01
  )

-- | Easing function type - takes normalized time (0-1) and returns eased value (0-1)
type EasingFunction = Double -> Double

-- Constants for specific easing calculations
c1 :: Double
c1 = 1.70158

c2 :: Double
c2 = c1 * 1.525

c3 :: Double
c3 = c1 + 1

c4 :: Double
c4 = 2 * pi / 3

c5 :: Double
c5 = 2 * pi / 4.5

-- ============================================================================
-- LINEAR
-- ============================================================================

-- | Linear - no easing
linear :: EasingFunction
linear t = t

-- ============================================================================
-- SINE
-- ============================================================================

-- | Sine easing - ease in
easeInSine :: EasingFunction
easeInSine t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = 1 - cos (t * pi / 2)

-- | Sine easing - ease out
easeOutSine :: EasingFunction
easeOutSine t = sin (t * pi / 2)

-- | Sine easing - ease in out
easeInOutSine :: EasingFunction
easeInOutSine t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = -(cos (pi * t) - 1) / 2

-- ============================================================================
-- QUAD (power of 2)
-- ============================================================================

-- | Quad easing - ease in
easeInQuad :: EasingFunction
easeInQuad t = t * t

-- | Quad easing - ease out
easeOutQuad :: EasingFunction
easeOutQuad t = 1 - (1 - t) * (1 - t)

-- | Quad easing - ease in out
easeInOutQuad :: EasingFunction
easeInOutQuad t
  | t < 0.5 = 2 * t * t
  | otherwise = 1 - ((-2 * t + 2) ** 2) / 2

-- ============================================================================
-- CUBIC (power of 3)
-- ============================================================================

-- | Cubic easing - ease in
easeInCubic :: EasingFunction
easeInCubic t = t * t * t

-- | Cubic easing - ease out
easeOutCubic :: EasingFunction
easeOutCubic t = 1 - (1 - t) ** 3

-- | Cubic easing - ease in out
easeInOutCubic :: EasingFunction
easeInOutCubic t
  | t < 0.5 = 4 * t * t * t
  | otherwise = 1 - ((-2 * t + 2) ** 3) / 2

-- ============================================================================
-- QUART (power of 4)
-- ============================================================================

-- | Quart easing - ease in
easeInQuart :: EasingFunction
easeInQuart t = t * t * t * t

-- | Quart easing - ease out
easeOutQuart :: EasingFunction
easeOutQuart t = 1 - (1 - t) ** 4

-- | Quart easing - ease in out
easeInOutQuart :: EasingFunction
easeInOutQuart t
  | t < 0.5 = 8 * t * t * t * t
  | otherwise = 1 - ((-2 * t + 2) ** 4) / 2

-- ============================================================================
-- QUINT (power of 5)
-- ============================================================================

-- | Quint easing - ease in
easeInQuint :: EasingFunction
easeInQuint t = t * t * t * t * t

-- | Quint easing - ease out
easeOutQuint :: EasingFunction
easeOutQuint t = 1 - (1 - t) ** 5

-- | Quint easing - ease in out
easeInOutQuint :: EasingFunction
easeInOutQuint t
  | t < 0.5 = 16 * t * t * t * t * t
  | otherwise = 1 - ((-2 * t + 2) ** 5) / 2

-- ============================================================================
-- EXPO (exponential)
-- ============================================================================

-- | Expo easing - ease in
easeInExpo :: EasingFunction
easeInExpo t
  | t == 0 = 0
  | otherwise = 2 ** (10 * t - 10)

-- | Expo easing - ease out
easeOutExpo :: EasingFunction
easeOutExpo t
  | t == 1 = 1
  | otherwise = 1 - 2 ** (-10 * t)

-- | Expo easing - ease in out
easeInOutExpo :: EasingFunction
easeInOutExpo t
  | t == 0 = 0
  | t == 1 = 1
  | t < 0.5 = 2 ** (20 * t - 10) / 2
  | otherwise = (2 - 2 ** (-20 * t + 10)) / 2

-- ============================================================================
-- CIRC (circular)
-- ============================================================================

-- | Circ easing - ease in
easeInCirc :: EasingFunction
easeInCirc t = 1 - sqrt (1 - t ** 2)

-- | Circ easing - ease out
easeOutCirc :: EasingFunction
easeOutCirc t = sqrt (1 - (t - 1) ** 2)

-- | Circ easing - ease in out
easeInOutCirc :: EasingFunction
easeInOutCirc t
  | t < 0.5 = (1 - sqrt (1 - (2 * t) ** 2)) / 2
  | otherwise = (sqrt (1 - (-2 * t + 2) ** 2) + 1) / 2

-- ============================================================================
-- BACK (overshoot)
-- ============================================================================

-- | Back easing - ease in
easeInBack :: EasingFunction
easeInBack t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = c3 * t * t * t - c1 * t * t

-- | Back easing - ease out
easeOutBack :: EasingFunction
easeOutBack t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2

-- | Back easing - ease in out
easeInOutBack :: EasingFunction
easeInOutBack t
  | t == 0 = 0
  | t == 1 = 1
  | t < 0.5 = ((2 * t) ** 2 * ((c2 + 1) * 2 * t - c2)) / 2
  | otherwise = ((2 * t - 2) ** 2 * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2

-- ============================================================================
-- ELASTIC
-- ============================================================================

-- | Elastic easing - ease in
easeInElastic :: EasingFunction
easeInElastic t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = -(2 ** (10 * t - 10)) * sin ((t * 10 - 10.75) * c4)

-- | Elastic easing - ease out
easeOutElastic :: EasingFunction
easeOutElastic t
  | t == 0 = 0
  | t == 1 = 1
  | otherwise = 2 ** (-10 * t) * sin ((t * 10 - 0.75) * c4) + 1

-- | Elastic easing - ease in out
easeInOutElastic :: EasingFunction
easeInOutElastic t
  | t == 0 = 0
  | t == 1 = 1
  | t < 0.5 = -(2 ** (20 * t - 10) * sin ((20 * t - 11.125) * c5)) / 2
  | otherwise = (2 ** (-20 * t + 10) * sin ((20 * t - 11.125) * c5)) / 2 + 1

-- ============================================================================
-- BOUNCE
-- ============================================================================

-- | Bounce easing - ease out
easeOutBounce :: EasingFunction
easeOutBounce t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1 / d1
       then n1 * t * t
       else if t < 2 / d1
         then n1 * (t - 1.5 / d1) * (t - 1.5 / d1) + 0.75
         else if t < 2.5 / d1
           then n1 * (t - 2.25 / d1) * (t - 2.25 / d1) + 0.9375
           else n1 * (t - 2.625 / d1) * (t - 2.625 / d1) + 0.984375

-- | Bounce easing - ease in
easeInBounce :: EasingFunction
easeInBounce t = 1 - easeOutBounce (1 - t)

-- | Bounce easing - ease in out
easeInOutBounce :: EasingFunction
easeInOutBounce t
  | t < 0.5 = (1 - easeOutBounce (1 - 2 * t)) / 2
  | otherwise = (1 + easeOutBounce (2 * t - 1)) / 2

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Get an easing function by name
-- Returns linear if the name is not found
getEasing :: String -> EasingFunction
getEasing name = case name of
  "linear" -> linear
  "easeInSine" -> easeInSine
  "easeOutSine" -> easeOutSine
  "easeInOutSine" -> easeInOutSine
  "easeInQuad" -> easeInQuad
  "easeOutQuad" -> easeOutQuad
  "easeInOutQuad" -> easeInOutQuad
  "easeInCubic" -> easeInCubic
  "easeOutCubic" -> easeOutCubic
  "easeInOutCubic" -> easeInOutCubic
  "easeInQuart" -> easeInQuart
  "easeOutQuart" -> easeOutQuart
  "easeInOutQuart" -> easeInOutQuart
  "easeInQuint" -> easeInQuint
  "easeOutQuint" -> easeOutQuint
  "easeInOutQuint" -> easeInOutQuint
  "easeInExpo" -> easeInExpo
  "easeOutExpo" -> easeOutExpo
  "easeInOutExpo" -> easeInOutExpo
  "easeInCirc" -> easeInCirc
  "easeOutCirc" -> easeOutCirc
  "easeInOutCirc" -> easeInOutCirc
  "easeInBack" -> easeInBack
  "easeOutBack" -> easeOutBack
  "easeInOutBack" -> easeInOutBack
  "easeInElastic" -> easeInElastic
  "easeOutElastic" -> easeOutElastic
  "easeInOutElastic" -> easeInOutElastic
  "easeInBounce" -> easeInBounce
  "easeOutBounce" -> easeOutBounce
  "easeInOutBounce" -> easeInOutBounce
  _ -> linear  -- Fallback to linear for unknown easings

-- | Apply easing to a value
applyEasing :: Double -> String -> Double
applyEasing t easingName = getEasing easingName (clamp01 t)

-- | Interpolate a value with easing
interpolateWithEasing :: Double -> Double -> Double -> String -> Double
interpolateWithEasing start end t easingName =
  let easedT = applyEasing t easingName
  in start + (end - start) * easedT
