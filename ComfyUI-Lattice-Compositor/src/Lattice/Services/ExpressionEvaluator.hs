-- |
-- Module      : Lattice.Services.ExpressionEvaluator
-- Description : Pure expression evaluation functions (time, math, easing)
-- 
-- Migrated from ui/src/services/expressions/expressionEvaluator.ts
-- Pure functions for time expressions, math expressions, and easing
-- Note: Custom expression evaluation (SES sandbox) deferred (security boundary)
--

module Lattice.Services.ExpressionEvaluator
  ( -- Time expressions
    timeRamp
  , periodic
  , sawtooth
  , triangle
  , square
  , sine
  , pulse
  -- Math expressions
  , lerp
  , clampD
  , mapRange
  , normalize
  , smoothstep
  , smootherstep
  , modSafe
  , distance
  , angleBetween
  , degreesToRadians
  , radiansToDegrees
  , seedRandom
  , gaussRandom
  -- Easing expressions
  , expressionEase
  , expressionEaseIn
  , expressionEaseOut
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (ensureFiniteD, safeSqrtD, safeLog)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ============================================================================
-- TIME EXPRESSIONS
-- ============================================================================

-- | Linear interpolation over time range
-- Pure function: same inputs → same outputs
timeRamp :: Double -> Double -> Double -> Double -> Double -> Double
timeRamp startTime endTime startValue endValue time =
  if time <= startTime
  then ensureFiniteD startValue 0.0
  else if time >= endTime
       then ensureFiniteD endValue 0.0
       else
         let duration = endTime - startTime
         in if not (isFinite duration) || duration == 0
            then ensureFiniteD startValue 0.0
            else
              let t = (time - startTime) / duration
                  finiteT = ensureFiniteD t 0.0
              in ensureFiniteD (startValue + (endValue - startValue) * finiteT) 0.0

-- | Periodic function: (time % period) / period
-- Pure function: same inputs → same outputs
periodic :: Double -> Double -> Double
periodic time period =
  if not (isFinite period) || period == 0
  then 0.0
  else
    let finiteTime = ensureFiniteD time 0.0
        finitePeriod = ensureFiniteD period 1.0
        result = (floatMod finiteTime finitePeriod) / finitePeriod
    in ensureFiniteD result 0.0
  where
    -- Floating-point modulo (Prelude mod is Integral only)
    floatMod a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Sawtooth wave
-- Pure function: same inputs → same outputs
sawtooth :: Double -> Double -> Double -> Double
sawtooth time frequency amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFiniteD time 0.0
        finiteFreq = ensureFiniteD frequency 1.0
        finiteAmp = ensureFiniteD amplitude 1.0
        t = finiteTime * finiteFreq
        result = finiteAmp * 2 * (t - fromIntegral (floor (t + 0.5)))
    in ensureFiniteD result 0.0

-- | Triangle wave
-- Pure function: same inputs → same outputs
triangle :: Double -> Double -> Double -> Double
triangle time frequency amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFiniteD time 0.0
        finiteFreq = ensureFiniteD frequency 1.0
        finiteAmp = ensureFiniteD amplitude 1.0
        t = finiteTime * finiteFreq
        result = finiteAmp * (2 * abs (2 * (t - fromIntegral (floor (t + 0.5)))) - 1)
    in ensureFiniteD result 0.0

-- | Square wave
-- Pure function: same inputs → same outputs
square :: Double -> Double -> Double -> Double
square time frequency amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFiniteD time 0.0
        finiteFreq = ensureFiniteD frequency 1.0
        finiteAmp = ensureFiniteD amplitude 1.0
        t = finiteTime * finiteFreq
        result = if (t - fromIntegral (floor t)) < 0.5
                 then finiteAmp
                 else -finiteAmp
    in ensureFiniteD result 0.0

-- | Sine wave with frequency, amplitude, and phase
-- Pure function: same inputs → same outputs
sine :: Double -> Double -> Double -> Double -> Double
sine time frequency amplitude phase =
  let finiteTime = ensureFiniteD time 0.0
      finiteFreq = ensureFiniteD frequency 1.0
      finiteAmp = ensureFiniteD amplitude 1.0
      finitePhase = ensureFiniteD phase 0.0
      result = finiteAmp * sin (2 * pi * finiteFreq * finiteTime + finitePhase)
  in ensureFiniteD result 0.0

-- | Pulse wave with duty cycle
-- Pure function: same inputs → same outputs
pulse :: Double -> Double -> Double -> Double -> Double
pulse time frequency dutyCycle amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite dutyCycle) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFiniteD time 0.0
        finiteFreq = ensureFiniteD frequency 1.0
        finiteDuty = max 0.0 (min 1.0 (ensureFiniteD dutyCycle 0.5))
        finiteAmp = ensureFiniteD amplitude 1.0
        t = floatMod (finiteTime * finiteFreq) 1.0
        result = if t < finiteDuty then finiteAmp else 0.0
    in ensureFiniteD result 0.0
  where
    floatMod a b = a - b * fromIntegral (floor (a / b) :: Int)

-- ============================================================================
-- MATH EXPRESSIONS
-- ============================================================================

-- | Linear interpolation
-- Pure function: same inputs → same outputs
lerp :: Double -> Double -> Double -> Double
lerp a b t =
  let finiteA = ensureFiniteD a 0.0
      finiteB = ensureFiniteD b 0.0
      finiteT = ensureFiniteD t 0.0
      result = finiteA + (finiteB - finiteA) * finiteT
  in ensureFiniteD result 0.0

-- | Clamp value between min and max
-- Pure function: same inputs → same outputs
clampD :: Double -> Double -> Double -> Double
clampD value minVal maxVal =
  let finiteVal = ensureFiniteD value 0.0
      finiteMin = ensureFiniteD minVal 0.0
      finiteMax = ensureFiniteD maxVal 0.0
      result = min finiteMax (max finiteMin finiteVal)
  in ensureFiniteD result 0.0

-- | Map value from one range to another
-- Pure function: same inputs → same outputs
mapRange :: Double -> Double -> Double -> Double -> Double -> Double
mapRange value inMin inMax outMin outMax =
  let finiteVal = ensureFiniteD value 0.0
      finiteInMin = ensureFiniteD inMin 0.0
      finiteInMax = ensureFiniteD inMax 0.0
      finiteOutMin = ensureFiniteD outMin 0.0
      finiteOutMax = ensureFiniteD outMax 0.0
      range = finiteInMax - finiteInMin
  in if not (isFinite range) || range == 0
     then ensureFiniteD finiteOutMin 0.0
     else
       let result = finiteOutMin + (finiteOutMax - finiteOutMin) * ((finiteVal - finiteInMin) / range)
       in ensureFiniteD result 0.0

-- | Normalize value to 0-1 range
-- Pure function: same inputs → same outputs
normalize :: Double -> Double -> Double -> Double
normalize value minVal maxVal =
  let finiteVal = ensureFiniteD value 0.0
      finiteMin = ensureFiniteD minVal 0.0
      finiteMax = ensureFiniteD maxVal 0.0
      range = finiteMax - finiteMin
  in if not (isFinite range) || range == 0
     then 0.0
     else
       let result = (finiteVal - finiteMin) / range
       in ensureFiniteD result 0.0

-- | Smoothstep interpolation
-- Pure function: same inputs → same outputs
smoothstep :: Double -> Double -> Double -> Double
smoothstep edge0 edge1 x =
  let finiteEdge0 = ensureFiniteD edge0 0.0
      finiteEdge1 = ensureFiniteD edge1 0.0
      finiteX = ensureFiniteD x 0.0
      range = finiteEdge1 - finiteEdge0
  in if not (isFinite range) || range == 0
     then if finiteX < finiteEdge0 then 0.0 else 1.0
     else
       let t = clampD ((finiteX - finiteEdge0) / range) 0.0 1.0
           result = t * t * (3 - 2 * t)
       in ensureFiniteD result 0.0

-- | Smootherstep interpolation
-- Pure function: same inputs → same outputs
smootherstep :: Double -> Double -> Double -> Double
smootherstep edge0 edge1 x =
  let finiteEdge0 = ensureFiniteD edge0 0.0
      finiteEdge1 = ensureFiniteD edge1 0.0
      finiteX = ensureFiniteD x 0.0
      range = finiteEdge1 - finiteEdge0
  in if not (isFinite range) || range == 0
     then if finiteX < finiteEdge0 then 0.0 else 1.0
     else
       let t = clampD ((finiteX - finiteEdge0) / range) 0.0 1.0
           result = t * t * t * (t * (t * 6 - 15) + 10)
       in ensureFiniteD result 0.0

-- | Safe modulo (handles negative numbers correctly)
-- Pure function: same inputs → same outputs
modSafe :: Double -> Double -> Double
modSafe a b =
  if not (isFinite b) || b == 0
  then 0.0
  else if not (isFinite a)
       then 0.0
       else
         let finiteA = ensureFiniteD a 0.0
             finiteB = ensureFiniteD b 1.0
             result = modSafeRem finiteA finiteB
         in ensureFiniteD result 0.0
  where
    modSafeRem a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | 2D distance calculation
-- Pure function: same inputs → same outputs
distance :: Double -> Double -> Double -> Double -> Double
distance x1 y1 x2 y2 =
  let finiteX1 = ensureFiniteD x1 0.0
      finiteY1 = ensureFiniteD y1 0.0
      finiteX2 = ensureFiniteD x2 0.0
      finiteY2 = ensureFiniteD y2 0.0
      dx = finiteX2 - finiteX1
      dy = finiteY2 - finiteY1
      squaredDist = dx * dx + dy * dy
      -- squaredDist is always >= 0, so sqrt is safe
      result = safeSqrtD squaredDist
  in ensureFiniteD result 0.0

-- | Angle between two points (in radians)
-- Pure function: same inputs → same outputs
angleBetween :: Double -> Double -> Double -> Double -> Double
angleBetween x1 y1 x2 y2 =
  let finiteX1 = ensureFiniteD x1 0.0
      finiteY1 = ensureFiniteD y1 0.0
      finiteX2 = ensureFiniteD x2 0.0
      finiteY2 = ensureFiniteD y2 0.0
      result = atan2 (finiteY2 - finiteY1) (finiteX2 - finiteX1)
  in ensureFiniteD result 0.0

-- | Convert degrees to radians
-- Pure function: same inputs → same outputs
degreesToRadians :: Double -> Double
degreesToRadians degrees =
  let finiteDegrees = ensureFiniteD degrees 0.0
      result = (finiteDegrees * pi) / 180.0
  in ensureFiniteD result 0.0

-- | Convert radians to degrees
-- Pure function: same inputs → same outputs
radiansToDegrees :: Double -> Double
radiansToDegrees radians =
  let finiteRadians = ensureFiniteD radians 0.0
      result = (finiteRadians * 180.0) / pi
  in ensureFiniteD result 0.0

-- | Deterministic seeded random (sine-based PRNG)
-- Pure function: same inputs → same outputs
seedRandom :: Double -> Double -> Double -> Double
seedRandom seed minVal maxVal =
  let finiteSeed = ensureFiniteD seed 0.0
      finiteMin = ensureFiniteD minVal 0.0
      finiteMax = ensureFiniteD maxVal 1.0
      x = sin (finiteSeed * 12.9898) * 43758.5453
      rand = x - fromIntegral (floor x)
      result = finiteMin + rand * (finiteMax - finiteMin)
  in ensureFiniteD result 0.0

-- | Gaussian random with seed (Box-Muller transform)
-- Pure function: same inputs → same outputs
gaussRandom :: Double -> Double -> Double -> Double
gaussRandom mean stdDev seed =
  if not (isFinite mean) || not (isFinite stdDev) || not (isFinite seed)
  then 0.0
  else
    let finiteMean = ensureFiniteD mean 0.0
        finiteStdDev = ensureFiniteD stdDev 1.0
        finiteSeed = ensureFiniteD seed 12345.0
        seededRand s = let x = sin (s * 12.9898) * 43758.5453
                       in x - fromIntegral (floor x)
        u1Raw = seededRand finiteSeed
        u1 = if isFinite u1Raw then max 0.0001 u1Raw else 0.0001
        u2Raw = seededRand (finiteSeed + 1.0)
        u2 = if isFinite u2Raw then u2Raw else 0.0
        -- u1 is guaranteed >= 0.0001, so log is safe
        logU1 = safeLog u1 0.0
        -- -2 * logU1 is always >= 0 (logU1 <= 0 since u1 <= 1), so sqrt is safe
        z0 = safeSqrtD (-2 * logU1) * cos (2 * pi * u2)
        result = finiteMean + z0 * finiteStdDev
    in ensureFiniteD result 0.0

-- ============================================================================
-- EXPRESSION EASING FUNCTIONS
-- ============================================================================

-- | Expression ease function (cubic ease in/out)
-- Pure function: same inputs → same outputs
-- Returns scalar or array based on input types
expressionEase :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEase t tMin tMax vMin vMax =
  let finiteT = ensureFiniteD t 0.0
      finiteTMin = ensureFiniteD tMin 0.0
      finiteTMax = ensureFiniteD tMax 0.0
      range = finiteTMax - finiteTMin
      normalized = if not (isFinite range) || range == 0
                   then if finiteT < finiteTMin then 0.0 else 1.0
                   else max 0.0 (min 1.0 ((finiteT - finiteTMin) / range))
      eased = if normalized < 0.5
              then 4 * normalized * normalized * normalized
              else 1 - ((-2 * normalized + 2) ** 3) / 2
  in case (vMin, vMax) :: (Either [Double] Double, Either [Double] Double) of
       (Left arrMin, Left arrMax) ->
         let maxLen = max (length arrMin) (length arrMax)
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) (safeGet arrMax i) | i <- [0 .. maxLen - 1]]
       (Right scalarMin, Right scalarMax) ->
         Right (scalarMin + (scalarMax - scalarMin) * eased)
       (Left arrMin, Right scalarMax) ->
         let scalarVal = ensureFiniteD scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFiniteD scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]

-- | Expression ease in function (cubic)
-- Pure function: same inputs → same outputs
expressionEaseIn :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEaseIn t tMin tMax vMin vMax =
  let finiteT = ensureFiniteD t 0.0
      finiteTMin = ensureFiniteD tMin 0.0
      finiteTMax = ensureFiniteD tMax 0.0
      range = finiteTMax - finiteTMin
      normalized = if not (isFinite range) || range == 0
                   then if finiteT < finiteTMin then 0.0 else 1.0
                   else max 0.0 (min 1.0 ((finiteT - finiteTMin) / range))
      eased = normalized * normalized * normalized
  in case (vMin, vMax) :: (Either [Double] Double, Either [Double] Double) of
       (Left arrMin, Left arrMax) ->
         let maxLen = max (length arrMin) (length arrMax)
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) (safeGet arrMax i) | i <- [0 .. maxLen - 1]]
       (Right scalarMin, Right scalarMax) ->
         Right (scalarMin + (scalarMax - scalarMin) * eased)
       (Left arrMin, Right scalarMax) ->
         let scalarVal = ensureFiniteD scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFiniteD scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]

-- | Expression ease out function (cubic)
-- Pure function: same inputs → same outputs
expressionEaseOut :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEaseOut t tMin tMax vMin vMax =
  let finiteT = ensureFiniteD t 0.0
      finiteTMin = ensureFiniteD tMin 0.0
      finiteTMax = ensureFiniteD tMax 0.0
      range = finiteTMax - finiteTMin
      normalized = if not (isFinite range) || range == 0
                   then if finiteT < finiteTMin then 0.0 else 1.0
                   else max 0.0 (min 1.0 ((finiteT - finiteTMin) / range))
      eased = 1 - (1 - normalized) ** 3
  in case (vMin, vMax) :: (Either [Double] Double, Either [Double] Double) of
       (Left arrMin, Left arrMax) ->
         let maxLen = max (length arrMin) (length arrMax)
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) (safeGet arrMax i) | i <- [0 .. maxLen - 1]]
       (Right scalarMin, Right scalarMax) ->
         Right (scalarMin + (scalarMax - scalarMin) * eased)
       (Left arrMin, Right scalarMax) ->
         let scalarVal = ensureFiniteD scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFiniteD scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]
