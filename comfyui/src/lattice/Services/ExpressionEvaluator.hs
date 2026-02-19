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
  , clamp
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
import Lattice.Utils.NumericSafety (ensureFinite, safeSqrt, safeLog)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // time // expressions
-- ════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation over time range
-- Pure function: same inputs → same outputs
timeRamp :: Double -> Double -> Double -> Double -> Double -> Double
timeRamp startTime endTime startValue endValue time =
  if time <= startTime
  then ensureFinite startValue 0.0
  else if time >= endTime
       then ensureFinite endValue 0.0
       else
         let duration = endTime - startTime
         in if not (isFinite duration) || duration == 0
            then ensureFinite startValue 0.0
            else
              let t = (time - startTime) / duration
                  finiteT = ensureFinite t 0.0
              in ensureFinite (startValue + (endValue - startValue) * finiteT) 0.0

-- | Periodic function: (time % period) / period
-- Pure function: same inputs → same outputs
periodic :: Double -> Double -> Double
periodic time period =
  if not (isFinite period) || period == 0
  then 0.0
  else
    let finiteTime = ensureFinite time 0.0
        finitePeriod = ensureFinite period 1.0
        result = (floatMod finiteTime finitePeriod) / finitePeriod
    in ensureFinite result 0.0
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
    let finiteTime = ensureFinite time 0.0
        finiteFreq = ensureFinite frequency 1.0
        finiteAmp = ensureFinite amplitude 1.0
        t = finiteTime * finiteFreq
        result = finiteAmp * 2 * (t - fromIntegral (floor (t + 0.5)))
    in ensureFinite result 0.0

-- | Triangle wave
-- Pure function: same inputs → same outputs
triangle :: Double -> Double -> Double -> Double
triangle time frequency amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFinite time 0.0
        finiteFreq = ensureFinite frequency 1.0
        finiteAmp = ensureFinite amplitude 1.0
        t = finiteTime * finiteFreq
        result = finiteAmp * (2 * abs (2 * (t - fromIntegral (floor (t + 0.5)))) - 1)
    in ensureFinite result 0.0

-- | Square wave
-- Pure function: same inputs → same outputs
square :: Double -> Double -> Double -> Double
square time frequency amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFinite time 0.0
        finiteFreq = ensureFinite frequency 1.0
        finiteAmp = ensureFinite amplitude 1.0
        t = finiteTime * finiteFreq
        result = if (t - fromIntegral (floor t)) < 0.5
                 then finiteAmp
                 else -finiteAmp
    in ensureFinite result 0.0

-- | Sine wave with frequency, amplitude, and phase
-- Pure function: same inputs → same outputs
sine :: Double -> Double -> Double -> Double -> Double
sine time frequency amplitude phase =
  let finiteTime = ensureFinite time 0.0
      finiteFreq = ensureFinite frequency 1.0
      finiteAmp = ensureFinite amplitude 1.0
      finitePhase = ensureFinite phase 0.0
      result = finiteAmp * sin (2 * pi * finiteFreq * finiteTime + finitePhase)
  in ensureFinite result 0.0

-- | Pulse wave with duty cycle
-- Pure function: same inputs → same outputs
pulse :: Double -> Double -> Double -> Double -> Double
pulse time frequency dutyCycle amplitude =
  if not (isFinite time) || not (isFinite frequency) || not (isFinite dutyCycle) || not (isFinite amplitude)
  then 0.0
  else
    let finiteTime = ensureFinite time 0.0
        finiteFreq = ensureFinite frequency 1.0
        finiteDuty = max 0.0 (min 1.0 (ensureFinite dutyCycle 0.5))
        finiteAmp = ensureFinite amplitude 1.0
        t = floatMod (finiteTime * finiteFreq) 1.0
        result = if t < finiteDuty then finiteAmp else 0.0
    in ensureFinite result 0.0
  where
    floatMod a b = a - b * fromIntegral (floor (a / b) :: Int)

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // math // expressions
-- ════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation
-- Pure function: same inputs → same outputs
lerp :: Double -> Double -> Double -> Double
lerp a b t =
  let finiteA = ensureFinite a 0.0
      finiteB = ensureFinite b 0.0
      finiteT = ensureFinite t 0.0
      result = finiteA + (finiteB - finiteA) * finiteT
  in ensureFinite result 0.0

-- | Clamp value between min and max
-- Pure function: same inputs → same outputs
clamp :: Double -> Double -> Double -> Double
clamp value minVal maxVal =
  let finiteVal = ensureFinite value 0.0
      finiteMin = ensureFinite minVal 0.0
      finiteMax = ensureFinite maxVal 0.0
      result = min finiteMax (max finiteMin finiteVal)
  in ensureFinite result 0.0

-- | Map value from one range to another
-- Pure function: same inputs → same outputs
mapRange :: Double -> Double -> Double -> Double -> Double -> Double
mapRange value inMin inMax outMin outMax =
  let finiteVal = ensureFinite value 0.0
      finiteInMin = ensureFinite inMin 0.0
      finiteInMax = ensureFinite inMax 0.0
      finiteOutMin = ensureFinite outMin 0.0
      finiteOutMax = ensureFinite outMax 0.0
      range = finiteInMax - finiteInMin
  in if not (isFinite range) || range == 0
     then ensureFinite finiteOutMin 0.0
     else
       let result = finiteOutMin + (finiteOutMax - finiteOutMin) * ((finiteVal - finiteInMin) / range)
       in ensureFinite result 0.0

-- | Normalize value to 0-1 range
-- Pure function: same inputs → same outputs
normalize :: Double -> Double -> Double -> Double
normalize value minVal maxVal =
  let finiteVal = ensureFinite value 0.0
      finiteMin = ensureFinite minVal 0.0
      finiteMax = ensureFinite maxVal 0.0
      range = finiteMax - finiteMin
  in if not (isFinite range) || range == 0
     then 0.0
     else
       let result = (finiteVal - finiteMin) / range
       in ensureFinite result 0.0

-- | Smoothstep interpolation
-- Pure function: same inputs → same outputs
smoothstep :: Double -> Double -> Double -> Double
smoothstep edge0 edge1 x =
  let finiteEdge0 = ensureFinite edge0 0.0
      finiteEdge1 = ensureFinite edge1 0.0
      finiteX = ensureFinite x 0.0
      range = finiteEdge1 - finiteEdge0
  in if not (isFinite range) || range == 0
     then if finiteX < finiteEdge0 then 0.0 else 1.0
     else
       let t = clamp ((finiteX - finiteEdge0) / range) 0.0 1.0
           result = t * t * (3 - 2 * t)
       in ensureFinite result 0.0

-- | Smootherstep interpolation
-- Pure function: same inputs → same outputs
smootherstep :: Double -> Double -> Double -> Double
smootherstep edge0 edge1 x =
  let finiteEdge0 = ensureFinite edge0 0.0
      finiteEdge1 = ensureFinite edge1 0.0
      finiteX = ensureFinite x 0.0
      range = finiteEdge1 - finiteEdge0
  in if not (isFinite range) || range == 0
     then if finiteX < finiteEdge0 then 0.0 else 1.0
     else
       let t = clamp ((finiteX - finiteEdge0) / range) 0.0 1.0
           result = t * t * t * (t * (t * 6 - 15) + 10)
       in ensureFinite result 0.0

-- | Safe modulo (handles negative numbers correctly)
-- Pure function: same inputs → same outputs
modSafe :: Double -> Double -> Double
modSafe a b =
  if not (isFinite b) || b == 0
  then 0.0
  else if not (isFinite a)
       then 0.0
       else
         let finiteA = ensureFinite a 0.0
             finiteB = ensureFinite b 1.0
             result = modSafeRem finiteA finiteB
         in ensureFinite result 0.0
  where
    modSafeRem a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | 2D distance calculation
-- Pure function: same inputs → same outputs
distance :: Double -> Double -> Double -> Double -> Double
distance x1 y1 x2 y2 =
  let finiteX1 = ensureFinite x1 0.0
      finiteY1 = ensureFinite y1 0.0
      finiteX2 = ensureFinite x2 0.0
      finiteY2 = ensureFinite y2 0.0
      dx = finiteX2 - finiteX1
      dy = finiteY2 - finiteY1
      squaredDist = dx * dx + dy * dy
      -- squaredDist is always >= 0, so sqrt is safe
      result = safeSqrt squaredDist
  in ensureFinite result 0.0

-- | Angle between two points (in radians)
-- Pure function: same inputs → same outputs
angleBetween :: Double -> Double -> Double -> Double -> Double
angleBetween x1 y1 x2 y2 =
  let finiteX1 = ensureFinite x1 0.0
      finiteY1 = ensureFinite y1 0.0
      finiteX2 = ensureFinite x2 0.0
      finiteY2 = ensureFinite y2 0.0
      result = atan2 (finiteY2 - finiteY1) (finiteX2 - finiteX1)
  in ensureFinite result 0.0

-- | Convert degrees to radians
-- Pure function: same inputs → same outputs
degreesToRadians :: Double -> Double
degreesToRadians degrees =
  let finiteDegrees = ensureFinite degrees 0.0
      result = (finiteDegrees * pi) / 180.0
  in ensureFinite result 0.0

-- | Convert radians to degrees
-- Pure function: same inputs → same outputs
radiansToDegrees :: Double -> Double
radiansToDegrees radians =
  let finiteRadians = ensureFinite radians 0.0
      result = (finiteRadians * 180.0) / pi
  in ensureFinite result 0.0

-- | Deterministic seeded random (sine-based PRNG)
-- Pure function: same inputs → same outputs
seedRandom :: Double -> Double -> Double -> Double
seedRandom seed minVal maxVal =
  let finiteSeed = ensureFinite seed 0.0
      finiteMin = ensureFinite minVal 0.0
      finiteMax = ensureFinite maxVal 1.0
      x = sin (finiteSeed * 12.9898) * 43758.5453
      rand = x - fromIntegral (floor x)
      result = finiteMin + rand * (finiteMax - finiteMin)
  in ensureFinite result 0.0

-- | Gaussian random with seed (Box-Muller transform)
-- Pure function: same inputs → same outputs
gaussRandom :: Double -> Double -> Double -> Double
gaussRandom mean stdDev seed =
  if not (isFinite mean) || not (isFinite stdDev) || not (isFinite seed)
  then 0.0
  else
    let finiteMean = ensureFinite mean 0.0
        finiteStdDev = ensureFinite stdDev 1.0
        finiteSeed = ensureFinite seed 12345.0
        seededRand s = let x = sin (s * 12.9898) * 43758.5453
                       in x - fromIntegral (floor x)
        u1Raw = seededRand finiteSeed
        u1 = if isFinite u1Raw then max 0.0001 u1Raw else 0.0001
        u2Raw = seededRand (finiteSeed + 1.0)
        u2 = if isFinite u2Raw then u2Raw else 0.0
        -- u1 is guaranteed >= 0.0001, so log is safe
        logU1 = safeLog u1 0.0
        -- -2 * logU1 is always >= 0 (logU1 <= 0 since u1 <= 1), so sqrt is safe
        z0 = safeSqrt (-2 * logU1) * cos (2 * pi * u2)
        result = finiteMean + z0 * finiteStdDev
    in ensureFinite result 0.0

-- ════════════════════════════════════════════════════════════════════════════
--                                         // expression // easing // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Expression ease function (cubic ease in/out)
-- Pure function: same inputs → same outputs
-- Returns scalar or array based on input types
expressionEase :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEase t tMin tMax vMin vMax =
  let finiteT = ensureFinite t 0.0
      finiteTMin = ensureFinite tMin 0.0
      finiteTMax = ensureFinite tMax 0.0
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
         let scalarVal = ensureFinite scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFinite scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]

-- | Expression ease in function (cubic)
-- Pure function: same inputs → same outputs
expressionEaseIn :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEaseIn t tMin tMax vMin vMax =
  let finiteT = ensureFinite t 0.0
      finiteTMin = ensureFinite tMin 0.0
      finiteTMax = ensureFinite tMax 0.0
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
         let scalarVal = ensureFinite scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFinite scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]

-- | Expression ease out function (cubic)
-- Pure function: same inputs → same outputs
expressionEaseOut :: Double -> Double -> Double -> Either [Double] Double -> Either [Double] Double -> Either [Double] Double
expressionEaseOut t tMin tMax vMin vMax =
  let finiteT = ensureFinite t 0.0
      finiteTMin = ensureFinite tMin 0.0
      finiteTMax = ensureFinite tMax 0.0
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
         let scalarVal = ensureFinite scalarMax 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair (safeGet arrMin i) scalarVal | i <- [0 .. length arrMin - 1]]
       (Right scalarMin, Left arrMax) ->
         let scalarVal = ensureFinite scalarMin 0.0
             safeGet arr idx =
               let v = safeArrayGet arr idx 0.0
               in if isFinite v then v else 0.0
             lerpPair aVal bVal = aVal + (bVal - aVal) * eased
         in Left [lerpPair scalarVal (safeGet arrMax i) | i <- [0 .. length arrMax - 1]]
