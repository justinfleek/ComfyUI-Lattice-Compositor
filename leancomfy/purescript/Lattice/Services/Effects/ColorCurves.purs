-- | Lattice.Services.Effects.ColorCurves - Curve-based Color Adjustments
-- |
-- | Pure mathematical functions for curve-based color adjustments:
-- | - Cubic Bezier curve interpolation
-- | - Curve LUT (lookup table) generation
-- | - S-curve and lift curve presets
-- |
-- | All functions operate on normalized [0,1] color values.
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.Effects.ColorCurves
  ( CurvePoint
  , CurveParams
  , defaultCurveParams
  , cubicBezier
  , buildCurveLUT
  , applyCurves
  , createSCurve
  , createLiftCurve
  , createGammaCurve
  ) where

import Prelude

import Data.Array ((..), length, index, mapWithIndex)
import Data.Int (round, toNumber)
import Data.Maybe (fromMaybe)
import Data.Number (abs, pow) as Number
import Data.Tuple (Tuple(..))
import Math (max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A point on a curve with input/output values
type CurvePoint =
  { input :: Number   -- Input value [0,1]
  , output :: Number  -- Output value [0,1]
  }

-- | Curve parameters for each channel
type CurveParams =
  { master :: Array CurvePoint  -- Master curve (affects all channels)
  , red :: Array CurvePoint     -- Red channel curve
  , green :: Array CurvePoint   -- Green channel curve
  , blue :: Array CurvePoint    -- Blue channel curve
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Identity curve (no change)
identityCurve :: Array CurvePoint
identityCurve =
  [ { input: 0.0, output: 0.0 }
  , { input: 1.0, output: 1.0 }
  ]

-- | Default curves (identity on all channels)
defaultCurveParams :: CurveParams
defaultCurveParams =
  { master: identityCurve
  , red: identityCurve
  , green: identityCurve
  , blue: identityCurve
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Safe array access with default
safeIndex :: forall a. Array a -> Int -> a -> a
safeIndex arr i def = fromMaybe def (index arr i)

--------------------------------------------------------------------------------
-- Cubic Bezier
--------------------------------------------------------------------------------

-- | Cubic Bezier interpolation for curve segment
cubicBezier :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezier t p0 p1 p2 p3 =
  let t' = clamp01 t
      mt = 1.0 - t'
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t' * t'
      t3 = t2 * t'
  in mt3 * p0 + 3.0 * mt2 * t' * p1 + 3.0 * mt * t2 * p2 + t3 * p3

-- | Find curve segment containing input value
findSegment :: Array CurvePoint -> Number -> Tuple CurvePoint CurvePoint
findSegment points x
  | length points < 2 = Tuple { input: 0.0, output: 0.0 } { input: 1.0, output: 1.0 }
  | otherwise = go 0
  where
    defaultP1 = { input: 0.0, output: 0.0 }
    defaultP2 = { input: 1.0, output: 1.0 }
    go i
      | i >= length points - 1 =
          Tuple (safeIndex points (length points - 2) defaultP1)
                (safeIndex points (length points - 1) defaultP2)
      | otherwise =
          let p1 = safeIndex points i defaultP1
              p2 = safeIndex points (i + 1) defaultP2
          in if x <= p2.input then Tuple p1 p2
             else go (i + 1)

-- | Interpolate on curve at given input
interpolateCurve :: Array CurvePoint -> Number -> Number
interpolateCurve points x
  | length points < 2 = x
  | otherwise =
      let Tuple p1 p2 = findSegment points x
          inRange = p2.input - p1.input
          t = if inRange > 0.0001
              then (x - p1.input) / inRange
              else 0.0
          cp1 = p1.output + (p2.output - p1.output) / 3.0
          cp2 = p2.output - (p2.output - p1.output) / 3.0
      in cubicBezier t p1.output cp1 cp2 p2.output

--------------------------------------------------------------------------------
-- Lookup Table Generation
--------------------------------------------------------------------------------

-- | Build 256-entry lookup table from curve points
buildCurveLUT :: Array CurvePoint -> Array Int
buildCurveLUT points =
  map (\i ->
    let normalized = toNumber i / 255.0
        result = interpolateCurve points normalized
    in round (max 0.0 (min 255.0 (result * 255.0)))
  ) (0 .. 255)

-- | Apply curve using LUT (safe indexing)
applyCurveLUT :: Array Int -> Number -> Number
applyCurveLUT lut value =
  let idx = round (clamp01 value * 255.0)
      safeIdx = max 0 (min 255 idx)
      result = safeIndex lut safeIdx idx
  in toNumber result / 255.0

-- | Apply curves to RGB
applyCurves :: CurveParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
applyCurves params (Tuple r (Tuple g b)) =
  let masterLUT = buildCurveLUT params.master
      redLUT = buildCurveLUT params.red
      greenLUT = buildCurveLUT params.green
      blueLUT = buildCurveLUT params.blue
      r' = applyCurveLUT redLUT (applyCurveLUT masterLUT r)
      g' = applyCurveLUT greenLUT (applyCurveLUT masterLUT g)
      b' = applyCurveLUT blueLUT (applyCurveLUT masterLUT b)
  in Tuple (clamp01 r') (Tuple (clamp01 g') (clamp01 b'))

--------------------------------------------------------------------------------
-- Curve Presets
--------------------------------------------------------------------------------

-- | Create S-curve for contrast enhancement
createSCurve :: Number -> Array CurvePoint
createSCurve amount =
  let amt = clamp01 (Number.abs amount) * 0.25
      sign = if amount < 0.0 then -1.0 else 1.0
      shadow = 0.25 - sign * amt
      highlight = 0.75 + sign * amt
  in [ { input: 0.0, output: 0.0 }
     , { input: 0.25, output: shadow }
     , { input: 0.75, output: highlight }
     , { input: 1.0, output: 1.0 }
     ]

-- | Create lift curve (raise shadows)
createLiftCurve :: Number -> Number -> Array CurvePoint
createLiftCurve lift gamma =
  let liftAmt = clamp01 lift
      gammaAmt = max 0.1 (min 10.0 gamma)
      midIn = 0.5
      midOut = Number.pow midIn (1.0 / gammaAmt)
  in [ { input: 0.0, output: liftAmt }
     , { input: midIn, output: midOut }
     , { input: 1.0, output: 1.0 }
     ]

-- | Create gamma curve
createGammaCurve :: Number -> Array CurvePoint
createGammaCurve gamma =
  let gammaAmt = max 0.1 (min 10.0 gamma)
      mkPoint x = { input: x, output: Number.pow x (1.0 / gammaAmt) }
  in map mkPoint [0.0, 0.25, 0.5, 0.75, 1.0]
