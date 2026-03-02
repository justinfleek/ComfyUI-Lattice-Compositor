{-|
Module      : Lattice.Services.Effects.ColorCurves
Description : Curve-based Color Adjustments
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for curve-based color adjustments:
- Cubic Bezier curve interpolation
- Curve LUT (lookup table) generation
- S-curve and lift curve presets

All functions operate on normalized [0,1] color values.
All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.ColorCurves
  ( -- * Types
    CurvePoint(..)
  , CurveParams(..)
    -- * Default Values
  , defaultCurveParams
    -- * Curve Functions
  , cubicBezier
  , buildCurveLUT
  , applyCurves
    -- * Curve Presets
  , createSCurve
  , createLiftCurve
  , createGammaCurve
  ) where

import Data.Word (Word8)
import qualified Data.Vector.Unboxed as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | A point on a curve with input/output values
data CurvePoint = CurvePoint
  { cpInput  :: !Double   -- ^ Input value [0,1]
  , cpOutput :: !Double   -- ^ Output value [0,1]
  } deriving (Eq, Show)

-- | Curve parameters for each channel
data CurveParams = CurveParams
  { cpMaster :: ![CurvePoint]  -- ^ Master curve (affects all channels)
  , cpRed    :: ![CurvePoint]  -- ^ Red channel curve
  , cpGreen  :: ![CurvePoint]  -- ^ Green channel curve
  , cpBlue   :: ![CurvePoint]  -- ^ Blue channel curve
  } deriving (Eq, Show)

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Identity curve (no change)
identityCurve :: [CurvePoint]
identityCurve =
  [ CurvePoint 0.0 0.0
  , CurvePoint 1.0 1.0
  ]

-- | Default curves (identity on all channels)
defaultCurveParams :: CurveParams
defaultCurveParams = CurveParams
  { cpMaster = identityCurve
  , cpRed = identityCurve
  , cpGreen = identityCurve
  , cpBlue = identityCurve
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Safe list access with default (no partial functions)
safeIndex :: [a] -> Int -> a -> a
safeIndex xs i def
  | i < 0 = def
  | otherwise = go xs i
  where
    go [] _ = def
    go (x:_) 0 = x
    go (_:rest) n = go rest (n - 1)

-- ────────────────────────────────────────────────────────────────────────────
-- Cubic Bezier
-- ────────────────────────────────────────────────────────────────────────────

-- | Cubic Bezier interpolation for curve segment
--   t: parameter [0,1]
--   p0, p1, p2, p3: control points
cubicBezier :: Double -> Double -> Double -> Double -> Double -> Double
cubicBezier t p0 p1 p2 p3 =
  let t' = clamp01 t
      mt = 1 - t'
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t' * t'
      t3 = t2 * t'
  in mt3 * p0 + 3 * mt2 * t' * p1 + 3 * mt * t2 * p2 + t3 * p3

-- | Find curve segment containing input value
findSegment :: [CurvePoint] -> Double -> (CurvePoint, CurvePoint)
findSegment points x
  | length points < 2 = (CurvePoint 0 0, CurvePoint 1 1)
  | otherwise = go points
  where
    go (p1:p2:rest)
      | x <= cpInput p2 = (p1, p2)
      | otherwise = case rest of
          [] -> (p1, p2)  -- Use last segment
          _  -> go (p2:rest)
    go [p] = (p, p)  -- Single point
    go []  = (CurvePoint 0 0, CurvePoint 1 1)

-- | Interpolate on curve at given input
interpolateCurve :: [CurvePoint] -> Double -> Double
interpolateCurve points x
  | length points < 2 = x  -- Identity if no curve
  | otherwise =
      let (p1, p2) = findSegment points x
          inRange = cpInput p2 - cpInput p1
          t = if inRange > 0.0001
              then (x - cpInput p1) / inRange
              else 0
          -- Simple linear interpolation (could use cubic for smoothness)
          -- For cubic bezier: use control points at 1/3 and 2/3 of segment
          cp1 = cpOutput p1 + (cpOutput p2 - cpOutput p1) / 3
          cp2 = cpOutput p2 - (cpOutput p2 - cpOutput p1) / 3
      in cubicBezier t (cpOutput p1) cp1 cp2 (cpOutput p2)

-- ────────────────────────────────────────────────────────────────────────────
-- Lookup Table Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Build 256-entry lookup table from curve points
buildCurveLUT :: [CurvePoint] -> V.Vector Word8
buildCurveLUT points =
  V.generate 256 $ \i ->
    let normalized = fromIntegral i / 255
        result = interpolateCurve points normalized
    in round (max 0 (min 255 (result * 255)))

-- | Apply curve using LUT (safe indexing)
applyCurveLUT :: V.Vector Word8 -> Double -> Double
applyCurveLUT lut value =
  let idx = round (clamp01 value * 255)
      safeIdx = max 0 (min 255 idx)
      -- Use safe indexing with fallback to input value
      result = case lut V.!? safeIdx of
        Just v  -> fromIntegral v / 255
        Nothing -> value  -- Fallback (should never happen with 256-element LUT)
  in result

-- | Apply curves to RGB
applyCurves :: CurveParams -> (Double, Double, Double) -> (Double, Double, Double)
applyCurves params (r, g, b) =
  let masterLUT = buildCurveLUT (cpMaster params)
      redLUT = buildCurveLUT (cpRed params)
      greenLUT = buildCurveLUT (cpGreen params)
      blueLUT = buildCurveLUT (cpBlue params)
      -- Apply master first, then channel-specific
      r' = applyCurveLUT redLUT (applyCurveLUT masterLUT r)
      g' = applyCurveLUT greenLUT (applyCurveLUT masterLUT g)
      b' = applyCurveLUT blueLUT (applyCurveLUT masterLUT b)
  in (clamp01 r', clamp01 g', clamp01 b')

-- ────────────────────────────────────────────────────────────────────────────
-- Curve Presets
-- ────────────────────────────────────────────────────────────────────────────

-- | Create S-curve for contrast enhancement
--   amount: -1 to 1 (negative = inverse S)
createSCurve :: Double -> [CurvePoint]
createSCurve amount =
  let amt = clamp01 (abs amount) * 0.25  -- Scale to reasonable range
      sign = if amount < 0 then -1 else 1
      -- S-curve: shadows down, highlights up (or inverse)
      shadow = 0.25 - sign * amt
      highlight = 0.75 + sign * amt
  in [ CurvePoint 0.0 0.0
     , CurvePoint 0.25 shadow
     , CurvePoint 0.75 highlight
     , CurvePoint 1.0 1.0
     ]

-- | Create lift curve (raise shadows)
--   lift: 0 to 1 (amount to lift shadows)
--   gamma: 0.1 to 10 (midtone adjustment)
createLiftCurve :: Double -> Double -> [CurvePoint]
createLiftCurve lift gamma =
  let liftAmt = clamp01 lift
      gammaAmt = max 0.1 (min 10 gamma)
      -- Lift raises the black point
      -- Gamma affects midtones
      midIn = 0.5
      midOut = midIn ** (1 / gammaAmt)  -- Gamma correction formula
  in [ CurvePoint 0.0 liftAmt
     , CurvePoint midIn midOut
     , CurvePoint 1.0 1.0
     ]

-- | Create gamma curve
--   gamma: 0.1 to 10 (< 1 = lighter, > 1 = darker)
createGammaCurve :: Double -> [CurvePoint]
createGammaCurve gamma =
  let gammaAmt = max 0.1 (min 10 gamma)
      -- Generate points along gamma curve
      mkPoint x = CurvePoint x (x ** (1 / gammaAmt))
  in map mkPoint [0.0, 0.25, 0.5, 0.75, 1.0]
