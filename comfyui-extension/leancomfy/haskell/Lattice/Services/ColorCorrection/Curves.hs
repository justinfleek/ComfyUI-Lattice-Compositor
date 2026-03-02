{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.ColorCorrection.Curves
Description : Curve Interpolation Functions
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for curve-based color adjustment:
- Cubic Bezier evaluation
- Catmull-Rom tangent calculation
- S-curve generation
- Lift curve generation

All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts (lines 468-705)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.ColorCorrection.Curves
  ( -- * Types
    CurvePoint(..)
    -- * Cubic Bezier
  , cubicBezier
    -- * Catmull-Rom
  , catmullRomTangent
    -- * Curve Evaluation
  , segmentParameter
  , evaluateCurveSegment
    -- * Preset Curves
  , createSCurve
  , createLiftCurve
  , identityCurve
    -- * Utilities
  , clampToUint8
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A point on a curve
data CurvePoint = CurvePoint
  { cpX :: Double  -- ^ Input value (0-255)
  , cpY :: Double  -- ^ Output value (0-255)
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Cubic Bezier
--------------------------------------------------------------------------------

-- | Evaluate a cubic Bezier curve at parameter t.
--
-- Formula: B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
cubicBezier :: Double  -- ^ p0 (start)
            -> Double  -- ^ p1 (control 1)
            -> Double  -- ^ p2 (control 2)
            -> Double  -- ^ p3 (end)
            -> Double  -- ^ t (0-1)
            -> Double
cubicBezier p0 p1 p2 p3 t =
  let t2 = t * t
      t3 = t2 * t
      mt = 1 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
  in mt3 * p0 + 3 * mt2 * t * p1 + 3 * mt * t2 * p2 + t3 * p3

--------------------------------------------------------------------------------
-- Catmull-Rom Tangent
--------------------------------------------------------------------------------

-- | Calculate Catmull-Rom tangent for a curve segment.
catmullRomTangent :: Double  -- ^ prevY
                  -> Double  -- ^ prevX
                  -> Double  -- ^ nextY
                  -> Double  -- ^ nextX
                  -> Double  -- ^ segmentWidth
                  -> Double
catmullRomTangent prevY prevX nextY nextX segmentWidth =
  let dx = nextX - prevX
  in if dx < 0.0001 then 0
     else ((nextY - prevY) / dx) * segmentWidth

--------------------------------------------------------------------------------
-- Curve Evaluation
--------------------------------------------------------------------------------

-- | Linear interpolation parameter for a value in a segment.
segmentParameter :: Double  -- ^ value
                 -> Double  -- ^ segmentStart
                 -> Double  -- ^ segmentEnd
                 -> Double  -- ^ Parameter t (0-1, clamped)
segmentParameter value segmentStart segmentEnd =
  let range = segmentEnd - segmentStart
  in if range < 0.0001 then 0
     else max 0 (min 1 ((value - segmentStart) / range))

-- | Evaluate a curve segment using cubic interpolation.
evaluateCurveSegment :: Double  -- ^ p0x
                     -> Double  -- ^ p0y
                     -> Double  -- ^ p1x
                     -> Double  -- ^ p1y
                     -> Bool    -- ^ hasPrev
                     -> Double  -- ^ prevX
                     -> Double  -- ^ prevY
                     -> Bool    -- ^ hasNext
                     -> Double  -- ^ nextX
                     -> Double  -- ^ nextY
                     -> Double  -- ^ t
                     -> Double
evaluateCurveSegment p0x p0y p1x p1y hasPrev prevX prevY hasNext nextX nextY t =
  let segWidth = p1x - p0x
      tangent0 = if hasPrev
                 then catmullRomTangent prevY prevX p1y p1x segWidth
                 else 0
      tangent1 = if hasNext
                 then catmullRomTangent p0y p0x nextY nextX segWidth
                 else 0
      cp1y = p0y + tangent0 / 3
      cp2y = p1y - tangent1 / 3
      result = cubicBezier p0y cp1y cp2y p1y t
  in max 0 (min 255 result)

--------------------------------------------------------------------------------
-- Preset Curves
--------------------------------------------------------------------------------

-- | Create an S-curve for contrast adjustment.
createSCurve :: Double  -- ^ amount (0-1)
             -> [CurvePoint]
createSCurve amount =
  let midPoint = 128
      adjustment = amount * 50
  in [ CurvePoint 0   0
     , CurvePoint 64  (max 0 (64 - adjustment))
     , CurvePoint midPoint midPoint
     , CurvePoint 192 (min 255 (192 + adjustment))
     , CurvePoint 255 255
     ]

-- | Create a lift curve for shadow/highlight adjustment.
createLiftCurve :: Double  -- ^ shadowLift (0-128)
                -> Double  -- ^ highlightLift (-127 to 0)
                -> [CurvePoint]
createLiftCurve shadowLift highlightLift =
  [ CurvePoint 0   (max 0 (min 128 shadowLift))
  , CurvePoint 128 128
  , CurvePoint 255 (max 128 (min 255 (255 + highlightLift)))
  ]

-- | Identity curve (input = output).
identityCurve :: [CurvePoint]
identityCurve = [CurvePoint 0 0, CurvePoint 255 255]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Clamp and round to valid 8-bit range.
clampToUint8 :: Double -> Double
clampToUint8 value = fromIntegral (round (max 0 (min 255 value)) :: Int)
