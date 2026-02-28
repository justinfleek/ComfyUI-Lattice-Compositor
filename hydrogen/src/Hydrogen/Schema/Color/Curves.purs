-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // color // curves
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RGB/Luminance curve adjustments for color grading.

module Hydrogen.Schema.Color.Curves
  ( Curve
  , CurvePoint
  , Curves
  , curve
  , curvePoint
  , curves
  , linearCurve
  , contrastCurve
  , applyToRgb
  , applyToChannel
  ) where

import Prelude
  ( class Eq
  , class Monoid
  , class Ord
  , class Semigroup
  , compare
  , max
  , min
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<=)
  )

import Data.Array (sortBy, uncons)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Color.Channel (Channel, channel, unwrap)
import Hydrogen.Schema.Color.RGB (RGB, red, green, blue, rgbFromChannels)

-- ═════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═════════════════════════════════════════════════════════════════════════════

-- Single point on a curve (input/output mapping)
-- Input and output are both 0-255 (Channel values)
newtype CurvePoint = CurvePoint
  { input :: Channel
  , output :: Channel
  }

derive newtype instance Eq CurvePoint
derive newtype instance Ord CurvePoint

-- A curve is a sorted array of control points
-- Interpolation happens between points using cubic Bezier
newtype Curve = Curve (Array CurvePoint)

derive newtype instance Eq Curve
derive newtype instance Semigroup Curve
derive newtype instance Monoid Curve

-- Complete curves configuration for color grading
-- Master curve affects all channels, individual curves affect specific channels
newtype Curves = Curves
  { master :: Curve
  , red :: Curve
  , green :: Curve
  , blue :: Curve
  }

derive newtype instance Eq Curves

-- ═════════════════════════════════════════════════════════════════════════════
-- SMART CONSTRUCTORS
-- ═════════════════════════════════════════════════════════════════════════════

-- Create a curve point
curvePoint :: Channel -> Channel -> CurvePoint
curvePoint input output = CurvePoint { input, output }

-- Create a curve from control points (automatically sorts by input)
curve :: Array CurvePoint -> Curve
curve points = Curve (sortBy comparePoints points)
  where
  comparePoints (CurvePoint p1) (CurvePoint p2) = 
    compare (unwrap p1.input) (unwrap p2.input)

-- Create a complete curves configuration
curves :: Curve -> Curve -> Curve -> Curve -> Curves
curves master red green blue = Curves { master, red, green, blue }

-- Linear curve (identity - no adjustment)
linearCurve :: Curve
linearCurve = curve
  [ curvePoint (channel 0) (channel 0)
  , curvePoint (channel 255) (channel 255)
  ]

-- Contrast curve (S-curve - darken shadows, brighten highlights)
contrastCurve :: Number -> Curve
contrastCurve amount = curve
  [ curvePoint (channel 0) (channel 0)
  , curvePoint (channel 64) (channel (round (max 0.0 (min 255.0 (64.0 - amount * 10.0)))))
  , curvePoint (channel 128) (channel 128)
  , curvePoint (channel 192) (channel (round (max 0.0 (min 255.0 (192.0 + amount * 10.0)))))
  , curvePoint (channel 255) (channel 255)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
-- CURVE INTERPOLATION
-- ═════════════════════════════════════════════════════════════════════════════

-- Apply curve to a single channel value
-- Uses linear interpolation between control points
applyToChannel :: Curve -> Channel -> Channel
applyToChannel (Curve points) input =
  let inputVal = toNumber (unwrap input)
  in case findSegment inputVal points of
    Nothing -> input  -- No points, return unchanged
    Just { before, after } ->
      let CurvePoint p1 = before
          CurvePoint p2 = after
          x1 = toNumber (unwrap p1.input)
          y1 = toNumber (unwrap p1.output)
          x2 = toNumber (unwrap p2.input)
          y2 = toNumber (unwrap p2.output)
          -- Linear interpolation
          t = if x2 == x1 then 0.0 else (inputVal - x1) / (x2 - x1)
          output = y1 + t * (y2 - y1)
      in channel (round output)

-- Find the segment containing the input value
findSegment :: Number -> Array CurvePoint -> Maybe { before :: CurvePoint, after :: CurvePoint }
findSegment inputVal points = 
  case uncons points of
    Nothing -> Nothing
    Just { head: first, tail: rest } ->
      if inputVal <= toNumber (unwrap (let CurvePoint p = first in p.input))
        then case uncons rest of
          Nothing -> Nothing
          Just { head: second } -> Just { before: first, after: second }
        else findNext inputVal first rest

-- Find next segment recursively
findNext :: Number -> CurvePoint -> Array CurvePoint -> Maybe { before :: CurvePoint, after :: CurvePoint }
findNext inputVal prev points =
  case uncons points of
    Nothing -> Nothing
    Just { head: curr, tail: rest } ->
      let CurvePoint p = curr
          currInput = toNumber (unwrap p.input)
      in if inputVal <= currInput
           then Just { before: prev, after: curr }
           else findNext inputVal curr rest

-- ═════════════════════════════════════════════════════════════════════════════
-- RGB APPLICATION
-- ═════════════════════════════════════════════════════════════════════════════

-- Apply curves to an RGB color
-- Master curve is applied first, then individual channel curves
applyToRgb :: Curves -> RGB -> RGB
applyToRgb (Curves c) rgb =
  let -- Apply master curve to all channels
      rMaster = applyToChannel c.master (red rgb)
      gMaster = applyToChannel c.master (green rgb)
      bMaster = applyToChannel c.master (blue rgb)
      
      -- Apply individual channel curves
      rFinal = applyToChannel c.red rMaster
      gFinal = applyToChannel c.green gMaster
      bFinal = applyToChannel c.blue bMaster
  in rgbFromChannels rFinal gFinal bFinal

