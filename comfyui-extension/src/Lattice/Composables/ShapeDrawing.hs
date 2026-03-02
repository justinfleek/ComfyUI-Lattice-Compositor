-- |
-- Module      : Lattice.Composables.ShapeDrawing
-- Description : Shape draw bounds and SVG path data (no Canvas/DOM)
--
-- Ported from ui/src/composables/useShapeDrawing.ts
-- Pure bounds and path computation; drawing stays in UI.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.ShapeDrawing
  ( -- Bounds
    ShapeDrawBounds(..)
  , computeShapeBounds
  -- Tool type
  , ShapeToolType(..)
  -- SVG path (relative to 0,0 with width/height)
  , shapePathFromBounds
  ) where

import Data.Text (Text)
import Lattice.Utils.NumericSafety (isFinite)
import qualified Data.Text as T

-- ============================================================================
-- BOUNDS
-- ============================================================================

data ShapeDrawBounds = ShapeDrawBounds
  { shapeDrawBoundsX1 :: Double
  , shapeDrawBoundsY1 :: Double
  , shapeDrawBoundsX2 :: Double
  , shapeDrawBoundsY2 :: Double
  }
  deriving (Eq, Show)

-- | Compute bounds from start/end with constrain (square/circle) and fromCenter.
-- Returns Left if any input is non-finite.
computeShapeBounds
  :: Double -> Double -> Double -> Double
  -> Bool -> Bool
  -> Either Text ShapeDrawBounds
computeShapeBounds startX startY endX endY constrain fromCenter
  | not (isFinite startX && isFinite startY && isFinite endX && isFinite endY) =
      Left "computeShapeBounds: non-finite start/end"
  | otherwise =
      let dx = endX - startX
          dy = endY - startY
          (x1, y1, x2, y2) =
            if fromCenter
              then (startX - dx, startY - dy, endX, endY)
              else (startX, startY, endX, endY)
          (x1', y1', x2', y2') =
            if constrain
              then let size = max (abs (x2 - x1)) (abs (y2 - y1))
                       sx = signum (x2 - x1)
                       sy = signum (y2 - y1)
                   in if sx == 0 && sy == 0
                        then (x1, y1, x1 + size, y1 + size)
                        else (x1, y1, x1 + size * sx, y1 + size * sy)
              else (x1, y1, x2, y2)
      in Right (ShapeDrawBounds x1' y1' x2' y2')

-- ============================================================================
-- TOOL TYPE
-- ============================================================================

data ShapeToolType
  = ShapeRectangle
  | ShapeEllipse
  | ShapePolygon Int  -- sides
  | ShapeStar Int Double  -- points, inner ratio
  deriving (Eq, Show)

-- ============================================================================
-- SVG PATH (relative to origin; width = |x2-x1|, height = |y2-y1|)
-- ============================================================================

widthHeight :: ShapeDrawBounds -> (Double, Double)
widthHeight b =
  ( abs (shapeDrawBoundsX2 b - shapeDrawBoundsX1 b)
  , abs (shapeDrawBoundsY2 b - shapeDrawBoundsY1 b)
  )

-- | Generate SVG path string for the shape in a 0,0-origin box with given width/height.
-- Returns empty string if width or height is 0.
shapePathFromBounds
  :: ShapeDrawBounds
  -> ShapeToolType
  -> Either Text Text
shapePathFromBounds b tool =
  let (w, h) = widthHeight b
  in if w <= 0 || h <= 0
       then Right ""
       else Right (pathFor w h tool)

pathFor :: Double -> Double -> ShapeToolType -> Text
pathFor w h ShapeRectangle =
  T.pack $ "M 0 0 L " ++ show w ++ " 0 L " ++ show w ++ " " ++ show h ++ " L 0 " ++ show h ++ " Z"
pathFor w h ShapeEllipse =
  let rx = w / 2
      ry = h / 2
      cx = rx
      cy = ry
  in T.pack $
       "M " ++ show cx ++ " " ++ show (cy - ry) ++
       " A " ++ show rx ++ " " ++ show ry ++ " 0 1 1 " ++ show cx ++ " " ++ show (cy + ry) ++
       " A " ++ show rx ++ " " ++ show ry ++ " 0 1 1 " ++ show cx ++ " " ++ show (cy - ry) ++ " Z"
pathFor w h (ShapePolygon sides)
  | sides < 3 = ""
  | otherwise =
      let cx = w / 2
          cy = h / 2
          r = min w h / 2
          n = fromIntegral sides
          angle i = (fromIntegral i / n) * (2 * pi) - pi / 2
          points = [ (cx + r * cos (angle i), cy + r * sin (angle i))
                   | i <- [0 .. sides - 1]
                   ]
          seg (i, (px, py)) = (if i == 0 then "M" else "L") ++ " " ++ show px ++ " " ++ show py
      in T.pack (unwords (zipWith (\i p -> seg (i, p)) [0 :: Int ..] points) ++ " Z")
pathFor w h (ShapeStar numPoints innerRatio)
  | numPoints < 2 = ""
  | otherwise =
      let cx = w / 2
          cy = h / 2
          outerR = min w h / 2
          innerR = outerR * innerRatio
          n = numPoints * 2
          angle i = (fromIntegral i / fromIntegral n) * (2 * pi) - pi / 2
          r i = if even i then outerR else innerR
          points = [ (cx + r i * cos (angle i), cy + r i * sin (angle i))
                   | i <- [0 .. n - 1]
                   ]
          seg (i, (px, py)) = (if i == 0 then "M" else "L") ++ " " ++ show px ++ " " ++ show py
      in T.pack (unwords (zipWith (\i p -> seg (i, p)) [0 :: Int ..] points) ++ " Z")
