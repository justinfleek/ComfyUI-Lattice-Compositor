{-|
  Lattice.Services.SVGExtrusion.Bounds - Bounding Box Mathematics

  Pure mathematical functions for bounding box calculations:
  - Min/Max from point sets
  - Center calculation
  - Width/Height computation
  - Bounds merging

  Source: ui/src/services/svgExtrusion.ts (lines 446-486)
-}

module Lattice.Services.SVGExtrusion.Bounds
  ( -- * Types
    BoundingBox2D(..)
  , BoundsWithMetrics(..)
    -- * Construction
  , emptyBounds
  , includePoint
  , fromPoints
    -- * Metrics
  , width
  , height
  , centerX
  , centerY
  , withMetrics
    -- * Merging
  , merge
  , mergeAll
    -- * Queries
  , containsPoint
  , isValid
  , area
  , diagonal
    -- * Transformation
  , expand
  , scale
  , translate
  ) where

import Data.Foldable (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D bounding box
data BoundingBox2D = BoundingBox2D
  { bbMinX :: !Double
  , bbMinY :: !Double
  , bbMaxX :: !Double
  , bbMaxY :: !Double
  } deriving (Show, Eq)

-- | Extended bounding box with derived properties
data BoundsWithMetrics = BoundsWithMetrics
  { bwmMinX :: !Double
  , bwmMinY :: !Double
  , bwmMaxX :: !Double
  , bwmMaxY :: !Double
  , bwmWidth :: !Double
  , bwmHeight :: !Double
  , bwmCenterX :: !Double
  , bwmCenterY :: !Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Empty bounds (for initial accumulator)
emptyBounds :: BoundingBox2D
emptyBounds = BoundingBox2D
  { bbMinX = 1e38  -- Infinity approximation
  , bbMinY = 1e38
  , bbMaxX = -1e38  -- -Infinity approximation
  , bbMaxY = -1e38
  }

-- | Update bounds to include a point.
includePoint :: BoundingBox2D -> Double -> Double -> BoundingBox2D
includePoint bounds x y = BoundingBox2D
  { bbMinX = min (bbMinX bounds) x
  , bbMinY = min (bbMinY bounds) y
  , bbMaxX = max (bbMaxX bounds) x
  , bbMaxY = max (bbMaxY bounds) y
  }

-- | Calculate bounds from a list of (x, y) points.
fromPoints :: [(Double, Double)] -> BoundingBox2D
fromPoints = foldl' (\acc (x, y) -> includePoint acc x y) emptyBounds

--------------------------------------------------------------------------------
-- Metrics
--------------------------------------------------------------------------------

-- | Calculate width of bounding box.
width :: BoundingBox2D -> Double
width bounds = bbMaxX bounds - bbMinX bounds

-- | Calculate height of bounding box.
height :: BoundingBox2D -> Double
height bounds = bbMaxY bounds - bbMinY bounds

-- | Calculate center X coordinate.
centerX :: BoundingBox2D -> Double
centerX bounds = bbMinX bounds + width bounds / 2.0

-- | Calculate center Y coordinate.
centerY :: BoundingBox2D -> Double
centerY bounds = bbMinY bounds + height bounds / 2.0

-- | Convert basic bounds to bounds with all metrics.
withMetrics :: BoundingBox2D -> BoundsWithMetrics
withMetrics bounds =
  let w = width bounds
      h = height bounds
  in BoundsWithMetrics
    { bwmMinX = bbMinX bounds
    , bwmMinY = bbMinY bounds
    , bwmMaxX = bbMaxX bounds
    , bwmMaxY = bbMaxY bounds
    , bwmWidth = w
    , bwmHeight = h
    , bwmCenterX = bbMinX bounds + w / 2.0
    , bwmCenterY = bbMinY bounds + h / 2.0
    }

--------------------------------------------------------------------------------
-- Merging
--------------------------------------------------------------------------------

-- | Merge two bounding boxes.
merge :: BoundingBox2D -> BoundingBox2D -> BoundingBox2D
merge a b = BoundingBox2D
  { bbMinX = min (bbMinX a) (bbMinX b)
  , bbMinY = min (bbMinY a) (bbMinY b)
  , bbMaxX = max (bbMaxX a) (bbMaxX b)
  , bbMaxY = max (bbMaxY a) (bbMaxY b)
  }

-- | Merge a list of bounding boxes.
mergeAll :: [BoundingBox2D] -> BoundingBox2D
mergeAll = foldl' merge emptyBounds

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Check if a point is inside the bounding box.
containsPoint :: BoundingBox2D -> Double -> Double -> Bool
containsPoint bounds x y =
  x >= bbMinX bounds && x <= bbMaxX bounds &&
  y >= bbMinY bounds && y <= bbMaxY bounds

-- | Check if bounds is valid (non-empty).
isValid :: BoundingBox2D -> Bool
isValid bounds =
  bbMaxX bounds >= bbMinX bounds && bbMaxY bounds >= bbMinY bounds

-- | Calculate area of bounding box.
area :: BoundingBox2D -> Double
area bounds = width bounds * height bounds

-- | Calculate diagonal length of bounding box.
diagonal :: BoundingBox2D -> Double
diagonal bounds =
  let w = width bounds
      h = height bounds
  in sqrt (w * w + h * h)

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Expand bounds by a margin.
expand :: BoundingBox2D -> Double -> BoundingBox2D
expand bounds margin = BoundingBox2D
  { bbMinX = bbMinX bounds - margin
  , bbMinY = bbMinY bounds - margin
  , bbMaxX = bbMaxX bounds + margin
  , bbMaxY = bbMaxY bounds + margin
  }

-- | Scale bounds around its center.
scale :: BoundingBox2D -> Double -> BoundingBox2D
scale bounds scaleFactor =
  let cx = centerX bounds
      cy = centerY bounds
      hw = width bounds / 2.0 * scaleFactor
      hh = height bounds / 2.0 * scaleFactor
  in BoundingBox2D
    { bbMinX = cx - hw
    , bbMinY = cy - hh
    , bbMaxX = cx + hw
    , bbMaxY = cy + hh
    }

-- | Translate bounds by offset.
translate :: BoundingBox2D -> Double -> Double -> BoundingBox2D
translate bounds dx dy = BoundingBox2D
  { bbMinX = bbMinX bounds + dx
  , bbMinY = bbMinY bounds + dy
  , bbMaxX = bbMaxX bounds + dx
  , bbMaxY = bbMaxY bounds + dy
  }
