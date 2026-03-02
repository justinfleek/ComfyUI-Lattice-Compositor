{-
  Lattice.Services.SVGExtrusion.Bounds - Bounding Box Mathematics

  Pure mathematical functions for bounding box calculations:
  - Min/Max from point sets
  - Center calculation
  - Width/Height computation
  - Bounds merging

  Source: ui/src/services/svgExtrusion.ts (lines 446-486)
-}

module Lattice.Services.SVGExtrusion.Bounds
  ( BoundingBox2D
  , BoundsWithMetrics
  , emptyBounds
  , includePoint
  , fromPoints
  , width
  , height
  , centerX
  , centerY
  , withMetrics
  , merge
  , mergeAll
  , containsPoint
  , isValid
  , area
  , diagonal
  , expand
  , scale
  , translate
  ) where

import Prelude

import Data.Foldable (foldl)
import Math (sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D bounding box
type BoundingBox2D =
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Extended bounding box with derived properties
type BoundsWithMetrics =
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  , width :: Number
  , height :: Number
  , centerX :: Number
  , centerY :: Number
  }

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Empty bounds (for initial accumulator)
emptyBounds :: BoundingBox2D
emptyBounds =
  { minX: 1.0e38
  , minY: 1.0e38
  , maxX: -1.0e38
  , maxY: -1.0e38
  }

-- | Update bounds to include a point.
includePoint :: BoundingBox2D -> Number -> Number -> BoundingBox2D
includePoint bounds x y =
  { minX: min bounds.minX x
  , minY: min bounds.minY y
  , maxX: max bounds.maxX x
  , maxY: max bounds.maxY y
  }

-- | Calculate bounds from an array of (x, y) points.
fromPoints :: Array { x :: Number, y :: Number } -> BoundingBox2D
fromPoints = foldl (\acc pt -> includePoint acc pt.x pt.y) emptyBounds

--------------------------------------------------------------------------------
-- Metrics
--------------------------------------------------------------------------------

-- | Calculate width of bounding box.
width :: BoundingBox2D -> Number
width bounds = bounds.maxX - bounds.minX

-- | Calculate height of bounding box.
height :: BoundingBox2D -> Number
height bounds = bounds.maxY - bounds.minY

-- | Calculate center X coordinate.
centerX :: BoundingBox2D -> Number
centerX bounds = bounds.minX + width bounds / 2.0

-- | Calculate center Y coordinate.
centerY :: BoundingBox2D -> Number
centerY bounds = bounds.minY + height bounds / 2.0

-- | Convert basic bounds to bounds with all metrics.
withMetrics :: BoundingBox2D -> BoundsWithMetrics
withMetrics bounds =
  let w = width bounds
      h = height bounds
  in { minX: bounds.minX
     , minY: bounds.minY
     , maxX: bounds.maxX
     , maxY: bounds.maxY
     , width: w
     , height: h
     , centerX: bounds.minX + w / 2.0
     , centerY: bounds.minY + h / 2.0
     }

--------------------------------------------------------------------------------
-- Merging
--------------------------------------------------------------------------------

-- | Merge two bounding boxes.
merge :: BoundingBox2D -> BoundingBox2D -> BoundingBox2D
merge a b =
  { minX: min a.minX b.minX
  , minY: min a.minY b.minY
  , maxX: max a.maxX b.maxX
  , maxY: max a.maxY b.maxY
  }

-- | Merge an array of bounding boxes.
mergeAll :: Array BoundingBox2D -> BoundingBox2D
mergeAll = foldl merge emptyBounds

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Check if a point is inside the bounding box.
containsPoint :: BoundingBox2D -> Number -> Number -> Boolean
containsPoint bounds x y =
  x >= bounds.minX && x <= bounds.maxX &&
  y >= bounds.minY && y <= bounds.maxY

-- | Check if bounds is valid (non-empty).
isValid :: BoundingBox2D -> Boolean
isValid bounds =
  bounds.maxX >= bounds.minX && bounds.maxY >= bounds.minY

-- | Calculate area of bounding box.
area :: BoundingBox2D -> Number
area bounds = width bounds * height bounds

-- | Calculate diagonal length of bounding box.
diagonal :: BoundingBox2D -> Number
diagonal bounds =
  let w = width bounds
      h = height bounds
  in sqrt (w * w + h * h)

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Expand bounds by a margin.
expand :: BoundingBox2D -> Number -> BoundingBox2D
expand bounds margin =
  { minX: bounds.minX - margin
  , minY: bounds.minY - margin
  , maxX: bounds.maxX + margin
  , maxY: bounds.maxY + margin
  }

-- | Scale bounds around its center.
scale :: BoundingBox2D -> Number -> BoundingBox2D
scale bounds scaleFactor =
  let cx = centerX bounds
      cy = centerY bounds
      hw = width bounds / 2.0 * scaleFactor
      hh = height bounds / 2.0 * scaleFactor
  in { minX: cx - hw
     , minY: cy - hh
     , maxX: cx + hw
     , maxY: cy + hh
     }

-- | Translate bounds by offset.
translate :: BoundingBox2D -> Number -> Number -> BoundingBox2D
translate bounds dx dy =
  { minX: bounds.minX + dx
  , minY: bounds.minY + dy
  , maxX: bounds.maxX + dx
  , maxY: bounds.maxY + dy
  }
