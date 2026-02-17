-- |
-- Module      : Lattice.Composables.CanvasSelection
-- Description : Canvas marquee selection geometry and mode logic (pure)
--
-- Ported from ui/src/composables/useCanvasSelection.ts
-- Pure: rect intersection/containment, rectFromPoints, pointDistance, applySelection.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.CanvasSelection
  ( -- Geometry
    Rect(..)
  , Point(..)
  , rectsIntersect
  , rectContains
  , rectFromPoints
  , pointDistance
  -- Selection
  , SelectionMode(..)
  , SelectableItem(..)
  , findItemsInRect
  , applySelection
  ) where

import Data.List (nub)
import Data.Text (Text)

-- ============================================================================
-- GEOMETRY
-- ============================================================================

data Point = Point
  { pointX :: Double
  , pointY :: Double
  }
  deriving (Eq, Show)

data Rect = Rect
  { rectX :: Double
  , rectY :: Double
  , rectWidth :: Double
  , rectHeight :: Double
  }
  deriving (Eq, Show)

-- | Two rectangles intersect iff they overlap (not disjoint).
rectsIntersect :: Rect -> Rect -> Bool
rectsIntersect a b =
  not
    ( rectX a + rectWidth a < rectX b
        || rectX b + rectWidth b < rectX a
        || rectY a + rectHeight a < rectY b
        || rectY b + rectHeight b < rectY a
    )

-- | Container completely contains item (inclusive edges).
rectContains :: Rect -> Rect -> Bool
rectContains container item =
  rectX container <= rectX item
    && rectY container <= rectY item
    && rectX container + rectWidth container >= rectX item + rectWidth item
    && rectY container + rectHeight container >= rectY item + rectHeight item

-- | Build rect from two corners (normalized to min x/y and non-negative size).
rectFromPoints :: Point -> Point -> Rect
rectFromPoints p1 p2 =
  Rect
    { rectX = min (pointX p1) (pointX p2)
    , rectY = min (pointY p1) (pointY p2)
    , rectWidth = abs (pointX p2 - pointX p1)
    , rectHeight = abs (pointY p2 - pointY p1)
    }

-- | Euclidean distance between two points.
pointDistance :: Point -> Point -> Double
pointDistance p1 p2 =
  let dx = pointX p2 - pointX p1
      dy = pointY p2 - pointY p1
  in sqrt (dx * dx + dy * dy)

-- ============================================================================
-- SELECTION
-- ============================================================================

data SelectionMode
  = Replace
  | Add
  | Subtract
  | Intersect
  deriving (Eq, Show, Enum, Bounded)

data SelectableItem = SelectableItem
  { selectableItemId :: Text
  , selectableItemBounds :: Rect
  }
  deriving (Eq, Show)

-- | Items whose bounds intersect the rect (returns their ids).
findItemsInRect :: Rect -> [SelectableItem] -> [Text]
findItemsInRect rect items =
  [ selectableItemId item
  | item <- items
  , rectsIntersect rect (selectableItemBounds item)
  ]

-- | Apply selection mode: new selection + mode + current selection -> result.
applySelection :: [Text] -> SelectionMode -> [Text] -> [Text]
applySelection selectedIds mode current =
  case mode of
    Replace -> selectedIds
    Add -> nub (current ++ selectedIds)
    Subtract -> filter (`notElem` selectedIds) current
    Intersect -> filter (`elem` selectedIds) current
