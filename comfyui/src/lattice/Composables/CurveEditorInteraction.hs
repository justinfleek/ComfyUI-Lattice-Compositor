-- |
-- Module      : Lattice.Composables.CurveEditorInteraction
-- Description : Curve editor hit-test and selection box (pure logic; no DOM)
--
-- Ported from ui/src/composables/useCurveEditorInteraction.ts
-- Pure: isKeyframeSelected, hitTestKeyframe, selection box containment.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.CurveEditorInteraction
  ( -- Selection box
    SelectionBox(..)
  , selectionBoxFromPoints
  , pointInSelectionBox
  , keyframesInBox
  -- Keyframe selection
  , isKeyframeSelected
  , hitTestKeyframe
  , defaultHitRadius
  ) where

import Data.Text (Text)

-- ============================================================================
-- SELECTION BOX
-- ============================================================================

data SelectionBox = SelectionBox
  { selectionBoxX :: Double
  , selectionBoxY :: Double
  , selectionBoxWidth :: Double
  , selectionBoxHeight :: Double
  }
  deriving (Eq, Show)

-- | Build normalized box from two corners (x1,y1) and (x2,y2).
selectionBoxFromPoints :: Double -> Double -> Double -> Double -> SelectionBox
selectionBoxFromPoints x1 y1 x2 y2 =
  SelectionBox
    { selectionBoxX = min x1 x2
    , selectionBoxY = min y1 y2
    , selectionBoxWidth = abs (x2 - x1)
    , selectionBoxHeight = abs (y2 - y1)
    }

-- | True if point (px, py) is inside the box (inclusive edges).
pointInSelectionBox :: Double -> Double -> SelectionBox -> Bool
pointInSelectionBox px py box =
  px >= selectionBoxX box
    && px <= selectionBoxX box + selectionBoxWidth box
    && py >= selectionBoxY box
    && py <= selectionBoxY box + selectionBoxHeight box

-- | Keyframe screen position: (propId, index, screenX, screenY)
type KeyframeScreenPos = (Text, Int, Double, Double)

-- | Keyframes whose (screenX, screenY) fall inside the box.
keyframesInBox :: SelectionBox -> [KeyframeScreenPos] -> [(Text, Int)]
keyframesInBox box positions =
  [ (pid, idx)
  | (pid, idx, kx, ky) <- positions
  , pointInSelectionBox kx ky box
  ]

-- ============================================================================
-- KEYFRAME SELECTION / HIT TEST
-- ============================================================================

defaultHitRadius :: Double
defaultHitRadius = 10

-- | True if (propId, index) is in the list of selected keyframe refs.
isKeyframeSelected :: Text -> Int -> [(Text, Int)] -> Bool
isKeyframeSelected propId index selected =
  any (\(p, i) -> p == propId && i == index) selected

-- | Find first keyframe within radius of (x, y). List is (propId, index, screenX, screenY).
hitTestKeyframe
  :: Double
  -> Double
  -> Double
  -> [KeyframeScreenPos]
  -> Maybe (Text, Int)
hitTestKeyframe x y radius positions =
  let radiusSq = radius * radius
      distSq (_, _, kx, ky) = (x - kx) ^ (2 :: Int) + (y - ky) ^ (2 :: Int)
      hit (pid, idx, kx, ky) = distSq (pid, idx, kx, ky) <= radiusSq
  in case filter (\(pid, idx, kx, ky) -> hit (pid, idx, kx, ky)) positions of
    [] -> Nothing
    (pid, idx, _, _) : _ -> Just (pid, idx)
