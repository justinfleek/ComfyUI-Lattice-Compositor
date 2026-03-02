-- |
-- Module      : Lattice.Composables.SplineInteraction
-- Description : Pure spline interaction types and helpers (pen mode, drag, hit-test)
--
-- Ported from ui/src/composables/useSplineInteraction.ts
-- Pure: types, constants, tool tips, screen-to-canvas, find clicked point, close-path check.
-- Delegate bezier/path logic to SplineUtils.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.SplineInteraction
  ( -- Types
    PenSubMode(..)
  , DragTargetType(..)
  , DragTarget(..)
  , PointWithId(..)
  -- Constants
  , closeThreshold
  -- Layer type check
  , isSplineOrPathType
  -- Tool tip
  , activeToolTipForPenSubMode
  -- Coordinate conversion (pure)
  , screenToCanvas
  -- Hit-test and close-path (pure)
  , findClickedPoint
  , closePathPreview
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Primitives (Vec2(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Pen tool sub-mode
data PenSubMode
  = PenSubModeAdd
  | PenSubModeInsert
  | PenSubModeDelete
  | PenSubModeConvert
  deriving (Eq, Show, Enum, Bounded)

-- | Drag target kind
data DragTargetType
  = DragPoint
  | DragHandleIn
  | DragHandleOut
  | DragDepth
  | DragNewPoint
  | DragAxisX
  | DragAxisY
  deriving (Eq, Show)

-- | Drag state (pure data; no IO)
data DragTarget = DragTarget
  { dragTargetType :: DragTargetType
  , dragTargetPointId :: Text
  , dragTargetStartX :: Double
  , dragTargetStartY :: Double
  , dragTargetStartDepth :: Maybe Double
  , dragTargetNewPointX :: Maybe Double
  , dragTargetNewPointY :: Maybe Double
  , dragTargetOriginalX :: Maybe Double
  , dragTargetOriginalY :: Maybe Double
  , dragTargetScreenStartX :: Maybe Double
  , dragTargetScreenStartY :: Maybe Double
  }
  deriving (Eq, Show)

-- | Point with id (for hit-test)
data PointWithId = PointWithId
  { pointWithIdId :: Text
  , pointWithIdX :: Double
  , pointWithIdY :: Double
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Distance (px) within which cursor is considered "over first point" for close-path
closeThreshold :: Double
closeThreshold = 15

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // layer // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if layer type is spline or path
isSplineOrPathType :: Maybe Text -> Bool
isSplineOrPathType (Just t) = t == "spline" || t == "path"
isSplineOrPathType Nothing = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // tool // tip
-- ════════════════════════════════════════════════════════════════════════════

-- | Tool tip text for current pen sub-mode
activeToolTipForPenSubMode :: PenSubMode -> Text
activeToolTipForPenSubMode PenSubModeAdd =
  "Click to add points. Drag after clicking to create curved handles. Right-click to finish drawing."
activeToolTipForPenSubMode PenSubModeInsert =
  "Click on the path to insert a new point on that segment."
activeToolTipForPenSubMode PenSubModeDelete =
  "Click on any point to delete it from the path."
activeToolTipForPenSubMode PenSubModeConvert =
  "Click on a point to toggle between smooth (curved) and corner (sharp) type."

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // coordinate // conversion
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert screen position (within SVG overlay) to canvas/composition coordinates.
-- Pure: (screenX, screenY) in overlay pixel space → (x, y) in composition space.
screenToCanvas
  :: Double  -- ^ screenX (relative to overlay)
  -> Double  -- ^ screenY
  -> Double  -- ^ overlay width (px)
  -> Double  -- ^ overlay height (px)
  -> Double  -- ^ canvas width (composition units)
  -> Double  -- ^ canvas height (composition units)
  -> (Double, Double)
screenToCanvas screenX screenY overlayW overlayH canvasW canvasH
  | overlayW <= 0 || overlayH <= 0 = (0, 0)
  | otherwise =
      let x = (screenX / overlayW) * canvasW
          y = (screenY / overlayH) * canvasH
      in (x, y)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // hit
-- ════════════════════════════════════════════════════════════════════════════

-- | Distance between two points
pointDistance :: Double -> Double -> Double -> Double -> Double
pointDistance x1 y1 x2 y2 =
  sqrt ((x2 - x1) ** 2 + (y2 - y1) ** 2)

-- | Find first control point within threshold of (posX, posY). Returns Maybe point.
findClickedPoint
  :: [PointWithId]
  -> Double  -- ^ posX
  -> Double  -- ^ posY
  -> Double  -- ^ threshold (px)
  -> Maybe PointWithId
findClickedPoint points posX posY threshold =
  let go [] = Nothing
      go (p : ps)
        | pointDistance (pointWithIdX p) (pointWithIdY p) posX posY < threshold = Just p
        | otherwise = go ps
  in go points

-- | Whether to show "close path" preview: cursor near first point, path has 3+ points, not closed.
closePathPreview
  :: Double  -- ^ first point x
  -> Double  -- ^ first point y
  -> Double  -- ^ cursor x
  -> Double  -- ^ cursor y
  -> Int     -- ^ number of control points
  -> Bool    -- ^ is path closed
  -> Bool
closePathPreview firstX firstY cursorX cursorY numPoints closed
  | closed = False
  | numPoints < 3 = False
  | otherwise = pointDistance firstX firstY cursorX cursorY < closeThreshold
