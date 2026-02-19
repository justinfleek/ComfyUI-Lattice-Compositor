-- |
-- Module      : Lattice.Composables.CurveEditorDraw
-- Description : Curve editor property colors and grid/segment data (no Canvas)
--
-- Ported from ui/src/composables/useCurveEditorDraw.ts
-- Pure data only; actual drawing stays in UI.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.CurveEditorDraw
  ( -- Property colors
    getPropertyColor
  , propertyColorDefault
  -- Grid line data (for UI to draw)
  , gridFrameLines
  , gridValueLines
  -- Segment type for curve drawing
  , CurveSegmentType(..)
  , curveSegmentData
  ) where

import Data.Text (Text)
import Lattice.Composables.CurveEditorCoords
  ( CurveMargin(..)
  , CurveViewState(..)
  , calculateGridStep
  , frameToScreenX
  , getNumericValue
  , valueToScreenY
  )
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , BaseInterpolationType(..)
  , BezierHandle(..)
  , InterpolationType(..)
  , Keyframe(..)
  , PropertyValue(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // property // colors
-- ════════════════════════════════════════════════════════════════════════════

propertyColorDefault :: Text
propertyColorDefault = "#7c9cff"

propertyColorMap :: [(Text, Text)]
propertyColorMap =
  [ ("Position", "#ff6b6b")
  , ("Position.x", "#ff6b6b")
  , ("Position.y", "#4ecdc4")
  , ("Position.z", "#45b7d1")
  , ("Scale", "#f7dc6f")
  , ("Scale.x", "#f7dc6f")
  , ("Scale.y", "#82e0aa")
  , ("Scale.z", "#85c1e9")
  , ("Rotation", "#bb8fce")
  , ("Opacity", "#f8b739")
  ]

-- | Get color for a property name; default if not found.
getPropertyColor :: Text -> Text
getPropertyColor propName =
  case lookup propName propertyColorMap of
    Just c -> c
    Nothing -> propertyColorDefault

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // grid // line // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Frame grid: list of (frame, screenX) for vertical lines
gridFrameLines
  :: CurveViewState
  -> Double
  -> Double
  -> CurveMargin
  -> Int
  -> [(Double, Double)]
gridFrameLines viewState canvasWidth _canvasHeight margin minSpacing =
  let graphWidth = canvasWidth - curveMarginLeft margin - curveMarginRight margin
      frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
      frameStep = calculateGridStep frameRange graphWidth (fromIntegral minSpacing)
      firstFrame = realToFrac (ceiling (curveViewStateFrameStart viewState / frameStep)) * frameStep
      go frame acc
        | frame > curveViewStateFrameEnd viewState = acc
        | otherwise =
            let x = frameToScreenX frame viewState canvasWidth margin
            in go (frame + frameStep) ((frame, x) : acc)
  in reverse (go firstFrame [])

-- | Value grid: list of (value, screenY) for horizontal lines
gridValueLines
  :: CurveViewState
  -> Double
  -> Double
  -> CurveMargin
  -> Int
  -> [(Double, Double)]
gridValueLines viewState _canvasWidth canvasHeight margin minSpacing =
  let graphHeight = canvasHeight - curveMarginTop margin - curveMarginBottom margin
      valueRange = curveViewStateValueMax viewState - curveViewStateValueMin viewState
      valueStep = calculateGridStep valueRange graphHeight (fromIntegral minSpacing)
      firstValue = realToFrac (ceiling (curveViewStateValueMin viewState / valueStep)) * valueStep
      go value acc
        | value > curveViewStateValueMax viewState = acc
        | otherwise =
            let y = valueToScreenY value viewState canvasHeight margin
            in go (value + valueStep) ((value, y) : acc)
  in reverse (go firstValue [])

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // curve // segment // data
-- ════════════════════════════════════════════════════════════════════════════

data CurveSegmentType
  = SegmentHold { segmentEndX :: Double, segmentEndY :: Double, segmentHoldY :: Double }
  | SegmentLinear { segmentEndX :: Double, segmentEndY :: Double }
  | SegmentBezier
      { segmentEndX :: Double
      , segmentEndY :: Double
      , segmentCp1X :: Double
      , segmentCp1Y :: Double
      , segmentCp2X :: Double
      , segmentCp2Y :: Double
      }
  deriving (Eq, Show)

-- | Out handle frame offset; 0 if disabled
outHandleFrameOffset :: Keyframe PropertyValue -> Double
outHandleFrameOffset kf =
  if bezierHandleEnabled (keyframeOutHandle kf) then bezierHandleFrame (keyframeOutHandle kf) else 0

-- | Out handle value offset; 0 if disabled
outHandleValueOffset :: Keyframe PropertyValue -> Double
outHandleValueOffset kf =
  if bezierHandleEnabled (keyframeOutHandle kf) then bezierHandleValue (keyframeOutHandle kf) else 0

-- | In handle frame offset; 0 if disabled
inHandleFrameOffset :: Keyframe PropertyValue -> Double
inHandleFrameOffset kf =
  if bezierHandleEnabled (keyframeInHandle kf) then bezierHandleFrame (keyframeInHandle kf) else 0

-- | In handle value offset; 0 if disabled
inHandleValueOffset :: Keyframe PropertyValue -> Double
inHandleValueOffset kf =
  if bezierHandleEnabled (keyframeInHandle kf) then bezierHandleValue (keyframeInHandle kf) else 0

-- | One segment between keyframe i and i+1. Nothing if segment is outside view or invalid.
curveSegmentData
  :: CurveViewState
  -> Double
  -> Double
  -> CurveMargin
  -> Keyframe PropertyValue
  -> Keyframe PropertyValue
  -> Double
  -> Double
  -> Double
  -> Double
  -> Maybe CurveSegmentType
curveSegmentData viewState canvasWidth canvasHeight margin kf1 kf2 x1 y1 x2 y2
  | keyframeFrame kf2 < curveViewStateFrameStart viewState = Nothing
  | keyframeFrame kf1 > curveViewStateFrameEnd viewState = Nothing
  | keyframeInterpolation kf1 == InterpolationBase InterpolationHold =
      Just (SegmentHold x2 y2 y1)
  | not (hasBezierHandles kf1 kf2) =
      Just (SegmentLinear x2 y2)
  | otherwise =
      let cp1x = frameToScreenX (keyframeFrame kf1 + outHandleFrameOffset kf1) viewState canvasWidth margin
          cp1y = valueToScreenY (getNumericValue (keyframeValue kf1) + outHandleValueOffset kf1) viewState canvasHeight margin
          cp2x = frameToScreenX (keyframeFrame kf2 + inHandleFrameOffset kf2) viewState canvasWidth margin
          cp2y = valueToScreenY (getNumericValue (keyframeValue kf2) + inHandleValueOffset kf2) viewState canvasHeight margin
      in Just (SegmentBezier x2 y2 cp1x cp1y cp2x cp2y)

hasBezierHandles :: Keyframe PropertyValue -> Keyframe PropertyValue -> Bool
hasBezierHandles kf1 kf2 =
  bezierHandleEnabled (keyframeOutHandle kf1) && bezierHandleEnabled (keyframeInHandle kf2)
