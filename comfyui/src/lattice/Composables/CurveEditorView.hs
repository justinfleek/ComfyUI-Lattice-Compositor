-- |
-- Module      : Lattice.Composables.CurveEditorView
-- Description : Curve editor view state (fit, zoom, pan)
--
-- Ported from ui/src/composables/useCurveEditorView.ts
-- Pure view state and zoom/pan math; no Vue/DOM.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.CurveEditorView
  ( -- Types
    SelectedKeyframe(..)
  -- View state
  , createViewState
  -- Fit to view
  , fitToView
  , fitSelectionToView
  -- Zoom
  , zoomIn
  , zoomOut
  , handleWheelZoomPure
  -- Pan
  , panView
  ) where

import Data.Text (Text)
import Lattice.Composables.CurveEditorCoords
  ( CurveMargin(..)
  , CurveViewState(..)
  , defaultCurveMargin
  , getNumericValue
  , screenXToFrame
  , screenYToValue
  )
import Lattice.Types.Animation (AnimatableProperty(..), Keyframe(..), PropertyValue)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Selected keyframe reference (prop id, index, keyframe)
data SelectedKeyframe = SelectedKeyframe
  { selectedKeyframePropId :: Text
  , selectedKeyframeIndex :: Int
  , selectedKeyframeKeyframe :: Keyframe PropertyValue
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // view // state
-- ════════════════════════════════════════════════════════════════════════════

-- | Create initial view state
createViewState
  :: Double
  -> Double
  -> Double
  -> Double
  -> CurveViewState
createViewState frameStart frameEnd valueMin valueMax =
  CurveViewState
    { curveViewStateFrameStart = frameStart
    , curveViewStateFrameEnd = frameEnd
    , curveViewStateValueMin = valueMin
    , curveViewStateValueMax = valueMax
    , curveViewStateZoom = 1
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // fit // to // view
-- ════════════════════════════════════════════════════════════════════════════

-- | Compute bounds (min/max frame and value) from visible properties.
-- If no keyframes, returns (0, 100, 0, 100).
boundsFromProperties :: [AnimatableProperty PropertyValue] -> (Double, Double, Double, Double)
boundsFromProperties [] = (0, 100, 0, 100)
boundsFromProperties props =
  let allFrames = concatMap (map keyframeFrame . animatablePropertyKeyframes) props
      allValues = concatMap (map (getNumericValue . keyframeValue) . animatablePropertyKeyframes) props
      minF = if null allFrames then 0 else minimum allFrames
      maxF = if null allFrames then 100 else maximum allFrames
      minV = if null allValues then 0 else minimum allValues
      maxV = if null allValues then 100 else maximum allValues
  in (minF, maxF, minV, maxV)

-- | Add 10% padding (or 10 if range is 0)
addPadding :: Double -> Double -> (Double, Double)
addPadding lo hi =
  let r = hi - lo
      margin = if r == 0 then 10 else r * 0.1
  in (lo - margin, hi + margin)

-- | Fit view to show all visible keyframes (pure: returns new view state)
fitToView
  :: [AnimatableProperty PropertyValue]
  -> CurveViewState
  -> CurveViewState
fitToView visibleProperties viewState
  | null visibleProperties = viewState
  | otherwise =
      let (minFrame, maxFrame, minValue, maxValue) = boundsFromProperties visibleProperties
          (frameStart', frameEnd') = addPadding minFrame maxFrame
          (valueMin', valueMax') = addPadding minValue maxValue
      in viewState
           { curveViewStateFrameStart = frameStart'
           , curveViewStateFrameEnd = frameEnd'
           , curveViewStateValueMin = valueMin'
           , curveViewStateValueMax = valueMax'
           }

-- | Fit view to selected keyframes; if none selected, fit to all visible
fitSelectionToView
  :: [SelectedKeyframe]
  -> [AnimatableProperty PropertyValue]
  -> CurveViewState
  -> CurveViewState
fitSelectionToView selected visibleProperties viewState
  | null selected = fitToView visibleProperties viewState
  | otherwise =
      let frames = map (keyframeFrame . selectedKeyframeKeyframe) selected
          values = map (getNumericValue . keyframeValue . selectedKeyframeKeyframe) selected
          minF = minimum frames
          maxF = maximum frames
          minV = minimum values
          maxV = maximum values
          (frameStart', frameEnd') = addPadding minF maxF
          (valueMin', valueMax') = addPadding minV maxV
      in viewState
           { curveViewStateFrameStart = frameStart'
           , curveViewStateFrameEnd = frameEnd'
           , curveViewStateValueMin = valueMin'
           , curveViewStateValueMax = valueMax'
           }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                      // zoom
-- ════════════════════════════════════════════════════════════════════════════

-- | Zoom in (narrow frame/value range by 40%)
zoomIn :: CurveViewState -> CurveViewState
zoomIn viewState =
  let centerFrame = (curveViewStateFrameStart viewState + curveViewStateFrameEnd viewState) / 2
      frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
      newRange = frameRange * 0.4
  in viewState
       { curveViewStateFrameStart = centerFrame - newRange / 2
       , curveViewStateFrameEnd = centerFrame + newRange / 2
       }

-- | Zoom out (widen frame/value range by 60%)
zoomOut :: CurveViewState -> CurveViewState
zoomOut viewState =
  let centerFrame = (curveViewStateFrameStart viewState + curveViewStateFrameEnd viewState) / 2
      frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
      newRange = frameRange * 0.6
  in viewState
       { curveViewStateFrameStart = centerFrame - newRange / 2
       , curveViewStateFrameEnd = centerFrame + newRange / 2
       }

-- | Handle wheel zoom around cursor (pure math). zoomFactor > 1 = zoom out, < 1 = zoom in.
-- If shiftOnly then only frame axis is zoomed; else both frame and value.
handleWheelZoomPure
  :: Double
  -> Double
  -> Double
  -> Bool
  -> CurveViewState
  -> Double
  -> Double
  -> CurveMargin
  -> CurveViewState
handleWheelZoomPure cursorX cursorY zoomFactor shiftOnly viewState canvasWidth canvasHeight margin =
  let frameAtCursor = screenXToFrame cursorX viewState canvasWidth margin
      valueAtCursor = screenYToValue cursorY viewState canvasHeight margin
      newFrameStart = frameAtCursor - (frameAtCursor - curveViewStateFrameStart viewState) * zoomFactor
      newFrameEnd = frameAtCursor + (curveViewStateFrameEnd viewState - frameAtCursor) * zoomFactor
      base = viewState
        { curveViewStateFrameStart = newFrameStart
        , curveViewStateFrameEnd = newFrameEnd
        }
  in if shiftOnly
       then base
       else base
            { curveViewStateValueMin = valueAtCursor - (valueAtCursor - curveViewStateValueMin viewState) * zoomFactor
            , curveViewStateValueMax = valueAtCursor + (curveViewStateValueMax viewState - valueAtCursor) * zoomFactor
            }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // pan
-- ════════════════════════════════════════════════════════════════════════════

-- | Pan view by delta pixels (pure: returns new view state).
-- No-op if graph width or height is non-positive (avoids division by zero).
panView
  :: CurveViewState
  -> Double
  -> Double
  -> Double
  -> Double
  -> CurveMargin
  -> CurveViewState
panView viewState deltaX deltaY canvasWidth canvasHeight margin
  | graphWidth <= 0 || graphHeight <= 0 = viewState
  | otherwise =
      viewState
        { curveViewStateFrameStart = curveViewStateFrameStart viewState + frameShift
        , curveViewStateFrameEnd = curveViewStateFrameEnd viewState + frameShift
        , curveViewStateValueMin = curveViewStateValueMin viewState + valueShift
        , curveViewStateValueMax = curveViewStateValueMax viewState + valueShift
        }
  where
    graphWidth = canvasWidth - curveMarginLeft margin - curveMarginRight margin
    graphHeight = canvasHeight - curveMarginTop margin - curveMarginBottom margin
    frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
    valueShift = (deltaY / graphHeight) * (curveViewStateValueMax viewState - curveViewStateValueMin viewState)
    frameShift = (-deltaX / graphWidth) * frameRange
