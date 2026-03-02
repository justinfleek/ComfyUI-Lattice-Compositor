-- |
-- Module      : Lattice.Composables.CurveEditorCoords
-- Description : Curve editor coordinate conversion (frame/value <-> screen pixels)
--
-- Ported from ui/src/composables/useCurveEditorCoords.ts
-- Pure coordinate conversion for the curve editor (graph editor).
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.CurveEditorCoords
  ( -- Types
    CurveViewState(..)
  , CurveMargin(..)
  , defaultCurveMargin
  -- Coordinate conversion
  , frameToScreenX
  , screenXToFrame
  , valueToScreenY
  , screenYToValue
  -- Keyframe position helpers
  , getKeyframeScreenX
  , getKeyframeScreenY
  , getNumericValue
  , getKeyframeDisplayValue
  -- Handle position helpers
  , getOutHandleX
  , getOutHandleY
  , getInHandleX
  , getInHandleY
  -- Utilities
  , isKeyframeInView
  , calculateGridStep
  , getPropertyPath
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , BezierHandle(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Primitives (Vec2(..), Vec3(..), validateFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | View state for the curve editor (frame/value range and zoom)
data CurveViewState = CurveViewState
  { curveViewStateFrameStart :: Double
  , curveViewStateFrameEnd :: Double
  , curveViewStateValueMin :: Double
  , curveViewStateValueMax :: Double
  , curveViewStateZoom :: Double
  }
  deriving (Eq, Show)

-- | Margin around the graph area (pixels)
data CurveMargin = CurveMargin
  { curveMarginTop :: Double
  , curveMarginRight :: Double
  , curveMarginBottom :: Double
  , curveMarginLeft :: Double
  }
  deriving (Eq, Show)

-- | Default margin values (10px on all sides)
defaultCurveMargin :: CurveMargin
defaultCurveMargin = CurveMargin 10 10 10 10

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // coordinate // conversion
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert frame number to screen X coordinate
frameToScreenX
  :: Double
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
frameToScreenX frame viewState canvasWidth margin =
  let graphWidth = canvasWidth - curveMarginLeft margin - curveMarginRight margin
      frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
      t = if frameRange == 0 then 0 else (frame - curveViewStateFrameStart viewState) / frameRange
  in curveMarginLeft margin + t * graphWidth

-- | Convert screen X coordinate to frame number
screenXToFrame
  :: Double
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
screenXToFrame screenX viewState canvasWidth margin =
  let graphWidth = canvasWidth - curveMarginLeft margin - curveMarginRight margin
      t = if graphWidth == 0 then 0 else (screenX - curveMarginLeft margin) / graphWidth
      frameRange = curveViewStateFrameEnd viewState - curveViewStateFrameStart viewState
  in curveViewStateFrameStart viewState + t * frameRange

-- | Convert value to screen Y coordinate (Y-down screen space)
valueToScreenY
  :: Double
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
valueToScreenY value viewState canvasHeight margin =
  let graphHeight = canvasHeight - curveMarginTop margin - curveMarginBottom margin
      valueRange = curveViewStateValueMax viewState - curveViewStateValueMin viewState
      t = if valueRange == 0 then 0 else (value - curveViewStateValueMin viewState) / valueRange
  in canvasHeight - curveMarginBottom margin - t * graphHeight

-- | Convert screen Y coordinate to value
screenYToValue
  :: Double
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
screenYToValue screenY viewState canvasHeight margin =
  let graphHeight = canvasHeight - curveMarginTop margin - curveMarginBottom margin
      t = if graphHeight == 0 then 0 else (canvasHeight - curveMarginBottom margin - screenY) / graphHeight
      valueRange = curveViewStateValueMax viewState - curveViewStateValueMin viewState
  in curveViewStateValueMin viewState + t * valueRange

-- ════════════════════════════════════════════════════════════════════════════
--                                           // keyframe // position // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Get screen X coordinate for a keyframe
getKeyframeScreenX
  :: Keyframe PropertyValue
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getKeyframeScreenX kf viewState canvasWidth margin =
  frameToScreenX (keyframeFrame kf) viewState canvasWidth margin

-- | Get screen Y coordinate for a keyframe (uses first numeric component of value)
getKeyframeScreenY
  :: AnimatableProperty PropertyValue
  -> Int
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getKeyframeScreenY prop kfIndex viewState canvasHeight margin =
  let kfs = animatablePropertyKeyframes prop
      kf = safeIndex kfs kfIndex
      val = case kf of
        Just k -> getNumericValue (keyframeValue k)
        Nothing -> 0
  in valueToScreenY val viewState canvasHeight margin

safeIndex :: [a] -> Int -> Maybe a
safeIndex [] _ = Nothing
safeIndex (x : _) 0 = Just x
safeIndex (_ : xs) n | n > 0 = safeIndex xs (n - 1)
safeIndex _ _ = Nothing

-- | Extract numeric value from PropertyValue (single number or first component of Vec2/Vec3)
getNumericValue :: PropertyValue -> Double
getNumericValue (PropertyValueNumber n) = n
getNumericValue (PropertyValueVec2 (Vec2 x _)) = x
getNumericValue (PropertyValuePosition2DOr3D (Vec2 x _) _) = x
getNumericValue (PropertyValueVec3 (Vec3 x _ _)) = x
getNumericValue (PropertyValueRGBA _) = 0
getNumericValue (PropertyValueString _) = 0
getNumericValue (PropertyValueBool _) = 0

-- | Get display value for a keyframe (for UI); same as getNumericValue on keyframe value
getKeyframeDisplayValue :: Maybe (Keyframe PropertyValue) -> Double
getKeyframeDisplayValue Nothing = 0
getKeyframeDisplayValue (Just kf) = getNumericValue (keyframeValue kf)

-- ════════════════════════════════════════════════════════════════════════════
--                                             // handle // position // helpers
-- ════════════════════════════════════════════════════════════════════════════

outHandleEnabled :: Keyframe a -> Bool
outHandleEnabled kf = bezierHandleEnabled (keyframeOutHandle kf)

inHandleEnabled :: Keyframe a -> Bool
inHandleEnabled kf = bezierHandleEnabled (keyframeInHandle kf)

-- | Get screen X for outgoing handle (or keyframe frame if handle disabled)
getOutHandleX
  :: AnimatableProperty PropertyValue
  -> Int
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getOutHandleX prop kfIndex viewState canvasWidth margin =
  case safeIndex (animatablePropertyKeyframes prop) kfIndex of
    Nothing -> curveMarginLeft margin
    Just kf ->
      if outHandleEnabled kf
        then let h = keyframeOutHandle kf
                 handleFrame = keyframeFrame kf + bezierHandleFrame h
             in frameToScreenX handleFrame viewState canvasWidth margin
        else frameToScreenX (keyframeFrame kf) viewState canvasWidth margin

-- | Get screen Y for outgoing handle
getOutHandleY
  :: AnimatableProperty PropertyValue
  -> Int
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getOutHandleY prop kfIndex viewState canvasHeight margin =
  case safeIndex (animatablePropertyKeyframes prop) kfIndex of
    Nothing -> 0
    Just kf ->
      if outHandleEnabled kf
        then let h = keyframeOutHandle kf
                 val = getNumericValue (keyframeValue kf) + bezierHandleValue h
             in valueToScreenY val viewState canvasHeight margin
        else valueToScreenY (getNumericValue (keyframeValue kf)) viewState canvasHeight margin

-- | Get screen X for incoming handle
getInHandleX
  :: AnimatableProperty PropertyValue
  -> Int
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getInHandleX prop kfIndex viewState canvasWidth margin =
  case safeIndex (animatablePropertyKeyframes prop) kfIndex of
    Nothing -> curveMarginLeft margin
    Just kf ->
      if inHandleEnabled kf
        then let h = keyframeInHandle kf
                 handleFrame = keyframeFrame kf + bezierHandleFrame h
             in frameToScreenX handleFrame viewState canvasWidth margin
        else frameToScreenX (keyframeFrame kf) viewState canvasWidth margin

-- | Get screen Y for incoming handle
getInHandleY
  :: AnimatableProperty PropertyValue
  -> Int
  -> CurveViewState
  -> Double
  -> CurveMargin
  -> Double
getInHandleY prop kfIndex viewState canvasHeight margin =
  case safeIndex (animatablePropertyKeyframes prop) kfIndex of
    Nothing -> 0
    Just kf ->
      if inHandleEnabled kf
        then let h = keyframeInHandle kf
                 val = getNumericValue (keyframeValue kf) + bezierHandleValue h
             in valueToScreenY val viewState canvasHeight margin
        else valueToScreenY (getNumericValue (keyframeValue kf)) viewState canvasHeight margin

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // utilities
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if a keyframe is within the current view bounds
isKeyframeInView :: Keyframe PropertyValue -> CurveViewState -> Bool
isKeyframeInView kf viewState =
  let f = keyframeFrame kf
      start = curveViewStateFrameStart viewState
      end = curveViewStateFrameEnd viewState
  in f >= start && f <= end

-- | Calculate optimal grid step size for axis labels
calculateGridStep :: Double -> Double -> Double -> Double
calculateGridStep range pixelSize targetSpacing
  | pixelSize <= 0 || not (validateFinite (range * targetSpacing / pixelSize)) = 1
  | otherwise =
      let rawStep = max 1e-10 ((range * targetSpacing) / pixelSize)
          magnitude = 10 ** fromIntegral (floor (logBase 10 rawStep) :: Int)
          normalized = rawStep / magnitude
      in if normalized <= 1 then magnitude
         else if normalized <= 2 then 2 * magnitude
         else if normalized <= 5 then 5 * magnitude
         else 10 * magnitude

-- | Get property path from AnimatableProperty name for store operations
getPropertyPath :: AnimatableProperty PropertyValue -> Text
getPropertyPath prop =
  let name = T.toLower (animatablePropertyName prop)
  in if name == "position" then "transform.position"
     else if name == "scale" then "transform.scale"
     else if name == "rotation" then "transform.rotation"
     else if name == "opacity" then "opacity"
     else if name == "origin" || name == "anchor point" then "transform.anchorPoint"
     else animatablePropertyId prop
