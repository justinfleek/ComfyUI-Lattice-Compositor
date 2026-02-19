-- |
-- Module      : Lattice.Composables.ViewportControls
-- Description : Viewport zoom/pan math and screen↔scene conversion
--
-- Ported from ui/src/composables/useViewportControls.ts
-- Pure math only; no engine refs or DOM.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.ViewportControls
  ( -- Zoom
    zoomInValue
  , zoomOutValue
  , clampZoom
  , setZoomChecked
  -- Fit / center
  , fitZoomWithPadding
  , viewportTransformFromFit
  -- Coordinate conversion
  , screenToScene
  ) where

import Data.Text (Text)
import Lattice.Utils.NumericSafety (isFinite)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                      // zoom
-- ════════════════════════════════════════════════════════════════════════════

minZoom, maxZoom :: Double
minZoom = 0.1
maxZoom = 10

zoomStepIn, zoomStepOut :: Double
zoomStepIn = 1.2
zoomStepOut = 0.8

-- | Next zoom value when zooming in (clamped)
zoomInValue :: Double -> Double
zoomInValue z = min maxZoom (z * zoomStepIn)

-- | Next zoom value when zooming out (clamped)
zoomOutValue :: Double -> Double
zoomOutValue z = max minZoom (z * zoomStepOut)

-- | Clamp zoom to [0.1, 10]
clampZoom :: Double -> Double
clampZoom z = max minZoom (min maxZoom z)

-- | Validate and clamp zoom. Left = invalid input message.
setZoomChecked :: Double -> Either Text Double
setZoomChecked z
  | not (isFinite z) = Left $ "Invalid zoom: not finite (" <> T.pack (show z) <> ")"
  | z <= 0 = Left $ "Invalid zoom: must be positive (" <> T.pack (show z) <> ")"
  | otherwise = Right (clampZoom z)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // fit
-- ════════════════════════════════════════════════════════════════════════════

-- | Fit zoom with padding (e.g. 0.85). Returns Nothing if any dimension <= 0.
fitZoomWithPadding
  :: Double
  -> Double
  -> Double
  -> Double
  -> Double
  -> Maybe Double
fitZoomWithPadding compW compH viewW viewH padding
  | compW <= 0 || compH <= 0 || viewW <= 0 || viewH <= 0 = Nothing
  | otherwise =
      Just $
        min
          ((viewW * padding) / compW)
          ((viewH * padding) / compH)

-- | Viewport transform [scaleX, skewX, skewY, scaleY, panX, panY] from fit.
-- Returns Nothing if dimensions invalid.
viewportTransformFromFit
  :: Double
  -> Double
  -> Double
  -> Double
  -> Double
  -> Maybe [Double]
viewportTransformFromFit compW compH viewW viewH padding = do
  fitZ <- fitZoomWithPadding compW compH viewW viewH padding
  let scaledW = compW * fitZ
      scaledH = compH * fitZ
      panX = (viewW - scaledW) / 2
      panY = (viewH - scaledH) / 2
  pure [fitZ, 0, 0, fitZ, panX, panY]

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // coordinate // conversion
-- ════════════════════════════════════════════════════════════════════════════

-- | Viewport transform: [scaleX, skewX, skewY, scaleY, panX, panY]
-- Convert screen (pixel) to scene coordinates.
-- Returns Left on invalid scale (zero or non-finite).
screenToScene
  :: Double
  -> Double
  -> [Double]
  -> Either Text (Double, Double)
screenToScene screenX screenY vpt =
  case vpt of
    (scaleX : _ : _ : scaleY : px : py : _) ->
      let panX = if isFinite px then px else 0
          panY = if isFinite py then py else 0
      in if not (isFinite scaleX) || scaleX == 0
           then Left $ "Invalid scaleX: " <> T.pack (show scaleX)
           else
             if not (isFinite scaleY) || scaleY == 0
               then Left $ "Invalid scaleY: " <> T.pack (show scaleY)
               else Right
                    ( (screenX - panX) / scaleX
                    , (screenY - panY) / scaleY
                    )
    _ -> Left "viewportTransform must have 6 elements"
