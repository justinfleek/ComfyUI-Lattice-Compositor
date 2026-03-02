{-|
Module      : Lattice.Services.Depth.LayerTraversal
Description : Layer depth extraction and screen bounds calculation
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for extracting depth information from layers:
- Layer Z position extraction (static and animated)
- Layer opacity extraction (static and animated)
- Screen bounds calculation with transform
- Layer sorting by depth

Source: ui/src/services/export/depthRenderer.ts (lines 160-314)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Depth.LayerTraversal
  ( -- * Types
    Position3D(..)
  , Scale2D(..)
  , AnchorPoint(..)
  , LayerTransform(..)
  , ScreenBounds(..)
  , Keyframe(..)
  , KeyframeMulti(..)
  , LayerWithDepth(..)
    -- * Default Values
  , defaultPosition
  , defaultScale
  , defaultAnchor
  , defaultTransform
  , defaultOpacity
    -- * Layer Depth Extraction
  , getStaticDepth
  , lerpValue
  , findSurroundingKeyframes
  , interpolateZFromKeyframes
  , getLayerDepth
    -- * Layer Opacity Extraction
  , normalizeOpacity
  , interpolateOpacityFromKeyframes
  , getLayerOpacity
    -- * Screen Bounds Calculation
  , calculateScaledDimensions
  , toScreenCoordinates
  , clipBoundsToScreen
  , calculateNormalizedAnchor
  , getLayerScreenBounds
    -- * Layer Sorting
  , sortLayersByDepth
  , filterVisibleLayers
  ) where

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D position with x, y, z coordinates.
data Position3D = Position3D
  { pos3dX :: Double
  , pos3dY :: Double
  , pos3dZ :: Double
  } deriving (Show, Eq)

-- | 2D scale factors.
data Scale2D = Scale2D
  { scale2dX :: Double
  , scale2dY :: Double
  } deriving (Show, Eq)

-- | 2D anchor point.
data AnchorPoint = AnchorPoint
  { anchorX :: Double
  , anchorY :: Double
  } deriving (Show, Eq)

-- | Layer transform data.
data LayerTransform = LayerTransform
  { ltPosition :: Position3D
  , ltScale    :: Scale2D
  , ltAnchor   :: AnchorPoint
  } deriving (Show, Eq)

-- | Screen bounds rectangle.
data ScreenBounds = ScreenBounds
  { sbX      :: Double
  , sbY      :: Double
  , sbWidth  :: Double
  , sbHeight :: Double
  } deriving (Show, Eq)

-- | Keyframe for interpolation (single value).
data Keyframe = Keyframe
  { kfFrame :: Int
  , kfValue :: Double
  } deriving (Show, Eq)

-- | Multi-dimensional keyframe (for position, scale, etc.).
data KeyframeMulti = KeyframeMulti
  { kfmFrame  :: Int
  , kfmValues :: Vector Double
  } deriving (Show, Eq)

-- | Layer with extracted depth for sorting.
data LayerWithDepth a = LayerWithDepth
  { lwdLayer :: a
  , lwdDepth :: Double
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default position at origin.
defaultPosition :: Position3D
defaultPosition = Position3D 0 0 0

-- | Default scale (100%).
defaultScale :: Scale2D
defaultScale = Scale2D 1 1

-- | Default anchor at center (0.5, 0.5).
defaultAnchor :: AnchorPoint
defaultAnchor = AnchorPoint 0.5 0.5

-- | Default transform.
defaultTransform :: LayerTransform
defaultTransform = LayerTransform defaultPosition defaultScale defaultAnchor

-- | Default opacity (100%).
defaultOpacity :: Double
defaultOpacity = 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Depth Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Extract Z value from static position.
getStaticDepth :: Position3D -> Double
getStaticDepth = pos3dZ

-- | Interpolate between two keyframe values.
-- t should be in [0, 1] range.
lerpValue :: Double -> Double -> Double -> Double
lerpValue prev next t = prev + (next - prev) * t

-- | Find surrounding keyframes for a given frame.
-- Returns (prevKeyframe, nextKeyframe, interpolationFactor).
findSurroundingKeyframes :: Vector KeyframeMulti -> Int
                         -> Maybe (KeyframeMulti, KeyframeMulti, Double)
findSurroundingKeyframes keyframes frame
  | V.null keyframes = Nothing
  | otherwise =
      let sorted = V.toList $ V.modify (sortBy (comparing kfmFrame)) keyframes
          first = head sorted
          lastKf = last sorted

          findPrev [] acc = acc
          findPrev (kf:rest) acc
            | kfmFrame kf <= frame = findPrev rest kf
            | otherwise = acc

          findNext [] acc = acc
          findNext (kf:rest) acc
            | kfmFrame kf >= frame && kfmFrame acc < frame = kf
            | otherwise = findNext rest acc

          prev = findPrev sorted first
          next = findNext sorted lastKf

          t = if kfmFrame prev == kfmFrame next
              then 0.0
              else fromIntegral (frame - kfmFrame prev) /
                   fromIntegral (kfmFrame next - kfmFrame prev)
      in Just (prev, next, t)

-- | Interpolate Z value from keyframes at given frame.
-- Z is typically at index 2 in position keyframes.
interpolateZFromKeyframes :: Vector KeyframeMulti -> Int -> Double
interpolateZFromKeyframes keyframes frame =
  case findSurroundingKeyframes keyframes frame of
    Nothing -> 0.0
    Just (prev, next, t) ->
      let prevZ = if V.length (kfmValues prev) > 2
                  then kfmValues prev V.! 2 else 0.0
          nextZ = if V.length (kfmValues next) > 2
                  then kfmValues next V.! 2 else 0.0
      in lerpValue prevZ nextZ t

-- | Get layer depth at frame.
-- Checks for animated position first, falls back to static.
getLayerDepth :: LayerTransform -> Maybe (Vector KeyframeMulti) -> Int -> Double
getLayerDepth transform maybeKeyframes frame =
  case maybeKeyframes of
    Just kfs | not (V.null kfs) -> interpolateZFromKeyframes kfs frame
    _ -> pos3dZ (ltPosition transform)

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Opacity Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert percentage opacity (0-100) to normalized (0-1).
normalizeOpacity :: Double -> Double
normalizeOpacity percentOpacity =
  max 0.0 (min 1.0 (percentOpacity / 100.0))

-- | Interpolate opacity from keyframes at given frame.
interpolateOpacityFromKeyframes :: Vector Keyframe -> Int -> Double
interpolateOpacityFromKeyframes keyframes frame
  | V.null keyframes = defaultOpacity
  | otherwise =
      let sorted = V.toList $ V.modify (sortBy (comparing kfFrame)) keyframes
          first = head sorted
          lastKf = last sorted

          findPrev [] acc = acc
          findPrev (kf:rest) acc
            | kfFrame kf <= frame = findPrev rest kf
            | otherwise = acc

          findNext [] acc = acc
          findNext (kf:rest) acc
            | kfFrame kf >= frame && kfFrame acc < frame = kf
            | otherwise = findNext rest acc

          prev = findPrev sorted first
          next = findNext sorted lastKf
      in if kfFrame prev == kfFrame next
         then normalizeOpacity (kfValue prev)
         else
           let t = fromIntegral (frame - kfFrame prev) /
                   fromIntegral (kfFrame next - kfFrame prev)
               interpolated = lerpValue (kfValue prev) (kfValue next) t
           in normalizeOpacity interpolated

-- | Get layer opacity at frame.
-- Returns value in [0, 1] range.
getLayerOpacity :: Double -> Maybe (Vector Keyframe) -> Int -> Double
getLayerOpacity staticOpacity maybeKeyframes frame =
  case maybeKeyframes of
    Just kfs | not (V.null kfs) -> interpolateOpacityFromKeyframes kfs frame
    _ -> normalizeOpacity staticOpacity

-- ────────────────────────────────────────────────────────────────────────────
-- Screen Bounds Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate scaled dimensions.
calculateScaledDimensions :: Double -> Double -> Scale2D -> (Double, Double)
calculateScaledDimensions layerWidth layerHeight scale =
  (layerWidth * scale2dX scale, layerHeight * scale2dY scale)

-- | Convert layer position to screen coordinates.
-- Compositor origin is center of screen.
toScreenCoordinates :: Position3D -> Double -> Double -> AnchorPoint
                    -> Double -> Double -> (Double, Double)
toScreenCoordinates position finalWidth finalHeight anchor screenWidth screenHeight =
  let screenX = pos3dX position - finalWidth * anchorX anchor + screenWidth / 2.0
      screenY = pos3dY position - finalHeight * anchorY anchor + screenHeight / 2.0
  in (screenX, screenY)

-- | Clip bounds to screen dimensions.
-- Returns Nothing if completely outside screen.
clipBoundsToScreen :: Double -> Double -> Double -> Double
                   -> Double -> Double -> Maybe ScreenBounds
clipBoundsToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight =
  let clippedX = max 0.0 (min screenWidth screenX)
      clippedY = max 0.0 (min screenHeight screenY)
      clippedWidth = max 0.0 $
        min (screenWidth - clippedX) (finalWidth - (clippedX - screenX))
      clippedHeight = max 0.0 $
        min (screenHeight - clippedY) (finalHeight - (clippedY - screenY))
  in if clippedWidth <= 0.0 || clippedHeight <= 0.0
     then Nothing
     else Just $ ScreenBounds clippedX clippedY clippedWidth clippedHeight

-- | Calculate normalized anchor from pixel anchor point.
calculateNormalizedAnchor :: AnchorPoint -> Double -> Double -> AnchorPoint
calculateNormalizedAnchor pixelAnchor layerWidth layerHeight =
  AnchorPoint
    { anchorX = anchorX pixelAnchor / layerWidth + 0.5
    , anchorY = anchorY pixelAnchor / layerHeight + 0.5
    }

-- | Get layer screen bounds.
getLayerScreenBounds :: LayerTransform -> Double -> Double
                     -> Double -> Double -> Maybe ScreenBounds
getLayerScreenBounds transform layerWidth layerHeight screenWidth screenHeight =
  let (finalWidth, finalHeight) =
        calculateScaledDimensions layerWidth layerHeight (ltScale transform)
      normalizedAnchor =
        calculateNormalizedAnchor (ltAnchor transform) layerWidth layerHeight
      (screenX, screenY) =
        toScreenCoordinates (ltPosition transform)
                           finalWidth finalHeight
                           normalizedAnchor
                           screenWidth screenHeight
  in clipBoundsToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Sorting
-- ────────────────────────────────────────────────────────────────────────────

-- | Sort layers by depth (front to back from camera).
-- Lower Z values are closer to camera.
sortLayersByDepth :: [LayerWithDepth a] -> [LayerWithDepth a]
sortLayersByDepth = sortBy (comparing lwdDepth)

-- | Filter out invisible layers (opacity below threshold).
filterVisibleLayers :: [(LayerWithDepth a, Double)] -> Double -> [LayerWithDepth a]
filterVisibleLayers layers opacityThreshold =
  [lwd | (lwd, opacity) <- layers, opacity >= opacityThreshold]
