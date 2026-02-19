-- | Lattice.Services.Depth.LayerTraversal - Layer Depth Extraction
-- |
-- | Pure functions for extracting depth information from layers:
-- | - Layer Z position extraction (static and animated)
-- | - Layer opacity extraction (static and animated)
-- | - Screen bounds calculation with transform
-- | - Layer sorting by depth
-- |
-- | Source: ui/src/services/export/depthRenderer.ts (lines 160-314)

module Lattice.Services.Depth.LayerTraversal
  ( Position3D(..)
  , Scale2D(..)
  , AnchorPoint(..)
  , LayerTransform(..)
  , ScreenBounds(..)
  , Keyframe(..)
  , KeyframeMulti(..)
  , LayerWithDepth(..)
  , defaultPosition
  , defaultScale
  , defaultAnchor
  , defaultTransform
  , defaultOpacity
  , getStaticDepth
  , lerpValue
  , findSurroundingKeyframes
  , interpolateZFromKeyframes
  , getLayerDepth
  , normalizeOpacity
  , interpolateOpacityFromKeyframes
  , getLayerOpacity
  , calculateScaledDimensions
  , toScreenCoordinates
  , clipBoundsToScreen
  , calculateNormalizedAnchor
  , getLayerScreenBounds
  , sortLayersByDepth
  , filterVisibleLayers
  ) where

import Prelude

import Data.Array (filter, head, last, length, sortBy, (!!))
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Math (abs, max, min)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D position with x, y, z coordinates.
type Position3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | 2D scale factors.
type Scale2D =
  { scaleX :: Number
  , scaleY :: Number
  }

-- | 2D anchor point.
type AnchorPoint =
  { anchorX :: Number
  , anchorY :: Number
  }

-- | Layer transform data.
type LayerTransform =
  { position :: Position3D
  , scale :: Scale2D
  , anchor :: AnchorPoint
  }

-- | Screen bounds rectangle.
type ScreenBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Keyframe for interpolation (single value).
type Keyframe =
  { frame :: Int
  , value :: Number
  }

-- | Multi-dimensional keyframe (for position, scale, etc.).
type KeyframeMulti =
  { frame :: Int
  , values :: Array Number
  }

-- | Layer with extracted depth for sorting.
type LayerWithDepth a =
  { layer :: a
  , depth :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default position at origin.
defaultPosition :: Position3D
defaultPosition = { x: 0.0, y: 0.0, z: 0.0 }

-- | Default scale (100%).
defaultScale :: Scale2D
defaultScale = { scaleX: 1.0, scaleY: 1.0 }

-- | Default anchor at center (0.5, 0.5).
defaultAnchor :: AnchorPoint
defaultAnchor = { anchorX: 0.5, anchorY: 0.5 }

-- | Default transform.
defaultTransform :: LayerTransform
defaultTransform =
  { position: defaultPosition
  , scale: defaultScale
  , anchor: defaultAnchor
  }

-- | Default opacity (100%).
defaultOpacity :: Number
defaultOpacity = 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Depth Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Extract Z value from static position.
getStaticDepth :: Position3D -> Number
getStaticDepth pos = pos.z

-- | Interpolate between two keyframe values.
-- | t should be in [0, 1] range.
lerpValue :: Number -> Number -> Number -> Number
lerpValue prev next t = prev + (next - prev) * t

-- | Find surrounding keyframes for a given frame.
-- | Returns (prevKeyframe, nextKeyframe, interpolationFactor).
findSurroundingKeyframes :: Array KeyframeMulti -> Int
                         -> Maybe { prev :: KeyframeMulti, next :: KeyframeMulti, t :: Number }
findSurroundingKeyframes keyframes frame
  | length keyframes == 0 = Nothing
  | otherwise =
      let sorted = sortBy (\a b -> compare a.frame b.frame) keyframes
          first = fromMaybe { frame: 0, values: [] } (head sorted)
          lastKf = fromMaybe first (last sorted)

          findPrev :: Array KeyframeMulti -> KeyframeMulti -> KeyframeMulti
          findPrev kfs acc = case head kfs of
            Nothing -> acc
            Just kf ->
              if kf.frame <= frame
              then findPrev (fromMaybe [] ((\arr -> filter (\_ -> true) arr) <$> Just (sortBy (\a b -> compare a.frame b.frame) keyframes))) kf
              else acc

          prev = first
          next = lastKf

          t = if prev.frame == next.frame
              then 0.0
              else toNumber (frame - prev.frame) /
                   toNumber (next.frame - prev.frame)
      in Just { prev, next, t }

-- | Interpolate Z value from keyframes at given frame.
-- | Z is typically at index 2 in position keyframes.
interpolateZFromKeyframes :: Array KeyframeMulti -> Int -> Number
interpolateZFromKeyframes keyframes frame =
  case findSurroundingKeyframes keyframes frame of
    Nothing -> 0.0
    Just { prev, next, t } ->
      let prevZ = fromMaybe 0.0 (prev.values !! 2)
          nextZ = fromMaybe 0.0 (next.values !! 2)
      in lerpValue prevZ nextZ t

-- | Get layer depth at frame.
-- | Checks for animated position first, falls back to static.
getLayerDepth :: LayerTransform -> Maybe (Array KeyframeMulti) -> Int -> Number
getLayerDepth transform maybeKeyframes frame =
  case maybeKeyframes of
    Just kfs | length kfs > 0 -> interpolateZFromKeyframes kfs frame
    _ -> transform.position.z

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Opacity Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert percentage opacity (0-100) to normalized (0-1).
normalizeOpacity :: Number -> Number
normalizeOpacity percentOpacity =
  max 0.0 (min 1.0 (percentOpacity / 100.0))

-- | Interpolate opacity from keyframes at given frame.
interpolateOpacityFromKeyframes :: Array Keyframe -> Int -> Number
interpolateOpacityFromKeyframes keyframes frame
  | length keyframes == 0 = defaultOpacity
  | otherwise =
      let sorted = sortBy (\a b -> compare a.frame b.frame) keyframes
          first = fromMaybe { frame: 0, value: 100.0 } (head sorted)
          lastKf = fromMaybe first (last sorted)
          prev = first
          next = lastKf
      in if prev.frame == next.frame
         then normalizeOpacity prev.value
         else
           let t = toNumber (frame - prev.frame) /
                   toNumber (next.frame - prev.frame)
               interpolated = lerpValue prev.value next.value t
           in normalizeOpacity interpolated

-- | Get layer opacity at frame.
-- | Returns value in [0, 1] range.
getLayerOpacity :: Number -> Maybe (Array Keyframe) -> Int -> Number
getLayerOpacity staticOpacity maybeKeyframes frame =
  case maybeKeyframes of
    Just kfs | length kfs > 0 -> interpolateOpacityFromKeyframes kfs frame
    _ -> normalizeOpacity staticOpacity

-- ────────────────────────────────────────────────────────────────────────────
-- Screen Bounds Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate scaled dimensions.
calculateScaledDimensions :: Number -> Number -> Scale2D -> Tuple Number Number
calculateScaledDimensions layerWidth layerHeight scale =
  Tuple (layerWidth * scale.scaleX) (layerHeight * scale.scaleY)

-- | Convert layer position to screen coordinates.
-- | Compositor origin is center of screen.
toScreenCoordinates :: Position3D -> Number -> Number -> AnchorPoint
                    -> Number -> Number -> Tuple Number Number
toScreenCoordinates position finalWidth finalHeight anchor screenWidth screenHeight =
  let screenX = position.x - finalWidth * anchor.anchorX + screenWidth / 2.0
      screenY = position.y - finalHeight * anchor.anchorY + screenHeight / 2.0
  in Tuple screenX screenY

-- | Clip bounds to screen dimensions.
-- | Returns Nothing if completely outside screen.
clipBoundsToScreen :: Number -> Number -> Number -> Number
                   -> Number -> Number -> Maybe ScreenBounds
clipBoundsToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight =
  let clippedX = max 0.0 (min screenWidth screenX)
      clippedY = max 0.0 (min screenHeight screenY)
      clippedWidth = max 0.0 $
        min (screenWidth - clippedX) (finalWidth - (clippedX - screenX))
      clippedHeight = max 0.0 $
        min (screenHeight - clippedY) (finalHeight - (clippedY - screenY))
  in if clippedWidth <= 0.0 || clippedHeight <= 0.0
     then Nothing
     else Just { x: clippedX, y: clippedY, width: clippedWidth, height: clippedHeight }

-- | Calculate normalized anchor from pixel anchor point.
calculateNormalizedAnchor :: AnchorPoint -> Number -> Number -> AnchorPoint
calculateNormalizedAnchor pixelAnchor layerWidth layerHeight =
  { anchorX: pixelAnchor.anchorX / layerWidth + 0.5
  , anchorY: pixelAnchor.anchorY / layerHeight + 0.5
  }

-- | Get layer screen bounds.
getLayerScreenBounds :: LayerTransform -> Number -> Number
                     -> Number -> Number -> Maybe ScreenBounds
getLayerScreenBounds transform layerWidth layerHeight screenWidth screenHeight =
  let Tuple finalWidth finalHeight =
        calculateScaledDimensions layerWidth layerHeight transform.scale
      normalizedAnchor =
        calculateNormalizedAnchor transform.anchor layerWidth layerHeight
      Tuple screenX screenY =
        toScreenCoordinates transform.position
                           finalWidth finalHeight
                           normalizedAnchor
                           screenWidth screenHeight
  in clipBoundsToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Sorting
-- ────────────────────────────────────────────────────────────────────────────

-- | Sort layers by depth (front to back from camera).
-- | Lower Z values are closer to camera.
sortLayersByDepth :: forall a. Array (LayerWithDepth a) -> Array (LayerWithDepth a)
sortLayersByDepth = sortBy (\a b -> compare a.depth b.depth)

-- | Filter out invisible layers (opacity below threshold).
filterVisibleLayers :: forall a. Array (Tuple (LayerWithDepth a) Number) -> Number
                    -> Array (LayerWithDepth a)
filterVisibleLayers layers opacityThreshold =
  map (\(Tuple lwd _) -> lwd) $
    filter (\(Tuple _ opacity) -> opacity >= opacityThreshold) layers
