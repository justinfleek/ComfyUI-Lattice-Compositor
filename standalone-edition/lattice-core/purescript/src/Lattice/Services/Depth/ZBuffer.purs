{-
  Lattice.Services.Depth.ZBuffer - Z-Buffer Operations

  Pure mathematical functions for depth buffer operations:
  - Z-buffer initialization
  - Depth testing (closer wins)
  - Layer depth sorting
  - Screen bounds calculation
  - Uniform depth fill
  - Circular splat rendering

  Source: ui/src/services/export/depthRenderer.ts (lines 45-511)
-}

module Lattice.Services.Depth.ZBuffer
  ( ScreenBounds
  , mkScreenBounds
  , sbX, sbY, sbWidth, sbHeight
  , CameraPosition
  , mkCameraPosition
  , cpX, cpY, cpZ
  , LayerTransform
  , mkLayerTransform
  , ltPositionX, ltPositionY, ltPositionZ
  , ltScaleX, ltScaleY
  , ltAnchorX, ltAnchorY
  , DepthResult
  , mkDepthResult
  , drMinDepth, drMaxDepth
  -- * Z-Buffer Initialization
  , initDepth
  , initialMinMax
  -- * Depth Testing
  , isCloser
  , updateDepth
  , updateMinMax
  -- * Layer Depth Calculation
  , relativeDepth
  , clampToClipRange
  , calculateLayerDepth
  -- * Screen Bounds Calculation
  , scaledDimensions
  , toScreenCoords
  , clipToScreen
  , calculateScreenBounds
  -- * Pixel Index Calculation
  , pixelIndex
  , inBounds
  , fillBounds
  -- * Circular Splat
  , inCircle
  , splatRadius
  -- * Depth Map Sampling
  , sampleDepthCoords
  , uint8ToNormalized
  , normalizedToWorld
  -- * Result Validation
  , validateDepthResult
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Global (infinity, isFinite)
import Math (abs)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Screen bounds rectangle.
type ScreenBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

mkScreenBounds :: Number -> Number -> Number -> Number -> ScreenBounds
mkScreenBounds x y w h = { x, y, width: w, height: h }

sbX :: ScreenBounds -> Number
sbX b = b.x

sbY :: ScreenBounds -> Number
sbY b = b.y

sbWidth :: ScreenBounds -> Number
sbWidth b = b.width

sbHeight :: ScreenBounds -> Number
sbHeight b = b.height

-- | Camera position in 3D.
type CameraPosition =
  { x :: Number
  , y :: Number
  , z :: Number
  }

mkCameraPosition :: Number -> Number -> Number -> CameraPosition
mkCameraPosition x y z = { x, y, z }

cpX :: CameraPosition -> Number
cpX c = c.x

cpY :: CameraPosition -> Number
cpY c = c.y

cpZ :: CameraPosition -> Number
cpZ c = c.z

-- | Layer transform data.
type LayerTransform =
  { positionX :: Number
  , positionY :: Number
  , positionZ :: Number
  , scaleX :: Number
  , scaleY :: Number
  , anchorX :: Number
  , anchorY :: Number
  }

mkLayerTransform :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> LayerTransform
mkLayerTransform px py pz sx sy ax ay =
  { positionX: px
  , positionY: py
  , positionZ: pz
  , scaleX: sx
  , scaleY: sy
  , anchorX: ax
  , anchorY: ay
  }

ltPositionX :: LayerTransform -> Number
ltPositionX t = t.positionX

ltPositionY :: LayerTransform -> Number
ltPositionY t = t.positionY

ltPositionZ :: LayerTransform -> Number
ltPositionZ t = t.positionZ

ltScaleX :: LayerTransform -> Number
ltScaleX t = t.scaleX

ltScaleY :: LayerTransform -> Number
ltScaleY t = t.scaleY

ltAnchorX :: LayerTransform -> Number
ltAnchorX t = t.anchorX

ltAnchorY :: LayerTransform -> Number
ltAnchorY t = t.anchorY

-- | Depth render result.
type DepthResult =
  { minDepth :: Number
  , maxDepth :: Number
  }

mkDepthResult :: Number -> Number -> DepthResult
mkDepthResult minD maxD = { minDepth: minD, maxDepth: maxD }

drMinDepth :: DepthResult -> Number
drMinDepth r = r.minDepth

drMaxDepth :: DepthResult -> Number
drMaxDepth r = r.maxDepth

-- ────────────────────────────────────────────────────────────────────────────
-- Z-Buffer Initialization
-- ────────────────────────────────────────────────────────────────────────────

-- | Initial depth value (far clip).
initDepth :: Number -> Number
initDepth farClip = farClip

-- | Initial min/max for tracking (opposite extremes).
initialMinMax :: Tuple Number Number
initialMinMax = Tuple infinity (-infinity)

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Testing
-- ────────────────────────────────────────────────────────────────────────────

-- | Test if new depth is closer (smaller) than current.
isCloser :: Number -> Number -> Boolean
isCloser newDepth currentDepth = newDepth < currentDepth

-- | Update depth buffer value: keep closer depth.
updateDepth :: Number -> Number -> Number
updateDepth newDepth currentDepth =
  if isCloser newDepth currentDepth then newDepth else currentDepth

-- | Update min/max tracking.
updateMinMax :: Number -> Number -> Number -> Tuple Number Number
updateMinMax depth minD maxD = Tuple (min minD depth) (max maxD depth)

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Depth Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate relative depth from camera.
--   relativeDepth = |layerZ - cameraZ|
relativeDepth :: Number -> Number -> Number
relativeDepth layerZ cameraZ = abs (layerZ - cameraZ)

-- | Clamp depth to clip range [nearClip, farClip].
clampToClipRange :: Number -> Number -> Number -> Number
clampToClipRange depth nearClip farClip =
  max nearClip (min farClip depth)

-- | Full depth calculation: layer Z → clamped relative depth.
calculateLayerDepth :: Number -> Number -> Number -> Number -> Number
calculateLayerDepth layerZ cameraZ nearClip farClip =
  let relative = relativeDepth layerZ cameraZ
  in clampToClipRange relative nearClip farClip

-- ────────────────────────────────────────────────────────────────────────────
-- Screen Bounds Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate final layer dimensions with scale.
scaledDimensions :: Number -> Number -> Number -> Number -> Tuple Number Number
scaledDimensions layerWidth layerHeight scaleX scaleY =
  Tuple (layerWidth * scaleX) (layerHeight * scaleY)

-- | Convert compositor coords (origin = center) to screen coords (origin = top-left).
toScreenCoords :: Number -> Number -> Number -> Number -> Number -> Number
              -> Number -> Number -> Tuple Number Number
toScreenCoords posX posY finalWidth finalHeight anchorX anchorY screenWidth screenHeight =
  let screenX = posX - finalWidth * anchorX + screenWidth / 2.0
      screenY = posY - finalHeight * anchorY + screenHeight / 2.0
  in Tuple screenX screenY

-- | Clip bounds to screen.
clipToScreen :: Number -> Number -> Number -> Number -> Number -> Number
             -> Maybe ScreenBounds
clipToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight =
  let clippedX = max 0.0 (min screenWidth screenX)
      clippedY = max 0.0 (min screenHeight screenY)
      clippedWidth = max 0.0 $
        min (screenWidth - clippedX) (finalWidth - (clippedX - screenX))
      clippedHeight = max 0.0 $
        min (screenHeight - clippedY) (finalHeight - (clippedY - screenY))
  in if clippedWidth <= 0.0 || clippedHeight <= 0.0
     then Nothing
     else Just { x: clippedX, y: clippedY, width: clippedWidth, height: clippedHeight }

-- | Full screen bounds calculation.
calculateScreenBounds :: LayerTransform -> Number -> Number -> Number -> Number
                     -> Maybe ScreenBounds
calculateScreenBounds transform layerWidth layerHeight screenWidth screenHeight =
  let Tuple finalWidth finalHeight = scaledDimensions layerWidth layerHeight
                                       transform.scaleX transform.scaleY
      Tuple screenX screenY = toScreenCoords
                                transform.positionX transform.positionY
                                finalWidth finalHeight
                                transform.anchorX transform.anchorY
                                screenWidth screenHeight
  in clipToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

-- ────────────────────────────────────────────────────────────────────────────
-- Pixel Index Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate linear pixel index from 2D coordinates.
pixelIndex :: Int -> Int -> Int -> Int
pixelIndex x y width = y * width + x

-- | Check if coordinates are within bounds.
inBounds :: Int -> Int -> Int -> Int -> Boolean
inBounds x y width height = x < width && y < height

-- | Calculate bounds for rectangular fill.
fillBounds :: ScreenBounds -> Int -> Int -> { startX :: Int, startY :: Int, endX :: Int, endY :: Int }
fillBounds bounds screenWidth screenHeight =
  let startX = floor bounds.x
      startY = floor bounds.y
      endX = min screenWidth (floor (bounds.x + bounds.width) + 1)
      endY = min screenHeight (floor (bounds.y + bounds.height) + 1)
  in { startX, startY, endX, endY }

-- ────────────────────────────────────────────────────────────────────────────
-- Circular Splat (for Particles)
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if point is within circular radius (for particle splats).
inCircle :: Int -> Int -> Int -> Boolean
inCircle dx dy radius = dx * dx + dy * dy <= radius * radius

-- | Calculate particle splat radius from size.
splatRadius :: Number -> Int
splatRadius particleSize =
  let half = particleSize / 2.0
  in if half < 1.0 then 1 else floor half

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Map Sampling
-- ────────────────────────────────────────────────────────────────────────────

-- | Sample depth from depth map at UV coordinates.
--   Maps bounds-relative position to depth map coordinates.
sampleDepthCoords :: Number -> Number -> Number -> Number -> Int -> Int
                  -> Tuple Int Int
sampleDepthCoords localX localY boundsWidth boundsHeight depthWidth depthHeight =
  let sampleX = floor ((localX / boundsWidth) * toNumber depthWidth)
      sampleY = floor ((localY / boundsHeight) * toNumber depthHeight)
  in Tuple (min sampleX (depthWidth - 1)) (min sampleY (depthHeight - 1))

-- | Convert uint8 depth to normalized [0, 1].
uint8ToNormalized :: Int -> Number
uint8ToNormalized value = toNumber value / 255.0

-- | Convert normalized depth to world units.
normalizedToWorld :: Number -> Number -> Number -> Number
normalizedToWorld normalized nearClip farClip =
  nearClip + normalized * (farClip - nearClip)

-- ────────────────────────────────────────────────────────────────────────────
-- Result Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate and normalize min/max depth result.
--   Handles empty scenes and ensures minDepth <= maxDepth.
validateDepthResult :: Number -> Number -> Number -> DepthResult
validateDepthResult minD maxD farClip =
  let Tuple min' max' =
        if not (isFinite minD) || not (isFinite maxD)
        then Tuple farClip farClip
        else Tuple minD maxD
  in if min' > max'
     then { minDepth: max', maxDepth: min' }
     else { minDepth: min', maxDepth: max' }
