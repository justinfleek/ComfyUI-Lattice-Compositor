{-# LANGUAGE Strict #-}
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
  ( -- * Types
    ScreenBounds(..)
  , CameraPosition(..)
  , LayerTransform(..)
  , DepthResult(..)
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

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Screen bounds rectangle.
data ScreenBounds = ScreenBounds
  { sbX      :: !Double
  , sbY      :: !Double
  , sbWidth  :: !Double
  , sbHeight :: !Double
  } deriving (Show, Eq)

-- | Camera position in 3D.
data CameraPosition = CameraPosition
  { cpX :: !Double
  , cpY :: !Double
  , cpZ :: !Double
  } deriving (Show, Eq)

-- | Layer transform data.
data LayerTransform = LayerTransform
  { ltPositionX :: !Double
  , ltPositionY :: !Double
  , ltPositionZ :: !Double
  , ltScaleX    :: !Double
  , ltScaleY    :: !Double
  , ltAnchorX   :: !Double
  , ltAnchorY   :: !Double
  } deriving (Show, Eq)

-- | Depth render result.
data DepthResult = DepthResult
  { drMinDepth :: !Double
  , drMaxDepth :: !Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Z-Buffer Initialization
--------------------------------------------------------------------------------

-- | Initial depth value (far clip).
initDepth :: Double -> Double
initDepth farClip = farClip

-- | Initial min/max for tracking (opposite extremes).
initialMinMax :: (Double, Double)
initialMinMax = (1/0, -1/0)  -- (Infinity, -Infinity)

--------------------------------------------------------------------------------
-- Depth Testing
--------------------------------------------------------------------------------

-- | Test if new depth is closer (smaller) than current.
isCloser :: Double -> Double -> Bool
isCloser newDepth currentDepth = newDepth < currentDepth

-- | Update depth buffer value: keep closer depth.
updateDepth :: Double -> Double -> Double
updateDepth newDepth currentDepth =
  if isCloser newDepth currentDepth then newDepth else currentDepth

-- | Update min/max tracking.
updateMinMax :: Double -> Double -> Double -> (Double, Double)
updateMinMax depth minD maxD = (min minD depth, max maxD depth)

--------------------------------------------------------------------------------
-- Layer Depth Calculation
--------------------------------------------------------------------------------

-- | Calculate relative depth from camera.
--   relativeDepth = |layerZ - cameraZ|
relativeDepth :: Double -> Double -> Double
relativeDepth layerZ cameraZ = abs (layerZ - cameraZ)

-- | Clamp depth to clip range [nearClip, farClip].
clampToClipRange :: Double -> Double -> Double -> Double
clampToClipRange depth nearClip farClip =
  max nearClip (min farClip depth)

-- | Full depth calculation: layer Z → clamped relative depth.
calculateLayerDepth :: Double -> Double -> Double -> Double -> Double
calculateLayerDepth layerZ cameraZ nearClip farClip =
  let relative = relativeDepth layerZ cameraZ
  in clampToClipRange relative nearClip farClip

--------------------------------------------------------------------------------
-- Screen Bounds Calculation
--------------------------------------------------------------------------------

-- | Calculate final layer dimensions with scale.
scaledDimensions :: Double -> Double -> Double -> Double -> (Double, Double)
scaledDimensions layerWidth layerHeight scaleX scaleY =
  (layerWidth * scaleX, layerHeight * scaleY)

-- | Convert compositor coords (origin = center) to screen coords (origin = top-left).
toScreenCoords :: Double -> Double -> Double -> Double -> Double -> Double
              -> Double -> Double -> (Double, Double)
toScreenCoords posX posY finalWidth finalHeight anchorX anchorY screenWidth screenHeight =
  let screenX = posX - finalWidth * anchorX + screenWidth / 2.0
      screenY = posY - finalHeight * anchorY + screenHeight / 2.0
  in (screenX, screenY)

-- | Clip bounds to screen.
clipToScreen :: Double -> Double -> Double -> Double -> Double -> Double
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
     else Just ScreenBounds
       { sbX = clippedX
       , sbY = clippedY
       , sbWidth = clippedWidth
       , sbHeight = clippedHeight
       }

-- | Full screen bounds calculation.
calculateScreenBounds :: LayerTransform -> Double -> Double -> Double -> Double
                     -> Maybe ScreenBounds
calculateScreenBounds transform layerWidth layerHeight screenWidth screenHeight =
  let (finalWidth, finalHeight) = scaledDimensions layerWidth layerHeight
                                    (ltScaleX transform) (ltScaleY transform)
      (screenX, screenY) = toScreenCoords
                             (ltPositionX transform) (ltPositionY transform)
                             finalWidth finalHeight
                             (ltAnchorX transform) (ltAnchorY transform)
                             screenWidth screenHeight
  in clipToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

--------------------------------------------------------------------------------
-- Pixel Index Calculation
--------------------------------------------------------------------------------

-- | Calculate linear pixel index from 2D coordinates.
pixelIndex :: Int -> Int -> Int -> Int
pixelIndex x y width = y * width + x

-- | Check if coordinates are within bounds.
inBounds :: Int -> Int -> Int -> Int -> Bool
inBounds x y width height = x < width && y < height

-- | Calculate bounds for rectangular fill.
fillBounds :: ScreenBounds -> Int -> Int -> (Int, Int, Int, Int)
fillBounds bounds screenWidth screenHeight =
  let startX = floor (sbX bounds)
      startY = floor (sbY bounds)
      endX = min screenWidth (ceiling (sbX bounds + sbWidth bounds))
      endY = min screenHeight (ceiling (sbY bounds + sbHeight bounds))
  in (startX, startY, endX, endY)

--------------------------------------------------------------------------------
-- Circular Splat (for Particles)
--------------------------------------------------------------------------------

-- | Check if point is within circular radius (for particle splats).
inCircle :: Int -> Int -> Int -> Bool
inCircle dx dy radius = dx * dx + dy * dy <= radius * radius

-- | Calculate particle splat radius from size.
splatRadius :: Double -> Int
splatRadius particleSize =
  let half = particleSize / 2.0
  in if half < 1.0 then 1 else floor half

--------------------------------------------------------------------------------
-- Depth Map Sampling
--------------------------------------------------------------------------------

-- | Sample depth from depth map at UV coordinates.
--   Maps bounds-relative position to depth map coordinates.
sampleDepthCoords :: Double -> Double -> Double -> Double -> Int -> Int
                  -> (Int, Int)
sampleDepthCoords localX localY boundsWidth boundsHeight depthWidth depthHeight =
  let sampleX = floor ((localX / boundsWidth) * fromIntegral depthWidth)
      sampleY = floor ((localY / boundsHeight) * fromIntegral depthHeight)
  in (min sampleX (depthWidth - 1), min sampleY (depthHeight - 1))

-- | Convert uint8 depth to normalized [0, 1].
uint8ToNormalized :: Int -> Double
uint8ToNormalized value = fromIntegral value / 255.0

-- | Convert normalized depth to world units.
normalizedToWorld :: Double -> Double -> Double -> Double
normalizedToWorld normalized nearClip farClip =
  nearClip + normalized * (farClip - nearClip)

--------------------------------------------------------------------------------
-- Result Validation
--------------------------------------------------------------------------------

-- | Validate and normalize min/max depth result.
--   Handles empty scenes and ensures minDepth <= maxDepth.
validateDepthResult :: Double -> Double -> Double -> DepthResult
validateDepthResult minD maxD farClip =
  let (min', max') =
        if isInfinite minD || isInfinite maxD
        then (farClip, farClip)
        else (minD, maxD)
  in if min' > max'
     then DepthResult { drMinDepth = max', drMaxDepth = min' }
     else DepthResult { drMinDepth = min', drMaxDepth = max' }
