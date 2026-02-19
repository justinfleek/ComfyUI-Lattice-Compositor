{-|
Module      : Lattice.Services.Depth.DepthFill
Description : Depth buffer filling operations
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for filling depth buffers from different sources:
- Depthflow layer depth map sampling
- Particle circular splat rendering
- Uniform depth fill for solid layers
- Z-buffer depth testing

Source: ui/src/services/export/depthRenderer.ts (lines 336-511)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Depth.DepthFill
  ( -- * Types
    FillBounds(..)
  , ParticleData(..)
  , CameraData(..)
  , DepthBufferInfo(..)
  , DepthflowParams(..)
    -- * Depth Sampling
  , calculateSampleCoords
  , sampleToIndex
  , normalizeUint8Depth
  , normalizedToWorldDepth
  , isInScreenBounds
  , screenToBufferIndex
    -- * Depthflow Sampling
  , depthflowSamplePosition
  , boundsToScreen
  , shouldWriteDepth
    -- * Particle Depth
  , particleRelativeDepth
  , clampDepthToClipRange
  , particleRadius
  , isInsideCircle
  , generateSplatOffsets
  , isValidParticle
  , particleScreenPosition
    -- * Uniform Depth Fill
  , calculateFillRegion
  , isOpaqueEnoughForDepth
  , generateFillPixels
    -- * Depth Buffer Operations
  , initDepthValue
  , updateDepthRange
  , validateDepthRange
  , handleEmptyScene
    -- * Float32 Precision
  , toFloat32Precision
  , prepareClipValues
  ) where

import Data.Word (Word8)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Screen bounds for depth fill operations.
data FillBounds = FillBounds
  { fbX      :: Double
  , fbY      :: Double
  , fbWidth  :: Double
  , fbHeight :: Double
  } deriving (Show, Eq)

-- | Particle data for depth rendering.
data ParticleData = ParticleData
  { pdX    :: Double
  , pdY    :: Double
  , pdZ    :: Double
  , pdSize :: Double
  } deriving (Show, Eq)

-- | Camera data for depth calculations.
data CameraData = CameraData
  { cdPositionZ :: Double
  } deriving (Show, Eq)

-- | Depth buffer state (dimensions and clip planes).
data DepthBufferInfo = DepthBufferInfo
  { dbiWidth    :: Int
  , dbiHeight   :: Int
  , dbiNearClip :: Double
  , dbiFarClip  :: Double
  } deriving (Show, Eq)

-- | Parameters for depthflow sampling.
data DepthflowParams = DepthflowParams
  { dpBounds      :: FillBounds
  , dpDepthWidth  :: Int
  , dpDepthHeight :: Int
  , dpNearClip    :: Double
  , dpFarClip     :: Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Depth Sampling
--------------------------------------------------------------------------------

-- | Calculate sample coordinates from depth map.
-- Maps screen position to depth map position.
calculateSampleCoords :: Double -> Double -> Double -> Double
                      -> Int -> Int -> (Int, Int)
calculateSampleCoords x y boundsWidth boundsHeight depthWidth depthHeight =
  let sampleX = floor ((x / boundsWidth) * fromIntegral depthWidth)
      sampleY = floor ((y / boundsHeight) * fromIntegral depthHeight)
  in (sampleX, sampleY)

-- | Convert sample coordinates to linear index.
sampleToIndex :: Int -> Int -> Int -> Int
sampleToIndex sampleX sampleY depthWidth =
  sampleY * depthWidth + sampleX

-- | Normalize Uint8 depth value to [0, 1].
normalizeUint8Depth :: Word8 -> Double
normalizeUint8Depth value = fromIntegral value / 255.0

-- | Convert normalized depth to world units.
-- worldDepth = nearClip + normalized * (farClip - nearClip)
normalizedToWorldDepth :: Double -> Double -> Double -> Double
normalizedToWorldDepth normalized nearClip farClip =
  nearClip + normalized * (farClip - nearClip)

-- | Screen bounds check for depth fill.
isInScreenBounds :: Int -> Int -> Int -> Int -> Bool
isInScreenBounds screenX screenY screenWidth screenHeight =
  screenX >= 0 && screenX < screenWidth &&
  screenY >= 0 && screenY < screenHeight

-- | Calculate buffer index from screen coordinates.
screenToBufferIndex :: Int -> Int -> Int -> Int
screenToBufferIndex screenX screenY screenWidth =
  screenY * screenWidth + screenX

--------------------------------------------------------------------------------
-- Depthflow Sampling Logic
--------------------------------------------------------------------------------

-- | Calculate depthflow sample position for a screen pixel.
depthflowSamplePosition :: Double -> Double -> DepthflowParams -> (Int, Int)
depthflowSamplePosition localX localY params =
  calculateSampleCoords localX localY
                        (fbWidth $ dpBounds params) (fbHeight $ dpBounds params)
                        (dpDepthWidth params) (dpDepthHeight params)

-- | Calculate screen position from local bounds position.
boundsToScreen :: Double -> Double -> Double -> Double -> (Int, Int)
boundsToScreen boundsX boundsY localX localY =
  (floor (boundsX + localX), floor (boundsY + localY))

-- | Determine if depth should be written (z-buffer test).
-- Closer depth wins (smaller value).
shouldWriteDepth :: Double -> Double -> Bool
shouldWriteDepth newDepth existingDepth = newDepth < existingDepth

--------------------------------------------------------------------------------
-- Particle Depth Logic
--------------------------------------------------------------------------------

-- | Calculate particle depth relative to camera.
particleRelativeDepth :: Double -> Double -> Double
particleRelativeDepth particleZ cameraZ = abs (particleZ - cameraZ)

-- | Clamp depth to clip range.
clampDepthToClipRange :: Double -> Double -> Double -> Double
clampDepthToClipRange depth nearClip farClip =
  max nearClip (min farClip depth)

-- | Calculate particle radius in pixels.
particleRadius :: Double -> Int
particleRadius size = max 1 (floor (size / 2.0))

-- | Check if point is inside circular splat.
isInsideCircle :: Int -> Int -> Int -> Bool
isInsideCircle dx dy radius =
  dx * dx + dy * dy <= radius * radius

-- | Generate splat pixel offsets for a given radius.
-- Returns list of (dx, dy) pairs inside the circle.
generateSplatOffsets :: Int -> [(Int, Int)]
generateSplatOffsets radius =
  [(dx, dy) | dy <- [-radius..radius]
            , dx <- [-radius..radius]
            , isInsideCircle dx dy radius]

-- | Validate particle has finite coordinates.
isValidParticle :: ParticleData -> Bool
isValidParticle p =
  not (isNaN (pdX p)) && not (isInfinite (pdX p)) &&
  not (isNaN (pdY p)) && not (isInfinite (pdY p)) &&
  not (isNaN (pdZ p)) && not (isInfinite (pdZ p))

-- | Calculate particle screen position (integer).
particleScreenPosition :: ParticleData -> (Int, Int)
particleScreenPosition p = (floor (pdX p), floor (pdY p))

--------------------------------------------------------------------------------
-- Uniform Depth Fill Logic
--------------------------------------------------------------------------------

-- | Calculate fill region from bounds.
-- Returns (startX, startY, endX, endY).
calculateFillRegion :: FillBounds -> Int -> Int -> (Int, Int, Int, Int)
calculateFillRegion bounds screenWidth screenHeight =
  let startX = floor (fbX bounds)
      startY = floor (fbY bounds)
      endX = min screenWidth (ceiling (fbX bounds + fbWidth bounds))
      endY = min screenHeight (ceiling (fbY bounds + fbHeight bounds))
  in (startX, startY, endX, endY)

-- | Check if layer is opaque enough for depth write.
-- Uses threshold of 0.5 for depth buffer.
isOpaqueEnoughForDepth :: Double -> Bool
isOpaqueEnoughForDepth opacity = opacity > 0.5

-- | Generate pixel coordinates for uniform fill region.
-- Returns list of (x, y) pairs.
generateFillPixels :: Int -> Int -> Int -> Int -> [(Int, Int)]
generateFillPixels startX startY endX endY =
  [(x, y) | y <- [startY..endY-1], x <- [startX..endX-1]]

--------------------------------------------------------------------------------
-- Depth Buffer Operations
--------------------------------------------------------------------------------

-- | Initialize depth buffer value (far clip).
initDepthValue :: Double -> Double
initDepthValue = id

-- | Calculate min/max depth range from written values.
updateDepthRange :: Double -> Double -> Double -> (Double, Double)
updateDepthRange currentMin currentMax writtenDepth =
  (min currentMin writtenDepth, max currentMax writtenDepth)

-- | Validate depth range invariant: min <= max.
validateDepthRange :: Double -> Double -> (Double, Double)
validateDepthRange minDepth maxDepth
  | minDepth > maxDepth = (maxDepth, minDepth)
  | otherwise = (minDepth, maxDepth)

-- | Handle empty scene (no layers updated depth).
handleEmptyScene :: Double -> Double -> Double -> (Double, Double)
handleEmptyScene minDepth maxDepth farClip
  | isNaN minDepth || isInfinite minDepth ||
    isNaN maxDepth || isInfinite maxDepth = (farClip, farClip)
  | otherwise = validateDepthRange minDepth maxDepth

--------------------------------------------------------------------------------
-- Float32 Precision
--------------------------------------------------------------------------------

-- | Round to Float32 precision for buffer consistency.
-- In Haskell, we use Double but could use realToFrac for actual Float32.
toFloat32Precision :: Double -> Double
toFloat32Precision = realToFrac . (realToFrac :: Double -> Float)

-- | Prepare clip values with Float32 precision.
prepareClipValues :: Double -> Double -> (Double, Double)
prepareClipValues nearClip farClip =
  (toFloat32Precision nearClip, toFloat32Precision farClip)
