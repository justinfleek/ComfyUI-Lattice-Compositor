-- | Lattice.Services.Depth.DepthFill - Depth Buffer Filling
-- |
-- | Pure functions for filling depth buffers from different sources:
-- | - Depthflow layer depth map sampling
-- | - Particle circular splat rendering
-- | - Uniform depth fill for solid layers
-- | - Z-buffer depth testing
-- |
-- | Source: ui/src/services/export/depthRenderer.ts (lines 336-511)

module Lattice.Services.Depth.DepthFill
  ( FillBounds
  , ParticleData
  , CameraData
  , DepthBufferInfo
  , DepthflowParams
  , calculateSampleCoords
  , sampleToIndex
  , normalizeUint8Depth
  , normalizedToWorldDepth
  , isInScreenBounds
  , screenToBufferIndex
  , depthflowSamplePosition
  , boundsToScreen
  , shouldWriteDepth
  , particleRelativeDepth
  , clampDepthToClipRange
  , particleRadius
  , isInsideCircle
  , generateSplatOffsets
  , isValidParticle
  , particleScreenPosition
  , calculateFillRegion
  , isOpaqueEnoughForDepth
  , generateFillPixels
  , initDepthValue
  , updateDepthRange
  , validateDepthRange
  , handleEmptyScene
  , toFloat32Precision
  , prepareClipValues
  ) where

import Prelude

import Data.Array (filter, range)
import Data.Int (floor, ceil, toNumber)
import Data.Number (isFinite, isNaN)
import Data.Tuple (Tuple(..))
import Math (abs)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Screen bounds for depth fill operations.
type FillBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Particle data for depth rendering.
type ParticleData =
  { x :: Number
  , y :: Number
  , z :: Number
  , size :: Number
  }

-- | Camera data for depth calculations.
type CameraData =
  { positionZ :: Number
  }

-- | Depth buffer state (dimensions and clip planes).
type DepthBufferInfo =
  { width :: Int
  , height :: Int
  , nearClip :: Number
  , farClip :: Number
  }

-- | Parameters for depthflow sampling.
type DepthflowParams =
  { bounds :: FillBounds
  , depthWidth :: Int
  , depthHeight :: Int
  , nearClip :: Number
  , farClip :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Sampling
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate sample coordinates from depth map.
-- | Maps screen position to depth map position.
calculateSampleCoords :: Number -> Number -> Number -> Number
                      -> Int -> Int -> Tuple Int Int
calculateSampleCoords x y boundsWidth boundsHeight depthWidth depthHeight =
  let sampleX = floor ((x / boundsWidth) * toNumber depthWidth)
      sampleY = floor ((y / boundsHeight) * toNumber depthHeight)
  in Tuple sampleX sampleY

-- | Convert sample coordinates to linear index.
sampleToIndex :: Int -> Int -> Int -> Int
sampleToIndex sampleX sampleY depthWidth =
  sampleY * depthWidth + sampleX

-- | Normalize Uint8 depth value to [0, 1].
normalizeUint8Depth :: Int -> Number
normalizeUint8Depth value = toNumber value / 255.0

-- | Convert normalized depth to world units.
-- | worldDepth = nearClip + normalized * (farClip - nearClip)
normalizedToWorldDepth :: Number -> Number -> Number -> Number
normalizedToWorldDepth normalized nearClip farClip =
  nearClip + normalized * (farClip - nearClip)

-- | Screen bounds check for depth fill.
isInScreenBounds :: Int -> Int -> Int -> Int -> Boolean
isInScreenBounds screenX screenY screenWidth screenHeight =
  screenX >= 0 && screenX < screenWidth &&
  screenY >= 0 && screenY < screenHeight

-- | Calculate buffer index from screen coordinates.
screenToBufferIndex :: Int -> Int -> Int -> Int
screenToBufferIndex screenX screenY screenWidth =
  screenY * screenWidth + screenX

-- ────────────────────────────────────────────────────────────────────────────
-- Depthflow Sampling Logic
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate depthflow sample position for a screen pixel.
depthflowSamplePosition :: Number -> Number -> DepthflowParams -> Tuple Int Int
depthflowSamplePosition localX localY params =
  calculateSampleCoords localX localY
                        params.bounds.width params.bounds.height
                        params.depthWidth params.depthHeight

-- | Calculate screen position from local bounds position.
boundsToScreen :: Number -> Number -> Number -> Number -> Tuple Int Int
boundsToScreen boundsX boundsY localX localY =
  Tuple (floor (boundsX + localX)) (floor (boundsY + localY))

-- | Determine if depth should be written (z-buffer test).
-- | Closer depth wins (smaller value).
shouldWriteDepth :: Number -> Number -> Boolean
shouldWriteDepth newDepth existingDepth = newDepth < existingDepth

-- ────────────────────────────────────────────────────────────────────────────
-- Particle Depth Logic
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate particle depth relative to camera.
particleRelativeDepth :: Number -> Number -> Number
particleRelativeDepth particleZ cameraZ = abs (particleZ - cameraZ)

-- | Clamp depth to clip range.
clampDepthToClipRange :: Number -> Number -> Number -> Number
clampDepthToClipRange depth nearClip farClip =
  max nearClip (min farClip depth)

-- | Calculate particle radius in pixels.
particleRadius :: Number -> Int
particleRadius size = max 1 (floor (size / 2.0))

-- | Check if point is inside circular splat.
isInsideCircle :: Int -> Int -> Int -> Boolean
isInsideCircle dx dy radius =
  dx * dx + dy * dy <= radius * radius

-- | Generate splat pixel offsets for a given radius.
-- | Returns array of (dx, dy) pairs inside the circle.
generateSplatOffsets :: Int -> Array (Tuple Int Int)
generateSplatOffsets radius =
  filter (\(Tuple dx dy) -> isInsideCircle dx dy radius) $
    do dy <- range (-radius) radius
       dx <- range (-radius) radius
       pure (Tuple dx dy)

-- | Validate particle has finite coordinates.
isValidParticle :: ParticleData -> Boolean
isValidParticle p =
  isFinite p.x && not (isNaN p.x) &&
  isFinite p.y && not (isNaN p.y) &&
  isFinite p.z && not (isNaN p.z)

-- | Calculate particle screen position (integer).
particleScreenPosition :: ParticleData -> Tuple Int Int
particleScreenPosition p = Tuple (floor p.x) (floor p.y)

-- ────────────────────────────────────────────────────────────────────────────
-- Uniform Depth Fill Logic
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate fill region from bounds.
-- | Returns (startX, startY, endX, endY).
calculateFillRegion :: FillBounds -> Int -> Int -> { startX :: Int, startY :: Int, endX :: Int, endY :: Int }
calculateFillRegion bounds screenWidth screenHeight =
  let startX = floor bounds.x
      startY = floor bounds.y
      endX = min screenWidth (ceil (bounds.x + bounds.width))
      endY = min screenHeight (ceil (bounds.y + bounds.height))
  in { startX, startY, endX, endY }

-- | Check if layer is opaque enough for depth write.
-- | Uses threshold of 0.5 for depth buffer.
isOpaqueEnoughForDepth :: Number -> Boolean
isOpaqueEnoughForDepth opacity = opacity > 0.5

-- | Generate pixel coordinates for uniform fill region.
-- | Returns array of (x, y) pairs.
generateFillPixels :: Int -> Int -> Int -> Int -> Array (Tuple Int Int)
generateFillPixels startX startY endX endY =
  do y <- range startY (endY - 1)
     x <- range startX (endX - 1)
     pure (Tuple x y)

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Buffer Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Initialize depth buffer value (far clip).
initDepthValue :: Number -> Number
initDepthValue farClip = farClip

-- | Calculate min/max depth range from written values.
updateDepthRange :: Number -> Number -> Number -> Tuple Number Number
updateDepthRange currentMin currentMax writtenDepth =
  Tuple (min currentMin writtenDepth) (max currentMax writtenDepth)

-- | Validate depth range invariant: min <= max.
validateDepthRange :: Number -> Number -> Tuple Number Number
validateDepthRange minDepth maxDepth
  | minDepth > maxDepth = Tuple maxDepth minDepth
  | otherwise = Tuple minDepth maxDepth

-- | Handle empty scene (no layers updated depth).
handleEmptyScene :: Number -> Number -> Number -> Tuple Number Number
handleEmptyScene minDepth maxDepth farClip
  | not (isFinite minDepth) || isNaN minDepth ||
    not (isFinite maxDepth) || isNaN maxDepth = Tuple farClip farClip
  | otherwise = validateDepthRange minDepth maxDepth

-- ────────────────────────────────────────────────────────────────────────────
-- Float32 Precision
-- ────────────────────────────────────────────────────────────────────────────

-- | Round to Float32 precision for buffer consistency.
-- | In PureScript, we approximate by using the value directly.
toFloat32Precision :: Number -> Number
toFloat32Precision value = value

-- | Prepare clip values with Float32 precision.
prepareClipValues :: Number -> Number -> Tuple Number Number
prepareClipValues nearClip farClip =
  Tuple (toFloat32Precision nearClip) (toFloat32Precision farClip)
