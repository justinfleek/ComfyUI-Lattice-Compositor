{-
  Lattice.Services.Time.OpticalFlow - Motion Estimation Math

  Pure mathematical functions for optical flow-based frame interpolation:
  - Block matching using SAD (Sum of Absolute Differences)
  - Motion vector interpolation
  - Motion-compensated pixel sampling coordinates

  Source: ui/src/services/effects/timeRenderer.ts (lines 814-964)
-}

module Lattice.Services.Time.OpticalFlow
  ( luminance
  , pixelSAD
  , normalizeSAD
  , pixelToBlockIndex
  , blockStartCoords
  , inBounds
  , MotionVector
  , zeroMotion
  , motionMagnitude
  , forwardSamplePosition
  , backwardSamplePosition
  , searchOffsets
  , isValidSearchOffset
  , updateBestMatch
  , initialBestMatch
  , defaultBlockSize
  , defaultSearchRadius
  , blockCount
  ) where

import Prelude

import Data.Array (concat, (..), (:))
import Data.Int (toNumber)
import Data.Tuple (Tuple(..), snd)
import Global (infinity)
import Math (abs, sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Luminance Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate luminance from RGB using BT.601 coefficients.
luminance :: Number -> Number -> Number -> Number
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- ────────────────────────────────────────────────────────────────────────────
-- Sum of Absolute Differences (SAD)
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate absolute difference between two luminance values.
pixelSAD :: Number -> Number -> Number
pixelSAD lum1 lum2 = abs (lum1 - lum2)

-- | Normalize SAD by number of valid pixels.
normalizeSAD :: Number -> Int -> Number
normalizeSAD _ 0 = infinity
normalizeSAD totalSAD validPixels = totalSAD / toNumber validPixels

-- ────────────────────────────────────────────────────────────────────────────
-- Block Coordinates
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate block index from pixel coordinates.
pixelToBlockIndex :: Int -> Int -> Int -> Int -> Int
pixelToBlockIndex x y width blockSize =
  let blockX = x / blockSize
      blockY = y / blockSize
      blocksPerRow = (width + blockSize - 1) / blockSize
  in blockY * blocksPerRow + blockX

-- | Calculate block start coordinates from block index.
blockStartCoords :: Int -> Int -> Int -> Tuple Int Int
blockStartCoords blockIndex width blockSize =
  let blocksPerRow = (width + blockSize - 1) / blockSize
      blockY = blockIndex / blocksPerRow
      blockX = blockIndex `mod` blocksPerRow
  in Tuple (blockX * blockSize) (blockY * blockSize)

-- | Check if coordinates are within image bounds.
inBounds :: Int -> Int -> Int -> Int -> Boolean
inBounds x y width height =
  x >= 0 && y >= 0 && x < width && y < height

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Vector
-- ────────────────────────────────────────────────────────────────────────────

-- | Motion vector (displacement in pixels).
type MotionVector = { x :: Int, y :: Int }

-- | Zero motion vector.
zeroMotion :: MotionVector
zeroMotion = { x: 0, y: 0 }

-- | Calculate motion vector magnitude.
motionMagnitude :: MotionVector -> Number
motionMagnitude mv =
  sqrt (toNumber mv.x * toNumber mv.x + toNumber mv.y * toNumber mv.y)

-- ────────────────────────────────────────────────────────────────────────────
-- Motion-Compensated Sampling Coordinates
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate forward-compensated source position.
forwardSamplePosition :: Number -> Number -> MotionVector -> Number -> Tuple Number Number
forwardSamplePosition x y mv blend =
  Tuple (x + toNumber mv.x * (1.0 - blend))
        (y + toNumber mv.y * (1.0 - blend))

-- | Calculate backward-compensated source position.
backwardSamplePosition :: Number -> Number -> MotionVector -> Number -> Tuple Number Number
backwardSamplePosition x y mv blend =
  Tuple (x - toNumber mv.x * blend)
        (y - toNumber mv.y * blend)

-- ────────────────────────────────────────────────────────────────────────────
-- Search Window
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate search offsets for motion estimation.
searchOffsets :: Int -> Array (Tuple Int Int)
searchOffsets searchRadius =
  concat (map (\dy -> map (\dx -> Tuple dx dy) ((-searchRadius) .. searchRadius))
              ((-searchRadius) .. searchRadius))

-- | Check if search offset produces valid block position.
isValidSearchOffset :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Boolean
isValidSearchOffset blockStartX blockStartY dx dy blockSize width height =
  let endX = blockStartX + blockSize + dx
      endY = blockStartY + blockSize + dy
  in blockStartX + dx >= 0 &&
     blockStartY + dy >= 0 &&
     endX <= width &&
     endY <= height

-- ────────────────────────────────────────────────────────────────────────────
-- Best Match Selection
-- ────────────────────────────────────────────────────────────────────────────

-- | Update best match if current SAD is lower.
updateBestMatch :: Tuple MotionVector Number -> MotionVector -> Number -> Tuple MotionVector Number
updateBestMatch currentBest candidate sad =
  if sad < snd currentBest
  then Tuple candidate sad
  else currentBest

-- | Initial best match (no motion, infinite SAD).
initialBestMatch :: Tuple MotionVector Number
initialBestMatch = Tuple zeroMotion infinity

-- ────────────────────────────────────────────────────────────────────────────
-- Block Matching Parameters
-- ────────────────────────────────────────────────────────────────────────────

-- | Default block size for motion estimation.
defaultBlockSize :: Int
defaultBlockSize = 8

-- | Default search radius for motion vectors.
defaultSearchRadius :: Int
defaultSearchRadius = 8

-- | Calculate number of blocks in image.
blockCount :: Int -> Int -> Int -> Int
blockCount width height blockSize =
  let blocksX = (width + blockSize - 1) / blockSize
      blocksY = (height + blockSize - 1) / blockSize
  in blocksX * blocksY
