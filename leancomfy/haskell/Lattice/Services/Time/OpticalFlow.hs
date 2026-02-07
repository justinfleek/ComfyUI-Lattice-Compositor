{-|
  Lattice.Services.Time.OpticalFlow - Motion Estimation Math

  Pure mathematical functions for optical flow-based frame interpolation:
  - Block matching using SAD (Sum of Absolute Differences)
  - Motion vector interpolation
  - Motion-compensated pixel sampling coordinates

  Source: ui/src/services/effects/timeRenderer.ts (lines 814-964)
-}

module Lattice.Services.Time.OpticalFlow
  ( -- * Luminance
    luminance
    -- * SAD Calculation
  , pixelSAD
  , normalizeSAD
    -- * Block Coordinates
  , pixelToBlockIndex
  , blockStartCoords
  , inBounds
    -- * Motion Vector
  , MotionVector(..)
  , zeroMotion
  , motionMagnitude
    -- * Motion-Compensated Sampling
  , forwardSamplePosition
  , backwardSamplePosition
    -- * Search Window
  , searchOffsets
  , isValidSearchOffset
    -- * Best Match
  , updateBestMatch
  , initialBestMatch
    -- * Parameters
  , defaultBlockSize
  , defaultSearchRadius
  , blockCount
  ) where

--------------------------------------------------------------------------------
-- Luminance Calculation
--------------------------------------------------------------------------------

-- | Calculate luminance from RGB using BT.601 coefficients.
--   Y = 0.299*R + 0.587*G + 0.114*B
luminance :: Double  -- ^ R
          -> Double  -- ^ G
          -> Double  -- ^ B
          -> Double
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

--------------------------------------------------------------------------------
-- Sum of Absolute Differences (SAD)
--------------------------------------------------------------------------------

-- | Calculate absolute difference between two luminance values.
pixelSAD :: Double -> Double -> Double
pixelSAD lum1 lum2 = abs (lum1 - lum2)

-- | Normalize SAD by number of valid pixels.
normalizeSAD :: Double  -- ^ Total SAD
             -> Int     -- ^ Valid pixel count
             -> Double
normalizeSAD _ 0 = 1.0 / 0.0  -- Infinity
normalizeSAD totalSAD validPixels = totalSAD / fromIntegral validPixels

--------------------------------------------------------------------------------
-- Block Coordinates
--------------------------------------------------------------------------------

-- | Calculate block index from pixel coordinates.
pixelToBlockIndex :: Int  -- ^ X
                  -> Int  -- ^ Y
                  -> Int  -- ^ Width
                  -> Int  -- ^ Block size
                  -> Int
pixelToBlockIndex x y width blockSize =
  let blockX = x `div` blockSize
      blockY = y `div` blockSize
      blocksPerRow = (width + blockSize - 1) `div` blockSize
  in blockY * blocksPerRow + blockX

-- | Calculate block start coordinates from block index.
blockStartCoords :: Int  -- ^ Block index
                 -> Int  -- ^ Width
                 -> Int  -- ^ Block size
                 -> (Int, Int)
blockStartCoords blockIndex width blockSize =
  let blocksPerRow = (width + blockSize - 1) `div` blockSize
      blockY = blockIndex `div` blocksPerRow
      blockX = blockIndex `mod` blocksPerRow
  in (blockX * blockSize, blockY * blockSize)

-- | Check if coordinates are within image bounds.
inBounds :: Int  -- ^ X
         -> Int  -- ^ Y
         -> Int  -- ^ Width
         -> Int  -- ^ Height
         -> Bool
inBounds x y width height =
  x >= 0 && y >= 0 && x < width && y < height

--------------------------------------------------------------------------------
-- Motion Vector
--------------------------------------------------------------------------------

-- | Motion vector (displacement in pixels).
data MotionVector = MotionVector
  { mvX :: Int
  , mvY :: Int
  } deriving (Show, Eq)

-- | Zero motion vector.
zeroMotion :: MotionVector
zeroMotion = MotionVector 0 0

-- | Calculate motion vector magnitude.
motionMagnitude :: MotionVector -> Double
motionMagnitude (MotionVector x y) =
  sqrt (fromIntegral x ^ (2 :: Int) + fromIntegral y ^ (2 :: Int))

--------------------------------------------------------------------------------
-- Motion-Compensated Sampling Coordinates
--------------------------------------------------------------------------------

-- | Calculate forward-compensated source position.
--   Used to sample from frame1 with motion compensation.
forwardSamplePosition :: Double  -- ^ X
                      -> Double  -- ^ Y
                      -> MotionVector
                      -> Double  -- ^ Blend factor
                      -> (Double, Double)
forwardSamplePosition x y (MotionVector mx my) blend =
  ( x + fromIntegral mx * (1.0 - blend)
  , y + fromIntegral my * (1.0 - blend)
  )

-- | Calculate backward-compensated source position.
--   Used to sample from frame2 with motion compensation.
backwardSamplePosition :: Double  -- ^ X
                       -> Double  -- ^ Y
                       -> MotionVector
                       -> Double  -- ^ Blend factor
                       -> (Double, Double)
backwardSamplePosition x y (MotionVector mx my) blend =
  ( x - fromIntegral mx * blend
  , y - fromIntegral my * blend
  )

--------------------------------------------------------------------------------
-- Search Window
--------------------------------------------------------------------------------

-- | Generate search offsets for motion estimation.
--   Returns list of (dx, dy) offsets within search radius.
searchOffsets :: Int  -- ^ Search radius
              -> [(Int, Int)]
searchOffsets searchRadius =
  [(dx, dy) | dy <- [-searchRadius..searchRadius]
            , dx <- [-searchRadius..searchRadius]]

-- | Check if search offset produces valid block position.
isValidSearchOffset :: Int  -- ^ Block start X
                    -> Int  -- ^ Block start Y
                    -> Int  -- ^ dx
                    -> Int  -- ^ dy
                    -> Int  -- ^ Block size
                    -> Int  -- ^ Width
                    -> Int  -- ^ Height
                    -> Bool
isValidSearchOffset blockStartX blockStartY dx dy blockSize width height =
  let endX = blockStartX + blockSize + dx
      endY = blockStartY + blockSize + dy
  in blockStartX + dx >= 0 &&
     blockStartY + dy >= 0 &&
     endX <= width &&
     endY <= height

--------------------------------------------------------------------------------
-- Best Match Selection
--------------------------------------------------------------------------------

-- | Update best match if current SAD is lower.
updateBestMatch :: (MotionVector, Double)  -- ^ Current best (vector, SAD)
                -> MotionVector            -- ^ Candidate vector
                -> Double                  -- ^ Candidate SAD
                -> (MotionVector, Double)
updateBestMatch currentBest candidate sad =
  if sad < snd currentBest
  then (candidate, sad)
  else currentBest

-- | Initial best match (no motion, infinite SAD).
initialBestMatch :: (MotionVector, Double)
initialBestMatch = (zeroMotion, 1.0 / 0.0)  -- Infinity

--------------------------------------------------------------------------------
-- Block Matching Parameters
--------------------------------------------------------------------------------

-- | Default block size for motion estimation.
defaultBlockSize :: Int
defaultBlockSize = 8

-- | Default search radius for motion vectors.
defaultSearchRadius :: Int
defaultSearchRadius = 8

-- | Calculate number of blocks in image.
blockCount :: Int  -- ^ Width
           -> Int  -- ^ Height
           -> Int  -- ^ Block size
           -> Int
blockCount width height blockSize =
  let blocksX = (width + blockSize - 1) `div` blockSize
      blocksY = (height + blockSize - 1) `div` blockSize
  in blocksX * blocksY
