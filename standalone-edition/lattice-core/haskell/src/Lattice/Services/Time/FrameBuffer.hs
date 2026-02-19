{-# LANGUAGE Strict #-}
{-
  Lattice.Services.Time.FrameBuffer - Temporal Frame Storage

  Frame buffer management for time-based effects:
  - Ring buffer of previous frames
  - Frame-based (deterministic) timestamps
  - Echo frame retrieval
  - Buffer statistics

  Source: ui/src/services/effects/timeRenderer.ts (lines 23-182)
-}

module Lattice.Services.Time.FrameBuffer
  ( -- * Types
    FrameBufferEntry(..)
  , FrameBufferStats(..)
  , EchoFrameResult(..)
    -- * Constants
  , maxBufferFrames
  , defaultMaxFrameDistance
    -- * Buffer Operations (pure)
  , shouldTrimBuffer
  , isFrameInRange
  , frameDistanceInRange
  , findClosestFrame
  , findClosestFrameIndex
  , calculateEchoTargetFrames
  , calculateEchoIntensity
    -- * Statistics
  , calculateBufferStats
  , emptyBufferStats
  ) where

import Data.List (sortBy, minimumBy)
import Data.Ord (comparing)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Frame buffer entry - stores frame image data with metadata.
data FrameBufferEntry a = FrameBufferEntry
  { fbeImageData    :: !a     -- Generic to support different image formats
  , fbeFrame        :: !Int   -- Frame number
  , fbeStoredAtFrame :: !Int  -- Frame-based timestamp for deterministic cleanup
  } deriving (Show, Eq)

-- | Buffer statistics.
data FrameBufferStats = FrameBufferStats
  { fbsFrameCount  :: !Int
  , fbsOldestFrame :: !Int
  , fbsNewestFrame :: !Int
  } deriving (Show, Eq)

-- | Echo frame result with echo index.
data EchoFrameResult a = EchoFrameResult
  { efrImageData :: !a
  , efrFrame     :: !Int
  , efrEchoIndex :: !Int
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Maximum number of frames to store in buffer.
maxBufferFrames :: Int
maxBufferFrames = 64

-- | Maximum frame distance for cleanup.
defaultMaxFrameDistance :: Int
defaultMaxFrameDistance = maxBufferFrames * 2

-- ────────────────────────────────────────────────────────────────────────────
-- Buffer Operations (pure)
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if buffer needs trimming.
shouldTrimBuffer :: Int -> Bool
shouldTrimBuffer bufferLength = bufferLength > maxBufferFrames

-- | Check if a frame is within acceptable range of current frame.
isFrameInRange :: Int -> Int -> Int -> Bool
isFrameInRange frameNum currentFrame maxDistance =
  abs (currentFrame - frameNum) < maxDistance

-- | Check frame distance is within range (for cleanup).
frameDistanceInRange :: Int -> Int -> Bool
frameDistanceInRange storedAtFrame currentFrame =
  abs (currentFrame - storedAtFrame) < defaultMaxFrameDistance

-- | Find the closest frame to target in a list of entries.
--   Returns Nothing if list is empty.
findClosestFrame :: [FrameBufferEntry a] -> Int -> Maybe (FrameBufferEntry a)
findClosestFrame [] _ = Nothing
findClosestFrame entries targetFrame =
  Just $ minimumBy (comparing (\e -> abs (fbeFrame e - targetFrame))) entries

-- | Find index of closest frame to target.
findClosestFrameIndex :: [FrameBufferEntry a] -> Int -> Maybe Int
findClosestFrameIndex [] _ = Nothing
findClosestFrameIndex entries targetFrame =
  let indexed = zip [0..] entries
      distances = map (\(i, e) -> (i, abs (fbeFrame e - targetFrame))) indexed
      sorted = sortBy (comparing snd) distances
  in case sorted of
       [] -> Nothing
       ((i, _):_) -> Just i

-- | Calculate target frames for echo effect.
--   Returns list of (targetFrame, echoIndex) pairs.
calculateEchoTargetFrames :: Int -> Double -> Int -> [(Int, Int)]
calculateEchoTargetFrames currentFrame echoTimeFrames numEchoes =
  let indices = [1..numEchoes]
      calcTarget i = round (fromIntegral currentFrame + echoTimeFrames * fromIntegral i)
  in map (\i -> (calcTarget i, i)) indices

-- | Calculate echo intensity using exponential decay.
--   intensity = startingIntensity * (1 - decay)^echoIndex
calculateEchoIntensity :: Double -> Double -> Int -> Double
calculateEchoIntensity startingIntensity decay echoIndex =
  startingIntensity * (1.0 - decay) ^^ echoIndex

-- ────────────────────────────────────────────────────────────────────────────
-- Statistics
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate buffer statistics from entries.
calculateBufferStats :: [FrameBufferEntry a] -> FrameBufferStats
calculateBufferStats [] = emptyBufferStats
calculateBufferStats entries =
  let frames = map fbeFrame entries
  in FrameBufferStats
       { fbsFrameCount = length entries
       , fbsOldestFrame = minimum frames
       , fbsNewestFrame = maximum frames
       }

-- | Empty buffer statistics.
emptyBufferStats :: FrameBufferStats
emptyBufferStats = FrameBufferStats
  { fbsFrameCount = 0
  , fbsOldestFrame = -1
  , fbsNewestFrame = -1
  }
