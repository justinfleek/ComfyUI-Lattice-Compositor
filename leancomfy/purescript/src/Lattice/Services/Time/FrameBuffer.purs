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
  ( FrameBufferEntry
  , mkFrameBufferEntry
  , fbeImageData, fbeFrame, fbeStoredAtFrame
  , FrameBufferStats
  , mkFrameBufferStats
  , fbsFrameCount, fbsOldestFrame, fbsNewestFrame
  , EchoFrameResult
  , mkEchoFrameResult
  , efrImageData, efrFrame, efrEchoIndex
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

import Prelude

import Data.Array (filter, findIndex, head, length, mapWithIndex, sortBy)
import Data.Foldable (foldl)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (abs)
import Data.Tuple (Tuple(..), fst, snd)
import Math (pow)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Frame buffer entry - stores frame image data with metadata.
type FrameBufferEntry a =
  { imageData :: a        -- Generic to support different image formats
  , frame :: Int          -- Frame number
  , storedAtFrame :: Int  -- Frame-based timestamp for deterministic cleanup
  }

mkFrameBufferEntry :: forall a. a -> Int -> Int -> FrameBufferEntry a
mkFrameBufferEntry imgData fr storedAt =
  { imageData: imgData
  , frame: fr
  , storedAtFrame: storedAt
  }

fbeImageData :: forall a. FrameBufferEntry a -> a
fbeImageData e = e.imageData

fbeFrame :: forall a. FrameBufferEntry a -> Int
fbeFrame e = e.frame

fbeStoredAtFrame :: forall a. FrameBufferEntry a -> Int
fbeStoredAtFrame e = e.storedAtFrame

-- | Buffer statistics.
type FrameBufferStats =
  { frameCount :: Int
  , oldestFrame :: Int
  , newestFrame :: Int
  }

mkFrameBufferStats :: Int -> Int -> Int -> FrameBufferStats
mkFrameBufferStats count oldest newest =
  { frameCount: count
  , oldestFrame: oldest
  , newestFrame: newest
  }

fbsFrameCount :: FrameBufferStats -> Int
fbsFrameCount s = s.frameCount

fbsOldestFrame :: FrameBufferStats -> Int
fbsOldestFrame s = s.oldestFrame

fbsNewestFrame :: FrameBufferStats -> Int
fbsNewestFrame s = s.newestFrame

-- | Echo frame result with echo index.
type EchoFrameResult a =
  { imageData :: a
  , frame :: Int
  , echoIndex :: Int
  }

mkEchoFrameResult :: forall a. a -> Int -> Int -> EchoFrameResult a
mkEchoFrameResult imgData fr idx =
  { imageData: imgData
  , frame: fr
  , echoIndex: idx
  }

efrImageData :: forall a. EchoFrameResult a -> a
efrImageData r = r.imageData

efrFrame :: forall a. EchoFrameResult a -> Int
efrFrame r = r.frame

efrEchoIndex :: forall a. EchoFrameResult a -> Int
efrEchoIndex r = r.echoIndex

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Maximum number of frames to store in buffer.
maxBufferFrames :: Int
maxBufferFrames = 64

-- | Maximum frame distance for cleanup.
defaultMaxFrameDistance :: Int
defaultMaxFrameDistance = maxBufferFrames * 2

--------------------------------------------------------------------------------
-- Buffer Operations (pure)
--------------------------------------------------------------------------------

-- | Check if buffer needs trimming.
shouldTrimBuffer :: Int -> Boolean
shouldTrimBuffer bufferLength = bufferLength > maxBufferFrames

-- | Check if a frame is within acceptable range of current frame.
isFrameInRange :: Int -> Int -> Int -> Boolean
isFrameInRange frameNum currentFrame maxDistance =
  abs (currentFrame - frameNum) < maxDistance

-- | Check frame distance is within range (for cleanup).
frameDistanceInRange :: Int -> Int -> Boolean
frameDistanceInRange storedAtFrame currentFrame =
  abs (currentFrame - storedAtFrame) < defaultMaxFrameDistance

-- | Find the closest frame to target in a list of entries.
--   Returns Nothing if array is empty.
findClosestFrame :: forall a. Array (FrameBufferEntry a) -> Int -> Maybe (FrameBufferEntry a)
findClosestFrame entries targetFrame
  | length entries == 0 = Nothing
  | otherwise =
      let withDist = map (\e -> Tuple (abs (e.frame - targetFrame)) e) entries
          sorted = sortBy (\a b -> compare (fst a) (fst b)) withDist
      in map snd (head sorted)

-- | Find index of closest frame to target.
findClosestFrameIndex :: forall a. Array (FrameBufferEntry a) -> Int -> Maybe Int
findClosestFrameIndex entries targetFrame
  | length entries == 0 = Nothing
  | otherwise =
      let indexed = mapWithIndex (\i e -> Tuple i (abs (e.frame - targetFrame))) entries
          sorted = sortBy (\a b -> compare (snd a) (snd b)) indexed
      in map fst (head sorted)

-- | Calculate target frames for echo effect.
--   Returns array of (targetFrame, echoIndex) pairs.
calculateEchoTargetFrames :: Int -> Number -> Int -> Array (Tuple Int Int)
calculateEchoTargetFrames currentFrame echoTimeFrames numEchoes =
  let indices = map (_ + 1) (0 .. (numEchoes - 1))
      calcTarget i = round (toNumber currentFrame + echoTimeFrames * toNumber i)
  in map (\i -> Tuple (calcTarget i) i) indices
  where
    (..) :: Int -> Int -> Array Int
    (..) start end = if start > end then [] else [start] <> ((start + 1) .. end)

-- | Calculate echo intensity using exponential decay.
--   intensity = startingIntensity * (1 - decay)^echoIndex
calculateEchoIntensity :: Number -> Number -> Int -> Number
calculateEchoIntensity startingIntensity decay echoIndex =
  startingIntensity * pow (1.0 - decay) (toNumber echoIndex)

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

-- | Calculate buffer statistics from entries.
calculateBufferStats :: forall a. Array (FrameBufferEntry a) -> FrameBufferStats
calculateBufferStats entries
  | length entries == 0 = emptyBufferStats
  | otherwise =
      let frames = map _.frame entries
          minMax = foldl (\acc f -> { minF: min acc.minF f, maxF: max acc.maxF f })
                         { minF: 2147483647, maxF: -2147483648 } -- Int max/min
                         frames
      in { frameCount: length entries
         , oldestFrame: minMax.minF
         , newestFrame: minMax.maxF
         }

-- | Empty buffer statistics.
emptyBufferStats :: FrameBufferStats
emptyBufferStats = { frameCount: 0, oldestFrame: -1, newestFrame: -1 }
