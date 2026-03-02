-- | Lattice.Services.RenderQueue.Types - Render queue types
-- |
-- | Pure types for background render queue management.
-- | No FFI required - just data types and pure functions.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts (types section)

module Lattice.Services.RenderQueue.Types
  ( -- * Job Types
    RenderJobStatus(..)
  , RenderJobConfig
  , RenderJobProgress
  , RenderJob
  , RenderedFrame
    -- * Queue Types
  , RenderQueueStats
  , RenderQueueConfig
  , OutputFormat(..)
    -- * Defaults
  , defaultQueueConfig
  , defaultJobProgress
    -- * Conversion
  , statusToString
  , stringToStatus
  , formatToString
  , stringToFormat
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Job Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Render job status
data RenderJobStatus
  = StatusPending
  | StatusRendering
  | StatusPaused
  | StatusCompleted
  | StatusFailed
  | StatusCancelled

derive instance Eq RenderJobStatus
derive instance Ord RenderJobStatus
derive instance Generic RenderJobStatus _
instance Show RenderJobStatus where show = genericShow

-- | Output format for render job
data OutputFormat
  = FormatPngSequence
  | FormatWebM
  | FormatMp4

derive instance Eq OutputFormat
derive instance Ord OutputFormat
derive instance Generic OutputFormat _
instance Show OutputFormat where show = genericShow

-- | Render job configuration
type RenderJobConfig =
  { id :: String              -- Unique job identifier
  , name :: String            -- Human-readable job name
  , compositionId :: String   -- Composition ID to render
  , startFrame :: Int         -- Start frame (inclusive)
  , endFrame :: Int           -- End frame (inclusive)
  , width :: Int              -- Output width
  , height :: Int             -- Output height
  , fps :: Number             -- Frames per second
  , format :: OutputFormat    -- Output format
  , quality :: Int            -- Quality (0-100)
  , priority :: Int           -- Priority (lower = higher priority)
  }

-- | Render job progress
type RenderJobProgress =
  { status :: RenderJobStatus
  , currentFrame :: Int
  , totalFrames :: Int
  , percentage :: Int           -- 0-100
  , framesPerSecond :: Number
  , estimatedTimeRemaining :: Number  -- Seconds
  , elapsedTime :: Number            -- Seconds
  , error :: Maybe String
  }

-- | Full render job with config and progress
type RenderJob =
  { id :: String
  , name :: String
  , compositionId :: String
  , startFrame :: Int
  , endFrame :: Int
  , width :: Int
  , height :: Int
  , fps :: Number
  , format :: OutputFormat
  , quality :: Int
  , priority :: Int
  , progress :: RenderJobProgress
  , createdAt :: Number           -- Timestamp
  , startedAt :: Maybe Number     -- Timestamp
  , completedAt :: Maybe Number   -- Timestamp
  , checkpointFrame :: Maybe Int  -- For resume capability
  }

-- | Rendered frame data
type RenderedFrame =
  { frameNumber :: Int
  , dataUrl :: String         -- Base64 encoded image data
  , timestamp :: Number       -- When rendered
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Queue Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Queue statistics
type RenderQueueStats =
  { totalJobs :: Int
  , activeJobs :: Int
  , pendingJobs :: Int
  , completedJobs :: Int
  , failedJobs :: Int
  , totalFramesRendered :: Int
  , averageFps :: Number
  }

-- | Queue configuration
type RenderQueueConfig =
  { maxConcurrentJobs :: Int
  , workerPoolSize :: Int
  , batchSize :: Int
  , autoSaveInterval :: Int    -- Milliseconds
  , dbName :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Default queue configuration
defaultQueueConfig :: RenderQueueConfig
defaultQueueConfig =
  { maxConcurrentJobs: 1
  , workerPoolSize: 4
  , batchSize: 10
  , autoSaveInterval: 5000
  , dbName: "lattice-render-queue"
  }

-- | Default job progress (pending state)
defaultJobProgress :: Int -> Int -> RenderJobProgress
defaultJobProgress startFrame endFrame =
  { status: StatusPending
  , currentFrame: startFrame
  , totalFrames: endFrame - startFrame + 1
  , percentage: 0
  , framesPerSecond: 0.0
  , estimatedTimeRemaining: 0.0
  , elapsedTime: 0.0
  , error: Nothing
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Conversion Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert status to string
statusToString :: RenderJobStatus -> String
statusToString = case _ of
  StatusPending -> "pending"
  StatusRendering -> "rendering"
  StatusPaused -> "paused"
  StatusCompleted -> "completed"
  StatusFailed -> "failed"
  StatusCancelled -> "cancelled"

-- | Parse string to status
stringToStatus :: String -> Maybe RenderJobStatus
stringToStatus = case _ of
  "pending" -> Just StatusPending
  "rendering" -> Just StatusRendering
  "paused" -> Just StatusPaused
  "completed" -> Just StatusCompleted
  "failed" -> Just StatusFailed
  "cancelled" -> Just StatusCancelled
  _ -> Nothing

-- | Convert format to string
formatToString :: OutputFormat -> String
formatToString = case _ of
  FormatPngSequence -> "png-sequence"
  FormatWebM -> "webm"
  FormatMp4 -> "mp4"

-- | Parse string to format
stringToFormat :: String -> Maybe OutputFormat
stringToFormat = case _ of
  "png-sequence" -> Just FormatPngSequence
  "webm" -> Just FormatWebM
  "mp4" -> Just FormatMp4
  _ -> Nothing
