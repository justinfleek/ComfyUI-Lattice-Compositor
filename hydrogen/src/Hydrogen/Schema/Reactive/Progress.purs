-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress - numeric progress atoms for reactive systems.
-- |
-- | Frame.io-level responsiveness requires tracking progress at every level:
-- | uploads, downloads, processing, rendering, seeking, buffering.

module Hydrogen.Schema.Reactive.Progress
  ( -- * Core Progress
    Progress
  , progress
  , unsafeProgress
  , unwrap
  , toPercent
  , isComplete
  , bounds
  -- * Specialized Progress Types
  , UploadProgress
  , DownloadProgress
  , BufferProgress
  , RenderProgress
  , ProcessingProgress
  , SeekProgress
  -- * Smart Constructors
  , uploadProgress
  , downloadProgress
  , bufferProgress
  , renderProgress
  , processingProgress
  , seekProgress
  -- * Transfer Progress
  , TransferProgress
  , transferProgress
  , bytesLoaded
  , bytesTotal
  , transferPercent
  , transferRate
  -- * Step Progress
  , StepProgress
  , stepProgress
  , currentStep
  , totalSteps
  , stepPercent
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress value (0.0 to 1.0)
-- |
-- | A normalized progress value where 0.0 is not started and 1.0 is complete.
newtype Progress = Progress Number

derive instance eqProgress :: Eq Progress
derive instance ordProgress :: Ord Progress

instance showProgress :: Show Progress where
  show (Progress p) = show (p * 100.0) <> "%"

-- | Create a progress value, clamping to 0.0-1.0
progress :: Number -> Progress
progress n = Progress (Bounded.clampNumber 0.0 1.0 n)

-- | Create a progress value without clamping
unsafeProgress :: Number -> Progress
unsafeProgress = Progress

-- | Extract the raw Number value
unwrap :: Progress -> Number
unwrap (Progress p) = p

-- | Convert to percentage (0-100)
toPercent :: Progress -> Number
toPercent (Progress p) = p * 100.0

-- | Check if progress is complete
isComplete :: Progress -> Boolean
isComplete (Progress p) = p >= 1.0

-- | Bounds documentation
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "progress" "Progress from 0.0 to 1.0"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // specialized progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Upload progress (0.0 to 1.0)
newtype UploadProgress = UploadProgress Progress
derive instance eqUploadProgress :: Eq UploadProgress
derive newtype instance showUploadProgress :: Show UploadProgress

-- | Download progress (0.0 to 1.0)
newtype DownloadProgress = DownloadProgress Progress
derive instance eqDownloadProgress :: Eq DownloadProgress
derive newtype instance showDownloadProgress :: Show DownloadProgress

-- | Buffer progress (0.0 to 1.0) - how much is buffered ahead
newtype BufferProgress = BufferProgress Progress
derive instance eqBufferProgress :: Eq BufferProgress
derive newtype instance showBufferProgress :: Show BufferProgress

-- | Render progress (0.0 to 1.0) - video/image render progress
newtype RenderProgress = RenderProgress Progress
derive instance eqRenderProgress :: Eq RenderProgress
derive newtype instance showRenderProgress :: Show RenderProgress

-- | Processing progress (0.0 to 1.0) - general computation
newtype ProcessingProgress = ProcessingProgress Progress
derive instance eqProcessingProgress :: Eq ProcessingProgress
derive newtype instance showProcessingProgress :: Show ProcessingProgress

-- | Seek progress (0.0 to 1.0) - media playhead position
newtype SeekProgress = SeekProgress Progress
derive instance eqSeekProgress :: Eq SeekProgress
derive newtype instance showSeekProgress :: Show SeekProgress

-- | Smart constructors
uploadProgress :: Number -> UploadProgress
uploadProgress = UploadProgress <<< progress

downloadProgress :: Number -> DownloadProgress
downloadProgress = DownloadProgress <<< progress

bufferProgress :: Number -> BufferProgress
bufferProgress = BufferProgress <<< progress

renderProgress :: Number -> RenderProgress
renderProgress = RenderProgress <<< progress

processingProgress :: Number -> ProcessingProgress
processingProgress = ProcessingProgress <<< progress

seekProgress :: Number -> SeekProgress
seekProgress = SeekProgress <<< progress

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transfer progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transfer progress with byte counts and rate
-- |
-- | For uploads/downloads where you need to show "5.2 MB / 12.8 MB at 2.1 MB/s"
type TransferProgress =
  { loaded :: Number        -- ^ Bytes transferred
  , total :: Number         -- ^ Total bytes (0 if unknown)
  , rate :: Number          -- ^ Bytes per second
  , progress :: Progress    -- ^ Normalized 0-1
  }

-- | Create transfer progress from loaded/total bytes
transferProgress :: Number -> Number -> Number -> TransferProgress
transferProgress loaded total rate =
  { loaded
  , total
  , rate
  , progress: if total > 0.0 then progress (loaded / total) else progress 0.0
  }

-- | Get bytes loaded
bytesLoaded :: TransferProgress -> Number
bytesLoaded tp = tp.loaded

-- | Get total bytes
bytesTotal :: TransferProgress -> Number
bytesTotal tp = tp.total

-- | Get transfer percentage
transferPercent :: TransferProgress -> Number
transferPercent tp = toPercent tp.progress

-- | Get transfer rate (bytes/sec)
transferRate :: TransferProgress -> Number
transferRate tp = tp.rate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // step progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step-based progress (wizard, multi-step process)
-- |
-- | For "Step 3 of 5" type progress indicators
type StepProgress =
  { current :: Int          -- ^ Current step (1-indexed)
  , total :: Int            -- ^ Total steps
  , progress :: Progress    -- ^ Normalized 0-1
  }

-- | Create step progress
stepProgress :: Int -> Int -> StepProgress
stepProgress current total =
  { current
  , total
  , progress: if total > 0 
      then progress (Int.toNumber current / Int.toNumber total)
      else progress 0.0
  }

-- | Get current step
currentStep :: StepProgress -> Int
currentStep sp = sp.current

-- | Get total steps
totalSteps :: StepProgress -> Int
totalSteps sp = sp.total

-- | Get step percentage
stepPercent :: StepProgress -> Number
stepPercent sp = toPercent sp.progress
