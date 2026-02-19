-- | Lattice.Services.RenderQueue.Database - Database request types
-- |
-- | Pure request/response types for render job persistence.
-- | Actual database operations are delegated to the Haskell backend via Bridge.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts (database section)

module Lattice.Services.RenderQueue.Database
  ( -- * Database Handle
    RenderQueueDB
  , mkRenderQueueDB
  , openDatabase
  , closeDatabase
    -- * Request Types
  , DatabaseRequest(..)
  , JobOperation(..)
  , FrameOperation(..)
    -- * Pure Operations (for testing/mock)
  , saveJob
  , getJob
  , getAllJobs
  , deleteJob
  , saveFrame
  , getFrames
  , clearCompletedFrames
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderedFrame
  )

-- | Database handle - pure representation
-- |
-- | This is a pure identifier for a database connection.
-- | The actual connection is managed by the runtime/backend.
newtype RenderQueueDB = RenderQueueDB
  { dbName :: String
  , isOpen :: Boolean
  }

derive instance Eq RenderQueueDB
derive newtype instance Show RenderQueueDB

-- | Create a database handle
mkRenderQueueDB :: String -> RenderQueueDB
mkRenderQueueDB name = RenderQueueDB { dbName: name, isOpen: false }

-- | Open a database connection
-- |
-- | In pure mode, this creates a handle marked as open.
-- | The actual connection is managed by the runtime/backend via Bridge.
openDatabase :: String -> Aff RenderQueueDB
openDatabase name = pure $ RenderQueueDB { dbName: name, isOpen: true }

-- | Close a database connection
-- |
-- | In pure mode, this is a no-op.
-- | The actual close happens via Bridge to the backend.
closeDatabase :: RenderQueueDB -> Effect Unit
closeDatabase _ = pure unit

-- | Job-related database operations
data JobOperation
  = SaveJob RenderJob
  | GetJob String
  | GetAllJobs
  | DeleteJob String

derive instance Eq JobOperation
derive instance Generic JobOperation _
instance Show JobOperation where show = genericShow

-- | Frame-related database operations
data FrameOperation
  = SaveFrame String RenderedFrame
  | GetFrames String
  | ClearCompletedFrames String

derive instance Eq FrameOperation
derive instance Generic FrameOperation _
instance Show FrameOperation where show = genericShow

-- | Database request type
-- |
-- | Send these to the Haskell backend via Bridge.
data DatabaseRequest
  = OpenDatabase String
  | CloseDatabase
  | JobOp JobOperation
  | FrameOp FrameOperation

derive instance Eq DatabaseRequest
derive instance Generic DatabaseRequest _
instance Show DatabaseRequest where show = genericShow

-- | Save a render job to the database
-- |
-- | In pure mode, this is a no-op. The actual save happens via Bridge.
saveJob :: RenderQueueDB -> RenderJob -> Aff Unit
saveJob _ _ = pure unit

-- | Get a job by ID
-- |
-- | In pure mode, returns Nothing. The actual lookup happens via Bridge.
getJob :: RenderQueueDB -> String -> Aff (Maybe RenderJob)
getJob _ _ = pure Nothing

-- | Get all jobs from the database
-- |
-- | In pure mode, returns empty. The actual lookup happens via Bridge.
getAllJobs :: RenderQueueDB -> Aff (Array RenderJob)
getAllJobs _ = pure []

-- | Delete a job and its associated frames
-- |
-- | In pure mode, this is a no-op. The actual delete happens via Bridge.
deleteJob :: RenderQueueDB -> String -> Aff Unit
deleteJob _ _ = pure unit

-- | Save a rendered frame to the database
-- |
-- | In pure mode, this is a no-op. The actual save happens via Bridge.
saveFrame :: RenderQueueDB -> String -> RenderedFrame -> Aff Unit
saveFrame _ _ _ = pure unit

-- | Get all frames for a job
-- |
-- | In pure mode, returns empty. The actual lookup happens via Bridge.
getFrames :: RenderQueueDB -> String -> Aff (Array RenderedFrame)
getFrames _ _ = pure []

-- | Clear all frames for a completed job
-- |
-- | In pure mode, this is a no-op. The actual clear happens via Bridge.
clearCompletedFrames :: RenderQueueDB -> String -> Aff Unit
clearCompletedFrames _ _ = pure unit
