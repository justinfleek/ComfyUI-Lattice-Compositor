-- |
-- Module      : Lattice.State.Animation.Types
-- Description : Types for animation store operations
-- 
-- Migrated from ui/src/stores/animationStore/types.ts
-- Types for animation/playback operations, state, and access interfaces
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Animation.Types
  ( AnimationState(..)
  , defaultAnimationState
  ) where

import Data.Aeson.Types ((.!=))
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Services.TimelineSnap (SnapConfig(..), defaultSnapConfig)
import Lattice.Types.Primitives (validateFinite, validateNonNegative)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // animation // state
-- ════════════════════════════════════════════════════════════════════════════

-- | State for animation store
--                             // every // value // has // explicit // defaults
data AnimationState = AnimationState
  { animationStateLoopPlayback :: Bool  -- Default: True
  , animationStateWorkAreaStart :: Double  -- Default: 0.0 (min: 0.0, max: no upper bound)
  , animationStateWorkAreaStartSet :: Bool  -- Explicit flag: work area start is set (default: False)
  , animationStateWorkAreaEnd :: Double  -- Default: 0.0 (min: 0.0, max: no upper bound)
  , animationStateWorkAreaEndSet :: Bool  -- Explicit flag: work area end is set (default: False)
  , animationStateTimelineZoom :: Double  -- Default: 1.0 (min: 0.1, max: 10.0)
  , animationStateSnapConfig :: SnapConfig  -- Timeline snap configuration
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimationState where
  toJSON (AnimationState loopPlayback workAreaStart startSet workAreaEnd endSet timelineZoom snapConfig) =
    let
      baseFields = ["loopPlayback" .= loopPlayback, "workAreaStartSet" .= startSet, "workAreaEndSet" .= endSet, "timelineZoom" .= timelineZoom, "snapConfig" .= snapConfig]
      withStart = if startSet then ("workAreaStart" .= workAreaStart) : baseFields else baseFields
      withEnd = if endSet then ("workAreaEnd" .= workAreaEnd) : withStart else withStart
    in object withEnd

instance FromJSON AnimationState where
  parseJSON = withObject "AnimationState" $ \o -> do
    loopPlayback <- o .:? "loopPlayback" .!= True
    workAreaStart <- o .:? "workAreaStart" .!= 0.0
    startSet <- o .:? "workAreaStartSet" .!= False
    workAreaEnd <- o .:? "workAreaEnd" .!= 0.0
    endSet <- o .:? "workAreaEndSet" .!= False
    timelineZoom <- o .:? "timelineZoom" .!= 1.0
    snapConfig <- o .:? "snapConfig" .!= defaultSnapConfig
    -- Validate work area frames are finite and non-negative if set
    let validateWorkAreaFrame frame set =
          if set
          then validateFinite frame && validateNonNegative frame
          else True
    -- Validate timeline zoom is finite and in range [0.1, 10]
    if validateWorkAreaFrame workAreaStart startSet && validateWorkAreaFrame workAreaEnd endSet && validateFinite timelineZoom && timelineZoom >= 0.1 && timelineZoom <= 10
      then return (AnimationState loopPlayback workAreaStart startSet workAreaEnd endSet timelineZoom snapConfig)
      else fail "AnimationState: workAreaStart and workAreaEnd must be finite and non-negative if set, timelineZoom must be finite and in range [0.1, 10]"

-- | Default animation state
-- All values have explicit defaults - no Maybe/Nothing
defaultAnimationState :: AnimationState
defaultAnimationState = AnimationState
  { animationStateLoopPlayback = True
  , animationStateWorkAreaStart = 0.0  -- Default: not set (use 0)
  , animationStateWorkAreaStartSet = False  -- Explicit flag: not set
  , animationStateWorkAreaEnd = 0.0  -- Default: not set (use frameCount - 1)
  , animationStateWorkAreaEndSet = False  -- Explicit flag: not set
  , animationStateTimelineZoom = 1.0
  , animationStateSnapConfig = defaultSnapConfig
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // access // interfaces
-- ════════════════════════════════════════════════════════════════════════════
--
--                                                                      // note
-- are not represented as Haskell types because they are TypeScript interfaces used for
-- dependency injection. In Haskell, we pass the required data directly as function parameters.
--
-- TypeScript interfaces:
-- - AnimationStoreAccess: Provides isPlaying, getActiveComp(), currentFrame, frameCount, fps, getActiveCompLayers(), getLayerById(), project, pushHistory()
-- - FrameEvaluationAccess: Extends AnimationStoreAccess with full project and activeCameraId
-- - SnapPointAccess: Extends AnimationStoreAccess with layers array
--
-- In Haskell, these are represented by:
-- - Passing Composition directly (instead of getActiveComp())
-- - Passing required values directly (currentFrame, frameCount, fps, etc.)
-- - Passing Layer list directly (instead of getActiveCompLayers())
-- - Passing LatticeProject directly (instead of project)
-- - Using Either Text for error handling (instead of null checks)
--
