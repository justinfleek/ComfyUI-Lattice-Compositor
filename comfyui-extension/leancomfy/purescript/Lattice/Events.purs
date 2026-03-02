-- | Lattice.Events - Layer 2A: Events with proofs
-- |
-- | Source: leancomfy/lean/Lattice/Events.lean

module Lattice.Events
  ( BaseEvent
  , CompositionCreated
  , CompositionDeleted
  , CompositionRendered
  , LayerCreated
  , LayerDeleted
  , LayerMoved
  , LayerDuplicated
  , LayerVisibilityChanged
  , KeyframeAdded
  , KeyframeRemoved
  , KeyframeModified
  , PropertyAnimated
  , PropertyExpressionChanged
  , EffectAdded
  , EffectRemoved
  , ExportStarted
  , ExportProgress
  , ExportCompleted
  , ExportFailed
  , CacheCleared
  , ErrorOccurred
  ) where

import Lattice.Primitives
import Lattice.Enums

--------------------------------------------------------------------------------
-- Base Event
--------------------------------------------------------------------------------

type BaseEvent =
  { id        :: NonEmptyString
  , timestamp :: PositiveFloat  -- Unix timestamp
  , eventType :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Composition Events
--------------------------------------------------------------------------------

type CompositionCreated =
  { base            :: BaseEvent
  , compositionId   :: NonEmptyString
  , compositionName :: NonEmptyString
  }

type CompositionDeleted =
  { base          :: BaseEvent
  , compositionId :: NonEmptyString
  }

type CompositionRendered =
  { base          :: BaseEvent
  , compositionId :: NonEmptyString
  , frameNumber   :: FrameNumber
  , duration      :: NonNegativeFloat
  }

--------------------------------------------------------------------------------
-- Layer Events
--------------------------------------------------------------------------------

type LayerCreated =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , layerType     :: LayerType
  }

type LayerDeleted =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  }

type LayerMoved =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , oldIndex      :: FrameNumber
  , newIndex      :: FrameNumber
  }

type LayerDuplicated =
  { base          :: BaseEvent
  , sourceLayerId :: NonEmptyString
  , newLayerId    :: NonEmptyString
  , compositionId :: NonEmptyString
  }

type LayerVisibilityChanged =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , visible       :: Boolean
  }

--------------------------------------------------------------------------------
-- Keyframe Events
--------------------------------------------------------------------------------

type KeyframeAdded =
  { base         :: BaseEvent
  , keyframeId   :: NonEmptyString
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  , value        :: String
  }

type KeyframeRemoved =
  { base         :: BaseEvent
  , keyframeId   :: NonEmptyString
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  }

type KeyframeModified =
  { base         :: BaseEvent
  , keyframeId   :: NonEmptyString
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  , oldValue     :: String
  , newValue     :: String
  }

--------------------------------------------------------------------------------
-- Property Events
--------------------------------------------------------------------------------

type PropertyAnimated =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , propertyPath  :: NonEmptyString
  , keyframeCount :: Int
  }

type PropertyExpressionChanged =
  { base          :: BaseEvent
  , layerId       :: NonEmptyString
  , propertyPath  :: NonEmptyString
  , oldExpression :: String
  , newExpression :: String
  }

--------------------------------------------------------------------------------
-- Effect Events
--------------------------------------------------------------------------------

type EffectAdded =
  { base           :: BaseEvent
  , effectId       :: NonEmptyString
  , layerId        :: NonEmptyString
  , effectCategory :: EffectCategory
  }

type EffectRemoved =
  { base     :: BaseEvent
  , effectId :: NonEmptyString
  , layerId  :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Export Events
--------------------------------------------------------------------------------

type ExportStarted =
  { base          :: BaseEvent
  , exportId      :: NonEmptyString
  , compositionId :: NonEmptyString
  , exportFormat  :: ExportFormat
  , exportTarget  :: ExportTarget
  }

type ExportProgress =
  { base          :: BaseEvent
  , exportId      :: NonEmptyString
  , compositionId :: NonEmptyString
  , progress      :: Percentage
  , currentFrame  :: FrameNumber
  , totalFrames   :: FrameNumber
  }

type ExportCompleted =
  { base          :: BaseEvent
  , exportId      :: NonEmptyString
  , compositionId :: NonEmptyString
  , outputPath    :: NonEmptyString
  , duration      :: NonNegativeFloat
  }

type ExportFailed =
  { base          :: BaseEvent
  , exportId      :: NonEmptyString
  , compositionId :: NonEmptyString
  , errorMessage  :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- System Events
--------------------------------------------------------------------------------

type CacheCleared =
  { base      :: BaseEvent
  , cacheType :: NonEmptyString
  , sizeBytes :: FrameNumber
  }

type ErrorOccurred =
  { base         :: BaseEvent
  , severity     :: Severity
  , errorMessage :: NonEmptyString
  , errorCode    :: NonEmptyString
  , stackTrace   :: String
  }
