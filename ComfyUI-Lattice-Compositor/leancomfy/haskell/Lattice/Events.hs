{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Events
Description : Layer 2A: Events with proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Events.lean
-}

module Lattice.Events
  ( -- * Base Event
    BaseEvent(..)
    -- * Composition Events
  , CompositionCreated(..)
  , CompositionDeleted(..)
  , CompositionRendered(..)
    -- * Layer Events
  , LayerCreated(..)
  , LayerDeleted(..)
  , LayerMoved(..)
  , LayerDuplicated(..)
  , LayerVisibilityChanged(..)
    -- * Keyframe Events
  , KeyframeAdded(..)
  , KeyframeRemoved(..)
  , KeyframeModified(..)
  , KeyframeInterpolationChanged(..)
    -- * Property Events
  , PropertyAnimated(..)
  , PropertyExpressionChanged(..)
  , PropertyDriverAdded(..)
    -- * Effect Events
  , EffectAdded(..)
  , EffectRemoved(..)
  , EffectParameterChanged(..)
    -- * Export Events
  , ExportStarted(..)
  , ExportProgress(..)
  , ExportCompleted(..)
  , ExportFailed(..)
    -- * System Events
  , CacheCleared(..)
  , ErrorOccurred(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Lattice.Primitives
import Lattice.Enums

--------------------------------------------------------------------------------
-- Base Event
--------------------------------------------------------------------------------

data BaseEvent = BaseEvent
  { beId        :: !NonEmptyString
  , beTimestamp :: !PositiveFloat  -- Unix timestamp in seconds
  , beEventType :: !NonEmptyString -- Type identifier
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Composition Events
--------------------------------------------------------------------------------

data CompositionCreated = CompositionCreated
  { ccBase            :: !BaseEvent
  , ccCompositionId   :: !NonEmptyString
  , ccCompositionName :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data CompositionDeleted = CompositionDeleted
  { cdBase          :: !BaseEvent
  , cdCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data CompositionRendered = CompositionRendered
  { crBase          :: !BaseEvent
  , crCompositionId :: !NonEmptyString
  , crFrameNumber   :: !FrameNumber
  , crDuration      :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Events
--------------------------------------------------------------------------------

data LayerCreated = LayerCreated
  { lcBase          :: !BaseEvent
  , lcLayerId       :: !NonEmptyString
  , lcCompositionId :: !NonEmptyString
  , lcLayerType     :: !LayerType
  } deriving stock (Eq, Show, Generic)

data LayerDeleted = LayerDeleted
  { ldBase          :: !BaseEvent
  , ldLayerId       :: !NonEmptyString
  , ldCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data LayerMoved = LayerMoved
  { lmBase          :: !BaseEvent
  , lmLayerId       :: !NonEmptyString
  , lmCompositionId :: !NonEmptyString
  , lmOldIndex      :: !FrameNumber
  , lmNewIndex      :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data LayerDuplicated = LayerDuplicated
  { ldupBase          :: !BaseEvent
  , ldupSourceLayerId :: !NonEmptyString
  , ldupNewLayerId    :: !NonEmptyString
  , ldupCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data LayerVisibilityChanged = LayerVisibilityChanged
  { lvcBase          :: !BaseEvent
  , lvcLayerId       :: !NonEmptyString
  , lvcCompositionId :: !NonEmptyString
  , lvcVisible       :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Keyframe Events
--------------------------------------------------------------------------------

data KeyframeAdded = KeyframeAdded
  { kaBase         :: !BaseEvent
  , kaKeyframeId   :: !NonEmptyString
  , kaLayerId      :: !NonEmptyString
  , kaPropertyPath :: !NonEmptyString
  , kaFrameNumber  :: !FrameNumber
  , kaValue        :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data KeyframeRemoved = KeyframeRemoved
  { krBase         :: !BaseEvent
  , krKeyframeId   :: !NonEmptyString
  , krLayerId      :: !NonEmptyString
  , krPropertyPath :: !NonEmptyString
  , krFrameNumber  :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data KeyframeModified = KeyframeModified
  { kmBase         :: !BaseEvent
  , kmKeyframeId   :: !NonEmptyString
  , kmLayerId      :: !NonEmptyString
  , kmPropertyPath :: !NonEmptyString
  , kmFrameNumber  :: !FrameNumber
  , kmOldValue     :: !Text
  , kmNewValue     :: !Text
  } deriving stock (Eq, Show, Generic)

data KeyframeInterpolationChanged = KeyframeInterpolationChanged
  { kicBase             :: !BaseEvent
  , kicKeyframeId       :: !NonEmptyString
  , kicLayerId          :: !NonEmptyString
  , kicPropertyPath     :: !NonEmptyString
  , kicOldInterpolation :: !InterpolationType
  , kicNewInterpolation :: !InterpolationType
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Property Events
--------------------------------------------------------------------------------

data PropertyAnimated = PropertyAnimated
  { paBase          :: !BaseEvent
  , paLayerId       :: !NonEmptyString
  , paPropertyPath  :: !NonEmptyString
  , paKeyframeCount :: !Int  -- > 0
  } deriving stock (Eq, Show, Generic)

data PropertyExpressionChanged = PropertyExpressionChanged
  { pecBase          :: !BaseEvent
  , pecLayerId       :: !NonEmptyString
  , pecPropertyPath  :: !NonEmptyString
  , pecOldExpression :: !Text
  , pecNewExpression :: !Text
  } deriving stock (Eq, Show, Generic)

data PropertyDriverAdded = PropertyDriverAdded
  { pdaBase               :: !BaseEvent
  , pdaLayerId            :: !NonEmptyString
  , pdaPropertyPath       :: !NonEmptyString
  , pdaDriverPropertyPath :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Effect Events
--------------------------------------------------------------------------------

data EffectAdded = EffectAdded
  { eaBase           :: !BaseEvent
  , eaEffectId       :: !NonEmptyString
  , eaLayerId        :: !NonEmptyString
  , eaEffectCategory :: !EffectCategory
  } deriving stock (Eq, Show, Generic)

data EffectRemoved = EffectRemoved
  { erBase     :: !BaseEvent
  , erEffectId :: !NonEmptyString
  , erLayerId  :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data EffectParameterChanged = EffectParameterChanged
  { epcBase          :: !BaseEvent
  , epcEffectId      :: !NonEmptyString
  , epcLayerId       :: !NonEmptyString
  , epcParameterName :: !NonEmptyString
  , epcOldValue      :: !Text
  , epcNewValue      :: !Text
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Export Events
--------------------------------------------------------------------------------

data ExportStarted = ExportStarted
  { esBase          :: !BaseEvent
  , esExportId      :: !NonEmptyString
  , esCompositionId :: !NonEmptyString
  , esExportFormat  :: !ExportFormat
  , esExportTarget  :: !ExportTarget
  } deriving stock (Eq, Show, Generic)

data ExportProgress = ExportProgress
  { epBase          :: !BaseEvent
  , epExportId      :: !NonEmptyString
  , epCompositionId :: !NonEmptyString
  , epProgress      :: !Percentage
  , epCurrentFrame  :: !FrameNumber
  , epTotalFrames   :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data ExportCompleted = ExportCompleted
  { ecBase          :: !BaseEvent
  , ecExportId      :: !NonEmptyString
  , ecCompositionId :: !NonEmptyString
  , ecOutputPath    :: !NonEmptyString
  , ecDuration      :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

data ExportFailed = ExportFailed
  { efBase          :: !BaseEvent
  , efExportId      :: !NonEmptyString
  , efCompositionId :: !NonEmptyString
  , efErrorMessage  :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- System Events
--------------------------------------------------------------------------------

data CacheCleared = CacheCleared
  { cclBase      :: !BaseEvent
  , cclCacheType :: !NonEmptyString
  , cclSizeBytes :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data ErrorOccurred = ErrorOccurred
  { eoBase         :: !BaseEvent
  , eoSeverity     :: !Severity
  , eoErrorMessage :: !NonEmptyString
  , eoErrorCode    :: !NonEmptyString
  , eoStackTrace   :: !Text
  } deriving stock (Eq, Show, Generic)
