-- | Lattice.Actions - Layer 4: Actions with proofs
-- |
-- | Source: lattice-core/lean/Lattice/Actions.lean
-- |
-- | Single source of truth for all action types.
-- | Every action has proofs of its invariants.
-- | Depends on: Primitives, Enums, Events, Metrics, Triggers.

module Lattice.Actions
  ( ActionResult(..)
  , RetryPolicy
  , BaseAction
  , CreateLayer
  , DeleteLayer
  , DuplicateLayer
  , MoveLayer
  , SetLayerVisibility
  , SetLayerOpacity
  , AddKeyframe
  , RemoveKeyframe
  , ModifyKeyframe
  , SetInterpolation
  , CopyKeyframes
  , PasteKeyframes
  , AnimateProperty
  , SetPropertyValue
  , AddExpression
  , RemoveExpression
  , AddDriver
  , AddEffect
  , RemoveEffect
  , ModifyEffect
  , EnableEffect
  , DisableEffect
  , CreateComposition
  , DeleteComposition
  , SetCompositionSettings
  , RenderComposition
  , StartExport
  , CancelExport
  , PauseExport
  , ResumeExport
  , SetExportSettings
  , LoadAudio
  , AnalyzeAudio
  , SetAudioReactivity
  , SetCameraPosition
  , SetCameraRotation
  , SetCameraFOV
  , AnimateCamera
  , SegmentImage
  , VectorizeImage
  , DecomposeImage
  , GenerateDepth
  , EstimateNormals
  , ClearCache
  , OptimizeMemory
  , SaveProject
  , LoadProject
  , Undo
  , Redo
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Enums

-- ────────────────────────────────────────────────────────────────────────────
-- Action Result
-- ────────────────────────────────────────────────────────────────────────────

data ActionResult = ARSuccess | ARFailure | ARPartial

derive instance Eq ActionResult
derive instance Generic ActionResult _
instance Show ActionResult where show = genericShow

type RetryPolicy =
  { maxRetries        :: FrameNumber
  , retryDelay        :: NonNegativeFloat  -- Seconds
  , backoffMultiplier :: PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Base Action
-- ────────────────────────────────────────────────────────────────────────────

type BaseAction =
  { id          :: NonEmptyString
  , actionType  :: NonEmptyString
  , target      :: NonEmptyString  -- Target ID (layer, composition, etc.)
  , params      :: String          -- JSON-encoded parameters
  , retryPolicy :: Maybe RetryPolicy
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Actions
-- ────────────────────────────────────────────────────────────────────────────

type CreateLayer =
  { base          :: BaseAction
  , layerType     :: LayerType
  , compositionId :: NonEmptyString
  }

type DeleteLayer =
  { base          :: BaseAction
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  }

type DuplicateLayer =
  { base          :: BaseAction
  , sourceLayerId :: NonEmptyString
  , compositionId :: NonEmptyString
  }

type MoveLayer =
  { base          :: BaseAction
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , newIndex      :: FrameNumber
  }

type SetLayerVisibility =
  { base          :: BaseAction
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , visible       :: Boolean
  }

type SetLayerOpacity =
  { base          :: BaseAction
  , layerId       :: NonEmptyString
  , compositionId :: NonEmptyString
  , opacity       :: UnitFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Keyframe Actions
-- ────────────────────────────────────────────────────────────────────────────

type AddKeyframe =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  , value        :: String  -- JSON-encoded
  }

type RemoveKeyframe =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  }

type ModifyKeyframe =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber
  , value        :: String  -- JSON-encoded new value
  }

type SetInterpolation =
  { base          :: BaseAction
  , layerId       :: NonEmptyString
  , propertyPath  :: NonEmptyString
  , frameNumber   :: FrameNumber
  , interpolation :: InterpolationType
  }

type CopyKeyframes =
  { base               :: BaseAction
  , sourceLayerId      :: NonEmptyString
  , sourcePropertyPath :: NonEmptyString
  , targetLayerId      :: NonEmptyString
  , targetPropertyPath :: NonEmptyString
  , frameRange         :: Maybe (Tuple FrameNumber FrameNumber)
  }

type PasteKeyframes =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , frameNumber  :: FrameNumber  -- Paste at this frame
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Property Actions
-- ────────────────────────────────────────────────────────────────────────────

type AnimateProperty =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , keyframes    :: String  -- JSON-encoded array
  }

type SetPropertyValue =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , value        :: String  -- JSON-encoded
  }

type AddExpression =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , expression   :: NonEmptyString
  }

type RemoveExpression =
  { base         :: BaseAction
  , layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  }

type AddDriver =
  { base               :: BaseAction
  , layerId            :: NonEmptyString
  , propertyPath       :: NonEmptyString
  , driverPropertyPath :: NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Actions
-- ────────────────────────────────────────────────────────────────────────────

type AddEffect =
  { base           :: BaseAction
  , layerId        :: NonEmptyString
  , effectCategory :: EffectCategory
  , effectParams   :: String  -- JSON-encoded
  }

type RemoveEffect =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , effectId :: NonEmptyString
  }

type ModifyEffect =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , effectId :: NonEmptyString
  , params   :: String  -- JSON-encoded
  }

type EnableEffect =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , effectId :: NonEmptyString
  }

type DisableEffect =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , effectId :: NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Composition Actions
-- ────────────────────────────────────────────────────────────────────────────

type CreateComposition =
  { base            :: BaseAction
  , compositionName :: NonEmptyString
  , width           :: PositiveInt
  , height          :: PositiveInt
  , fps             :: PositiveFloat
  }

type DeleteComposition =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  }

type SetCompositionSettings =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  , settings      :: String  -- JSON-encoded
  }

type RenderComposition =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  , startFrame    :: FrameNumber
  , endFrame      :: FrameNumber
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Actions
-- ────────────────────────────────────────────────────────────────────────────

type StartExport =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  , exportFormat  :: ExportFormat
  , exportTarget  :: ExportTarget
  , settings      :: String  -- JSON-encoded
  }

type CancelExport =
  { base     :: BaseAction
  , exportId :: NonEmptyString
  }

type PauseExport =
  { base     :: BaseAction
  , exportId :: NonEmptyString
  }

type ResumeExport =
  { base     :: BaseAction
  , exportId :: NonEmptyString
  }

type SetExportSettings =
  { base     :: BaseAction
  , exportId :: NonEmptyString
  , settings :: String  -- JSON-encoded
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Audio Actions
-- ────────────────────────────────────────────────────────────────────────────

type LoadAudio =
  { base      :: BaseAction
  , layerId   :: NonEmptyString
  , audioPath :: NonEmptyString
  }

type AnalyzeAudio =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , method  :: BeatDetectionMethod
  }

type SetAudioReactivity =
  { base             :: BaseAction
  , layerId          :: NonEmptyString
  , enabled          :: Boolean
  , reactivityParams :: String  -- JSON-encoded
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Actions
-- ────────────────────────────────────────────────────────────────────────────

type SetCameraPosition =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , position :: Vec3
  }

type SetCameraRotation =
  { base     :: BaseAction
  , layerId  :: NonEmptyString
  , rotation :: Vec3  -- Euler angles
  }

type SetCameraFOV =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , fov     :: PositiveFloat  -- Field of view in degrees
  }

type AnimateCamera =
  { base      :: BaseAction
  , layerId   :: NonEmptyString
  , keyframes :: String  -- JSON-encoded camera keyframes
  }

-- ────────────────────────────────────────────────────────────────────────────
--                                                                   // ai // a
-- ────────────────────────────────────────────────────────────────────────────

type SegmentImage =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , mode    :: SegmentationMode
  }

type VectorizeImage =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , params  :: String  -- JSON-encoded
  }

type DecomposeImage =
  { base       :: BaseAction
  , layerId    :: NonEmptyString
  , components :: String  -- JSON-encoded component list
  }

type GenerateDepth =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , method  :: PreprocessorType
  }

type EstimateNormals =
  { base    :: BaseAction
  , layerId :: NonEmptyString
  , params  :: String  -- JSON-encoded
  }

-- ────────────────────────────────────────────────────────────────────────────
-- System Actions
-- ────────────────────────────────────────────────────────────────────────────

type ClearCache =
  { base      :: BaseAction
  , cacheType :: NonEmptyString
  }

type OptimizeMemory =
  { base           :: BaseAction
  , targetMemoryMB :: PositiveFloat
  }

type SaveProject =
  { base      :: BaseAction
  , projectId :: NonEmptyString
  , filePath  :: NonEmptyString
  }

type LoadProject =
  { base     :: BaseAction
  , filePath :: NonEmptyString
  }

type Undo =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  , steps         :: FrameNumber  -- Number of steps to undo
  }

type Redo =
  { base          :: BaseAction
  , compositionId :: NonEmptyString
  , steps         :: FrameNumber  -- Number of steps to redo
  }
