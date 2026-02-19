{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Actions
Description : Layer 4: Actions with proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/Actions.lean

Single source of truth for all action types.
Every action has proofs of its invariants.
Depends on: Primitives, Enums, Events, Metrics, Triggers.
-}

module Lattice.Actions
  ( -- * Action Result
    ActionResult(..)
  , RetryPolicy(..)
    -- * Base Action
  , BaseAction(..)
    -- * Layer Actions
  , CreateLayer(..)
  , DeleteLayer(..)
  , DuplicateLayer(..)
  , MoveLayer(..)
  , SetLayerVisibility(..)
  , SetLayerOpacity(..)
    -- * Keyframe Actions
  , AddKeyframe(..)
  , RemoveKeyframe(..)
  , ModifyKeyframe(..)
  , SetInterpolation(..)
  , CopyKeyframes(..)
  , PasteKeyframes(..)
    -- * Property Actions
  , AnimateProperty(..)
  , SetPropertyValue(..)
  , AddExpression(..)
  , RemoveExpression(..)
  , AddDriver(..)
    -- * Effect Actions
  , AddEffect(..)
  , RemoveEffect(..)
  , ModifyEffect(..)
  , EnableEffect(..)
  , DisableEffect(..)
    -- * Composition Actions
  , CreateComposition(..)
  , DeleteComposition(..)
  , SetCompositionSettings(..)
  , RenderComposition(..)
    -- * Export Actions
  , StartExport(..)
  , CancelExport(..)
  , PauseExport(..)
  , ResumeExport(..)
  , SetExportSettings(..)
    -- * Audio Actions
  , LoadAudio(..)
  , AnalyzeAudio(..)
  , SetAudioReactivity(..)
    -- * Camera Actions
  , SetCameraPosition(..)
  , SetCameraRotation(..)
  , SetCameraFOV(..)
  , AnimateCamera(..)
    -- * AI Actions
  , SegmentImage(..)
  , VectorizeImage(..)
  , DecomposeImage(..)
  , GenerateDepth(..)
  , EstimateNormals(..)
    -- * System Actions
  , ClearCache(..)
  , OptimizeMemory(..)
  , SaveProject(..)
  , LoadProject(..)
  , Undo(..)
  , Redo(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Lattice.Primitives
import Lattice.Enums

-- ────────────────────────────────────────────────────────────────────────────
-- Action Result
-- ────────────────────────────────────────────────────────────────────────────

data ActionResult = ARSuccess | ARFailure | ARPartial
  deriving stock (Eq, Show, Generic)

data RetryPolicy = RetryPolicy
  { rpMaxRetries        :: !FrameNumber
  , rpRetryDelay        :: !NonNegativeFloat  -- Seconds
  , rpBackoffMultiplier :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Base Action
-- ────────────────────────────────────────────────────────────────────────────

data BaseAction = BaseAction
  { baId          :: !NonEmptyString
  , baActionType  :: !NonEmptyString
  , baTarget      :: !NonEmptyString  -- Target ID (layer, composition, etc.)
  , baParams      :: !Text            -- JSON-encoded parameters
  , baRetryPolicy :: !(Maybe RetryPolicy)
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Actions
-- ────────────────────────────────────────────────────────────────────────────

data CreateLayer = CreateLayer
  { clBase          :: !BaseAction
  , clLayerType     :: !LayerType
  , clCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data DeleteLayer = DeleteLayer
  { dlBase          :: !BaseAction
  , dlLayerId       :: !NonEmptyString
  , dlCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data DuplicateLayer = DuplicateLayer
  { duplBase          :: !BaseAction
  , duplSourceLayerId :: !NonEmptyString
  , duplCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data MoveLayer = MoveLayer
  { mlBase          :: !BaseAction
  , mlLayerId       :: !NonEmptyString
  , mlCompositionId :: !NonEmptyString
  , mlNewIndex      :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data SetLayerVisibility = SetLayerVisibility
  { slvBase          :: !BaseAction
  , slvLayerId       :: !NonEmptyString
  , slvCompositionId :: !NonEmptyString
  , slvVisible       :: !Bool
  } deriving stock (Eq, Show, Generic)

data SetLayerOpacity = SetLayerOpacity
  { sloBase          :: !BaseAction
  , sloLayerId       :: !NonEmptyString
  , sloCompositionId :: !NonEmptyString
  , sloOpacity       :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Keyframe Actions
-- ────────────────────────────────────────────────────────────────────────────

data AddKeyframe = AddKeyframe
  { akBase         :: !BaseAction
  , akLayerId      :: !NonEmptyString
  , akPropertyPath :: !NonEmptyString
  , akFrameNumber  :: !FrameNumber
  , akValue        :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data RemoveKeyframe = RemoveKeyframe
  { rkBase         :: !BaseAction
  , rkLayerId      :: !NonEmptyString
  , rkPropertyPath :: !NonEmptyString
  , rkFrameNumber  :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data ModifyKeyframe = ModifyKeyframe
  { mkBase         :: !BaseAction
  , mkLayerId      :: !NonEmptyString
  , mkPropertyPath :: !NonEmptyString
  , mkFrameNumber  :: !FrameNumber
  , mkValue        :: !Text  -- JSON-encoded new value
  } deriving stock (Eq, Show, Generic)

data SetInterpolation = SetInterpolation
  { siBase          :: !BaseAction
  , siLayerId       :: !NonEmptyString
  , siPropertyPath  :: !NonEmptyString
  , siFrameNumber   :: !FrameNumber
  , siInterpolation :: !InterpolationType
  } deriving stock (Eq, Show, Generic)

data CopyKeyframes = CopyKeyframes
  { ckBase               :: !BaseAction
  , ckSourceLayerId      :: !NonEmptyString
  , ckSourcePropertyPath :: !NonEmptyString
  , ckTargetLayerId      :: !NonEmptyString
  , ckTargetPropertyPath :: !NonEmptyString
  , ckFrameRange         :: !(Maybe (FrameNumber, FrameNumber))
  } deriving stock (Eq, Show, Generic)

data PasteKeyframes = PasteKeyframes
  { pkBase         :: !BaseAction
  , pkLayerId      :: !NonEmptyString
  , pkPropertyPath :: !NonEmptyString
  , pkFrameNumber  :: !FrameNumber  -- Paste at this frame
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Property Actions
-- ────────────────────────────────────────────────────────────────────────────

data AnimateProperty = AnimateProperty
  { apBase         :: !BaseAction
  , apLayerId      :: !NonEmptyString
  , apPropertyPath :: !NonEmptyString
  , apKeyframes    :: !Text  -- JSON-encoded array
  } deriving stock (Eq, Show, Generic)

data SetPropertyValue = SetPropertyValue
  { spvBase         :: !BaseAction
  , spvLayerId      :: !NonEmptyString
  , spvPropertyPath :: !NonEmptyString
  , spvValue        :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data AddExpression = AddExpression
  { aeBase         :: !BaseAction
  , aeLayerId      :: !NonEmptyString
  , aePropertyPath :: !NonEmptyString
  , aeExpression   :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data RemoveExpression = RemoveExpression
  { reBase         :: !BaseAction
  , reLayerId      :: !NonEmptyString
  , rePropertyPath :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data AddDriver = AddDriver
  { adBase               :: !BaseAction
  , adLayerId            :: !NonEmptyString
  , adPropertyPath       :: !NonEmptyString
  , adDriverPropertyPath :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Actions
-- ────────────────────────────────────────────────────────────────────────────

data AddEffect = AddEffect
  { aefBase           :: !BaseAction
  , aefLayerId        :: !NonEmptyString
  , aefEffectCategory :: !EffectCategory
  , aefEffectParams   :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data RemoveEffect = RemoveEffect
  { refBase     :: !BaseAction
  , refLayerId  :: !NonEmptyString
  , refEffectId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data ModifyEffect = ModifyEffect
  { mefBase     :: !BaseAction
  , mefLayerId  :: !NonEmptyString
  , mefEffectId :: !NonEmptyString
  , mefParams   :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data EnableEffect = EnableEffect
  { eefBase     :: !BaseAction
  , eefLayerId  :: !NonEmptyString
  , eefEffectId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data DisableEffect = DisableEffect
  { defBase     :: !BaseAction
  , defLayerId  :: !NonEmptyString
  , defEffectId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Composition Actions
-- ────────────────────────────────────────────────────────────────────────────

data CreateComposition = CreateComposition
  { ccBase            :: !BaseAction
  , ccCompositionName :: !NonEmptyString
  , ccWidth           :: !PositiveInt
  , ccHeight          :: !PositiveInt
  , ccFps             :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

data DeleteComposition = DeleteComposition
  { dcBase          :: !BaseAction
  , dcCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data SetCompositionSettings = SetCompositionSettings
  { scsBase          :: !BaseAction
  , scsCompositionId :: !NonEmptyString
  , scsSettings      :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data RenderComposition = RenderComposition
  { rcBase          :: !BaseAction
  , rcCompositionId :: !NonEmptyString
  , rcStartFrame    :: !FrameNumber
  , rcEndFrame      :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Export Actions
-- ────────────────────────────────────────────────────────────────────────────

data StartExport = StartExport
  { seBase          :: !BaseAction
  , seCompositionId :: !NonEmptyString
  , seExportFormat  :: !ExportFormat
  , seExportTarget  :: !ExportTarget
  , seSettings      :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data CancelExport = CancelExport
  { ceBase     :: !BaseAction
  , ceExportId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data PauseExport = PauseExport
  { peBase     :: !BaseAction
  , peExportId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data ResumeExport = ResumeExport
  { resBase     :: !BaseAction
  , resExportId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data SetExportSettings = SetExportSettings
  { sesBase     :: !BaseAction
  , sesExportId :: !NonEmptyString
  , sesSettings :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Audio Actions
-- ────────────────────────────────────────────────────────────────────────────

data LoadAudio = LoadAudio
  { laBase      :: !BaseAction
  , laLayerId   :: !NonEmptyString
  , laAudioPath :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data AnalyzeAudio = AnalyzeAudio
  { aaBase    :: !BaseAction
  , aaLayerId :: !NonEmptyString
  , aaMethod  :: !BeatDetectionMethod
  } deriving stock (Eq, Show, Generic)

data SetAudioReactivity = SetAudioReactivity
  { sarBase             :: !BaseAction
  , sarLayerId          :: !NonEmptyString
  , sarEnabled          :: !Bool
  , sarReactivityParams :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Actions
-- ────────────────────────────────────────────────────────────────────────────

data SetCameraPosition = SetCameraPosition
  { scpBase     :: !BaseAction
  , scpLayerId  :: !NonEmptyString
  , scpPosition :: !Vec3
  } deriving stock (Eq, Show, Generic)

data SetCameraRotation = SetCameraRotation
  { scrBase     :: !BaseAction
  , scrLayerId  :: !NonEmptyString
  , scrRotation :: !Vec3  -- Euler angles
  } deriving stock (Eq, Show, Generic)

data SetCameraFOV = SetCameraFOV
  { scfBase    :: !BaseAction
  , scfLayerId :: !NonEmptyString
  , scfFov     :: !PositiveFloat  -- Field of view in degrees
  } deriving stock (Eq, Show, Generic)

data AnimateCamera = AnimateCamera
  { acBase      :: !BaseAction
  , acLayerId   :: !NonEmptyString
  , acKeyframes :: !Text  -- JSON-encoded camera keyframes
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                   // ai // a
-- ────────────────────────────────────────────────────────────────────────────

data SegmentImage = SegmentImage
  { sgiBase    :: !BaseAction
  , sgiLayerId :: !NonEmptyString
  , sgiMode    :: !SegmentationMode
  } deriving stock (Eq, Show, Generic)

data VectorizeImage = VectorizeImage
  { viBase    :: !BaseAction
  , viLayerId :: !NonEmptyString
  , viParams  :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data DecomposeImage = DecomposeImage
  { diBase       :: !BaseAction
  , diLayerId    :: !NonEmptyString
  , diComponents :: !Text  -- JSON-encoded component list
  } deriving stock (Eq, Show, Generic)

data GenerateDepth = GenerateDepth
  { gdBase    :: !BaseAction
  , gdLayerId :: !NonEmptyString
  , gdMethod  :: !PreprocessorType
  } deriving stock (Eq, Show, Generic)

data EstimateNormals = EstimateNormals
  { enBase    :: !BaseAction
  , enLayerId :: !NonEmptyString
  , enParams  :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- System Actions
-- ────────────────────────────────────────────────────────────────────────────

data ClearCache = ClearCache
  { clcBase      :: !BaseAction
  , clcCacheType :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data OptimizeMemory = OptimizeMemory
  { omBase           :: !BaseAction
  , omTargetMemoryMB :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

data SaveProject = SaveProject
  { spBase      :: !BaseAction
  , spProjectId :: !NonEmptyString
  , spFilePath  :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data LoadProject = LoadProject
  { lpBase     :: !BaseAction
  , lpFilePath :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data Undo = Undo
  { undoBase          :: !BaseAction
  , undoCompositionId :: !NonEmptyString
  , undoSteps         :: !FrameNumber  -- Number of steps to undo
  } deriving stock (Eq, Show, Generic)

data Redo = Redo
  { redoBase          :: !BaseAction
  , redoCompositionId :: !NonEmptyString
  , redoSteps         :: !FrameNumber  -- Number of steps to redo
  } deriving stock (Eq, Show, Generic)
