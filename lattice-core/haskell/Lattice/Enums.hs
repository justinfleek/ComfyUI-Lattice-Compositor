{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Enums
Description : Layer 1 - Enums with exhaustiveness proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Single source of truth for all enum types.
Every enum has exhaustiveness proofs (no catch-all cases).

Source: lattice-core/lean/Lattice/Enums.lean
-}

module Lattice.Enums
  ( -- * Layer Types
    LayerType(..)
    -- * Blend Modes
  , BlendMode(..)
    -- * Mask Modes
  , MaskMode(..)
    -- * Layer Status
  , LayerStatus(..)
    -- * Interpolation
  , InterpolationType(..)
  , EasingType(..)
  , KeyframeType(..)
    -- * Effects
  , EffectCategory(..)
  , EffectStatus(..)
  , EffectType(..)
    -- * Color
  , ColorSpace(..)
  , ColorFormat(..)
  , TransferFunction(..)
    -- * Export
  , ExportFormat(..)
  , ExportStatus(..)
  , ExportTarget(..)
    -- * Camera
  , CameraType(..)
  , ProjectionType(..)
  , DepthOfFieldMode(..)
    -- * Text
  , TextAlign(..)
  , TextDirection(..)
  , FontStyle(..)
  , FontWeight(..)
  , TextRangeMode(..)
  , TextRangeBasedOn(..)
  , TextRangeShape(..)
    -- * Job Status
  , JobStatus(..)
  , RenderStatus(..)
  , QualityMode(..)
    -- * Validation
  , ValidationResult(..)
  , Severity(..)
    -- * Particles
  , EmitterShape(..)
  , ParticleShape(..)
  , CollisionType(..)
    -- * Material
  , MaterialType(..)
    -- * Audio
  , AudioFormat(..)
  , AudioChannel(..)
  , BeatDetectionMethod(..)
    -- * Model
  , ModelType(..)
    -- * Preprocessing
  , PreprocessorType(..)
  , SegmentationMode(..)
    -- * System
  , AuditCategory(..)
  , RateLimitScope(..)
  , SyncStatus(..)
  , ExpressionType(..)
  ) where

import GHC.Generics (Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Types
-- ────────────────────────────────────────────────────────────────────────────

data LayerType
  = LTShape | LTText | LTImage | LTVideo | LTAudio
  | LTGroup | LTCamera | LTLight | LTParticle | LTEffect
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

data BlendMode
  = BMNormal | BMMultiply | BMScreen | BMOverlay
  | BMSoftLight | BMHardLight | BMColorDodge | BMColorBurn
  | BMDarken | BMLighten | BMDifference | BMExclusion
  | BMHue | BMSaturation | BMColor | BMLuminosity
  | BMAdd | BMSubtract | BMDivide
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Mask Modes
-- ────────────────────────────────────────────────────────────────────────────

data MaskMode = MMAdd | MMSubtract | MMIntersect | MMDifference
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Status
-- ────────────────────────────────────────────────────────────────────────────

data LayerStatus = LSActive | LSHidden | LSLocked | LSDisabled
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

data InterpolationType
  = ITLinear | ITBezier | ITHold | ITEaseIn | ITEaseOut | ITEaseInOut | ITCustom
  deriving stock (Eq, Show, Generic)

data EasingType
  = ETLinear
  | ETEaseInQuad | ETEaseOutQuad | ETEaseInOutQuad
  | ETEaseInCubic | ETEaseOutCubic | ETEaseInOutCubic
  | ETEaseInQuart | ETEaseOutQuart | ETEaseInOutQuart
  | ETEaseInQuint | ETEaseOutQuint | ETEaseInOutQuint
  | ETEaseInSine | ETEaseOutSine | ETEaseInOutSine
  | ETEaseInExpo | ETEaseOutExpo | ETEaseInOutExpo
  | ETEaseInCirc | ETEaseOutCirc | ETEaseInOutCirc
  | ETEaseInElastic | ETEaseOutElastic | ETEaseInOutElastic
  | ETEaseInBack | ETEaseOutBack | ETEaseInOutBack
  | ETEaseInBounce | ETEaseOutBounce | ETEaseInOutBounce
  deriving stock (Eq, Show, Generic)

data KeyframeType = KTLinear | KTBezier | KTHold | KTAuto
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Effects
-- ────────────────────────────────────────────────────────────────────────────

data EffectCategory
  = ECBlurSharpen | ECColorCorrection | ECDistort | ECGenerate
  | ECKeying | ECMatte | ECNoiseGrain | ECPerspective
  | ECStylize | ECTime | ECTransition | ECUtility
  deriving stock (Eq, Show, Generic)

data EffectStatus = ESActive | ESDisabled | ESBypassed
  deriving stock (Eq, Show, Generic)

data EffectType
  = EFBlur | EFSharpen | EFGlow | EFShadow | EFBevel
  | EFGradientOverlay | EFStroke | EFColorCorrection | EFDistort
  | EFKeying | EFMatte | EFNoise | EFGrain | EFMotionBlur
  | EFTimewarp | EFTransition
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Color
-- ────────────────────────────────────────────────────────────────────────────

data ColorSpace
  = CSSRGB | CSLinearSRGB | CSWideGamutRGB | CSDisplayP3
  | CSProPhotoRGB | CSACESCG | CSRec709 | CSRec2020
  deriving stock (Eq, Show, Generic)

data ColorFormat
  = CFRGB8 | CFRGB16 | CFRGBA8 | CFRGBA16
  | CFHSL | CFHSV | CFLAB | CFXYZ
  deriving stock (Eq, Show, Generic)

data TransferFunction
  = TFLinear | TFSRGB | TFGamma | TFLog | TFPQ | TFHLG
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Export
-- ────────────────────────────────────────────────────────────────────────────

data ExportFormat
  = EFMP4 | EFMOV | EFAVI | EFWebM
  | EFPNG | EFJPG | EFEXR | EFH264 | EFH265 | EFProRes
  deriving stock (Eq, Show, Generic)

data ExportStatus
  = EXQueued | EXProcessing | EXCompleted | EXFailed | EXCancelled
  deriving stock (Eq, Show, Generic)

data ExportTarget
  = ETWan22I2V | ETWan22T2V | ETWan22FunCamera | ETWan22FirstLast
  | ETUni3cCamera | ETUni3cMotion | ETMotionctrl | ETMotionctrlSvd
  | ETCogvideox | ETControlnetDepth | ETControlnetCanny
  | ETControlnetLineart | ETControlnetPose | ETAnimatediffCameractrl
  | ETCustomWorkflow | ETLightX | ETWanMove | ETATI
  | ETTTM | ETTTMWan | ETTTMCogvideox | ETTTMSvd
  | ETScail | ETCameraComfyui
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera
-- ────────────────────────────────────────────────────────────────────────────

data CameraType = CTPerspective | CTOrthographic | CTFisheye | CTSpherical
  deriving stock (Eq, Show, Generic)

data ProjectionType = PTPerspective | PTOrthographic
  deriving stock (Eq, Show, Generic)

data DepthOfFieldMode = DOFOff | DOFGaussian | DOFBokeh | DOFCustom
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Text
-- ────────────────────────────────────────────────────────────────────────────

data TextAlign = TALeft | TACenter | TARight | TAJustify
  deriving stock (Eq, Show, Generic)

data TextDirection = TDLTR | TDRTL
  deriving stock (Eq, Show, Generic)

data FontStyle = FSNormal | FSItalic | FSOblique
  deriving stock (Eq, Show, Generic)

data FontWeight
  = FWThin | FWExtraLight | FWLight | FWRegular | FWMedium
  | FWSemiBold | FWBold | FWExtraBold | FWBlack
  deriving stock (Eq, Show, Generic)

data TextRangeMode = TRMPercent | TRMIndex
  deriving stock (Eq, Show, Generic)

data TextRangeBasedOn
  = TRBCharacters | TRBCharactersExcludingSpaces | TRBWords | TRBLines
  deriving stock (Eq, Show, Generic)

data TextRangeShape
  = TRSSquare | TRSRampUp | TRSRampDown | TRSTriangle | TRSRound | TRSSmooth
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Job Status
-- ────────────────────────────────────────────────────────────────────────────

data JobStatus = JSQueued | JSRunning | JSCompleted | JSFailed | JSCancelled
  deriving stock (Eq, Show, Generic)

data RenderStatus = RSIdle | RSRendering | RSPaused | RSCompleted | RSFailed
  deriving stock (Eq, Show, Generic)

data QualityMode = QMLow | QMMedium | QMHigh | QMUltra
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

data ValidationResult = VRValid | VRInvalid | VRWarning
  deriving stock (Eq, Show, Generic)

data Severity = SVDebug | SVInfo | SVWarning | SVError | SVCritical
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Particles
-- ────────────────────────────────────────────────────────────────────────────

data EmitterShape
  = ESPoint | ESLine | ESCircle | ESBox | ESSphere | ESRing
  | ESSpline | ESDepthMap | ESMask | ESCone | ESImage | ESDepthEdge | ESMesh
  deriving stock (Eq, Show, Generic)

data ParticleShape
  = PSPoint | PSCircle | PSSquare | PSTriangle | PSStar | PSCustom
  deriving stock (Eq, Show, Generic)

data CollisionType = CLNone | CLBoundingBox | CLPrecise | CLTrigger
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Material
-- ────────────────────────────────────────────────────────────────────────────

data MaterialType
  = MTStandard | MTPhysical | MTToon | MTEmissive | MTTransparent | MTCustom
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Audio
-- ────────────────────────────────────────────────────────────────────────────

data AudioFormat = AFMP3 | AFWav | AFOgg | AFAac | AFFlac | AFM4a
  deriving stock (Eq, Show, Generic)

data AudioChannel = ACMono | ACStereo | ACQuad | ACSurround51 | ACSurround71
  deriving stock (Eq, Show, Generic)

data BeatDetectionMethod = BDEnergy | BDOnset | BDSpectral | BDTempo | BDCustom
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Model
-- ────────────────────────────────────────────────────────────────────────────

data ModelType = MTMesh | MTPointCloud | MTVolume | MTProcedural
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Preprocessing
-- ────────────────────────────────────────────────────────────────────────────

data PreprocessorType
  = PPDepth | PPNormal | PPPose | PPEdge | PPLineart
  | PPScribble | PPSegmentation | PPVideo | PPOther
  deriving stock (Eq, Show, Generic)

data SegmentationMode = SMSemantic | SMInstance | SMPanoptic | SMCustom
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- System
-- ────────────────────────────────────────────────────────────────────────────

data AuditCategory
  = ACSecurity | ACPerformance | ACError | ACAccess | ACModification | ACSystem
  deriving stock (Eq, Show, Generic)

data RateLimitScope = RLGlobal | RLUser | RLIP | RLEndpoint | RLCustom
  deriving stock (Eq, Show, Generic)

data SyncStatus = SSSynced | SSSyncing | SSPending | SSFailed | SSConflict
  deriving stock (Eq, Show, Generic)

data ExpressionType = EXPreset | EXCustom
  deriving stock (Eq, Show, Generic)
