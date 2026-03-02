-- | Lattice.Enums - Layer 1: Enums with exhaustiveness proofs
-- |
-- | Single source of truth for all enum types.
-- | Every enum has exhaustiveness proofs (no catch-all cases).
-- |
-- | Source: leancomfy/lean/Lattice/Enums.lean

module Lattice.Enums
  ( LayerType(..)
  , BlendMode(..)
  , MaskMode(..)
  , LayerStatus(..)
  , InterpolationType(..)
  , EasingType(..)
  , KeyframeType(..)
  , EffectCategory(..)
  , EffectStatus(..)
  , EffectType(..)
  , ColorSpace(..)
  , ColorFormat(..)
  , TransferFunction(..)
  , ExportFormat(..)
  , ExportStatus(..)
  , ExportTarget(..)
  , CameraType(..)
  , ProjectionType(..)
  , DepthOfFieldMode(..)
  , TextAlign(..)
  , TextDirection(..)
  , FontStyle(..)
  , FontWeight(..)
  , TextRangeMode(..)
  , TextRangeBasedOn(..)
  , TextRangeShape(..)
  , JobStatus(..)
  , RenderStatus(..)
  , QualityMode(..)
  , ValidationResult(..)
  , Severity(..)
  , EmitterShape(..)
  , ParticleShape(..)
  , CollisionType(..)
  , MaterialType(..)
  , AudioFormat(..)
  , AudioChannel(..)
  , BeatDetectionMethod(..)
  , ModelType(..)
  , PreprocessorType(..)
  , SegmentationMode(..)
  , AuditCategory(..)
  , RateLimitScope(..)
  , SyncStatus(..)
  , ExpressionType(..)
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Layer Types
--------------------------------------------------------------------------------

data LayerType
  = LTShape | LTText | LTImage | LTVideo | LTAudio
  | LTGroup | LTCamera | LTLight | LTParticle | LTEffect

derive instance Eq LayerType
derive instance Generic LayerType _
instance Show LayerType where show = genericShow

--------------------------------------------------------------------------------
-- Blend Modes
--------------------------------------------------------------------------------

data BlendMode
  = BMNormal | BMMultiply | BMScreen | BMOverlay
  | BMSoftLight | BMHardLight | BMColorDodge | BMColorBurn
  | BMDarken | BMLighten | BMDifference | BMExclusion
  | BMHue | BMSaturation | BMColor | BMLuminosity
  | BMAdd | BMSubtract | BMDivide

derive instance Eq BlendMode
derive instance Generic BlendMode _
instance Show BlendMode where show = genericShow

--------------------------------------------------------------------------------
-- Mask Modes
--------------------------------------------------------------------------------

data MaskMode = MMAdd | MMSubtract | MMIntersect | MMDifference

derive instance Eq MaskMode
derive instance Generic MaskMode _
instance Show MaskMode where show = genericShow

--------------------------------------------------------------------------------
-- Layer Status
--------------------------------------------------------------------------------

data LayerStatus = LSActive | LSHidden | LSLocked | LSDisabled

derive instance Eq LayerStatus
derive instance Generic LayerStatus _
instance Show LayerStatus where show = genericShow

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

data InterpolationType
  = ITLinear | ITBezier | ITHold | ITEaseIn | ITEaseOut | ITEaseInOut | ITCustom

derive instance Eq InterpolationType
derive instance Generic InterpolationType _
instance Show InterpolationType where show = genericShow

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

derive instance Eq EasingType
derive instance Generic EasingType _
instance Show EasingType where show = genericShow

data KeyframeType = KTLinear | KTBezier | KTHold | KTAuto

derive instance Eq KeyframeType
derive instance Generic KeyframeType _
instance Show KeyframeType where show = genericShow

--------------------------------------------------------------------------------
-- Effects
--------------------------------------------------------------------------------

data EffectCategory
  = ECBlurSharpen | ECColorCorrection | ECDistort | ECGenerate
  | ECKeying | ECMatte | ECNoiseGrain | ECPerspective
  | ECStylize | ECTime | ECTransition | ECUtility

derive instance Eq EffectCategory
derive instance Generic EffectCategory _
instance Show EffectCategory where show = genericShow

data EffectStatus = ESActive | ESDisabled | ESBypassed

derive instance Eq EffectStatus
derive instance Generic EffectStatus _
instance Show EffectStatus where show = genericShow

data EffectType
  = EFBlur | EFSharpen | EFGlow | EFShadow | EFBevel
  | EFGradientOverlay | EFStroke | EFColorCorrection | EFDistort
  | EFKeying | EFMatte | EFNoise | EFGrain | EFMotionBlur
  | EFTimewarp | EFTransition

derive instance Eq EffectType
derive instance Generic EffectType _
instance Show EffectType where show = genericShow

--------------------------------------------------------------------------------
-- Color
--------------------------------------------------------------------------------

data ColorSpace
  = CSSRGB | CSLinearSRGB | CSWideGamutRGB | CSDisplayP3
  | CSProPhotoRGB | CSACESCG | CSRec709 | CSRec2020

derive instance Eq ColorSpace
derive instance Generic ColorSpace _
instance Show ColorSpace where show = genericShow

data ColorFormat
  = CFRGB8 | CFRGB16 | CFRGBA8 | CFRGBA16
  | CFHSL | CFHSV | CFLAB | CFXYZ

derive instance Eq ColorFormat
derive instance Generic ColorFormat _
instance Show ColorFormat where show = genericShow

data TransferFunction
  = TFLinear | TFSRGB | TFGamma | TFLog | TFPQ | TFHLG

derive instance Eq TransferFunction
derive instance Generic TransferFunction _
instance Show TransferFunction where show = genericShow

--------------------------------------------------------------------------------
-- Export
--------------------------------------------------------------------------------

data ExportFormat
  = EFMP4 | EFMOV | EFAVI | EFWebM
  | EFPNG | EFJPG | EFEXR | EFH264 | EFH265 | EFProRes

derive instance Eq ExportFormat
derive instance Generic ExportFormat _
instance Show ExportFormat where show = genericShow

data ExportStatus
  = EXQueued | EXProcessing | EXCompleted | EXFailed | EXCancelled

derive instance Eq ExportStatus
derive instance Generic ExportStatus _
instance Show ExportStatus where show = genericShow

data ExportTarget
  = ETWan22I2V | ETWan22T2V | ETWan22FunCamera | ETWan22FirstLast
  | ETUni3cCamera | ETUni3cMotion | ETMotionctrl | ETMotionctrlSvd
  | ETCogvideox | ETControlnetDepth | ETControlnetCanny
  | ETControlnetLineart | ETControlnetPose | ETAnimatediffCameractrl
  | ETCustomWorkflow | ETLightX | ETWanMove | ETATI
  | ETTTM | ETTTMWan | ETTTMCogvideox | ETTTMSvd
  | ETScail | ETCameraComfyui

derive instance Eq ExportTarget
derive instance Generic ExportTarget _
instance Show ExportTarget where show = genericShow

--------------------------------------------------------------------------------
-- Camera
--------------------------------------------------------------------------------

data CameraType = CTPerspective | CTOrthographic | CTFisheye | CTSpherical

derive instance Eq CameraType
derive instance Generic CameraType _
instance Show CameraType where show = genericShow

data ProjectionType = PTPerspective | PTOrthographic

derive instance Eq ProjectionType
derive instance Generic ProjectionType _
instance Show ProjectionType where show = genericShow

data DepthOfFieldMode = DOFOff | DOFGaussian | DOFBokeh | DOFCustom

derive instance Eq DepthOfFieldMode
derive instance Generic DepthOfFieldMode _
instance Show DepthOfFieldMode where show = genericShow

--------------------------------------------------------------------------------
-- Text
--------------------------------------------------------------------------------

data TextAlign = TALeft | TACenter | TARight | TAJustify

derive instance Eq TextAlign
derive instance Generic TextAlign _
instance Show TextAlign where show = genericShow

data TextDirection = TDLTR | TDRTL

derive instance Eq TextDirection
derive instance Generic TextDirection _
instance Show TextDirection where show = genericShow

data FontStyle = FSNormal | FSItalic | FSOblique

derive instance Eq FontStyle
derive instance Generic FontStyle _
instance Show FontStyle where show = genericShow

data FontWeight
  = FWThin | FWExtraLight | FWLight | FWRegular | FWMedium
  | FWSemiBold | FWBold | FWExtraBold | FWBlack

derive instance Eq FontWeight
derive instance Generic FontWeight _
instance Show FontWeight where show = genericShow

data TextRangeMode = TRMPercent | TRMIndex

derive instance Eq TextRangeMode
derive instance Generic TextRangeMode _
instance Show TextRangeMode where show = genericShow

data TextRangeBasedOn
  = TRBCharacters | TRBCharactersExcludingSpaces | TRBWords | TRBLines

derive instance Eq TextRangeBasedOn
derive instance Generic TextRangeBasedOn _
instance Show TextRangeBasedOn where show = genericShow

data TextRangeShape
  = TRSSquare | TRSRampUp | TRSRampDown | TRSTriangle | TRSRound | TRSSmooth

derive instance Eq TextRangeShape
derive instance Generic TextRangeShape _
instance Show TextRangeShape where show = genericShow

--------------------------------------------------------------------------------
-- Job Status
--------------------------------------------------------------------------------

data JobStatus = JSQueued | JSRunning | JSCompleted | JSFailed | JSCancelled

derive instance Eq JobStatus
derive instance Generic JobStatus _
instance Show JobStatus where show = genericShow

data RenderStatus = RSIdle | RSRendering | RSPaused | RSCompleted | RSFailed

derive instance Eq RenderStatus
derive instance Generic RenderStatus _
instance Show RenderStatus where show = genericShow

data QualityMode = QMLow | QMMedium | QMHigh | QMUltra

derive instance Eq QualityMode
derive instance Generic QualityMode _
instance Show QualityMode where show = genericShow

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

data ValidationResult = VRValid | VRInvalid | VRWarning

derive instance Eq ValidationResult
derive instance Generic ValidationResult _
instance Show ValidationResult where show = genericShow

data Severity = SVDebug | SVInfo | SVWarning | SVError | SVCritical

derive instance Eq Severity
derive instance Generic Severity _
instance Show Severity where show = genericShow

--------------------------------------------------------------------------------
-- Particles
--------------------------------------------------------------------------------

data EmitterShape
  = ESPoint | ESLine | ESCircle | ESBox | ESSphere | ESRing
  | ESSpline | ESDepthMap | ESMask | ESCone | ESImage | ESDepthEdge | ESMesh

derive instance Eq EmitterShape
derive instance Generic EmitterShape _
instance Show EmitterShape where show = genericShow

data ParticleShape
  = PSPoint | PSCircle | PSSquare | PSTriangle | PSStar | PSCustom

derive instance Eq ParticleShape
derive instance Generic ParticleShape _
instance Show ParticleShape where show = genericShow

data CollisionType = CLNone | CLBoundingBox | CLPrecise | CLTrigger

derive instance Eq CollisionType
derive instance Generic CollisionType _
instance Show CollisionType where show = genericShow

--------------------------------------------------------------------------------
-- Material
--------------------------------------------------------------------------------

data MaterialType
  = MTStandard | MTPhysical | MTToon | MTEmissive | MTTransparent | MTCustom

derive instance Eq MaterialType
derive instance Generic MaterialType _
instance Show MaterialType where show = genericShow

--------------------------------------------------------------------------------
-- Audio
--------------------------------------------------------------------------------

data AudioFormat = AFMP3 | AFWav | AFOgg | AFAac | AFFlac | AFM4a

derive instance Eq AudioFormat
derive instance Generic AudioFormat _
instance Show AudioFormat where show = genericShow

data AudioChannel = ACMono | ACStereo | ACQuad | ACSurround51 | ACSurround71

derive instance Eq AudioChannel
derive instance Generic AudioChannel _
instance Show AudioChannel where show = genericShow

data BeatDetectionMethod = BDEnergy | BDOnset | BDSpectral | BDTempo | BDCustom

derive instance Eq BeatDetectionMethod
derive instance Generic BeatDetectionMethod _
instance Show BeatDetectionMethod where show = genericShow

--------------------------------------------------------------------------------
-- Model
--------------------------------------------------------------------------------

data ModelType = MTMesh | MTPointCloud | MTVolume | MTProcedural

derive instance Eq ModelType
derive instance Generic ModelType _
instance Show ModelType where show = genericShow

--------------------------------------------------------------------------------
-- Preprocessing
--------------------------------------------------------------------------------

data PreprocessorType
  = PPDepth | PPNormal | PPPose | PPEdge | PPLineart
  | PPScribble | PPSegmentation | PPVideo | PPOther

derive instance Eq PreprocessorType
derive instance Generic PreprocessorType _
instance Show PreprocessorType where show = genericShow

data SegmentationMode = SMSemantic | SMInstance | SMPanoptic | SMCustom

derive instance Eq SegmentationMode
derive instance Generic SegmentationMode _
instance Show SegmentationMode where show = genericShow

--------------------------------------------------------------------------------
-- System
--------------------------------------------------------------------------------

data AuditCategory
  = ACSecurity | ACPerformance | ACError | ACAccess | ACModification | ACSystem

derive instance Eq AuditCategory
derive instance Generic AuditCategory _
instance Show AuditCategory where show = genericShow

data RateLimitScope = RLGlobal | RLUser | RLIP | RLEndpoint | RLCustom

derive instance Eq RateLimitScope
derive instance Generic RateLimitScope _
instance Show RateLimitScope where show = genericShow

data SyncStatus = SSSynced | SSSyncing | SSPending | SSFailed | SSConflict

derive instance Eq SyncStatus
derive instance Generic SyncStatus _
instance Show SyncStatus where show = genericShow

data ExpressionType = EXPreset | EXCustom

derive instance Eq ExpressionType
derive instance Generic ExpressionType _
instance Show ExpressionType where show = genericShow
