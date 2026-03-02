{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Effects
Description : Effect types, enums, and parameters
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/Effects/
Consolidates: Enums, Parameters, Core
-}

module Lattice.Effects
  ( -- * Effect Parameter Type
    EffectParameterType(..)
  , EffectAnimatableType(..)
    -- * Blur Enums
  , BlurDimension(..)
  , RadialBlurType(..)
  , AntialiasingQuality(..)
    -- * Distortion Enums
  , RampShape(..)
  , WarpStyle(..)
  , DisplacementMapType(..)
  , DisplacementChannel(..)
  , EdgeBehavior(..)
    -- * Glow Enums
  , GlowCompositeMode(..)
  , GlowColorsMode(..)
  , ColorLooping(..)
  , FalloffMode(..)
  , TonemapMode(..)
  , BloomBlendMode(..)
    -- * Noise Enums
  , FractalType(..)
  , NoiseType(..)
    -- * Time Enums
  , EchoOperator(..)
  , TimeResolution(..)
    -- * Mesh Enums
  , PinFalloff(..)
  , TurbulentDisplaceType(..)
  , PinningMode(..)
    -- * Stylize Enums
  , ScanlinesDirection(..)
  , RGBSplitBlendMode(..)
  , PixelSortDirection(..)
  , SortByCriterion(..)
  , HalftoneColorMode(..)
  , DitherMethod(..)
  , DitherMatrixSize(..)
  , EffectColorChannel(..)
  , HSLChannel(..)
    -- * Parameter Types
  , EffectPoint2D(..)
  , EffectPoint3D(..)
  , EffectRGBA(..)
  , CurvePoint(..)
  , EffectParameterValue(..)
  , EffectDropdownOption(..)
  , EffectParameterDef(..)
  , EffectParameter(..)
    -- * Effect Types
  , Effect(..)
  , EffectInstance(..)
  , MeshDeformEffectInstance(..)
  , EffectDefinition(..)
  , EffectCategoryInfo(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives
import Lattice.Enums
import Lattice.MeshWarp

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Parameter Type
-- ────────────────────────────────────────────────────────────────────────────

data EffectParameterType
  = EPTNumber | EPTColor | EPTPoint | EPTPoint3D | EPTAngle
  | EPTCheckbox | EPTDropdown | EPTLayer | EPTString | EPTCurve | EPTData
  deriving stock (Eq, Show, Generic)

data EffectAnimatableType
  = EATNumber | EATPosition | EATColor | EATEnum | EATVector3
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Blur Enums
-- ────────────────────────────────────────────────────────────────────────────

data BlurDimension = BDHorizontal | BDVertical | BDBoth
  deriving stock (Eq, Show, Generic)

data RadialBlurType = RBTSpin | RBTZoom
  deriving stock (Eq, Show, Generic)

data AntialiasingQuality = AAQLow | AAQMedium | AAQHigh
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Distortion Enums
-- ────────────────────────────────────────────────────────────────────────────

data RampShape = RSLinear | RSRadial
  deriving stock (Eq, Show, Generic)

data WarpStyle
  = WSArc | WSArcLower | WSArcUpper | WSArch | WSBulge
  | WSShellLower | WSShellUpper | WSFlag | WSWave | WSFish
  | WSRise | WSFisheye | WSInflate | WSSqueeze | WSTwist
  deriving stock (Eq, Show, Generic)

data DisplacementMapType
  = DMTLayer | DMTNoise | DMTGradientH | DMTGradientV
  | DMTRadial | DMTSineH | DMTSineV | DMTChecker
  deriving stock (Eq, Show, Generic)

data DisplacementChannel
  = DCRed | DCGreen | DCBlue | DCAlpha | DCLuminance | DCOff
  deriving stock (Eq, Show, Generic)

data EdgeBehavior = EBOff | EBTiles | EBMirror
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Glow Enums
-- ────────────────────────────────────────────────────────────────────────────

data GlowCompositeMode = GCMOnTop | GCMBehind | GCMNone
  deriving stock (Eq, Show, Generic)

data GlowColorsMode = GCMOriginal | GCMAB
  deriving stock (Eq, Show, Generic)

data ColorLooping = CLNone | CLSawtoothAB | CLSawtoothBA | CLTriangle
  deriving stock (Eq, Show, Generic)

data FalloffMode = FMInverseSquare | FMGaussian | FMExponential
  deriving stock (Eq, Show, Generic)

data TonemapMode = TMNone | TMACES | TMReinhard | TMHable
  deriving stock (Eq, Show, Generic)

data BloomBlendMode = BBMAdd | BBMScreen | BBMOverlay | BBMSoftLight
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Noise Enums
-- ────────────────────────────────────────────────────────────────────────────

data FractalType = FTBasic | FTTurbulentBasic | FTSoftLinear | FTTurbulentSoft
  deriving stock (Eq, Show, Generic)

data NoiseType = NTBlock | NTLinear | NTSoftLinear | NTSpline
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Time Enums
-- ────────────────────────────────────────────────────────────────────────────

data EchoOperator
  = EOAdd | EOScreen | EOMaximum | EOMinimum
  | EOCompositeBack | EOCompositeFront | EOBlend
  deriving stock (Eq, Show, Generic)

data TimeResolution = TRFrame | TRHalf | TRQuarter
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Mesh Enums
-- ────────────────────────────────────────────────────────────────────────────

data PinFalloff = PFInverseDistance | PFRadialBasis
  deriving stock (Eq, Show, Generic)

data TurbulentDisplaceType
  = TDTTurbulent | TDTBulge | TDTTwist | TDTTurbulentSmoother
  | TDTHorizontal | TDTVertical | TDTCross
  deriving stock (Eq, Show, Generic)

data PinningMode = PMNone | PMAll | PMHorizontal | PMVertical
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Stylize Enums
-- ────────────────────────────────────────────────────────────────────────────

data ScanlinesDirection = SDHorizontal | SDVertical
  deriving stock (Eq, Show, Generic)

data RGBSplitBlendMode = RSBMScreen | RSBMAdd | RSBMNormal
  deriving stock (Eq, Show, Generic)

data PixelSortDirection = PSDHorizontal | PSDVertical
  deriving stock (Eq, Show, Generic)

data SortByCriterion = SBCSaturation | SBCBrightness | SBCHue
  deriving stock (Eq, Show, Generic)

data HalftoneColorMode = HCMGrayscale | HCMRGB | HCMCMYK
  deriving stock (Eq, Show, Generic)

data DitherMethod = DMOrdered | DMFloydSteinberg | DMAtkinson
  deriving stock (Eq, Show, Generic)

data DitherMatrixSize = DMS2x2 | DMS4x4 | DMS8x8
  deriving stock (Eq, Show, Generic)

data EffectColorChannel = ECCRGB | ECCRed | ECCGreen | ECCBlue | ECCAlpha
  deriving stock (Eq, Show, Generic)

data HSLChannel
  = HSLMaster | HSLReds | HSLYellows | HSLGreens
  | HSLCyans | HSLBlues | HSLMagentas
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Parameter Types
-- ────────────────────────────────────────────────────────────────────────────

data EffectPoint2D = EffectPoint2D
  { ep2dX :: !FiniteFloat
  , ep2dY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data EffectPoint3D = EffectPoint3D
  { ep3dX :: !FiniteFloat
  , ep3dY :: !FiniteFloat
  , ep3dZ :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data EffectRGBA = EffectRGBA
  { ergbaR :: !Int  -- 0-255
  , ergbaG :: !Int  -- 0-255
  , ergbaB :: !Int  -- 0-255
  , ergbaA :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

data CurvePoint = CurvePoint
  { cpX :: !FiniteFloat
  , cpY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data EffectParameterValue
  = EPVNumber !FiniteFloat
  | EPVString !Text
  | EPVBoolean !Bool
  | EPVPoint2D !EffectPoint2D
  | EPVPoint3D !EffectPoint3D
  | EPVColor !EffectRGBA
  | EPVCurve !(Vector CurvePoint)
  | EPVData !Text  -- JSON-encoded
  | EPVNull
  deriving stock (Eq, Show, Generic)

data EffectDropdownOption = EffectDropdownOption
  { edoLabel :: !NonEmptyString
  , edoValue :: !EffectParameterValue
  } deriving stock (Eq, Show, Generic)

data EffectParameterDef = EffectParameterDef
  { epdName          :: !NonEmptyString
  , epdParameterType :: !EffectParameterType
  , epdDefaultValue  :: !EffectParameterValue
  , epdMin           :: !(Maybe FiniteFloat)
  , epdMax           :: !(Maybe FiniteFloat)
  , epdStep          :: !(Maybe PositiveFloat)
  , epdOptions       :: !(Maybe (Vector EffectDropdownOption))
  , epdAnimatable    :: !Bool
  , epdGroup         :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data EffectParameter = EffectParameter
  { epId            :: !NonEmptyString
  , epName          :: !NonEmptyString
  , epParameterType :: !EffectParameterType
  , epValue         :: !EffectParameterValue
  , epDefaultValue  :: !EffectParameterValue
  , epMin           :: !(Maybe FiniteFloat)
  , epMax           :: !(Maybe FiniteFloat)
  , epStep          :: !(Maybe PositiveFloat)
  , epOptions       :: !(Maybe (Vector EffectDropdownOption))
  , epAnimatable    :: !Bool
  , epGroup         :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Types
-- ────────────────────────────────────────────────────────────────────────────

data Effect = Effect
  { efId             :: !NonEmptyString
  , efName           :: !NonEmptyString
  , efCategory       :: !EffectCategory
  , efEnabled        :: !Bool
  , efExpanded       :: !Bool
  , efParameters     :: !(Vector EffectParameter)
  , efFragmentShader :: !(Maybe Text)
  } deriving stock (Eq, Show, Generic)

data EffectInstance = EffectInstance
  { eiId         :: !NonEmptyString
  , eiEffectKey  :: !NonEmptyString
  , eiName       :: !NonEmptyString
  , eiCategory   :: !EffectCategory
  , eiEnabled    :: !Bool
  , eiExpanded   :: !Bool
  , eiParameters :: !(Vector NonEmptyString)  -- AnimatableProperty IDs
  } deriving stock (Eq, Show, Generic)

data MeshDeformEffectInstance = MeshDeformEffectInstance
  { mdeiInstance     :: !EffectInstance
  , mdeiPins         :: !(Vector WarpPin)
  , mdeiCachedMeshId :: !(Maybe NonEmptyString)
  , mdeiMeshDirty    :: !Bool
  } deriving stock (Eq, Show, Generic)

data EffectDefinition = EffectDefinition
  { edName           :: !NonEmptyString
  , edCategory       :: !EffectCategory
  , edDescription    :: !Text
  , edParameters     :: !(Vector EffectParameterDef)
  , edFragmentShader :: !(Maybe Text)
  } deriving stock (Eq, Show, Generic)

data EffectCategoryInfo = EffectCategoryInfo
  { eciLabel       :: !NonEmptyString
  , eciIcon        :: !Text
  , eciDescription :: !Text
  } deriving stock (Eq, Show, Generic)
