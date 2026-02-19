-- | Lattice.Effects - Effect types, enums, and parameters
-- |
-- | Source: lattice-core/lean/Lattice/Effects/
-- | Consolidates: Enums, Parameters, Core

module Lattice.Effects
  ( EffectParameterType(..)
  , EffectAnimatableType(..)
  , BlurDimension(..)
  , RadialBlurType(..)
  , AntialiasingQuality(..)
  , RampShape(..)
  , WarpStyle(..)
  , DisplacementMapType(..)
  , DisplacementChannel(..)
  , EdgeBehavior(..)
  , GlowCompositeMode(..)
  , GlowColorsMode(..)
  , ColorLooping(..)
  , FalloffMode(..)
  , TonemapMode(..)
  , BloomBlendMode(..)
  , FractalType(..)
  , NoiseType(..)
  , EchoOperator(..)
  , TimeResolution(..)
  , PinFalloff(..)
  , TurbulentDisplaceType(..)
  , PinningMode(..)
  , ScanlinesDirection(..)
  , RGBSplitBlendMode(..)
  , PixelSortDirection(..)
  , SortByCriterion(..)
  , HalftoneColorMode(..)
  , DitherMethod(..)
  , DitherMatrixSize(..)
  , EffectColorChannel(..)
  , HSLChannel(..)
  , EffectPoint2D
  , EffectPoint3D
  , EffectRGBA
  , CurvePoint
  , EffectParameterValue(..)
  , EffectDropdownOption
  , EffectParameterDef
  , EffectParameter
  , Effect
  , EffectInstance
  , MeshDeformEffectInstance
  , EffectDefinition
  , EffectCategoryInfo
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Enums
import Lattice.MeshWarp

--------------------------------------------------------------------------------
-- Effect Parameter Type
--------------------------------------------------------------------------------

data EffectParameterType
  = EPTNumber | EPTColor | EPTPoint | EPTPoint3D | EPTAngle
  | EPTCheckbox | EPTDropdown | EPTLayer | EPTString | EPTCurve | EPTData

derive instance Eq EffectParameterType
derive instance Generic EffectParameterType _
instance Show EffectParameterType where show = genericShow

data EffectAnimatableType
  = EATNumber | EATPosition | EATColor | EATEnum | EATVector3

derive instance Eq EffectAnimatableType
derive instance Generic EffectAnimatableType _
instance Show EffectAnimatableType where show = genericShow

--------------------------------------------------------------------------------
-- Blur Enums
--------------------------------------------------------------------------------

data BlurDimension = BDHorizontal | BDVertical | BDBoth

derive instance Eq BlurDimension
derive instance Generic BlurDimension _
instance Show BlurDimension where show = genericShow

data RadialBlurType = RBTSpin | RBTZoom

derive instance Eq RadialBlurType
derive instance Generic RadialBlurType _
instance Show RadialBlurType where show = genericShow

data AntialiasingQuality = AAQLow | AAQMedium | AAQHigh

derive instance Eq AntialiasingQuality
derive instance Generic AntialiasingQuality _
instance Show AntialiasingQuality where show = genericShow

--------------------------------------------------------------------------------
-- Distortion Enums
--------------------------------------------------------------------------------

data RampShape = RSLinear | RSRadial

derive instance Eq RampShape
derive instance Generic RampShape _
instance Show RampShape where show = genericShow

data WarpStyle
  = WSArc | WSArcLower | WSArcUpper | WSArch | WSBulge
  | WSShellLower | WSShellUpper | WSFlag | WSWave | WSFish
  | WSRise | WSFisheye | WSInflate | WSSqueeze | WSTwist

derive instance Eq WarpStyle
derive instance Generic WarpStyle _
instance Show WarpStyle where show = genericShow

data DisplacementMapType
  = DMTLayer | DMTNoise | DMTGradientH | DMTGradientV
  | DMTRadial | DMTSineH | DMTSineV | DMTChecker

derive instance Eq DisplacementMapType
derive instance Generic DisplacementMapType _
instance Show DisplacementMapType where show = genericShow

data DisplacementChannel
  = DCRed | DCGreen | DCBlue | DCAlpha | DCLuminance | DCOff

derive instance Eq DisplacementChannel
derive instance Generic DisplacementChannel _
instance Show DisplacementChannel where show = genericShow

data EdgeBehavior = EBOff | EBTiles | EBMirror

derive instance Eq EdgeBehavior
derive instance Generic EdgeBehavior _
instance Show EdgeBehavior where show = genericShow

--------------------------------------------------------------------------------
-- Glow Enums
--------------------------------------------------------------------------------

data GlowCompositeMode = GCMOnTop | GCMBehind | GCMNone

derive instance Eq GlowCompositeMode
derive instance Generic GlowCompositeMode _
instance Show GlowCompositeMode where show = genericShow

data GlowColorsMode = GCMOriginal | GCMAB

derive instance Eq GlowColorsMode
derive instance Generic GlowColorsMode _
instance Show GlowColorsMode where show = genericShow

data ColorLooping = CLNone | CLSawtoothAB | CLSawtoothBA | CLTriangle

derive instance Eq ColorLooping
derive instance Generic ColorLooping _
instance Show ColorLooping where show = genericShow

data FalloffMode = FMInverseSquare | FMGaussian | FMExponential

derive instance Eq FalloffMode
derive instance Generic FalloffMode _
instance Show FalloffMode where show = genericShow

data TonemapMode = TMNone | TMACES | TMReinhard | TMHable

derive instance Eq TonemapMode
derive instance Generic TonemapMode _
instance Show TonemapMode where show = genericShow

data BloomBlendMode = BBMAdd | BBMScreen | BBMOverlay | BBMSoftLight

derive instance Eq BloomBlendMode
derive instance Generic BloomBlendMode _
instance Show BloomBlendMode where show = genericShow

--------------------------------------------------------------------------------
-- Noise Enums
--------------------------------------------------------------------------------

data FractalType = FTBasic | FTTurbulentBasic | FTSoftLinear | FTTurbulentSoft

derive instance Eq FractalType
derive instance Generic FractalType _
instance Show FractalType where show = genericShow

data NoiseType = NTBlock | NTLinear | NTSoftLinear | NTSpline

derive instance Eq NoiseType
derive instance Generic NoiseType _
instance Show NoiseType where show = genericShow

--------------------------------------------------------------------------------
-- Time Enums
--------------------------------------------------------------------------------

data EchoOperator
  = EOAdd | EOScreen | EOMaximum | EOMinimum
  | EOCompositeBack | EOCompositeFront | EOBlend

derive instance Eq EchoOperator
derive instance Generic EchoOperator _
instance Show EchoOperator where show = genericShow

data TimeResolution = TRFrame | TRHalf | TRQuarter

derive instance Eq TimeResolution
derive instance Generic TimeResolution _
instance Show TimeResolution where show = genericShow

--------------------------------------------------------------------------------
-- Mesh Enums
--------------------------------------------------------------------------------

data PinFalloff = PFInverseDistance | PFRadialBasis

derive instance Eq PinFalloff
derive instance Generic PinFalloff _
instance Show PinFalloff where show = genericShow

data TurbulentDisplaceType
  = TDTTurbulent | TDTBulge | TDTTwist | TDTTurbulentSmoother
  | TDTHorizontal | TDTVertical | TDTCross

derive instance Eq TurbulentDisplaceType
derive instance Generic TurbulentDisplaceType _
instance Show TurbulentDisplaceType where show = genericShow

data PinningMode = PMNone | PMAll | PMHorizontal | PMVertical

derive instance Eq PinningMode
derive instance Generic PinningMode _
instance Show PinningMode where show = genericShow

--------------------------------------------------------------------------------
-- Stylize Enums
--------------------------------------------------------------------------------

data ScanlinesDirection = SDHorizontal | SDVertical

derive instance Eq ScanlinesDirection
derive instance Generic ScanlinesDirection _
instance Show ScanlinesDirection where show = genericShow

data RGBSplitBlendMode = RSBMScreen | RSBMAdd | RSBMNormal

derive instance Eq RGBSplitBlendMode
derive instance Generic RGBSplitBlendMode _
instance Show RGBSplitBlendMode where show = genericShow

data PixelSortDirection = PSDHorizontal | PSDVertical

derive instance Eq PixelSortDirection
derive instance Generic PixelSortDirection _
instance Show PixelSortDirection where show = genericShow

data SortByCriterion = SBCSaturation | SBCBrightness | SBCHue

derive instance Eq SortByCriterion
derive instance Generic SortByCriterion _
instance Show SortByCriterion where show = genericShow

data HalftoneColorMode = HCMGrayscale | HCMRGB | HCMCMYK

derive instance Eq HalftoneColorMode
derive instance Generic HalftoneColorMode _
instance Show HalftoneColorMode where show = genericShow

data DitherMethod = DMOrdered | DMFloydSteinberg | DMAtkinson

derive instance Eq DitherMethod
derive instance Generic DitherMethod _
instance Show DitherMethod where show = genericShow

data DitherMatrixSize = DMS2x2 | DMS4x4 | DMS8x8

derive instance Eq DitherMatrixSize
derive instance Generic DitherMatrixSize _
instance Show DitherMatrixSize where show = genericShow

data EffectColorChannel = ECCRGB | ECCRed | ECCGreen | ECCBlue | ECCAlpha

derive instance Eq EffectColorChannel
derive instance Generic EffectColorChannel _
instance Show EffectColorChannel where show = genericShow

data HSLChannel
  = HSLMaster | HSLReds | HSLYellows | HSLGreens
  | HSLCyans | HSLBlues | HSLMagentas

derive instance Eq HSLChannel
derive instance Generic HSLChannel _
instance Show HSLChannel where show = genericShow

--------------------------------------------------------------------------------
-- Parameter Types
--------------------------------------------------------------------------------

type EffectPoint2D =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

type EffectPoint3D =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

type EffectRGBA =
  { r :: Int  -- 0-255
  , g :: Int  -- 0-255
  , b :: Int  -- 0-255
  , a :: UnitFloat
  }

type CurvePoint =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

data EffectParameterValue
  = EPVNumber FiniteFloat
  | EPVString String
  | EPVBoolean Boolean
  | EPVPoint2D EffectPoint2D
  | EPVPoint3D EffectPoint3D
  | EPVColor EffectRGBA
  | EPVCurve (Array CurvePoint)
  | EPVData String  -- JSON-encoded
  | EPVNull

derive instance Eq EffectParameterValue
derive instance Generic EffectParameterValue _
instance Show EffectParameterValue where show = genericShow

type EffectDropdownOption =
  { label :: NonEmptyString
  , value :: EffectParameterValue
  }

type EffectParameterDef =
  { name          :: NonEmptyString
  , parameterType :: EffectParameterType
  , defaultValue  :: EffectParameterValue
  , min           :: Maybe FiniteFloat
  , max           :: Maybe FiniteFloat
  , step          :: Maybe PositiveFloat
  , options       :: Maybe (Array EffectDropdownOption)
  , animatable    :: Boolean
  , group         :: Maybe NonEmptyString
  }

type EffectParameter =
  { id            :: NonEmptyString
  , name          :: NonEmptyString
  , parameterType :: EffectParameterType
  , value         :: EffectParameterValue
  , defaultValue  :: EffectParameterValue
  , min           :: Maybe FiniteFloat
  , max           :: Maybe FiniteFloat
  , step          :: Maybe PositiveFloat
  , options       :: Maybe (Array EffectDropdownOption)
  , animatable    :: Boolean
  , group         :: Maybe NonEmptyString
  }

--------------------------------------------------------------------------------
-- Effect Types
--------------------------------------------------------------------------------

type Effect =
  { id             :: NonEmptyString
  , name           :: NonEmptyString
  , category       :: EffectCategory
  , enabled        :: Boolean
  , expanded       :: Boolean
  , parameters     :: Array EffectParameter
  , fragmentShader :: Maybe String
  }

type EffectInstance =
  { id         :: NonEmptyString
  , effectKey  :: NonEmptyString
  , name       :: NonEmptyString
  , category   :: EffectCategory
  , enabled    :: Boolean
  , expanded   :: Boolean
  , parameters :: Array NonEmptyString  -- AnimatableProperty IDs
  }

type MeshDeformEffectInstance =
  { instance     :: EffectInstance
  , pins         :: Array WarpPin
  , cachedMeshId :: Maybe NonEmptyString
  , meshDirty    :: Boolean
  }

type EffectDefinition =
  { name           :: NonEmptyString
  , category       :: EffectCategory
  , description    :: String
  , parameters     :: Array EffectParameterDef
  , fragmentShader :: Maybe String
  }

type EffectCategoryInfo =
  { label       :: NonEmptyString
  , icon        :: String
  , description :: String
  }
