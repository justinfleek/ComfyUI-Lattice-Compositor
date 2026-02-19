-- | Lattice.Spline - Spline and path types
-- |
-- | Source: lattice-core/lean/Lattice/Spline.lean
-- | Bezier paths, control points, path effects, level of detail.

module Lattice.Spline
  ( ControlPointType(..)
  , LODMode(..)
  , WaveType(..)
  , SplinePathEffectType(..)
  , StrokeType(..)
  , SplineZigZagPointType(..)
  , Handle
  , ControlPoint
  , AnimatableControlPoint
  , EvaluatedControlPoint
  , SplineRGBA
  , SplineGradientStop
  , SplineStrokeGradient
  , PathEffectBase
  , OffsetPathEffect
  , RoughenEffect
  , WigglePathEffect
  , ZigZagEffect
  , WaveEffect
  , SplinePathEffectInstance(..)
  , LODLevel
  , SplineLODSettings
  , SplineData
  , PathLayerData
  , createDefaultSplineData
  , createDefaultPathLayerData
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Shapes (LineJoin(..), LineCap(..), GradientType)

-- ────────────────────────────────────────────────────────────────────────────
-- Control Point Enums
-- ────────────────────────────────────────────────────────────────────────────

data ControlPointType = CPTCorner | CPTSmooth | CPTSymmetric

derive instance Eq ControlPointType
derive instance Generic ControlPointType _
instance Show ControlPointType where show = genericShow

data LODMode = LODZoom | LODPlayback | LODBoth

derive instance Eq LODMode
derive instance Generic LODMode _
instance Show LODMode where show = genericShow

data WaveType = WTSine | WTTriangle | WTSquare

derive instance Eq WaveType
derive instance Generic WaveType _
instance Show WaveType where show = genericShow

data SplinePathEffectType
  = SPETOffsetPath | SPETRoughen | SPETWiggle | SPETZigzag | SPETWave

derive instance Eq SplinePathEffectType
derive instance Generic SplinePathEffectType _
instance Show SplinePathEffectType where show = genericShow

data StrokeType = STSolid | STGradient

derive instance Eq StrokeType
derive instance Generic StrokeType _
instance Show StrokeType where show = genericShow

data SplineZigZagPointType = SZZCorner | SZZSmooth

derive instance Eq SplineZigZagPointType
derive instance Generic SplineZigZagPointType _
instance Show SplineZigZagPointType where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Handle
-- ────────────────────────────────────────────────────────────────────────────

type Handle =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Control Point
-- ────────────────────────────────────────────────────────────────────────────

type ControlPoint =
  { id        :: NonEmptyString
  , x         :: FiniteFloat
  , y         :: FiniteFloat
  , depth     :: Maybe FiniteFloat
  , handleIn  :: Maybe Handle
  , handleOut :: Maybe Handle
  , pointType :: ControlPointType
  , group     :: Maybe NonEmptyString
  }

type AnimatableControlPoint =
  { id        :: NonEmptyString
  , x         :: NonEmptyString  -- Property ID
  , y         :: NonEmptyString  -- Property ID
  , depth     :: Maybe NonEmptyString
  , handleIn  :: Maybe { x :: NonEmptyString, y :: NonEmptyString }
  , handleOut :: Maybe { x :: NonEmptyString, y :: NonEmptyString }
  , pointType :: ControlPointType
  , group     :: Maybe NonEmptyString
  }

type EvaluatedControlPoint =
  { id        :: NonEmptyString
  , x         :: FiniteFloat
  , y         :: FiniteFloat
  , depth     :: FiniteFloat
  , handleIn  :: Maybe Handle
  , handleOut :: Maybe Handle
  , pointType :: ControlPointType
  , group     :: Maybe NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Gradient
-- ────────────────────────────────────────────────────────────────────────────

type SplineRGBA =
  { r :: Int  -- 0-255
  , g :: Int
  , b :: Int
  , a :: UnitFloat
  }

type SplineGradientStop =
  { position :: UnitFloat
  , color    :: SplineRGBA
  }

type SplineStrokeGradient =
  { gradientType    :: GradientType
  , stops           :: Array SplineGradientStop  -- min 2
  , followPath      :: Boolean
  , spread          :: Percentage  -- 0-100
  , offsetKeyframes :: Maybe (Array { frame :: FrameNumber, offset :: FiniteFloat })
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Path Effects
-- ────────────────────────────────────────────────────────────────────────────

type PathEffectBase =
  { id      :: NonEmptyString
  , enabled :: Boolean
  , order   :: Int
  }

type OffsetPathEffect =
  { base       :: PathEffectBase
  , amount     :: NonEmptyString
  , lineJoin   :: LineJoin
  , miterLimit :: NonEmptyString
  }

type RoughenEffect =
  { base   :: PathEffectBase
  , size   :: NonEmptyString
  , detail :: NonEmptyString
  , seed   :: Int
  }

type WigglePathEffect =
  { base          :: PathEffectBase
  , size          :: NonEmptyString
  , detail        :: NonEmptyString
  , temporalPhase :: NonEmptyString
  , spatialPhase  :: NonEmptyString
  , correlation   :: NonEmptyString
  , seed          :: Int
  }

type ZigZagEffect =
  { base            :: PathEffectBase
  , size            :: NonEmptyString
  , ridgesPerSegment :: NonEmptyString
  , pointType       :: SplineZigZagPointType
  }

type WaveEffect =
  { base      :: PathEffectBase
  , amplitude :: NonEmptyString
  , frequency :: NonEmptyString
  , phase     :: NonEmptyString
  , waveType  :: WaveType
  }

data SplinePathEffectInstance
  = SPEIOffsetPath OffsetPathEffect
  | SPEIRoughen RoughenEffect
  | SPEIWiggle WigglePathEffect
  | SPEIZigzag ZigZagEffect
  | SPEIWave WaveEffect

derive instance Eq SplinePathEffectInstance
derive instance Generic SplinePathEffectInstance _
instance Show SplinePathEffectInstance where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // lod
-- ────────────────────────────────────────────────────────────────────────────

type LODLevel =
  { tolerance     :: PositiveFloat
  , controlPoints :: Array ControlPoint
  , pointCount    :: Int
  , quality       :: Maybe Int
  , complexity    :: Maybe FiniteFloat
  }

type SplineLODSettings =
  { enabled                 :: Boolean
  , mode                    :: LODMode
  , levels                  :: Array LODLevel
  , maxPointsForPreview     :: Int
  , simplificationTolerance :: PositiveFloat
  , cullingEnabled          :: Boolean
  , cullMargin              :: NonNegativeFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Spline Data
-- ────────────────────────────────────────────────────────────────────────────

type SplineData =
  { pathData              :: String
  , controlPoints         :: Array ControlPoint
  , closed                :: Boolean
  , strokeType            :: StrokeType
  , stroke                :: NonEmptyString
  , strokeGradient        :: Maybe SplineStrokeGradient
  , strokeWidth           :: PositiveFloat
  , strokeOpacity         :: Percentage
  , lineCap               :: LineCap
  , lineJoin              :: LineJoin
  , strokeMiterLimit      :: FiniteFloat
  , dashArray             :: Maybe (Array FiniteFloat)
  , dashOffset            :: Maybe FiniteFloat
  , fill                  :: Maybe NonEmptyString
  , fillOpacity           :: Percentage
  , trimStart             :: Maybe Percentage
  , trimEnd               :: Maybe Percentage
  , trimOffset            :: Maybe FiniteFloat
  , pathEffects           :: Array SplinePathEffectInstance
  , animatedControlPoints :: Maybe (Array AnimatableControlPoint)
  , animated              :: Boolean
  , lod                   :: Maybe SplineLODSettings
  , audioReactiveEnabled  :: Boolean
  , audioReactiveSourceLayerId :: Maybe NonEmptyString
  }

type PathLayerData =
  { pathData              :: String
  , controlPoints         :: Array ControlPoint
  , closed                :: Boolean
  , showGuide             :: Boolean
  , guideColor            :: NonEmptyString
  , guideDashPattern      :: { dash :: FiniteFloat, gap :: FiniteFloat }
  , animatedControlPoints :: Maybe (Array AnimatableControlPoint)
  , animated              :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Factory Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Create default spline data (empty path, white stroke)
createDefaultSplineData :: SplineData
createDefaultSplineData =
  { pathData: ""
  , controlPoints: []
  , closed: false
  , strokeType: STSolid
  , stroke: nes "#ffffff"
  , strokeGradient: Nothing
  , strokeWidth: pf 2.0
  , strokeOpacity: pct 100.0
  , lineCap: LCButt
  , lineJoin: LJMiter
  , strokeMiterLimit: ff 4.0
  , dashArray: Nothing
  , dashOffset: Nothing
  , fill: Nothing
  , fillOpacity: pct 100.0
  , trimStart: Nothing
  , trimEnd: Nothing
  , trimOffset: Nothing
  , pathEffects: []
  , animatedControlPoints: Nothing
  , animated: false
  , lod: Nothing
  , audioReactiveEnabled: false
  , audioReactiveSourceLayerId: Nothing
  }
  where
    nes s = case mkNonEmptyString s of
      Just v -> v
      Nothing -> NonEmptyString "error"
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    pct n = case mkPercentage n of
      Just v -> v
      Nothing -> Percentage 0.0
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0

-- | Create default path layer data (empty path, cyan guide)
createDefaultPathLayerData :: PathLayerData
createDefaultPathLayerData =
  { pathData: ""
  , controlPoints: []
  , closed: false
  , showGuide: true
  , guideColor: nes "#00FFFF"
  , guideDashPattern: { dash: ff 5.0, gap: ff 5.0 }
  , animatedControlPoints: Nothing
  , animated: false
  }
  where
    nes s = case mkNonEmptyString s of
      Just v -> v
      Nothing -> NonEmptyString "error"
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0
