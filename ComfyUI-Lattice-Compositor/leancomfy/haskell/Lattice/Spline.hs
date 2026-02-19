{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Spline
Description : Spline and path types
Copyright   : (c) Lattice, 2026
License     : MIT

Bezier paths, control points, path effects, level of detail.
-}

module Lattice.Spline
  ( -- * Control Point Enums
    ControlPointType(..)
  , LODMode(..)
  , WaveType(..)
  , SplinePathEffectType(..)
  , StrokeType(..)
  , SplineZigZagPointType(..)
    -- * Handle
  , Handle(..)
    -- * Control Point
  , ControlPoint(..)
  , AnimatableControlPoint(..)
  , EvaluatedControlPoint(..)
    -- * Gradient
  , SplineRGBA(..)
  , SplineGradientStop(..)
  , SplineStrokeGradient(..)
    -- * Path Effects
  , PathEffectBase(..)
  , OffsetPathEffect(..)
  , RoughenEffect(..)
  , WigglePathEffect(..)
  , ZigZagEffect(..)
  , WaveEffect(..)
  , SplinePathEffectInstance(..)
    -- * LOD
  , LODLevel(..)
  , SplineLODSettings(..)
    -- * Spline Data
  , SplineData(..)
  , PathLayerData(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives
import Lattice.Shapes (LineJoin, LineCap, GradientType)

--------------------------------------------------------------------------------
-- Control Point Enums
--------------------------------------------------------------------------------

data ControlPointType = CPTCorner | CPTSmooth | CPTSymmetric
  deriving stock (Eq, Show, Generic)

data LODMode = LODZoom | LODPlayback | LODBoth
  deriving stock (Eq, Show, Generic)

data WaveType = WTSine | WTTriangle | WTSquare
  deriving stock (Eq, Show, Generic)

data SplinePathEffectType
  = SPETOffsetPath | SPETRoughen | SPETWiggle | SPETZigzag | SPETWave
  deriving stock (Eq, Show, Generic)

data StrokeType = STSolid | STGradient
  deriving stock (Eq, Show, Generic)

data SplineZigZagPointType = SZZCorner | SZZSmooth
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Handle
--------------------------------------------------------------------------------

data Handle = Handle
  { hX :: !FiniteFloat
  , hY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Control Point
--------------------------------------------------------------------------------

data ControlPoint = ControlPoint
  { cpId        :: !NonEmptyString
  , cpX         :: !FiniteFloat
  , cpY         :: !FiniteFloat
  , cpDepth     :: !(Maybe FiniteFloat)
  , cpHandleIn  :: !(Maybe Handle)
  , cpHandleOut :: !(Maybe Handle)
  , cpPointType :: !ControlPointType
  , cpGroup     :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data AnimatableControlPoint = AnimatableControlPoint
  { acpId        :: !NonEmptyString
  , acpX         :: !NonEmptyString  -- Property ID
  , acpY         :: !NonEmptyString  -- Property ID
  , acpDepth     :: !(Maybe NonEmptyString)
  , acpHandleIn  :: !(Maybe (NonEmptyString, NonEmptyString))
  , acpHandleOut :: !(Maybe (NonEmptyString, NonEmptyString))
  , acpPointType :: !ControlPointType
  , acpGroup     :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data EvaluatedControlPoint = EvaluatedControlPoint
  { ecpId        :: !NonEmptyString
  , ecpX         :: !FiniteFloat
  , ecpY         :: !FiniteFloat
  , ecpDepth     :: !FiniteFloat
  , ecpHandleIn  :: !(Maybe Handle)
  , ecpHandleOut :: !(Maybe Handle)
  , ecpPointType :: !ControlPointType
  , ecpGroup     :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Gradient
--------------------------------------------------------------------------------

data SplineRGBA = SplineRGBA
  { srgbaR :: !Int  -- 0-255
  , srgbaG :: !Int
  , srgbaB :: !Int
  , srgbaA :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

data SplineGradientStop = SplineGradientStop
  { sgsPosition :: !UnitFloat
  , sgsColor    :: !SplineRGBA
  } deriving stock (Eq, Show, Generic)

data SplineStrokeGradient = SplineStrokeGradient
  { ssgGradientType    :: !GradientType
  , ssgStops           :: !(Vector SplineGradientStop)  -- min 2
  , ssgFollowPath      :: !Bool
  , ssgSpread          :: !Percentage  -- 0-100
  , ssgOffsetKeyframes :: !(Maybe (Vector (FrameNumber, FiniteFloat)))
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Path Effects
--------------------------------------------------------------------------------

data PathEffectBase = PathEffectBase
  { pebId      :: !NonEmptyString
  , pebEnabled :: !Bool
  , pebOrder   :: !Int
  } deriving stock (Eq, Show, Generic)

data OffsetPathEffect = OffsetPathEffect
  { opeBase       :: !PathEffectBase
  , opeAmount     :: !NonEmptyString
  , opeLineJoin   :: !LineJoin
  , opeMiterLimit :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data RoughenEffect = RoughenEffect
  { reBase   :: !PathEffectBase
  , reSize   :: !NonEmptyString
  , reDetail :: !NonEmptyString
  , reSeed   :: !Int
  } deriving stock (Eq, Show, Generic)

data WigglePathEffect = WigglePathEffect
  { wpeBase          :: !PathEffectBase
  , wpeSize          :: !NonEmptyString
  , wpeDetail        :: !NonEmptyString
  , wpeTemporalPhase :: !NonEmptyString
  , wpeSpatialPhase  :: !NonEmptyString
  , wpeCorrelation   :: !NonEmptyString
  , wpeSeed          :: !Int
  } deriving stock (Eq, Show, Generic)

data ZigZagEffect = ZigZagEffect
  { zzeBase            :: !PathEffectBase
  , zzeSize            :: !NonEmptyString
  , zzeRidgesPerSegment :: !NonEmptyString
  , zzePointType       :: !SplineZigZagPointType
  } deriving stock (Eq, Show, Generic)

data WaveEffect = WaveEffect
  { weBase      :: !PathEffectBase
  , weAmplitude :: !NonEmptyString
  , weFrequency :: !NonEmptyString
  , wePhase     :: !NonEmptyString
  , weWaveType  :: !WaveType
  } deriving stock (Eq, Show, Generic)

data SplinePathEffectInstance
  = SPEIOffsetPath !OffsetPathEffect
  | SPEIRoughen !RoughenEffect
  | SPEIWiggle !WigglePathEffect
  | SPEIZigzag !ZigZagEffect
  | SPEIWave !WaveEffect
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- LOD
--------------------------------------------------------------------------------

data LODLevel = LODLevel
  { lodTolerance     :: !PositiveFloat
  , lodControlPoints :: !(Vector ControlPoint)
  , lodPointCount    :: !Int
  , lodQuality       :: !(Maybe Int)
  , lodComplexity    :: !(Maybe FiniteFloat)
  } deriving stock (Eq, Show, Generic)

data SplineLODSettings = SplineLODSettings
  { slsEnabled                 :: !Bool
  , slsMode                    :: !LODMode
  , slsLevels                  :: !(Vector LODLevel)
  , slsMaxPointsForPreview     :: !Int
  , slsSimplificationTolerance :: !PositiveFloat
  , slsCullingEnabled          :: !Bool
  , slsCullMargin              :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Spline Data
--------------------------------------------------------------------------------

data SplineData = SplineData
  { sdPathData              :: !Text
  , sdControlPoints         :: !(Vector ControlPoint)
  , sdClosed                :: !Bool
  , sdStrokeType            :: !StrokeType
  , sdStroke                :: !NonEmptyString
  , sdStrokeGradient        :: !(Maybe SplineStrokeGradient)
  , sdStrokeWidth           :: !PositiveFloat
  , sdStrokeOpacity         :: !Percentage
  , sdLineCap               :: !LineCap
  , sdLineJoin              :: !LineJoin
  , sdStrokeMiterLimit      :: !FiniteFloat
  , sdDashArray             :: !(Maybe (Vector FiniteFloat))
  , sdDashOffset            :: !(Maybe FiniteFloat)
  , sdFill                  :: !(Maybe NonEmptyString)
  , sdFillOpacity           :: !Percentage
  , sdTrimStart             :: !(Maybe Percentage)
  , sdTrimEnd               :: !(Maybe Percentage)
  , sdTrimOffset            :: !(Maybe FiniteFloat)
  , sdPathEffects           :: !(Vector SplinePathEffectInstance)
  , sdAnimatedControlPoints :: !(Maybe (Vector AnimatableControlPoint))
  , sdAnimated              :: !Bool
  , sdLod                   :: !(Maybe SplineLODSettings)
  , sdAudioReactiveEnabled  :: !Bool
  , sdAudioReactiveSourceLayerId :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data PathLayerData = PathLayerData
  { pldPathData              :: !Text
  , pldControlPoints         :: !(Vector ControlPoint)
  , pldClosed                :: !Bool
  , pldShowGuide             :: !Bool
  , pldGuideColor            :: !NonEmptyString
  , pldGuideDashPattern      :: !(FiniteFloat, FiniteFloat)
  , pldAnimatedControlPoints :: !(Maybe (Vector AnimatableControlPoint))
  , pldAnimated              :: !Bool
  } deriving stock (Eq, Show, Generic)
