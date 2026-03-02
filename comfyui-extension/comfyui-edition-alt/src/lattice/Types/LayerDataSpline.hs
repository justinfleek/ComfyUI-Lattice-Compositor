-- |
-- Module      : Lattice.Types.LayerDataSpline
-- Description : Spline and path layer data types
-- 
-- Migrated from ui/src/types/spline.ts
-- These types depend heavily on AnimatableProperty
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataSpline
  ( -- Control points
    ControlPoint(..)
  , ControlPointType(..)
  , ControlPointHandle(..)
  , AnimatableControlPoint(..)
  , AnimatableHandle(..)
  -- Spline data
  , SplineData(..)
  , SplineStrokeType(..)
  , SplineGradientStop(..)
  , SplineStrokeGradient(..)
  , SplineGradientOffsetKeyframe(..)
  , SplineLineCap(..)
  , SplineLineJoin(..)
  -- Path layer data
  , PathLayerData(..)
  -- Path effects
  , SplinePathEffectInstance(..)
  , SplinePathEffectType(..)
  , OffsetPathEffect(..)
  , RoughenEffect(..)
  , WigglePathEffect(..)
  , ZigZagEffect(..)
  , WaveEffect(..)
  , WaveType(..)
  --                                                                       // lod
  , SplineLODSettings(..)
  , SplineLODMode(..)
  , LODLevel(..)
  -- Audio reactive
  , SplineAudioReactive(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // control // points
-- ════════════════════════════════════════════════════════════════════════════

-- | Control point type
data ControlPointType
  = ControlPointTypeCorner
  | ControlPointTypeSmooth
  | ControlPointTypeSymmetric
  deriving (Eq, Show, Generic)

instance ToJSON ControlPointType where
  toJSON ControlPointTypeCorner = toJSON (T.pack "corner")
  toJSON ControlPointTypeSmooth = toJSON (T.pack "smooth")
  toJSON ControlPointTypeSymmetric = toJSON (T.pack "symmetric")

instance FromJSON ControlPointType where
  parseJSON = withText "ControlPointType" $ \s ->
    case s of
      "corner" -> return ControlPointTypeCorner
      "smooth" -> return ControlPointTypeSmooth
      "symmetric" -> return ControlPointTypeSymmetric
      _ -> fail "Invalid ControlPointType"

-- | Control point handle (static)
data ControlPointHandle = ControlPointHandle
  { controlPointHandleX :: Double
  , controlPointHandleY :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ControlPointHandle where
  toJSON (ControlPointHandle x y) =
    object ["x" .= x, "y" .= y]

instance FromJSON ControlPointHandle where
  parseJSON = withObject "ControlPointHandle" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    if validateFinite x && validateFinite y
      then return (ControlPointHandle x y)
      else fail "ControlPointHandle: x and y must be finite"

-- | Static control point - for non-animated splines
data ControlPoint = ControlPoint
  { controlPointId :: Text
  , controlPointX :: Double
  , controlPointY :: Double
  , controlPointDepth :: Maybe Double  -- Sampled from depth map
  , controlPointHandleIn :: Maybe ControlPointHandle
  , controlPointHandleOut :: Maybe ControlPointHandle
  , controlPointType :: ControlPointType
  , controlPointGroup :: Maybe Text  -- Group ID for grouped animations
  }
  deriving (Eq, Show, Generic)

instance ToJSON ControlPoint where
  toJSON (ControlPoint id_ x y mDepth mHandleIn mHandleOut cType mGroup) =
    let
      baseFields = ["id" .= id_, "x" .= x, "y" .= y, "type" .= cType]
      withDepth = case mDepth of Just d -> ("depth" .= d) : baseFields; Nothing -> baseFields
      withHandleIn = case mHandleIn of Just h -> ("handleIn" .= h) : withDepth; Nothing -> withDepth
      withHandleOut = case mHandleOut of Just h -> ("handleOut" .= h) : withHandleIn; Nothing -> withHandleIn
      withGroup = case mGroup of Just g -> ("group" .= g) : withHandleOut; Nothing -> withHandleOut
    in object withGroup

instance FromJSON ControlPoint where
  parseJSON = withObject "ControlPoint" $ \o -> do
    id_ <- o .: "id"
    x <- o .: "x"
    y <- o .: "y"
    mDepth <- o .:? "depth"
    mHandleIn <- o .:? "handleIn"
    mHandleOut <- o .:? "handleOut"
    cType <- o .: "type"
    mGroup <- o .:? "group"
    if validateFinite x && validateFinite y &&
       maybe True (\d -> validateFinite d) mDepth
      then return (ControlPoint id_ x y mDepth mHandleIn mHandleOut cType mGroup)
      else fail "ControlPoint: x, y, and depth must be finite"

-- | Animated bezier handle - for advanced handle animation
data AnimatableHandle = AnimatableHandle
  { animatableHandleX :: AnimatableProperty Double
  , animatableHandleY :: AnimatableProperty Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimatableHandle where
  toJSON (AnimatableHandle x y) =
    object ["x" .= x, "y" .= y]

instance FromJSON AnimatableHandle where
  parseJSON = withObject "AnimatableHandle" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    return (AnimatableHandle x y)

-- | Animated control point - for keyframe-animated splines
data AnimatableControlPoint = AnimatableControlPoint
  { animatableControlPointId :: Text
  , animatableControlPointX :: AnimatableProperty Double
  , animatableControlPointY :: AnimatableProperty Double
  , animatableControlPointDepth :: Maybe (AnimatableProperty Double)  -- Can also be animated
  , animatableControlPointHandleIn :: Maybe AnimatableHandle
  , animatableControlPointHandleOut :: Maybe AnimatableHandle
  , animatableControlPointType :: ControlPointType
  , animatableControlPointGroup :: Maybe Text  -- Group ID for grouped animations
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimatableControlPoint where
  toJSON (AnimatableControlPoint id_ x y mDepth mHandleIn mHandleOut cType mGroup) =
    let
      baseFields = ["id" .= id_, "x" .= x, "y" .= y, "type" .= cType]
      withDepth = case mDepth of Just d -> ("depth" .= d) : baseFields; Nothing -> baseFields
      withHandleIn = case mHandleIn of Just h -> ("handleIn" .= h) : withDepth; Nothing -> withDepth
      withHandleOut = case mHandleOut of Just h -> ("handleOut" .= h) : withHandleIn; Nothing -> withHandleIn
      withGroup = case mGroup of Just g -> ("group" .= g) : withHandleOut; Nothing -> withHandleOut
    in object withGroup

instance FromJSON AnimatableControlPoint where
  parseJSON = withObject "AnimatableControlPoint" $ \o -> do
    id_ <- o .: "id"
    x <- o .: "x"
    y <- o .: "y"
    mDepth <- o .:? "depth"
    mHandleIn <- o .:? "handleIn"
    mHandleOut <- o .:? "handleOut"
    cType <- o .: "type"
    mGroup <- o .:? "group"
    return (AnimatableControlPoint id_ x y mDepth mHandleIn mHandleOut cType mGroup)

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // spline // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Stroke type
data SplineStrokeType
  = SplineStrokeTypeSolid
  | SplineStrokeTypeGradient
  deriving (Eq, Show, Generic)

instance ToJSON SplineStrokeType where
  toJSON SplineStrokeTypeSolid = toJSON (T.pack "solid")
  toJSON SplineStrokeTypeGradient = toJSON (T.pack "gradient")

instance FromJSON SplineStrokeType where
  parseJSON = withText "SplineStrokeType" $ \s ->
    case s of
      "solid" -> return SplineStrokeTypeSolid
      "gradient" -> return SplineStrokeTypeGradient
      _ -> fail "Invalid SplineStrokeType"

-- | Line cap style
data SplineLineCap
  = SplineLineCapButt
  | SplineLineCapRound
  | SplineLineCapSquare
  deriving (Eq, Show, Generic)

instance ToJSON SplineLineCap where
  toJSON SplineLineCapButt = toJSON (T.pack "butt")
  toJSON SplineLineCapRound = toJSON (T.pack "round")
  toJSON SplineLineCapSquare = toJSON (T.pack "square")

instance FromJSON SplineLineCap where
  parseJSON = withText "SplineLineCap" $ \s ->
    case s of
      "butt" -> return SplineLineCapButt
      "round" -> return SplineLineCapRound
      "square" -> return SplineLineCapSquare
      _ -> fail "Invalid SplineLineCap"

-- | Line join style
data SplineLineJoin
  = SplineLineJoinMiter
  | SplineLineJoinRound
  | SplineLineJoinBevel
  deriving (Eq, Show, Generic)

instance ToJSON SplineLineJoin where
  toJSON SplineLineJoinMiter = toJSON (T.pack "miter")
  toJSON SplineLineJoinRound = toJSON (T.pack "round")
  toJSON SplineLineJoinBevel = toJSON (T.pack "bevel")

instance FromJSON SplineLineJoin where
  parseJSON = withText "SplineLineJoin" $ \s ->
    case s of
      "miter" -> return SplineLineJoinMiter
      "round" -> return SplineLineJoinRound
      "bevel" -> return SplineLineJoinBevel
      _ -> fail "Invalid SplineLineJoin"

-- | Gradient stop for stroke gradients
data SplineGradientStop = SplineGradientStop
  { splineGradientStopPosition :: Double  -- 0-1
  , splineGradientStopColorR :: Double  -- RGBA color 0-255
  , splineGradientStopColorG :: Double
  , splineGradientStopColorB :: Double
  , splineGradientStopColorA :: Double  -- 0-1
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineGradientStop where
  toJSON (SplineGradientStop pos r g b a) =
    object
      [ "position" .= pos
      , "color" .= object ["r" .= r, "g" .= g, "b" .= b, "a" .= a]
      ]

instance FromJSON SplineGradientStop where
  parseJSON = withObject "SplineGradientStop" $ \o -> do
    pos <- o .: "position"
    colorObj <- o .: "color"
    r <- colorObj .: "r"
    g <- colorObj .: "g"
    b <- colorObj .: "b"
    a <- colorObj .: "a"
    if validateNormalized01 pos && validateFinite r && validateFinite g &&
       validateFinite b && validateNormalized01 a &&
       validateNonNegative r && validateNonNegative g && validateNonNegative b &&
       r <= 255 && g <= 255 && b <= 255
      then return (SplineGradientStop pos r g b a)
      else fail "SplineGradientStop: position must be in [0,1], color components must be valid"

-- | Gradient offset keyframe
data SplineGradientOffsetKeyframe = SplineGradientOffsetKeyframe
  { splineGradientOffsetKeyframeFrame :: Double
  , splineGradientOffsetKeyframeValue :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineGradientOffsetKeyframe where
  toJSON (SplineGradientOffsetKeyframe frame value) =
    object ["frame" .= frame, "value" .= value]

instance FromJSON SplineGradientOffsetKeyframe where
  parseJSON = withObject "SplineGradientOffsetKeyframe" $ \o -> do
    frame <- o .: "frame"
    value <- o .: "value"
    if validateFinite frame && validateFinite value && validateNonNegative frame
      then return (SplineGradientOffsetKeyframe frame value)
      else fail "SplineGradientOffsetKeyframe: frame and value must be finite"

-- | Gradient definition for stroke gradients
data SplineStrokeGradient = SplineStrokeGradient
  { splineStrokeGradientType :: Text  -- "linear" | "radial"
  , splineStrokeGradientStops :: [SplineGradientStop]
  , splineStrokeGradientFollowPath :: Maybe Bool  -- Gradient follows the stroke path
  , splineStrokeGradientSpread :: Maybe Double  -- Gradient spread along path (0-100%, default 100)
  , splineStrokeGradientOffsetKeyframes :: Maybe [SplineGradientOffsetKeyframe]  -- Animated gradient offset along path
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineStrokeGradient where
  toJSON (SplineStrokeGradient gType stops mFollowPath mSpread mOffsetKeyframes) =
    let
      baseFields = ["type" .= gType, "stops" .= stops]
      withFollowPath = case mFollowPath of Just f -> ("followPath" .= f) : baseFields; Nothing -> baseFields
      withSpread = case mSpread of Just s -> ("spread" .= s) : withFollowPath; Nothing -> withFollowPath
      withOffsetKeyframes = case mOffsetKeyframes of Just o -> ("offsetKeyframes" .= o) : withSpread; Nothing -> withSpread
    in object withOffsetKeyframes

instance FromJSON SplineStrokeGradient where
  parseJSON = withObject "SplineStrokeGradient" $ \o -> do
    gType <- o .: "type"
    stops <- o .: "stops"
    mFollowPath <- o .:? "followPath"
    mSpread <- o .:? "spread"
    mOffsetKeyframes <- o .:? "offsetKeyframes"
    if maybe True (\s -> validateFinite s && validateNormalized01 (s / 100)) mSpread
      then return (SplineStrokeGradient gType stops mFollowPath mSpread mOffsetKeyframes)
      else fail "SplineStrokeGradient: spread must be finite and in range [0, 100]"

-- | Union type for dash array (static number array or AnimatableProperty)
data DashArrayValue
  = DashArrayStatic [Double]
  | DashArrayAnimatable (AnimatableProperty [Double])
  deriving (Eq, Show, Generic)

instance ToJSON DashArrayValue where
  toJSON (DashArrayStatic arr) = toJSON arr
  toJSON (DashArrayAnimatable prop) = toJSON prop

instance FromJSON DashArrayValue where
  parseJSON v@(Array _) = do
    arr <- parseJSON v
    return (DashArrayStatic arr)
  parseJSON v = do
    prop <- parseJSON v
    return (DashArrayAnimatable prop)

-- | Union type for number or AnimatableProperty
data NumberOrAnimatable
  = NumberOrAnimatableStatic Double
  | NumberOrAnimatableAnimatable (AnimatableProperty Double)
  deriving (Eq, Show, Generic)

instance ToJSON NumberOrAnimatable where
  toJSON (NumberOrAnimatableStatic n) = toJSON n
  toJSON (NumberOrAnimatableAnimatable prop) = toJSON prop

instance FromJSON NumberOrAnimatable where
  parseJSON v@(Number _) = do
    n <- parseJSON v
    return (NumberOrAnimatableStatic n)
  parseJSON v = do
    prop <- parseJSON v
    return (NumberOrAnimatableAnimatable prop)

-- | Spline data
data SplineData = SplineData
  { splineDataPathData :: Text  -- SVG path commands (M, C, Q, L, Z)
  , splineDataControlPoints :: [ControlPoint]
  , splineDataClosed :: Bool
  , splineDataStrokeType :: Maybe SplineStrokeType  -- Stroke type (default: "solid" when stroke is set)
  , splineDataStroke :: Text  -- Stroke color hex (used when strokeType is "solid" or undefined)
  , splineDataStrokeGradient :: Maybe SplineStrokeGradient  -- Gradient definition (used when strokeType is "gradient")
  , splineDataStrokeWidth :: Double  -- Stroke width in pixels
  , splineDataStrokeOpacity :: Maybe Double  -- Stroke opacity 0-100 (default 100)
  , splineDataLineCap :: Maybe SplineLineCap  -- Line cap style
  , splineDataLineJoin :: Maybe SplineLineJoin  -- Line join style
  , splineDataStrokeMiterLimit :: Maybe Double  -- Miter limit (default 4)
  , splineDataDashArray :: Maybe DashArrayValue  -- Dash pattern [dash, gap, ...]
  , splineDataDashOffset :: Maybe NumberOrAnimatable  -- Animated dash offset
  , splineDataFill :: Maybe Text  -- Fill color hex (empty = no fill)
  , splineDataFillOpacity :: Maybe Double  -- Fill opacity 0-100 (default 100)
  , splineDataTrimStart :: Maybe NumberOrAnimatable  -- Trim start 0-100%
  , splineDataTrimEnd :: Maybe NumberOrAnimatable  -- Trim end 0-100%
  , splineDataTrimOffset :: Maybe NumberOrAnimatable  -- Trim offset in degrees
  , splineDataPathEffects :: Maybe [SplinePathEffectInstance]  -- Path Effects (applied in order before trim)
  , splineDataAnimatedControlPoints :: Maybe [AnimatableControlPoint]  -- Animated spline support
  , splineDataAnimated :: Maybe Bool  -- True if using animatedControlPoints
  , splineDataLOD :: Maybe SplineLODSettings  -- Level of Detail (for complex vectors)
  , splineDataWarpPins :: Maybe [Value]  -- Mesh Warp deformation pins (TODO: migrate WarpPin type)
  , splineDataPuppetPins :: Maybe [Value]  -- @deprecated Use warpPins instead
  , splineDataAudioReactive :: Maybe SplineAudioReactive  -- Audio-reactive animation configuration
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineData where
  toJSON (SplineData pathData controlPoints closed mStrokeType stroke mStrokeGradient strokeWidth mStrokeOpacity mLineCap mLineJoin mStrokeMiterLimit mDashArray mDashOffset mFill mFillOpacity mTrimStart mTrimEnd mTrimOffset mPathEffects mAnimatedControlPoints mAnimated mLOD mWarpPins mPuppetPins mAudioReactive) =
    let
      baseFields = ["pathData" .= pathData, "controlPoints" .= controlPoints, "closed" .= closed, "stroke" .= stroke, "strokeWidth" .= strokeWidth]
      f1 = case mStrokeType of Just t -> ("strokeType" .= t) : baseFields; Nothing -> baseFields
      f2 = case mStrokeGradient of Just g -> ("strokeGradient" .= g) : f1; Nothing -> f1
      f3 = case mStrokeOpacity of Just o -> ("strokeOpacity" .= o) : f2; Nothing -> f2
      f4 = case mLineCap of Just c -> ("lineCap" .= c) : f3; Nothing -> f3
      f5 = case mLineJoin of Just j -> ("lineJoin" .= j) : f4; Nothing -> f4
      f6 = case mStrokeMiterLimit of Just m -> ("strokeMiterLimit" .= m) : f5; Nothing -> f5
      f7 = case mDashArray of Just d -> ("dashArray" .= d) : f6; Nothing -> f6
      f8 = case mDashOffset of Just o -> ("dashOffset" .= o) : f7; Nothing -> f7
      f9 = case mFill of Just f -> ("fill" .= f) : f8; Nothing -> f8
      f10 = case mFillOpacity of Just o -> ("fillOpacity" .= o) : f9; Nothing -> f9
      f11 = case mTrimStart of Just s -> ("trimStart" .= s) : f10; Nothing -> f10
      f12 = case mTrimEnd of Just e -> ("trimEnd" .= e) : f11; Nothing -> f11
      f13 = case mTrimOffset of Just o -> ("trimOffset" .= o) : f12; Nothing -> f12
      f14 = case mPathEffects of Just e -> ("pathEffects" .= e) : f13; Nothing -> f13
      f15 = case mAnimatedControlPoints of Just a -> ("animatedControlPoints" .= a) : f14; Nothing -> f14
      f16 = case mAnimated of Just a -> ("animated" .= a) : f15; Nothing -> f15
      f17 = case mLOD of Just l -> ("lod" .= l) : f16; Nothing -> f16
      f18 = case mWarpPins of Just w -> ("warpPins" .= w) : f17; Nothing -> f17
      f19 = case mPuppetPins of Just p -> ("puppetPins" .= p) : f18; Nothing -> f18
      f20 = case mAudioReactive of Just ar -> ("audioReactive" .= ar) : f19; Nothing -> f19
    in object f20

instance FromJSON SplineData where
  parseJSON = withObject "SplineData" $ \o -> do
    pathData <- o .: "pathData"
    controlPoints <- o .: "controlPoints"
    closed <- o .: "closed"
    mStrokeType <- o .:? "strokeType"
    stroke <- o .: "stroke"
    mStrokeGradient <- o .:? "strokeGradient"
    strokeWidth <- o .: "strokeWidth"
    mStrokeOpacity <- o .:? "strokeOpacity"
    mLineCap <- o .:? "lineCap"
    mLineJoin <- o .:? "lineJoin"
    mStrokeMiterLimit <- o .:? "strokeMiterLimit"
    mDashArray <- o .:? "dashArray"
    mDashOffset <- o .:? "dashOffset"
    mFill <- o .:? "fill"
    mFillOpacity <- o .:? "fillOpacity"
    mTrimStart <- o .:? "trimStart"
    mTrimEnd <- o .:? "trimEnd"
    mTrimOffset <- o .:? "trimOffset"
    mPathEffects <- o .:? "pathEffects"
    mAnimatedControlPoints <- o .:? "animatedControlPoints"
    mAnimated <- o .:? "animated"
    mLOD <- o .:? "lod"
    mWarpPins <- o .:? "warpPins"
    mPuppetPins <- o .:? "puppetPins"
    mAudioReactive <- o .:? "audioReactive"
    -- Validate closed paths must have at least 3 control points (matches Zod schema refinement)
    if closed && length controlPoints < 3
      then fail "Closed splines must have at least 3 control points"
      else
        -- Validate numeric values
        if validateFinite strokeWidth && validateNonNegative strokeWidth &&
           maybe True (\o -> validateFinite o && validateNormalized01 (o / 100)) mStrokeOpacity &&
           maybe True (\o -> validateFinite o && validateNormalized01 (o / 100)) mFillOpacity &&
       maybe True (\m -> validateFinite m && validateNonNegative m) mStrokeMiterLimit
      then return (SplineData pathData controlPoints closed mStrokeType stroke mStrokeGradient strokeWidth mStrokeOpacity mLineCap mLineJoin mStrokeMiterLimit mDashArray mDashOffset mFill mFillOpacity mTrimStart mTrimEnd mTrimOffset mPathEffects mAnimatedControlPoints mAnimated mLOD mWarpPins mPuppetPins mAudioReactive)
      else fail "SplineData: numeric values must be finite and within valid ranges"

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // path // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Path layer data (motion path for text-on-path, camera paths, particle emitters)
data PathLayerData = PathLayerData
  { pathLayerDataPathData :: Text  -- SVG path commands (M, C, Q, L, Z)
  , pathLayerDataControlPoints :: [ControlPoint]  -- Control points defining the path
  , pathLayerDataClosed :: Bool  -- Whether the path is closed
  , pathLayerDataShowGuide :: Bool  -- Show dashed guide line in editor (default: true)
  , pathLayerDataGuideColor :: Text  -- Guide line color (default: '#00FFFF' cyan)
  , pathLayerDataGuideDashPattern :: (Double, Double)  -- Guide line dash pattern [dash, gap]
  , pathLayerDataAnimatedControlPoints :: Maybe [AnimatableControlPoint]  -- Animated control points for path morphing
  , pathLayerDataAnimated :: Maybe Bool  -- True if using animatedControlPoints
  }
  deriving (Eq, Show, Generic)

instance ToJSON PathLayerData where
  toJSON (PathLayerData pathData controlPoints closed showGuide guideColor (dash, gap) mAnimatedControlPoints mAnimated) =
    let
      baseFields = ["pathData" .= pathData, "controlPoints" .= controlPoints, "closed" .= closed, "showGuide" .= showGuide, "guideColor" .= guideColor, "guideDashPattern" .= [dash, gap]]
      withAnimatedControlPoints = case mAnimatedControlPoints of Just a -> ("animatedControlPoints" .= a) : baseFields; Nothing -> baseFields
      withAnimated = case mAnimated of Just a -> ("animated" .= a) : withAnimatedControlPoints; Nothing -> withAnimatedControlPoints
    in object withAnimated

instance FromJSON PathLayerData where
  parseJSON = withObject "PathLayerData" $ \o -> do
    pathData <- o .: "pathData"
    controlPoints <- o .: "controlPoints"
    closed <- o .: "closed"
    showGuide <- o .: "showGuide"
    guideColor <- o .: "guideColor"
    dashPatternArr <- o .: "guideDashPattern"
    dash <- case dashPatternArr of
      [d, g] -> return (d, g)
      _ -> fail "PathLayerData: guideDashPattern must be [dash, gap]"
    mAnimatedControlPoints <- o .:? "animatedControlPoints"
    mAnimated <- o .:? "animated"
    -- Validate closed paths must have at least 3 control points (matches Zod schema refinement)
    if closed && length controlPoints < 3
      then fail "Closed paths must have at least 3 control points"
      else
        if validateFinite (fst dash) && validateFinite (snd dash) &&
           validateNonNegative (fst dash) && validateNonNegative (snd dash)
          then return (PathLayerData pathData controlPoints closed showGuide guideColor dash mAnimatedControlPoints mAnimated)
          else fail "PathLayerData: guideDashPattern values must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // path // effects
-- ════════════════════════════════════════════════════════════════════════════

-- | Path effect type
data SplinePathEffectType
  = SplinePathEffectTypeOffsetPath
  | SplinePathEffectTypeRoughen
  | SplinePathEffectTypeWiggle
  | SplinePathEffectTypeZigzag
  | SplinePathEffectTypeWave
  deriving (Eq, Show, Generic)

instance ToJSON SplinePathEffectType where
  toJSON SplinePathEffectTypeOffsetPath = toJSON (T.pack "offsetPath")
  toJSON SplinePathEffectTypeRoughen = toJSON (T.pack "roughen")
  toJSON SplinePathEffectTypeWiggle = toJSON (T.pack "wiggle")
  toJSON SplinePathEffectTypeZigzag = toJSON (T.pack "zigzag")
  toJSON SplinePathEffectTypeWave = toJSON (T.pack "wave")

instance FromJSON SplinePathEffectType where
  parseJSON = withText "SplinePathEffectType" $ \s ->
    case s of
      "offsetPath" -> return SplinePathEffectTypeOffsetPath
      "roughen" -> return SplinePathEffectTypeRoughen
      "wiggle" -> return SplinePathEffectTypeWiggle
      "zigzag" -> return SplinePathEffectTypeZigzag
      "wave" -> return SplinePathEffectTypeWave
      _ -> fail "Invalid SplinePathEffectType"

-- | Offset join
data OffsetJoin
  = OffsetJoinMiter
  | OffsetJoinRound
  | OffsetJoinBevel
  deriving (Eq, Show, Generic)

instance ToJSON OffsetJoin where
  toJSON OffsetJoinMiter = toJSON (T.pack "miter")
  toJSON OffsetJoinRound = toJSON (T.pack "round")
  toJSON OffsetJoinBevel = toJSON (T.pack "bevel")

instance FromJSON OffsetJoin where
  parseJSON = withText "OffsetJoin" $ \s ->
    case s of
      "miter" -> return OffsetJoinMiter
      "round" -> return OffsetJoinRound
      "bevel" -> return OffsetJoinBevel
      _ -> fail "Invalid OffsetJoin"

-- | Zigzag point type
data ZigZagPointType
  = ZigZagPointTypeCorner
  | ZigZagPointTypeSmooth
  deriving (Eq, Show, Generic)

instance ToJSON ZigZagPointType where
  toJSON ZigZagPointTypeCorner = toJSON (T.pack "corner")
  toJSON ZigZagPointTypeSmooth = toJSON (T.pack "smooth")

instance FromJSON ZigZagPointType where
  parseJSON = withText "ZigZagPointType" $ \s ->
    case s of
      "corner" -> return ZigZagPointTypeCorner
      "smooth" -> return ZigZagPointTypeSmooth
      _ -> fail "Invalid ZigZagPointType"

-- | Wave type
data WaveType
  = WaveTypeSine
  | WaveTypeTriangle
  | WaveTypeSquare
  deriving (Eq, Show, Generic)

instance ToJSON WaveType where
  toJSON WaveTypeSine = toJSON (T.pack "sine")
  toJSON WaveTypeTriangle = toJSON (T.pack "triangle")
  toJSON WaveTypeSquare = toJSON (T.pack "square")

instance FromJSON WaveType where
  parseJSON = withText "WaveType" $ \s ->
    case s of
      "sine" -> return WaveTypeSine
      "triangle" -> return WaveTypeTriangle
      "square" -> return WaveTypeSquare
      _ -> fail "Invalid WaveType"

-- | Offset Path Effect - grow/shrink paths
data OffsetPathEffect = OffsetPathEffect
  { offsetPathEffectId :: Text
  , offsetPathEffectType :: SplinePathEffectType  -- "offsetPath"
  , offsetPathEffectEnabled :: Bool
  , offsetPathEffectOrder :: Double  -- Execution order (lower = first)
  , offsetPathEffectAmount :: AnimatableProperty Double  -- Positive = expand, negative = contract
  , offsetPathEffectLineJoin :: OffsetJoin
  , offsetPathEffectMiterLimit :: AnimatableProperty Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON OffsetPathEffect where
  toJSON (OffsetPathEffect id_ _ enabled order amount lineJoin miterLimit) =
    object
      [ "id" .= id_
      , "type" .= T.pack "offsetPath"
      , "enabled" .= enabled
      , "order" .= order
      , "amount" .= amount
      , "lineJoin" .= lineJoin
      , "miterLimit" .= miterLimit
      ]

instance FromJSON OffsetPathEffect where
  parseJSON = withObject "OffsetPathEffect" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    order <- o .: "order"
    amount <- o .: "amount"
    lineJoin <- o .: "lineJoin"
    miterLimit <- o .: "miterLimit"
    if validateFinite order && validateNonNegative order
      then return (OffsetPathEffect id_ SplinePathEffectTypeOffsetPath enabled order amount lineJoin miterLimit)
      else fail "OffsetPathEffect: order must be finite and non-negative"

-- | Roughen Effect - organic hand-drawn look
data RoughenEffect = RoughenEffect
  { roughenEffectId :: Text
  , roughenEffectType :: SplinePathEffectType  -- "roughen"
  , roughenEffectEnabled :: Bool
  , roughenEffectOrder :: Double  -- Execution order
  , roughenEffectSize :: AnimatableProperty Double  -- Roughness magnitude
  , roughenEffectDetail :: AnimatableProperty Double  -- Points per segment
  , roughenEffectSeed :: Double  -- Deterministic randomness
  }
  deriving (Eq, Show, Generic)

instance ToJSON RoughenEffect where
  toJSON (RoughenEffect id_ _ enabled order size detail seed) =
    object
      [ "id" .= id_
      , "type" .= T.pack "roughen"
      , "enabled" .= enabled
      , "order" .= order
      , "size" .= size
      , "detail" .= detail
      , "seed" .= seed
      ]

instance FromJSON RoughenEffect where
  parseJSON = withObject "RoughenEffect" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    order <- o .: "order"
    size <- o .: "size"
    detail <- o .: "detail"
    seed <- o .: "seed"
    if validateFinite order && validateFinite seed && validateNonNegative order
      then return (RoughenEffect id_ SplinePathEffectTypeRoughen enabled order size detail seed)
      else fail "RoughenEffect: order and seed must be finite, order must be non-negative"

-- | Wiggle Path Effect - animated jitter
data WigglePathEffect = WigglePathEffect
  { wigglePathEffectId :: Text
  , wigglePathEffectType :: SplinePathEffectType  -- "wiggle"
  , wigglePathEffectEnabled :: Bool
  , wigglePathEffectOrder :: Double  -- Execution order
  , wigglePathEffectSize :: AnimatableProperty Double
  , wigglePathEffectDetail :: AnimatableProperty Double
  , wigglePathEffectTemporalPhase :: AnimatableProperty Double  -- Animated offset for motion
  , wigglePathEffectSpatialPhase :: AnimatableProperty Double
  , wigglePathEffectCorrelation :: AnimatableProperty Double  -- 0-100%
  , wigglePathEffectSeed :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON WigglePathEffect where
  toJSON (WigglePathEffect id_ _ enabled order size detail temporalPhase spatialPhase correlation seed) =
    object
      [ "id" .= id_
      , "type" .= T.pack "wiggle"
      , "enabled" .= enabled
      , "order" .= order
      , "size" .= size
      , "detail" .= detail
      , "temporalPhase" .= temporalPhase
      , "spatialPhase" .= spatialPhase
      , "correlation" .= correlation
      , "seed" .= seed
      ]

instance FromJSON WigglePathEffect where
  parseJSON = withObject "WigglePathEffect" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    order <- o .: "order"
    size <- o .: "size"
    detail <- o .: "detail"
    temporalPhase <- o .: "temporalPhase"
    spatialPhase <- o .: "spatialPhase"
    correlation <- o .: "correlation"
    seed <- o .: "seed"
    if validateFinite order && validateFinite seed && validateNonNegative order
      then return (WigglePathEffect id_ SplinePathEffectTypeWiggle enabled order size detail temporalPhase spatialPhase correlation seed)
      else fail "WigglePathEffect: order and seed must be finite, order must be non-negative"

-- | ZigZag Effect - decorative zigzag pattern
data ZigZagEffect = ZigZagEffect
  { zigZagEffectId :: Text
  , zigZagEffectType :: SplinePathEffectType  -- "zigzag"
  , zigZagEffectEnabled :: Bool
  , zigZagEffectOrder :: Double  -- Execution order
  , zigZagEffectSize :: AnimatableProperty Double
  , zigZagEffectRidgesPerSegment :: AnimatableProperty Double
  , zigZagEffectPointType :: ZigZagPointType
  }
  deriving (Eq, Show, Generic)

instance ToJSON ZigZagEffect where
  toJSON (ZigZagEffect id_ _ enabled order size ridgesPerSegment pointType) =
    object
      [ "id" .= id_
      , "type" .= T.pack "zigzag"
      , "enabled" .= enabled
      , "order" .= order
      , "size" .= size
      , "ridgesPerSegment" .= ridgesPerSegment
      , "pointType" .= pointType
      ]

instance FromJSON ZigZagEffect where
  parseJSON = withObject "ZigZagEffect" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    order <- o .: "order"
    size <- o .: "size"
    ridgesPerSegment <- o .: "ridgesPerSegment"
    pointType <- o .: "pointType"
    if validateFinite order && validateNonNegative order
      then return (ZigZagEffect id_ SplinePathEffectTypeZigzag enabled order size ridgesPerSegment pointType)
      else fail "ZigZagEffect: order must be finite and non-negative"

-- | Wave Effect - sine/triangle/square wave distortion
data WaveEffect = WaveEffect
  { waveEffectId :: Text
  , waveEffectType :: SplinePathEffectType  -- "wave"
  , waveEffectEnabled :: Bool
  , waveEffectOrder :: Double  -- Execution order
  , waveEffectAmplitude :: AnimatableProperty Double
  , waveEffectFrequency :: AnimatableProperty Double
  , waveEffectPhase :: AnimatableProperty Double  -- Animated phase for wave motion
  , waveEffectWaveType :: WaveType
  }
  deriving (Eq, Show, Generic)

instance ToJSON WaveEffect where
  toJSON (WaveEffect id_ _ enabled order amplitude frequency phase waveType) =
    object
      [ "id" .= id_
      , "type" .= T.pack "wave"
      , "enabled" .= enabled
      , "order" .= order
      , "amplitude" .= amplitude
      , "frequency" .= frequency
      , "phase" .= phase
      , "waveType" .= waveType
      ]

instance FromJSON WaveEffect where
  parseJSON = withObject "WaveEffect" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    order <- o .: "order"
    amplitude <- o .: "amplitude"
    frequency <- o .: "frequency"
    phase <- o .: "phase"
    waveType <- o .: "waveType"
    if validateFinite order && validateNonNegative order
      then return (WaveEffect id_ SplinePathEffectTypeWave enabled order amplitude frequency phase waveType)
      else fail "WaveEffect: order must be finite and non-negative"

-- | Union type for all path effects
data SplinePathEffectInstance
  = SplinePathEffectInstanceOffsetPath OffsetPathEffect
  | SplinePathEffectInstanceRoughen RoughenEffect
  | SplinePathEffectInstanceWiggle WigglePathEffect
  | SplinePathEffectInstanceZigzag ZigZagEffect
  | SplinePathEffectInstanceWave WaveEffect
  deriving (Eq, Show, Generic)

instance ToJSON SplinePathEffectInstance where
  toJSON (SplinePathEffectInstanceOffsetPath e) = toJSON e
  toJSON (SplinePathEffectInstanceRoughen e) = toJSON e
  toJSON (SplinePathEffectInstanceWiggle e) = toJSON e
  toJSON (SplinePathEffectInstanceZigzag e) = toJSON e
  toJSON (SplinePathEffectInstanceWave e) = toJSON e

instance FromJSON SplinePathEffectInstance where
  parseJSON = withObject "SplinePathEffectInstance" $ \o -> do
    effectType <- o .: "type" :: Parser Text
    case effectType of
      "offsetPath" -> do
        e <- parseJSON (Object o)
        return (SplinePathEffectInstanceOffsetPath e)
      "roughen" -> do
        e <- parseJSON (Object o)
        return (SplinePathEffectInstanceRoughen e)
      "wiggle" -> do
        e <- parseJSON (Object o)
        return (SplinePathEffectInstanceWiggle e)
      "zigzag" -> do
        e <- parseJSON (Object o)
        return (SplinePathEffectInstanceZigzag e)
      "wave" -> do
        e <- parseJSON (Object o)
        return (SplinePathEffectInstanceWave e)
      _ -> fail "Invalid SplinePathEffectInstance type"

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // level // of // detail
-- ════════════════════════════════════════════════════════════════════════════

-- | LOD mode
data SplineLODMode
  = SplineLODModeZoom
  | SplineLODModePlayback
  | SplineLODModeBoth
  deriving (Eq, Show, Generic)

instance ToJSON SplineLODMode where
  toJSON SplineLODModeZoom = toJSON (T.pack "zoom")
  toJSON SplineLODModePlayback = toJSON (T.pack "playback")
  toJSON SplineLODModeBoth = toJSON (T.pack "both")

instance FromJSON SplineLODMode where
  parseJSON = withText "SplineLODMode" $ \s ->
    case s of
      "zoom" -> return SplineLODModeZoom
      "playback" -> return SplineLODModePlayback
      "both" -> return SplineLODModeBoth
      _ -> fail "Invalid SplineLODMode"

-- | Single LOD level with pre-simplified points
data LODLevel = LODLevel
  { lodLevelTolerance :: Double
  , lodLevelControlPoints :: [ControlPoint]
  , lodLevelPointCount :: Double
  , lodLevelQuality :: Maybe Double  -- Quality index (0 = highest, higher = more simplified)
  , lodLevelComplexity :: Maybe Double  -- Complexity metric for this level
  }
  deriving (Eq, Show, Generic)

instance ToJSON LODLevel where
  toJSON (LODLevel tolerance controlPoints pointCount mQuality mComplexity) =
    let
      baseFields = ["tolerance" .= tolerance, "controlPoints" .= controlPoints, "pointCount" .= pointCount]
      withQuality = case mQuality of Just q -> ("quality" .= q) : baseFields; Nothing -> baseFields
      withComplexity = case mComplexity of Just c -> ("complexity" .= c) : withQuality; Nothing -> withQuality
    in object withComplexity

instance FromJSON LODLevel where
  parseJSON = withObject "LODLevel" $ \o -> do
    tolerance <- o .: "tolerance"
    controlPoints <- o .: "controlPoints"
    pointCount <- o .: "pointCount"
    mQuality <- o .:? "quality"
    mComplexity <- o .:? "complexity"
    if validateFinite tolerance && validateFinite pointCount &&
       validateNonNegative tolerance && validateNonNegative pointCount &&
       maybe True (\q -> validateFinite q && validateNonNegative q) mQuality &&
       maybe True (\c -> validateFinite c && validateNonNegative c) mComplexity
      then return (LODLevel tolerance controlPoints pointCount mQuality mComplexity)
      else fail "LODLevel: numeric values must be finite and non-negative"

-- | Level of Detail settings for complex vectors
data SplineLODSettings = SplineLODSettings
  { splineLODSettingsEnabled :: Bool
  , splineLODSettingsMode :: SplineLODMode
  , splineLODSettingsLevels :: [LODLevel]
  , splineLODSettingsMaxPointsForPreview :: Double
  , splineLODSettingsSimplificationTolerance :: Double
  , splineLODSettingsCullingEnabled :: Bool
  , splineLODSettingsCullMargin :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineLODSettings where
  toJSON (SplineLODSettings enabled mode levels maxPoints tolerance cullingEnabled cullMargin) =
    object
      [ "enabled" .= enabled
      , "mode" .= mode
      , "levels" .= levels
      , "maxPointsForPreview" .= maxPoints
      , "simplificationTolerance" .= tolerance
      , "cullingEnabled" .= cullingEnabled
      , "cullMargin" .= cullMargin
      ]

instance FromJSON SplineLODSettings where
  parseJSON = withObject "SplineLODSettings" $ \o -> do
    enabled <- o .: "enabled"
    mode <- o .: "mode"
    levels <- o .: "levels"
    maxPoints <- o .: "maxPointsForPreview"
    tolerance <- o .: "simplificationTolerance"
    cullingEnabled <- o .: "cullingEnabled"
    cullMargin <- o .: "cullMargin"
    if validateFinite maxPoints && validateFinite tolerance && validateFinite cullMargin &&
       validateNonNegative maxPoints && validateNonNegative tolerance && validateNonNegative cullMargin
      then return (SplineLODSettings enabled mode levels maxPoints tolerance cullingEnabled cullMargin)
      else fail "SplineLODSettings: numeric values must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // audio // reactive
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio-reactive animation configuration
data SplineAudioReactive = SplineAudioReactive
  { splineAudioReactiveEnabled :: Bool
  , splineAudioReactiveSourceLayerId :: Text  -- ID of audio layer to react to
  , splineAudioReactiveProperty :: Text  -- Property to animate (e.g., 'scale', 'opacity')
  , splineAudioReactiveMultiplier :: Double  -- Amplitude multiplier
  , splineAudioReactiveSmoothing :: Double  -- Frames of smoothing
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplineAudioReactive where
  toJSON (SplineAudioReactive enabled sourceLayerId property multiplier smoothing) =
    object
      [ "enabled" .= enabled
      , "sourceLayerId" .= sourceLayerId
      , "property" .= property
      , "multiplier" .= multiplier
      , "smoothing" .= smoothing
      ]

instance FromJSON SplineAudioReactive where
  parseJSON = withObject "SplineAudioReactive" $ \o -> do
    enabled <- o .: "enabled"
    sourceLayerId <- o .: "sourceLayerId"
    property <- o .: "property"
    multiplier <- o .: "multiplier"
    smoothing <- o .: "smoothing"
    if validateFinite multiplier && validateFinite smoothing &&
       validateNonNegative multiplier && validateNonNegative smoothing
      then return (SplineAudioReactive enabled sourceLayerId property multiplier smoothing)
      else fail "SplineAudioReactive: multiplier and smoothing must be finite and non-negative"
