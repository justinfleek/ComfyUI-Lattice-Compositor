-- |
-- Module      : Lattice.Types.LayerDataShapes
-- Description : Shape layer data types
-- 
-- Migrated from ui/src/types/shapes.ts
-- These types depend heavily on AnimatableProperty and Vec2
-- This is a large cohesive module for the entire shape system
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataShapes
  ( -- Main type
    ShapeLayerData(..)
  , ShapeQuality(..)
  -- Base types
  , Point2D(..)
  , BezierVertex(..)
  , BezierPath(..)
  , ShapeColor(..)
  , GradientStop(..)
  , GradientDef(..)
  , GradientType(..)
  -- Shape content union
  , ShapeContent(..)
  , NonGroupShapeContent(..)
  -- Shape generators
  , RectangleShape(..)
  , EllipseShape(..)
  , PolygonShape(..)
  , StarShape(..)
  , PathShape(..)
  , ShapeDirection(..)
  -- Shape modifiers
  , FillShape(..)
  , StrokeShape(..)
  , GradientFillShape(..)
  , GradientStrokeShape(..)
  , FillRule(..)
  , LineCap(..)
  , LineJoin(..)
  -- Path operators
  , TrimPathsOperator(..)
  , TrimMode(..)
  , MergePathsOperator(..)
  , MergeMode(..)
  , OffsetPathsOperator(..)
  , OffsetJoin(..)
  , PuckerBloatOperator(..)
  , WigglePathsOperator(..)
  , WigglePointType(..)
  , ZigZagOperator(..)
  , ZigZagPointType(..)
  , TwistOperator(..)
  , RoundedCornersOperator(..)
  -- Transform and repeater
  , ShapeTransform(..)
  , RepeaterOperator(..)
  , RepeaterComposite(..)
  , RepeaterTransform(..)
  -- Shape group
  , ShapeGroup(..)
  -- Illustrator operators
  , SimplifyPathOperator(..)
  , SmoothPathOperator(..)
  , ExtrudeOperator(..)
  , ExtrudeCapType(..)
  , ExtrudeMaterial(..)
  , TraceOperator(..)
  , TraceMode(..)
  -- Validation functions
  , validateGradientStopsSorted
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
import Data.Aeson.Key (fromString)
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
import Lattice.Schema.SharedValidation
  ( validateBoundedArray
  )
import qualified Data.Text as T

-- ============================================================================
-- VALIDATION FUNCTIONS
-- ============================================================================

-- | Validate that gradient stops are sorted by position (non-decreasing)
-- Matches Zod schema refinement: "stops must be sorted by position"
validateGradientStopsSorted :: [GradientStop] -> Bool
validateGradientStopsSorted [] = True
validateGradientStopsSorted [_] = True
validateGradientStopsSorted (s1:s2:ss) =
  gradientStopPosition s2 >= gradientStopPosition s1 &&
  validateGradientStopsSorted (s2:ss)

-- ============================================================================
-- BASE TYPES
-- ============================================================================

-- | 2D Point
data Point2D = Point2D
  { point2DX :: Double
  , point2DY :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Point2D where
  toJSON (Point2D x y) =
    object ["x" .= x, "y" .= y]

instance FromJSON Point2D where
  parseJSON = withObject "Point2D" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    if validateFinite x && validateFinite y
      then return (Point2D x y)
      else fail "Point2D: x and y must be finite"

-- | Bezier control point with handles
data BezierVertex = BezierVertex
  { bezierVertexPoint :: Point2D
  , bezierVertexInHandle :: Point2D  -- Relative to point
  , bezierVertexOutHandle :: Point2D  -- Relative to point
  }
  deriving (Eq, Show, Generic)

instance ToJSON BezierVertex where
  toJSON (BezierVertex point inHandle outHandle) =
    object
      [ "point" .= point
      , "inHandle" .= inHandle
      , "outHandle" .= outHandle
      ]

instance FromJSON BezierVertex where
  parseJSON = withObject "BezierVertex" $ \o -> do
    point <- o .: "point"
    inHandle <- o .: "inHandle"
    outHandle <- o .: "outHandle"
    return (BezierVertex point inHandle outHandle)

-- | A bezier path (can be open or closed)
data BezierPath = BezierPath
  { bezierPathVertices :: [BezierVertex]
  , bezierPathClosed :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON BezierPath where
  toJSON (BezierPath vertices closed) =
    object
      [ "vertices" .= vertices
      , "closed" .= closed
      ]

instance FromJSON BezierPath where
  parseJSON = withObject "BezierPath" $ \o -> do
    verticesRaw <- o .: "vertices"
    closed <- o .: "closed"
    -- Validate max 100,000 vertices per path (matches Zod schema)
    vertices <- case validateBoundedArray 100000 verticesRaw of
      Left err -> fail (T.unpack err)
      Right vs ->
        -- Closed paths must have at least 3 vertices (matches Zod schema)
        if closed && length vs < 3
          then fail "Closed paths must have at least 3 vertices"
          else return vs
    return (BezierPath vertices closed)

-- | Color with alpha
data ShapeColor = ShapeColor
  { shapeColorR :: Double  -- 0-255
  , shapeColorG :: Double
  , shapeColorB :: Double
  , shapeColorA :: Double  -- 0-1
  }
  deriving (Eq, Show, Generic)

instance ToJSON ShapeColor where
  toJSON (ShapeColor r g b a) =
    object ["r" .= r, "g" .= g, "b" .= b, "a" .= a]

instance FromJSON ShapeColor where
  parseJSON = withObject "ShapeColor" $ \o -> do
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    a <- o .: "a"
    if validateFinite r && validateFinite g && validateFinite b && validateFinite a &&
       validateNonNegative r && validateNonNegative g && validateNonNegative b &&
       validateNormalized01 a && r <= 255 && g <= 255 && b <= 255
      then return (ShapeColor r g b a)
      else fail "ShapeColor: r, g, b must be in [0,255], a must be in [0,1]"

-- | Gradient stop
data GradientStop = GradientStop
  { gradientStopPosition :: Double  -- 0-1
  , gradientStopColor :: ShapeColor
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientStop where
  toJSON (GradientStop position color) =
    object ["position" .= position, "color" .= color]

instance FromJSON GradientStop where
  parseJSON = withObject "GradientStop" $ \o -> do
    position <- o .: "position"
    color <- o .: "color"
    if validateNormalized01 position
      then return (GradientStop position color)
      else fail "GradientStop: position must be in [0,1]"

-- | Gradient type
data GradientType
  = GradientTypeLinear
  | GradientTypeRadial
  deriving (Eq, Show, Generic)

instance ToJSON GradientType where
  toJSON GradientTypeLinear = "linear"
  toJSON GradientTypeRadial = "radial"

instance FromJSON GradientType where
  parseJSON = withText "GradientType" $ \s ->
    case s of
      t | t == T.pack "linear" -> return GradientTypeLinear
      t | t == T.pack "radial" -> return GradientTypeRadial
      _ -> fail "Invalid GradientType"

-- | Gradient definition
data GradientDef = GradientDef
  { gradientDefType :: GradientType
  , gradientDefStops :: [GradientStop]
  , gradientDefStartPoint :: Point2D  -- Normalized 0-1
  , gradientDefEndPoint :: Point2D  -- For linear: end point, for radial: edge point
  , gradientDefHighlightLength :: Maybe Double  -- Radial only: 0-100
  , gradientDefHighlightAngle :: Maybe Double  -- Radial only: degrees
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientDef where
  toJSON (GradientDef gType stops startPoint endPoint mHighlightLength mHighlightAngle) =
    let
      baseFields = ["type" .= gType, "stops" .= stops, "startPoint" .= startPoint, "endPoint" .= endPoint]
      withHighlightLength = case mHighlightLength of Just l -> ("highlightLength" .= l) : baseFields; Nothing -> baseFields
      withHighlightAngle = case mHighlightAngle of Just a -> ("highlightAngle" .= a) : withHighlightLength; Nothing -> withHighlightLength
    in object withHighlightAngle

instance FromJSON GradientDef where
  parseJSON = withObject "GradientDef" $ \o -> do
    gType <- o .: "type"
    stopsRaw <- o .: "stops"
    startPoint <- o .: "startPoint"
    endPoint <- o .: "endPoint"
    mHighlightLength <- o .:? "highlightLength"
    mHighlightAngle <- o .:? "highlightAngle"
    -- Validate max 100 stops per gradient (matches Zod schema)
    stops <- case validateBoundedArray 100 stopsRaw of
      Left err -> fail (T.unpack err)
      Right sts ->
        -- Must have at least 2 stops (matches Zod schema)
        if length sts < 2
          then fail "Gradient must have at least 2 stops"
          else
            -- Stops must be sorted by position (matches Zod schema)
            if validateGradientStopsSorted sts
              then return sts
              else fail "Gradient stops must be sorted by position"
    if validateNormalized01 (point2DX startPoint) && validateNormalized01 (point2DY startPoint) &&
       validateNormalized01 (point2DX endPoint) && validateNormalized01 (point2DY endPoint) &&
       maybe True (\l -> validateFinite l && validateNormalized01 (l / 100)) mHighlightLength &&
       maybe True (\a -> validateFinite a) mHighlightAngle
      then return (GradientDef gType stops startPoint endPoint mHighlightLength mHighlightAngle)
      else fail "GradientDef: startPoint and endPoint must be normalized [0,1], highlightLength must be in [0,100]"

-- ============================================================================
-- SHAPE GENERATORS
-- ============================================================================

-- | Shape direction
data ShapeDirection
  = ShapeDirectionClockwise  -- 1
  | ShapeDirectionCounterClockwise  -- -1
  deriving (Eq, Show, Generic)

instance ToJSON ShapeDirection where
  toJSON ShapeDirectionClockwise = toJSON (1 :: Int)
  toJSON ShapeDirectionCounterClockwise = toJSON (-1 :: Int)

instance FromJSON ShapeDirection where
  parseJSON v = do
    n <- (parseJSON v :: Parser Int)
    case n of
      1 -> return ShapeDirectionClockwise
      (-1) -> return ShapeDirectionCounterClockwise
      _ -> fail "ShapeDirection must be 1 or -1"

-- | Rectangle shape
data RectangleShape = RectangleShape
  { rectangleShapeType :: Text  -- "rectangle"
  , rectangleShapeName :: Text
  , rectangleShapePosition :: AnimatableProperty Point2D
  , rectangleShapeSize :: AnimatableProperty Point2D
  , rectangleShapeRoundness :: AnimatableProperty Double  -- Corner radius in pixels
  , rectangleShapeDirection :: ShapeDirection
  }
  deriving (Eq, Show, Generic)

instance ToJSON RectangleShape where
  toJSON (RectangleShape _ name position size roundness direction) =
    object
      [ "type" .= ("rectangle" :: Text)
      , "name" .= name
      , "position" .= position
      , "size" .= size
      , "roundness" .= roundness
      , "direction" .= direction
      ]

instance FromJSON RectangleShape where
  parseJSON = withObject "RectangleShape" $ \o -> do
    name <- o .: "name"
    position <- o .: "position"
    size <- o .: "size"
    roundness <- o .: "roundness"
    direction <- o .: "direction"
    return (RectangleShape "rectangle" name position size roundness direction)

-- | Ellipse shape
data EllipseShape = EllipseShape
  { ellipseShapeType :: Text  -- "ellipse"
  , ellipseShapeName :: Text
  , ellipseShapePosition :: AnimatableProperty Point2D
  , ellipseShapeSize :: AnimatableProperty Point2D
  , ellipseShapeDirection :: ShapeDirection
  }
  deriving (Eq, Show, Generic)

instance ToJSON EllipseShape where
  toJSON (EllipseShape _ name position size direction) =
    object
      [ "type" .= ("ellipse" :: Text)
      , "name" .= name
      , "position" .= position
      , "size" .= size
      , "direction" .= direction
      ]

instance FromJSON EllipseShape where
  parseJSON = withObject "EllipseShape" $ \o -> do
    name <- o .: "name"
    position <- o .: "position"
    size <- o .: "size"
    direction <- o .: "direction"
    return (EllipseShape "ellipse" name position size direction)

-- | Polygon shape
data PolygonShape = PolygonShape
  { polygonShapeType :: Text  -- "polygon"
  , polygonShapeName :: Text
  , polygonShapePosition :: AnimatableProperty Point2D
  , polygonShapePoints :: AnimatableProperty Double  -- Number of sides (3+)
  , polygonShapeOuterRadius :: AnimatableProperty Double
  , polygonShapeOuterRoundness :: AnimatableProperty Double  -- 0-100%
  , polygonShapeRotation :: AnimatableProperty Double  -- Degrees
  , polygonShapeDirection :: ShapeDirection
  }
  deriving (Eq, Show, Generic)

instance ToJSON PolygonShape where
  toJSON (PolygonShape _ name position points outerRadius outerRoundness rotation direction) =
    object
      [ "type" .= ("polygon" :: Text)
      , "name" .= name
      , "position" .= position
      , "points" .= points
      , "outerRadius" .= outerRadius
      , "outerRoundness" .= outerRoundness
      , "rotation" .= rotation
      , "direction" .= direction
      ]

instance FromJSON PolygonShape where
  parseJSON = withObject "PolygonShape" $ \o -> do
    name <- o .: "name"
    position <- o .: "position"
    points <- o .: "points"
    outerRadius <- o .: "outerRadius"
    outerRoundness <- o .: "outerRoundness"
    rotation <- o .: "rotation"
    direction <- o .: "direction"
    return (PolygonShape "polygon" name position points outerRadius outerRoundness rotation direction)

-- | Star shape
data StarShape = StarShape
  { starShapeType :: Text  -- "star"
  , starShapeName :: Text
  , starShapePosition :: AnimatableProperty Point2D
  , starShapePoints :: AnimatableProperty Double  -- Number of points (3+)
  , starShapeOuterRadius :: AnimatableProperty Double
  , starShapeInnerRadius :: AnimatableProperty Double
  , starShapeOuterRoundness :: AnimatableProperty Double  -- 0-100%
  , starShapeInnerRoundness :: AnimatableProperty Double  -- 0-100%
  , starShapeRotation :: AnimatableProperty Double
  , starShapeDirection :: ShapeDirection
  }
  deriving (Eq, Show, Generic)

instance ToJSON StarShape where
  toJSON (StarShape _ name position points outerRadius innerRadius outerRoundness innerRoundness rotation direction) =
    object
      [ "type" .= ("star" :: Text)
      , "name" .= name
      , "position" .= position
      , "points" .= points
      , "outerRadius" .= outerRadius
      , "innerRadius" .= innerRadius
      , "outerRoundness" .= outerRoundness
      , "innerRoundness" .= innerRoundness
      , "rotation" .= rotation
      , "direction" .= direction
      ]

instance FromJSON StarShape where
  parseJSON = withObject "StarShape" $ \o -> do
    name <- o .: "name"
    position <- o .: "position"
    points <- o .: "points"
    outerRadius <- o .: "outerRadius"
    innerRadius <- o .: "innerRadius"
    outerRoundness <- o .: "outerRoundness"
    innerRoundness <- o .: "innerRoundness"
    rotation <- o .: "rotation"
    direction <- o .: "direction"
    return (StarShape "star" name position points outerRadius innerRadius outerRoundness innerRoundness rotation direction)

-- | Path shape
data PathShape = PathShape
  { pathShapeType :: Text  -- "path"
  , pathShapeName :: Text
  , pathShapePath :: AnimatableProperty BezierPath
  , pathShapeDirection :: ShapeDirection
  }
  deriving (Eq, Show, Generic)

instance ToJSON PathShape where
  toJSON (PathShape _ name path direction) =
    object
      [ "type" .= ("path" :: Text)
      , "name" .= name
      , "path" .= path
      , "direction" .= direction
      ]

instance FromJSON PathShape where
  parseJSON = withObject "PathShape" $ \o -> do
    name <- o .: "name"
    path <- o .: "path"
    direction <- o .: "direction"
    return (PathShape "path" name path direction)

-- ============================================================================
-- SHAPE MODIFIERS
-- ============================================================================

-- | Fill rule
data FillRule
  = FillRuleNonzero
  | FillRuleEvenodd
  deriving (Eq, Show, Generic)

instance ToJSON FillRule where
  toJSON FillRuleNonzero = "nonzero"
  toJSON FillRuleEvenodd = "evenodd"

instance FromJSON FillRule where
  parseJSON = withText "FillRule" $ \s ->
    case s of
      t | t == T.pack "nonzero" -> return FillRuleNonzero
      t | t == T.pack "evenodd" -> return FillRuleEvenodd
      _ -> fail "Invalid FillRule"

-- | Line cap
data LineCap
  = LineCapButt
  | LineCapRound
  | LineCapSquare
  deriving (Eq, Show, Generic)

instance ToJSON LineCap where
  toJSON LineCapButt = "butt"
  toJSON LineCapRound = "round"
  toJSON LineCapSquare = "square"

instance FromJSON LineCap where
  parseJSON = withText "LineCap" $ \s ->
    case s of
      t | t == T.pack "butt" -> return LineCapButt
      t | t == T.pack "round" -> return LineCapRound
      t | t == T.pack "square" -> return LineCapSquare
      _ -> fail "Invalid LineCap"

-- | Line join
data LineJoin
  = LineJoinMiter
  | LineJoinRound
  | LineJoinBevel
  deriving (Eq, Show, Generic)

instance ToJSON LineJoin where
  toJSON LineJoinMiter = "miter"
  toJSON LineJoinRound = "round"
  toJSON LineJoinBevel = "bevel"

instance FromJSON LineJoin where
  parseJSON = withText "LineJoin" $ \s ->
    case s of
      t | t == T.pack "miter" -> return LineJoinMiter
      t | t == T.pack "round" -> return LineJoinRound
      t | t == T.pack "bevel" -> return LineJoinBevel
      _ -> fail "Invalid LineJoin"

-- | Fill shape
data FillShape = FillShape
  { fillShapeType :: Text  -- "fill"
  , fillShapeName :: Text
  , fillShapeColor :: AnimatableProperty ShapeColor
  , fillShapeOpacity :: AnimatableProperty Double  -- 0-100
  , fillShapeFillRule :: FillRule
  , fillShapeBlendMode :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON FillShape where
  toJSON (FillShape _ name color opacity fillRule blendMode) =
    object
      [ "type" .= ("fill" :: Text)
      , "name" .= name
      , "color" .= color
      , "opacity" .= opacity
      , "fillRule" .= fillRule
      , "blendMode" .= blendMode
      ]

instance FromJSON FillShape where
  parseJSON = withObject "FillShape" $ \o -> do
    name <- o .: "name"
    color <- o .: "color"
    opacity <- o .: "opacity"
    fillRule <- o .: "fillRule"
    blendMode <- o .: "blendMode"
    return (FillShape "fill" name color opacity fillRule blendMode)

-- | Stroke shape
data StrokeShape = StrokeShape
  { strokeShapeType :: Text  -- "stroke"
  , strokeShapeName :: Text
  , strokeShapeColor :: AnimatableProperty ShapeColor
  , strokeShapeOpacity :: AnimatableProperty Double  -- 0-100
  , strokeShapeWidth :: AnimatableProperty Double
  , strokeShapeLineCap :: LineCap
  , strokeShapeLineJoin :: LineJoin
  , strokeShapeMiterLimit :: Double
  , strokeShapeDashPattern :: AnimatableProperty [Double]  -- [dash, gap, dash, gap, ...]
  , strokeShapeDashOffset :: AnimatableProperty Double
  , strokeShapeBlendMode :: Text
  , strokeShapeTaperEnabled :: Bool
  , strokeShapeTaperStartLength :: AnimatableProperty Double  -- 0-100%
  , strokeShapeTaperEndLength :: AnimatableProperty Double
  , strokeShapeTaperStartWidth :: AnimatableProperty Double  -- 0-100%
  , strokeShapeTaperEndWidth :: AnimatableProperty Double
  , strokeShapeTaperStartEase :: AnimatableProperty Double  -- 0-100%
  , strokeShapeTaperEndEase :: AnimatableProperty Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON StrokeShape where
  toJSON (StrokeShape _ name color opacity width lineCap lineJoin miterLimit dashPattern dashOffset blendMode taperEnabled taperStartLength taperEndLength taperStartWidth taperEndWidth taperStartEase taperEndEase) =
    object
      [ "type" .= ("stroke" :: Text)
      , "name" .= name
      , "color" .= color
      , "opacity" .= opacity
      , "width" .= width
      , "lineCap" .= lineCap
      , "lineJoin" .= lineJoin
      , "miterLimit" .= miterLimit
      , "dashPattern" .= dashPattern
      , "dashOffset" .= dashOffset
      , "blendMode" .= blendMode
      , "taperEnabled" .= taperEnabled
      , "taperStartLength" .= taperStartLength
      , "taperEndLength" .= taperEndLength
      , "taperStartWidth" .= taperStartWidth
      , "taperEndWidth" .= taperEndWidth
      , "taperStartEase" .= taperStartEase
      , "taperEndEase" .= taperEndEase
      ]

instance FromJSON StrokeShape where
  parseJSON = withObject "StrokeShape" $ \o -> do
    name <- o .: "name"
    color <- o .: "color"
    opacity <- o .: "opacity"
    width <- o .: "width"
    lineCap <- o .: "lineCap"
    lineJoin <- o .: "lineJoin"
    miterLimit <- o .: "miterLimit"
    dashPattern <- o .: "dashPattern"
    dashOffset <- o .: "dashOffset"
    blendMode <- o .: "blendMode"
    taperEnabled <- o .: "taperEnabled"
    taperStartLength <- o .: "taperStartLength"
    taperEndLength <- o .: "taperEndLength"
    taperStartWidth <- o .: "taperStartWidth"
    taperEndWidth <- o .: "taperEndWidth"
    taperStartEase <- o .: "taperStartEase"
    taperEndEase <- o .: "taperEndEase"
    if validateFinite miterLimit && validateNonNegative miterLimit
      then return (StrokeShape "stroke" name color opacity width lineCap lineJoin miterLimit dashPattern dashOffset blendMode taperEnabled taperStartLength taperEndLength taperStartWidth taperEndWidth taperStartEase taperEndEase)
      else fail "StrokeShape: miterLimit must be finite and non-negative"

-- | Gradient fill shape
data GradientFillShape = GradientFillShape
  { gradientFillShapeType :: Text  -- "gradientFill"
  , gradientFillShapeName :: Text
  , gradientFillShapeGradient :: AnimatableProperty GradientDef
  , gradientFillShapeOpacity :: AnimatableProperty Double
  , gradientFillShapeFillRule :: FillRule
  , gradientFillShapeBlendMode :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientFillShape where
  toJSON (GradientFillShape _ name gradient opacity fillRule blendMode) =
    object
      [ "type" .= ("gradientFill" :: Text)
      , "name" .= name
      , "gradient" .= gradient
      , "opacity" .= opacity
      , "fillRule" .= fillRule
      , "blendMode" .= blendMode
      ]

instance FromJSON GradientFillShape where
  parseJSON = withObject "GradientFillShape" $ \o -> do
    name <- o .: "name"
    gradient <- o .: "gradient"
    opacity <- o .: "opacity"
    fillRule <- o .: "fillRule"
    blendMode <- o .: "blendMode"
    return (GradientFillShape "gradientFill" name gradient opacity fillRule blendMode)

-- | Gradient stroke shape
data GradientStrokeShape = GradientStrokeShape
  { gradientStrokeShapeType :: Text  -- "gradientStroke"
  , gradientStrokeShapeName :: Text
  , gradientStrokeShapeGradient :: AnimatableProperty GradientDef
  , gradientStrokeShapeOpacity :: AnimatableProperty Double
  , gradientStrokeShapeWidth :: AnimatableProperty Double
  , gradientStrokeShapeLineCap :: LineCap
  , gradientStrokeShapeLineJoin :: LineJoin
  , gradientStrokeShapeMiterLimit :: Double
  , gradientStrokeShapeDashPattern :: AnimatableProperty [Double]
  , gradientStrokeShapeDashOffset :: AnimatableProperty Double
  , gradientStrokeShapeBlendMode :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientStrokeShape where
  toJSON (GradientStrokeShape _ name gradient opacity width lineCap lineJoin miterLimit dashPattern dashOffset blendMode) =
    object
      [ "type" .= ("gradientStroke" :: Text)
      , "name" .= name
      , "gradient" .= gradient
      , "opacity" .= opacity
      , "width" .= width
      , "lineCap" .= lineCap
      , "lineJoin" .= lineJoin
      , "miterLimit" .= miterLimit
      , "dashPattern" .= dashPattern
      , "dashOffset" .= dashOffset
      , "blendMode" .= blendMode
      ]

instance FromJSON GradientStrokeShape where
  parseJSON = withObject "GradientStrokeShape" $ \o -> do
    name <- o .: "name"
    gradient <- o .: "gradient"
    opacity <- o .: "opacity"
    width <- o .: "width"
    lineCap <- o .: "lineCap"
    lineJoin <- o .: "lineJoin"
    miterLimit <- o .: "miterLimit"
    dashPattern <- o .: "dashPattern"
    dashOffset <- o .: "dashOffset"
    blendMode <- o .: "blendMode"
    if validateFinite miterLimit && validateNonNegative miterLimit
      then return (GradientStrokeShape "gradientStroke" name gradient opacity width lineCap lineJoin miterLimit dashPattern dashOffset blendMode)
      else fail "GradientStrokeShape: miterLimit must be finite and non-negative"

-- ============================================================================
-- PATH OPERATORS
-- ============================================================================

-- | Trim mode
data TrimMode
  = TrimModeSimultaneously
  | TrimModeIndividually
  deriving (Eq, Show, Generic)

instance ToJSON TrimMode where
  toJSON TrimModeSimultaneously = "simultaneously"
  toJSON TrimModeIndividually = "individually"

instance FromJSON TrimMode where
  parseJSON = withText "TrimMode" $ \s ->
    case s of
      t | t == T.pack "simultaneously" -> return TrimModeSimultaneously
      t | t == T.pack "individually" -> return TrimModeIndividually
      _ -> fail "Invalid TrimMode"

-- | Trim paths operator
data TrimPathsOperator = TrimPathsOperator
  { trimPathsOperatorType :: Text  -- "trimPaths"
  , trimPathsOperatorName :: Text
  , trimPathsOperatorStart :: AnimatableProperty Double  -- 0-100%
  , trimPathsOperatorEnd :: AnimatableProperty Double  -- 0-100%
  , trimPathsOperatorOffset :: AnimatableProperty Double  -- Degrees (-360 to 360)
  , trimPathsOperatorMode :: TrimMode
  }
  deriving (Eq, Show, Generic)

instance ToJSON TrimPathsOperator where
  toJSON (TrimPathsOperator _ name start end offset mode) =
    object
      [ "type" .= ("trimPaths" :: Text)
      , "name" .= name
      , "start" .= start
      , "end" .= end
      , "offset" .= offset
      , "mode" .= mode
      ]

instance FromJSON TrimPathsOperator where
  parseJSON = withObject "TrimPathsOperator" $ \o -> do
    name <- o .: "name"
    start <- o .: "start"
    end <- o .: "end"
    offset <- o .: "offset"
    mode <- o .: "mode"
    return (TrimPathsOperator "trimPaths" name start end offset mode)

-- | Merge mode
data MergeMode
  = MergeModeAdd  -- Union
  | MergeModeSubtract  -- Minus Front
  | MergeModeIntersect  -- Intersection
  | MergeModeExclude  -- Exclude Intersection
  | MergeModeMinusFront  -- Same as subtract
  | MergeModeMinusBack  -- Minus Back (Illustrator)
  deriving (Eq, Show, Generic)

instance ToJSON MergeMode where
  toJSON MergeModeAdd = "add"
  toJSON MergeModeSubtract = "subtract"
  toJSON MergeModeIntersect = "intersect"
  toJSON MergeModeExclude = "exclude"
  toJSON MergeModeMinusFront = "minusFront"
  toJSON MergeModeMinusBack = "minusBack"

instance FromJSON MergeMode where
  parseJSON = withText "MergeMode" $ \s ->
    case s of
      t | t == T.pack "add" -> return MergeModeAdd
      t | t == T.pack "subtract" -> return MergeModeSubtract
      t | t == T.pack "intersect" -> return MergeModeIntersect
      t | t == T.pack "exclude" -> return MergeModeExclude
      t | t == T.pack "minusFront" -> return MergeModeMinusFront
      t | t == T.pack "minusBack" -> return MergeModeMinusBack
      _ -> fail "Invalid MergeMode"

-- | Merge paths operator
data MergePathsOperator = MergePathsOperator
  { mergePathsOperatorType :: Text  -- "mergePaths"
  , mergePathsOperatorName :: Text
  , mergePathsOperatorMode :: MergeMode
  }
  deriving (Eq, Show, Generic)

instance ToJSON MergePathsOperator where
  toJSON (MergePathsOperator _ name mode) =
    object
      [ "type" .= ("mergePaths" :: Text)
      , "name" .= name
      , "mode" .= mode
      ]

instance FromJSON MergePathsOperator where
  parseJSON = withObject "MergePathsOperator" $ \o -> do
    name <- o .: "name"
    mode <- o .: "mode"
    return (MergePathsOperator "mergePaths" name mode)

-- | Offset join
data OffsetJoin
  = OffsetJoinMiter
  | OffsetJoinRound
  | OffsetJoinBevel
  deriving (Eq, Show, Generic)

instance ToJSON OffsetJoin where
  toJSON OffsetJoinMiter = "miter"
  toJSON OffsetJoinRound = "round"
  toJSON OffsetJoinBevel = "bevel"

instance FromJSON OffsetJoin where
  parseJSON = withText "OffsetJoin" $ \s ->
    case s of
      t | t == T.pack "miter" -> return OffsetJoinMiter
      t | t == T.pack "round" -> return OffsetJoinRound
      t | t == T.pack "bevel" -> return OffsetJoinBevel
      _ -> fail "Invalid OffsetJoin"

-- | Offset paths operator
data OffsetPathsOperator = OffsetPathsOperator
  { offsetPathsOperatorType :: Text  -- "offsetPaths"
  , offsetPathsOperatorName :: Text
  , offsetPathsOperatorAmount :: AnimatableProperty Double  -- Positive = expand, negative = contract
  , offsetPathsOperatorLineJoin :: OffsetJoin
  , offsetPathsOperatorMiterLimit :: AnimatableProperty Double
  , offsetPathsOperatorCopies :: AnimatableProperty Double  -- AE: can create multiple offset copies
  , offsetPathsOperatorCopyOffset :: AnimatableProperty Double  -- Distance between copies
  }
  deriving (Eq, Show, Generic)

instance ToJSON OffsetPathsOperator where
  toJSON (OffsetPathsOperator _ name amount lineJoin miterLimit copies copyOffset) =
    object
      [ "type" .= ("offsetPaths" :: Text)
      , "name" .= name
      , "amount" .= amount
      , "lineJoin" .= lineJoin
      , "miterLimit" .= miterLimit
      , "copies" .= copies
      , "copyOffset" .= copyOffset
      ]

instance FromJSON OffsetPathsOperator where
  parseJSON = withObject "OffsetPathsOperator" $ \o -> do
    name <- o .: "name"
    amount <- o .: "amount"
    lineJoin <- o .: "lineJoin"
    miterLimit <- o .: "miterLimit"
    copies <- o .: "copies"
    copyOffset <- o .: "copyOffset"
    return (OffsetPathsOperator "offsetPaths" name amount lineJoin miterLimit copies copyOffset)

-- | Pucker bloat operator
data PuckerBloatOperator = PuckerBloatOperator
  { puckerBloatOperatorType :: Text  -- "puckerBloat"
  , puckerBloatOperatorName :: Text
  , puckerBloatOperatorAmount :: AnimatableProperty Double  -- -100 (pucker) to 100 (bloat)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PuckerBloatOperator where
  toJSON (PuckerBloatOperator _ name amount) =
    object
      [ "type" .= ("puckerBloat" :: Text)
      , "name" .= name
      , "amount" .= amount
      ]

instance FromJSON PuckerBloatOperator where
  parseJSON = withObject "PuckerBloatOperator" $ \o -> do
    name <- o .: "name"
    amount <- o .: "amount"
    return (PuckerBloatOperator "puckerBloat" name amount)

-- | Wiggle point type
data WigglePointType
  = WigglePointTypeCorner
  | WigglePointTypeSmooth
  deriving (Eq, Show, Generic)

instance ToJSON WigglePointType where
  toJSON WigglePointTypeCorner = "corner"
  toJSON WigglePointTypeSmooth = "smooth"

instance FromJSON WigglePointType where
  parseJSON = withText "WigglePointType" $ \s ->
    case s of
      t | t == T.pack "corner" -> return WigglePointTypeCorner
      t | t == T.pack "smooth" -> return WigglePointTypeSmooth
      _ -> fail "Invalid WigglePointType"

-- | Wiggle paths operator
data WigglePathsOperator = WigglePathsOperator
  { wigglePathsOperatorType :: Text  -- "wigglePaths"
  , wigglePathsOperatorName :: Text
  , wigglePathsOperatorSize :: AnimatableProperty Double  -- Wiggle magnitude
  , wigglePathsOperatorDetail :: AnimatableProperty Double  -- Segments per curve (1-10)
  , wigglePathsOperatorPoints :: WigglePointType
  , wigglePathsOperatorCorrelation :: AnimatableProperty Double  -- 0-100% how linked adjacent points are
  , wigglePathsOperatorTemporalPhase :: AnimatableProperty Double  -- Animation offset
  , wigglePathsOperatorSpatialPhase :: AnimatableProperty Double  -- Spatial offset
  , wigglePathsOperatorRandomSeed :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON WigglePathsOperator where
  toJSON (WigglePathsOperator _ name size detail points correlation temporalPhase spatialPhase randomSeed) =
    object
      [ "type" .= ("wigglePaths" :: Text)
      , "name" .= name
      , "size" .= size
      , "detail" .= detail
      , "points" .= points
      , "correlation" .= correlation
      , "temporalPhase" .= temporalPhase
      , "spatialPhase" .= spatialPhase
      , "randomSeed" .= randomSeed
      ]

instance FromJSON WigglePathsOperator where
  parseJSON = withObject "WigglePathsOperator" $ \o -> do
    name <- o .: "name"
    size <- o .: "size"
    detail <- o .: "detail"
    points <- o .: "points"
    correlation <- o .: "correlation"
    temporalPhase <- o .: "temporalPhase"
    spatialPhase <- o .: "spatialPhase"
    randomSeed <- o .: "randomSeed"
    if validateFinite randomSeed && validateNonNegative randomSeed
      then return (WigglePathsOperator "wigglePaths" name size detail points correlation temporalPhase spatialPhase randomSeed)
      else fail "WigglePathsOperator: randomSeed must be finite and non-negative"

-- | Zigzag point type
data ZigZagPointType
  = ZigZagPointTypeCorner
  | ZigZagPointTypeSmooth
  deriving (Eq, Show, Generic)

instance ToJSON ZigZagPointType where
  toJSON ZigZagPointTypeCorner = "corner"
  toJSON ZigZagPointTypeSmooth = "smooth"

instance FromJSON ZigZagPointType where
  parseJSON = withText "ZigZagPointType" $ \s ->
    case s of
      t | t == T.pack "corner" -> return ZigZagPointTypeCorner
      t | t == T.pack "smooth" -> return ZigZagPointTypeSmooth
      _ -> fail "Invalid ZigZagPointType"

-- | Zigzag operator
data ZigZagOperator = ZigZagOperator
  { zigZagOperatorType :: Text  -- "zigZag"
  , zigZagOperatorName :: Text
  , zigZagOperatorSize :: AnimatableProperty Double  -- Peak height
  , zigZagOperatorRidgesPerSegment :: AnimatableProperty Double  -- Zigzags per path segment
  , zigZagOperatorPoints :: ZigZagPointType
  }
  deriving (Eq, Show, Generic)

instance ToJSON ZigZagOperator where
  toJSON (ZigZagOperator _ name size ridgesPerSegment points) =
    object
      [ "type" .= ("zigZag" :: Text)
      , "name" .= name
      , "size" .= size
      , "ridgesPerSegment" .= ridgesPerSegment
      , "points" .= points
      ]

instance FromJSON ZigZagOperator where
  parseJSON = withObject "ZigZagOperator" $ \o -> do
    name <- o .: "name"
    size <- o .: "size"
    ridgesPerSegment <- o .: "ridgesPerSegment"
    points <- o .: "points"
    return (ZigZagOperator "zigZag" name size ridgesPerSegment points)

-- | Twist operator
data TwistOperator = TwistOperator
  { twistOperatorType :: Text  -- "twist"
  , twistOperatorName :: Text
  , twistOperatorAngle :: AnimatableProperty Double  -- Total twist in degrees
  , twistOperatorCenter :: AnimatableProperty Point2D
  }
  deriving (Eq, Show, Generic)

instance ToJSON TwistOperator where
  toJSON (TwistOperator _ name angle center) =
    object
      [ "type" .= ("twist" :: Text)
      , "name" .= name
      , "angle" .= angle
      , "center" .= center
      ]

instance FromJSON TwistOperator where
  parseJSON = withObject "TwistOperator" $ \o -> do
    name <- o .: "name"
    angle <- o .: "angle"
    center <- o .: "center"
    return (TwistOperator "twist" name angle center)

-- | Rounded corners operator
data RoundedCornersOperator = RoundedCornersOperator
  { roundedCornersOperatorType :: Text  -- "roundedCorners"
  , roundedCornersOperatorName :: Text
  , roundedCornersOperatorRadius :: AnimatableProperty Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON RoundedCornersOperator where
  toJSON (RoundedCornersOperator _ name radius) =
    object
      [ "type" .= ("roundedCorners" :: Text)
      , "name" .= name
      , "radius" .= radius
      ]

instance FromJSON RoundedCornersOperator where
  parseJSON = withObject "RoundedCornersOperator" $ \o -> do
    name <- o .: "name"
    radius <- o .: "radius"
    return (RoundedCornersOperator "roundedCorners" name radius)

-- ============================================================================
-- TRANSFORM AND REPEATER
-- ============================================================================

-- | Shape transform
data ShapeTransform = ShapeTransform
  { shapeTransformType :: Text  -- "transform"
  , shapeTransformName :: Text
  , shapeTransformAnchorPoint :: AnimatableProperty Point2D
  , shapeTransformPosition :: AnimatableProperty Point2D
  , shapeTransformScale :: AnimatableProperty Point2D  -- Percentage (100 = 100%)
  , shapeTransformRotation :: AnimatableProperty Double  -- Degrees
  , shapeTransformSkew :: AnimatableProperty Double  -- Degrees
  , shapeTransformSkewAxis :: AnimatableProperty Double  -- Degrees
  , shapeTransformOpacity :: AnimatableProperty Double  -- 0-100%
  }
  deriving (Eq, Show, Generic)

instance ToJSON ShapeTransform where
  toJSON (ShapeTransform _ name anchorPoint position scale rotation skew skewAxis opacity) =
    object
      [ "type" .= ("transform" :: Text)
      , "name" .= name
      , "anchorPoint" .= anchorPoint
      , "position" .= position
      , "scale" .= scale
      , "rotation" .= rotation
      , "skew" .= skew
      , "skewAxis" .= skewAxis
      , "opacity" .= opacity
      ]

instance FromJSON ShapeTransform where
  parseJSON = withObject "ShapeTransform" $ \o -> do
    name <- o .: "name"
    anchorPoint <- o .: "anchorPoint"
    position <- o .: "position"
    scale <- o .: "scale"
    rotation <- o .: "rotation"
    skew <- o .: "skew"
    skewAxis <- o .: "skewAxis"
    opacity <- o .: "opacity"
    return (ShapeTransform "transform" name anchorPoint position scale rotation skew skewAxis opacity)

-- | Repeater composite
data RepeaterComposite
  = RepeaterCompositeAbove
  | RepeaterCompositeBelow
  deriving (Eq, Show, Generic)

instance ToJSON RepeaterComposite where
  toJSON RepeaterCompositeAbove = "above"
  toJSON RepeaterCompositeBelow = "below"

instance FromJSON RepeaterComposite where
  parseJSON = withText "RepeaterComposite" $ \s ->
    case s of
      t | t == T.pack "above" -> return RepeaterCompositeAbove
      t | t == T.pack "below" -> return RepeaterCompositeBelow
      _ -> fail "Invalid RepeaterComposite"

-- | Repeater transform
data RepeaterTransform = RepeaterTransform
  { repeaterTransformAnchorPoint :: AnimatableProperty Point2D
  , repeaterTransformPosition :: AnimatableProperty Point2D
  , repeaterTransformScale :: AnimatableProperty Point2D  -- End scale (100 = no change)
  , repeaterTransformRotation :: AnimatableProperty Double  -- Rotation per copy
  , repeaterTransformStartOpacity :: AnimatableProperty Double  -- Opacity of first copy
  , repeaterTransformEndOpacity :: AnimatableProperty Double  -- Opacity of last copy
  }
  deriving (Eq, Show, Generic)

instance ToJSON RepeaterTransform where
  toJSON (RepeaterTransform anchorPoint position scale rotation startOpacity endOpacity) =
    object
      [ "anchorPoint" .= anchorPoint
      , "position" .= position
      , "scale" .= scale
      , "rotation" .= rotation
      , "startOpacity" .= startOpacity
      , "endOpacity" .= endOpacity
      ]

instance FromJSON RepeaterTransform where
  parseJSON = withObject "RepeaterTransform" $ \o -> do
    anchorPoint <- o .: "anchorPoint"
    position <- o .: "position"
    scale <- o .: "scale"
    rotation <- o .: "rotation"
    startOpacity <- o .: "startOpacity"
    endOpacity <- o .: "endOpacity"
    return (RepeaterTransform anchorPoint position scale rotation startOpacity endOpacity)

-- | Repeater operator
data RepeaterOperator = RepeaterOperator
  { repeaterOperatorType :: Text  -- "repeater"
  , repeaterOperatorName :: Text
  , repeaterOperatorCopies :: AnimatableProperty Double
  , repeaterOperatorOffset :: AnimatableProperty Double  -- Offset from original (degrees for radial)
  , repeaterOperatorComposite :: RepeaterComposite  -- Stack order
  , repeaterOperatorTransform :: RepeaterTransform  -- Transform per copy
  }
  deriving (Eq, Show, Generic)

instance ToJSON RepeaterOperator where
  toJSON (RepeaterOperator _ name copies offset composite transform) =
    object
      [ "type" .= ("repeater" :: Text)
      , "name" .= name
      , "copies" .= copies
      , "offset" .= offset
      , "composite" .= composite
      , "transform" .= transform
      ]

instance FromJSON RepeaterOperator where
  parseJSON = withObject "RepeaterOperator" $ \o -> do
    name <- o .: "name"
    copies <- o .: "copies"
    offset <- o .: "offset"
    composite <- o .: "composite"
    transform <- o .: "transform"
    return (RepeaterOperator "repeater" name copies offset composite transform)

-- ============================================================================
-- ILLUSTRATOR OPERATORS
-- ============================================================================

-- | Simplify path operator
data SimplifyPathOperator = SimplifyPathOperator
  { simplifyPathOperatorType :: Text  -- "simplifyPath"
  , simplifyPathOperatorName :: Text
  , simplifyPathOperatorTolerance :: AnimatableProperty Double  -- Curve precision (0-100)
  , simplifyPathOperatorAngleTolerance :: AnimatableProperty Double  -- Corner angle threshold
  , simplifyPathOperatorStraightLines :: Bool  -- Convert to straight segments
  }
  deriving (Eq, Show, Generic)

instance ToJSON SimplifyPathOperator where
  toJSON (SimplifyPathOperator _ name tolerance angleTolerance straightLines) =
    object
      [ "type" .= ("simplifyPath" :: Text)
      , "name" .= name
      , "tolerance" .= tolerance
      , "angleTolerance" .= angleTolerance
      , "straightLines" .= straightLines
      ]

instance FromJSON SimplifyPathOperator where
  parseJSON = withObject "SimplifyPathOperator" $ \o -> do
    name <- o .: "name"
    tolerance <- o .: "tolerance"
    angleTolerance <- o .: "angleTolerance"
    straightLines <- o .: "straightLines"
    return (SimplifyPathOperator "simplifyPath" name tolerance angleTolerance straightLines)

-- | Smooth path operator
data SmoothPathOperator = SmoothPathOperator
  { smoothPathOperatorType :: Text  -- "smoothPath"
  , smoothPathOperatorName :: Text
  , smoothPathOperatorAmount :: AnimatableProperty Double  -- 0-100%
  }
  deriving (Eq, Show, Generic)

instance ToJSON SmoothPathOperator where
  toJSON (SmoothPathOperator _ name amount) =
    object
      [ "type" .= ("smoothPath" :: Text)
      , "name" .= name
      , "amount" .= amount
      ]

instance FromJSON SmoothPathOperator where
  parseJSON = withObject "SmoothPathOperator" $ \o -> do
    name <- o .: "name"
    amount <- o .: "amount"
    return (SmoothPathOperator "smoothPath" name amount)

-- | Extrude cap type
data ExtrudeCapType
  = ExtrudeCapTypeFlat
  | ExtrudeCapTypeRound
  | ExtrudeCapTypeBevel
  deriving (Eq, Show, Generic)

instance ToJSON ExtrudeCapType where
  toJSON ExtrudeCapTypeFlat = "flat"
  toJSON ExtrudeCapTypeRound = "round"
  toJSON ExtrudeCapTypeBevel = "bevel"

instance FromJSON ExtrudeCapType where
  parseJSON = withText "ExtrudeCapType" $ \s ->
    case s of
      t | t == T.pack "flat" -> return ExtrudeCapTypeFlat
      t | t == T.pack "round" -> return ExtrudeCapTypeRound
      t | t == T.pack "bevel" -> return ExtrudeCapTypeBevel
      _ -> fail "Invalid ExtrudeCapType"

-- | Extrude material
data ExtrudeMaterial = ExtrudeMaterial
  { extrudeMaterialFrontColor :: AnimatableProperty ShapeColor
  , extrudeMaterialSideColor :: AnimatableProperty ShapeColor
  , extrudeMaterialBevelColor :: AnimatableProperty ShapeColor
  }
  deriving (Eq, Show, Generic)

instance ToJSON ExtrudeMaterial where
  toJSON (ExtrudeMaterial frontColor sideColor bevelColor) =
    object
      [ "frontColor" .= frontColor
      , "sideColor" .= sideColor
      , "bevelColor" .= bevelColor
      ]

instance FromJSON ExtrudeMaterial where
  parseJSON = withObject "ExtrudeMaterial" $ \o -> do
    frontColor <- o .: "frontColor"
    sideColor <- o .: "sideColor"
    bevelColor <- o .: "bevelColor"
    return (ExtrudeMaterial frontColor sideColor bevelColor)

-- | Extrude operator
data ExtrudeOperator = ExtrudeOperator
  { extrudeOperatorType :: Text  -- "extrude"
  , extrudeOperatorName :: Text
  , extrudeOperatorDepth :: AnimatableProperty Double  -- Extrusion depth
  , extrudeOperatorBevelDepth :: AnimatableProperty Double  -- Bevel size
  , extrudeOperatorBevelSegments :: Double  -- Smoothness of bevel
  , extrudeOperatorCapType :: ExtrudeCapType
  , extrudeOperatorMaterial :: ExtrudeMaterial
  }
  deriving (Eq, Show, Generic)

instance ToJSON ExtrudeOperator where
  toJSON (ExtrudeOperator _ name depth bevelDepth bevelSegments capType material) =
    object
      [ "type" .= ("extrude" :: Text)
      , "name" .= name
      , "depth" .= depth
      , "bevelDepth" .= bevelDepth
      , "bevelSegments" .= bevelSegments
      , "capType" .= capType
      , "material" .= material
      ]

instance FromJSON ExtrudeOperator where
  parseJSON = withObject "ExtrudeOperator" $ \o -> do
    name <- o .: "name"
    depth <- o .: "depth"
    bevelDepth <- o .: "bevelDepth"
    bevelSegments <- o .: "bevelSegments"
    capType <- o .: "capType"
    material <- o .: "material"
    if validateFinite bevelSegments && validateNonNegative bevelSegments
      then return (ExtrudeOperator "extrude" name depth bevelDepth bevelSegments capType material)
      else fail "ExtrudeOperator: bevelSegments must be finite and non-negative"

-- | Trace mode
data TraceMode
  = TraceModeBlackAndWhite
  | TraceModeGrayscale
  | TraceModeColor
  deriving (Eq, Show, Generic)

instance ToJSON TraceMode where
  toJSON TraceModeBlackAndWhite = "blackAndWhite"
  toJSON TraceModeGrayscale = "grayscale"
  toJSON TraceModeColor = "color"

instance FromJSON TraceMode where
  parseJSON = withText "TraceMode" $ \s ->
    case s of
      t | t == T.pack "blackAndWhite" -> return TraceModeBlackAndWhite
      t | t == T.pack "grayscale" -> return TraceModeGrayscale
      t | t == T.pack "color" -> return TraceModeColor
      _ -> fail "Invalid TraceMode"

-- | Trace operator
data TraceOperator = TraceOperator
  { traceOperatorType :: Text  -- "trace"
  , traceOperatorName :: Text
  , traceOperatorMode :: TraceMode
  , traceOperatorThreshold :: AnimatableProperty Double  -- B&W threshold (0-255)
  , traceOperatorColors :: Double  -- Max colors for color mode
  , traceOperatorCornerAngle :: Double  -- Corner detection threshold
  , traceOperatorPathFitting :: AnimatableProperty Double  -- Tolerance for path simplification
  , traceOperatorNoiseReduction :: AnimatableProperty Double  -- Ignore small features
  , traceOperatorSourceLayerId :: Maybe Text  -- Layer to trace
  , traceOperatorSourceFrame :: Maybe Double  -- Frame to trace (for video)
  }
  deriving (Eq, Show, Generic)

instance ToJSON TraceOperator where
  toJSON (TraceOperator _ name mode threshold colors cornerAngle pathFitting noiseReduction mSourceLayerId mSourceFrame) =
    let
      baseFields = ["type" .= ("trace" :: Text), "name" .= name, "mode" .= mode, "threshold" .= threshold, "colors" .= colors, "cornerAngle" .= cornerAngle, "pathFitting" .= pathFitting, "noiseReduction" .= noiseReduction]
      withSourceLayerId = case mSourceLayerId of Just id -> ("sourceLayerId" .= id) : baseFields; Nothing -> baseFields
      withSourceFrame = case mSourceFrame of Just f -> ("sourceFrame" .= f) : withSourceLayerId; Nothing -> withSourceLayerId
    in object withSourceFrame

instance FromJSON TraceOperator where
  parseJSON = withObject "TraceOperator" $ \o -> do
    name <- o .: "name"
    mode <- o .: "mode"
    threshold <- o .: "threshold"
    colors <- o .: "colors"
    cornerAngle <- o .: "cornerAngle"
    pathFitting <- o .: "pathFitting"
    noiseReduction <- o .: "noiseReduction"
    mSourceLayerId <- o .:? "sourceLayerId"
    mSourceFrame <- o .:? "sourceFrame"
    if validateFinite colors && validateFinite cornerAngle &&
       validateNonNegative colors && validateNonNegative cornerAngle &&
       colors >= 1 && cornerAngle >= 0 && cornerAngle <= 180 &&
       maybe True (\f -> validateFinite f && validateNonNegative f) mSourceFrame
      then return (TraceOperator "trace" name mode threshold colors cornerAngle pathFitting noiseReduction mSourceLayerId mSourceFrame)
      else fail "TraceOperator: colors must be >= 1, cornerAngle must be in [0,180], sourceFrame must be finite and non-negative"

-- ============================================================================
-- SHAPE GROUP
-- ============================================================================

-- | Shape group (non-recursive: groups cannot contain other groups)
data ShapeGroup = ShapeGroup
  { shapeGroupType :: Text  -- "group"
  , shapeGroupName :: Text
  , shapeGroupContents :: [NonGroupShapeContent]  -- Non-recursive: groups cannot contain other groups
  , shapeGroupTransform :: ShapeTransform
  , shapeGroupBlendMode :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON ShapeGroup where
  toJSON (ShapeGroup _ name contents transform blendMode) =
    object
      [ "type" .= ("group" :: Text)
      , "name" .= name
      , "contents" .= contents
      , "transform" .= transform
      , "blendMode" .= blendMode
      ]

instance FromJSON ShapeGroup where
  parseJSON = withObject "ShapeGroup" $ \o -> do
    name <- o .: "name"
    contentsRaw <- o .: "contents"
    transform <- o .: "transform"
    blendMode <- o .: "blendMode"
    -- Validate max 1,000 items per group (matches Zod schema)
    contents <- case validateBoundedArray 1000 contentsRaw of
      Left err -> fail (T.unpack err)
      Right cs -> return cs
    return (ShapeGroup "group" name contents transform blendMode)

-- ============================================================================
-- SHAPE CONTENT UNION TYPES
-- ============================================================================

-- | Non-group shape content (used inside ShapeGroup.contents to avoid circular dependency)
data NonGroupShapeContent
  = NonGroupShapeContentGenerator RectangleShape
  | NonGroupShapeContentGeneratorEllipse EllipseShape
  | NonGroupShapeContentGeneratorPolygon PolygonShape
  | NonGroupShapeContentGeneratorStar StarShape
  | NonGroupShapeContentGeneratorPath PathShape
  | NonGroupShapeContentModifierFill FillShape
  | NonGroupShapeContentModifierStroke StrokeShape
  | NonGroupShapeContentModifierGradientFill GradientFillShape
  | NonGroupShapeContentModifierGradientStroke GradientStrokeShape
  | NonGroupShapeContentOperatorTrimPaths TrimPathsOperator
  | NonGroupShapeContentOperatorMergePaths MergePathsOperator
  | NonGroupShapeContentOperatorOffsetPaths OffsetPathsOperator
  | NonGroupShapeContentOperatorPuckerBloat PuckerBloatOperator
  | NonGroupShapeContentOperatorWigglePaths WigglePathsOperator
  | NonGroupShapeContentOperatorZigZag ZigZagOperator
  | NonGroupShapeContentOperatorTwist TwistOperator
  | NonGroupShapeContentOperatorRoundedCorners RoundedCornersOperator
  | NonGroupShapeContentTransform ShapeTransform
  | NonGroupShapeContentRepeater RepeaterOperator
  | NonGroupShapeContentIllustratorSimplifyPath SimplifyPathOperator
  | NonGroupShapeContentIllustratorSmoothPath SmoothPathOperator
  | NonGroupShapeContentIllustratorExtrude ExtrudeOperator
  | NonGroupShapeContentIllustratorTrace TraceOperator
  deriving (Eq, Show, Generic)

instance ToJSON NonGroupShapeContent where
  toJSON (NonGroupShapeContentGenerator g) = toJSON g
  toJSON (NonGroupShapeContentGeneratorEllipse e) = toJSON e
  toJSON (NonGroupShapeContentGeneratorPolygon p) = toJSON p
  toJSON (NonGroupShapeContentGeneratorStar s) = toJSON s
  toJSON (NonGroupShapeContentGeneratorPath p) = toJSON p
  toJSON (NonGroupShapeContentModifierFill f) = toJSON f
  toJSON (NonGroupShapeContentModifierStroke s) = toJSON s
  toJSON (NonGroupShapeContentModifierGradientFill g) = toJSON g
  toJSON (NonGroupShapeContentModifierGradientStroke g) = toJSON g
  toJSON (NonGroupShapeContentOperatorTrimPaths t) = toJSON t
  toJSON (NonGroupShapeContentOperatorMergePaths m) = toJSON m
  toJSON (NonGroupShapeContentOperatorOffsetPaths o) = toJSON o
  toJSON (NonGroupShapeContentOperatorPuckerBloat p) = toJSON p
  toJSON (NonGroupShapeContentOperatorWigglePaths w) = toJSON w
  toJSON (NonGroupShapeContentOperatorZigZag z) = toJSON z
  toJSON (NonGroupShapeContentOperatorTwist t) = toJSON t
  toJSON (NonGroupShapeContentOperatorRoundedCorners r) = toJSON r
  toJSON (NonGroupShapeContentTransform t) = toJSON t
  toJSON (NonGroupShapeContentRepeater r) = toJSON r
  toJSON (NonGroupShapeContentIllustratorSimplifyPath s) = toJSON s
  toJSON (NonGroupShapeContentIllustratorSmoothPath s) = toJSON s
  toJSON (NonGroupShapeContentIllustratorExtrude e) = toJSON e
  toJSON (NonGroupShapeContentIllustratorTrace t) = toJSON t

instance FromJSON NonGroupShapeContent where
  parseJSON = withObject "NonGroupShapeContent" $ \o -> do
    contentType <- (o .: fromString "type") :: Parser Text
    case () of
      _ | contentType == T.pack "rectangle" -> do
        g <- parseJSON (Object o)
        return (NonGroupShapeContentGenerator g)
      _ | contentType == T.pack "ellipse" -> do
        e <- parseJSON (Object o)
        return (NonGroupShapeContentGeneratorEllipse e)
      _ | contentType == T.pack "polygon" -> do
        p <- parseJSON (Object o)
        return (NonGroupShapeContentGeneratorPolygon p)
      _ | contentType == T.pack "star" -> do
        s <- parseJSON (Object o)
        return (NonGroupShapeContentGeneratorStar s)
      _ | contentType == T.pack "path" -> do
        p <- parseJSON (Object o)
        return (NonGroupShapeContentGeneratorPath p)
      _ | contentType == T.pack "fill" -> do
        f <- parseJSON (Object o)
        return (NonGroupShapeContentModifierFill f)
      _ | contentType == T.pack "stroke" -> do
        s <- parseJSON (Object o)
        return (NonGroupShapeContentModifierStroke s)
      _ | contentType == T.pack "gradientFill" -> do
        g <- parseJSON (Object o)
        return (NonGroupShapeContentModifierGradientFill g)
      _ | contentType == T.pack "gradientStroke" -> do
        g <- parseJSON (Object o)
        return (NonGroupShapeContentModifierGradientStroke g)
      _ | contentType == T.pack "trimPaths" -> do
        t <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorTrimPaths t)
      _ | contentType == T.pack "mergePaths" -> do
        m <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorMergePaths m)
      _ | contentType == T.pack "offsetPaths" -> do
        o' <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorOffsetPaths o')
      _ | contentType == T.pack "puckerBloat" -> do
        p <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorPuckerBloat p)
      _ | contentType == T.pack "wigglePaths" -> do
        w <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorWigglePaths w)
      _ | contentType == T.pack "zigZag" -> do
        z <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorZigZag z)
      _ | contentType == T.pack "twist" -> do
        t <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorTwist t)
      _ | contentType == T.pack "roundedCorners" -> do
        r <- parseJSON (Object o)
        return (NonGroupShapeContentOperatorRoundedCorners r)
      _ | contentType == T.pack "transform" -> do
        t <- parseJSON (Object o)
        return (NonGroupShapeContentTransform t)
      _ | contentType == T.pack "repeater" -> do
        r <- parseJSON (Object o)
        return (NonGroupShapeContentRepeater r)
      _ | contentType == T.pack "simplifyPath" -> do
        s <- parseJSON (Object o)
        return (NonGroupShapeContentIllustratorSimplifyPath s)
      _ | contentType == T.pack "smoothPath" -> do
        s <- parseJSON (Object o)
        return (NonGroupShapeContentIllustratorSmoothPath s)
      _ | contentType == T.pack "extrude" -> do
        e <- parseJSON (Object o)
        return (NonGroupShapeContentIllustratorExtrude e)
      _ | contentType == T.pack "trace" -> do
        t <- parseJSON (Object o)
        return (NonGroupShapeContentIllustratorTrace t)
      _ -> fail ("Invalid NonGroupShapeContent type: " ++ show contentType)

-- | Full shape content (includes groups for root-level ShapeLayerData.contents)
data ShapeContent
  = ShapeContentNonGroup NonGroupShapeContent
  | ShapeContentGroup ShapeGroup
  deriving (Eq, Show, Generic)

instance ToJSON ShapeContent where
  toJSON (ShapeContentNonGroup ng) = toJSON ng
  toJSON (ShapeContentGroup g) = toJSON g

instance FromJSON ShapeContent where
  parseJSON = withObject "ShapeContent" $ \o -> do
    contentType <- (o .: fromString "type") :: Parser Text
    case () of
      _ | contentType == T.pack "group" -> do
        g <- parseJSON (Object o)
        return (ShapeContentGroup g)
      _ -> do
        ng <- parseJSON (Object o)
        return (ShapeContentNonGroup ng)

-- ============================================================================
-- SHAPE LAYER DATA
-- ============================================================================

-- | Shape quality
data ShapeQuality
  = ShapeQualityDraft
  | ShapeQualityNormal
  | ShapeQualityHigh
  deriving (Eq, Show, Generic)

instance ToJSON ShapeQuality where
  toJSON ShapeQualityDraft = "draft"
  toJSON ShapeQualityNormal = "normal"
  toJSON ShapeQualityHigh = "high"

instance FromJSON ShapeQuality where
  parseJSON = withText "ShapeQuality" $ \s ->
    case s of
      t | t == T.pack "draft" -> return ShapeQualityDraft
      t | t == T.pack "normal" -> return ShapeQualityNormal
      t | t == T.pack "high" -> return ShapeQualityHigh
      _ -> fail "Invalid ShapeQuality"

-- | Shape layer data
data ShapeLayerData = ShapeLayerData
  { shapeLayerDataContents :: [ShapeContent]  -- Root contents (groups, shapes, operators)
  , shapeLayerDataBlendMode :: Text  -- Layer-level blend mode
  , shapeLayerDataQuality :: ShapeQuality  -- Quality settings
  , shapeLayerDataGPUAccelerated :: Bool  -- Enable GPU acceleration if available
  }
  deriving (Eq, Show, Generic)

instance ToJSON ShapeLayerData where
  toJSON (ShapeLayerData contents blendMode quality gpuAccelerated) =
    object
      [ "contents" .= contents
      , "blendMode" .= blendMode
      , "quality" .= quality
      , "gpuAccelerated" .= gpuAccelerated
      ]

instance FromJSON ShapeLayerData where
  parseJSON = withObject "ShapeLayerData" $ \o -> do
    contentsRaw <- o .: "contents"
    blendMode <- o .: "blendMode"
    quality <- o .: "quality"
    gpuAccelerated <- o .: "gpuAccelerated"
    -- Validate max 1,000 root items (matches Zod schema)
    contents <- case validateBoundedArray 1000 contentsRaw of
      Left err -> fail (T.unpack err)
      Right cs -> return cs
    return (ShapeLayerData contents blendMode quality gpuAccelerated)
