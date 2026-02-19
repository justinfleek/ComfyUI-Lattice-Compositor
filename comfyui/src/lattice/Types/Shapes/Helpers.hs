-- |
-- Module      : Lattice.Types.Shapes.Helpers
-- Description : Helper functions for creating default shape instances
-- 
-- Migrated from ui/src/types/shapes.ts factory functions
-- Pure functions for creating default shape configurations
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.Shapes.Helpers
  ( -- Animatable property factories
    createDefaultAnimatablePoint,
    createDefaultAnimatableNumber,
    createDefaultAnimatableColor,
    createDefaultAnimatablePath,
    createDefaultAnimatableNumberArray,
    -- Shape generator factories
    createDefaultRectangle,
    createDefaultEllipse,
    createDefaultPolygon,
    createDefaultStar,
    createDefaultPath,
    -- Shape modifier factories
    createDefaultFill,
    createDefaultStroke,
    createDefaultGradientFill,
    createDefaultGradientStroke,
    -- Path operator factories
    createDefaultTrimPaths,
    createDefaultMergePaths,
    createDefaultOffsetPaths,
    createDefaultPuckerBloat,
    createDefaultWigglePaths,
    createDefaultZigZag,
    createDefaultTwist,
    createDefaultRoundedCorners,
    -- Transform and repeater factories
    createDefaultShapeTransform,
    createDefaultRepeater,
    -- Group factory
    createDefaultGroup,
    -- Illustrator operator factories
    createDefaultExtrude,
    createDefaultTrace,
    createDefaultSimplifyPath,
    createDefaultSmoothPath,
    -- Layer data factory
    createDefaultShapeLayerData,
  )
where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
    createAnimatableProperty,
  )
import Lattice.Types.LayerDataShapes
  ( BezierPath (..),
    EllipseShape (..),
    ExtrudeCapType (..),
    ExtrudeMaterial (..),
    ExtrudeOperator (..),
    FillRule (..),
    FillShape (..),
    GradientDef (..),
    GradientFillShape (..),
    GradientStrokeShape (..),
    GradientStop (..),
    GradientType (..),
    LineCap (..),
    LineJoin (..),
    MergeMode (..),
    MergePathsOperator (..),
    OffsetJoin (..),
    OffsetPathsOperator (..),
    PathShape (..),
    Point2D (..),
    PolygonShape (..),
    PuckerBloatOperator (..),
    RectangleShape (..),
    RepeaterComposite (..),
    RepeaterOperator (..),
    RepeaterTransform (..),
    RoundedCornersOperator (..),
    ShapeColor (..),
    ShapeDirection (..),
    ShapeGroup (..),
    ShapeLayerData (..),
    ShapeQuality (..),
    ShapeTransform (..),
    SimplifyPathOperator (..),
    SmoothPathOperator (..),
    StarShape (..),
    StrokeShape (..),
    TraceMode (..),
    TraceOperator (..),
    TrimMode (..),
    TrimPathsOperator (..),
    TwistOperator (..),
    WigglePathsOperator (..),
    WigglePointType (..),
    ZigZagOperator (..),
    ZigZagPointType (..),
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // animatable // property // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default animatable point property
--                                                                      // note
createDefaultAnimatablePoint :: Text -> AnimatableProperty Point2D
createDefaultAnimatablePoint name =
  createAnimatableProperty
    ("shape_prop_" <> name <> "_point")
    name
    (Point2D 0.0 0.0)
    PropertyTypePosition
    Nothing

-- | Create default animatable number property
createDefaultAnimatableNumber :: Double -> Text -> AnimatableProperty Double
createDefaultAnimatableNumber value name =
  createAnimatableProperty
    ("shape_prop_" <> name <> "_number")
    name
    value
    PropertyTypeNumber
    Nothing

-- | Create default animatable color property
--                                                                       // rgb
createDefaultAnimatableColor ::
  Double ->
  Double ->
  Double ->
  Double ->
  Text ->
  AnimatableProperty ShapeColor
createDefaultAnimatableColor r g b a name =
  createAnimatableProperty
    ("shape_prop_" <> name <> "_color")
    name
    (ShapeColor r g b a)
    PropertyTypeColor
    Nothing

-- | Create default animatable path property
createDefaultAnimatablePath :: Text -> AnimatableProperty BezierPath
createDefaultAnimatablePath name =
  createAnimatableProperty
    ("shape_prop_" <> name <> "_path")
    name
    (BezierPath [] False)
    PropertyTypePosition -- Using 'position' as closest match for path type
    Nothing

-- | Create default animatable number array property
createDefaultAnimatableNumberArray ::
  [Double] ->
  Text ->
  AnimatableProperty [Double]
createDefaultAnimatableNumberArray value name =
  createAnimatableProperty
    ("shape_prop_" <> name <> "_array")
    name
    value
    PropertyTypeNumber -- Closest match
    Nothing

-- ════════════════════════════════════════════════════════════════════════════
--                                           // shape // generator // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default rectangle shape
createDefaultRectangle :: RectangleShape
createDefaultRectangle =
  RectangleShape
    { rectangleShapeType = "rectangle",
      rectangleShapeName = "Rectangle",
      rectangleShapePosition = createDefaultAnimatablePoint "Position",
      rectangleShapeSize =
        createAnimatableProperty
          "shape_prop_Size_point"
          "Size"
          (Point2D 100.0 100.0)
          PropertyTypePosition
          Nothing,
      rectangleShapeRoundness = createDefaultAnimatableNumber 0.0 "Roundness",
      rectangleShapeDirection = ShapeDirectionClockwise
    }

-- | Create default ellipse shape
createDefaultEllipse :: EllipseShape
createDefaultEllipse =
  EllipseShape
    { ellipseShapeType = "ellipse",
      ellipseShapeName = "Ellipse",
      ellipseShapePosition = createDefaultAnimatablePoint "Position",
      ellipseShapeSize =
        createAnimatableProperty
          "shape_prop_Size_point"
          "Size"
          (Point2D 100.0 100.0)
          PropertyTypePosition
          Nothing,
      ellipseShapeDirection = ShapeDirectionClockwise
    }

-- | Create default polygon shape
createDefaultPolygon :: PolygonShape
createDefaultPolygon =
  PolygonShape
    { polygonShapeType = "polygon",
      polygonShapeName = "Polygon",
      polygonShapePosition = createDefaultAnimatablePoint "Position",
      polygonShapePoints = createDefaultAnimatableNumber 6.0 "Points",
      polygonShapeOuterRadius = createDefaultAnimatableNumber 50.0 "Outer Radius",
      polygonShapeOuterRoundness =
        createDefaultAnimatableNumber 0.0 "Outer Roundness",
      polygonShapeRotation = createDefaultAnimatableNumber 0.0 "Rotation",
      polygonShapeDirection = ShapeDirectionClockwise
    }

-- | Create default star shape
createDefaultStar :: StarShape
createDefaultStar =
  StarShape
    { starShapeType = "star",
      starShapeName = "Star",
      starShapePosition = createDefaultAnimatablePoint "Position",
      starShapePoints = createDefaultAnimatableNumber 5.0 "Points",
      starShapeOuterRadius = createDefaultAnimatableNumber 50.0 "Outer Radius",
      starShapeInnerRadius = createDefaultAnimatableNumber 25.0 "Inner Radius",
      starShapeOuterRoundness =
        createDefaultAnimatableNumber 0.0 "Outer Roundness",
      starShapeInnerRoundness =
        createDefaultAnimatableNumber 0.0 "Inner Roundness",
      starShapeRotation = createDefaultAnimatableNumber 0.0 "Rotation",
      starShapeDirection = ShapeDirectionClockwise
    }

-- | Create default path shape
createDefaultPath :: PathShape
createDefaultPath =
  PathShape
    { pathShapeType = "path",
      pathShapeName = "Path",
      pathShapePath = createDefaultAnimatablePath "Path",
      pathShapeDirection = ShapeDirectionClockwise
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                            // shape // modifier // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default fill shape
createDefaultFill :: FillShape
createDefaultFill =
  FillShape
    { fillShapeType = "fill",
      fillShapeName = "Fill",
      fillShapeColor =
        createDefaultAnimatableColor 255.0 255.0 255.0 1.0 "Color",
      fillShapeOpacity = createDefaultAnimatableNumber 100.0 "Opacity",
      fillShapeFillRule = FillRuleNonzero,
      fillShapeBlendMode = "normal"
    }

-- | Create default stroke shape
createDefaultStroke :: StrokeShape
createDefaultStroke =
  StrokeShape
    { strokeShapeType = "stroke",
      strokeShapeName = "Stroke",
      strokeShapeColor =
        createDefaultAnimatableColor 255.0 255.0 255.0 1.0 "Color",
      strokeShapeOpacity = createDefaultAnimatableNumber 100.0 "Opacity",
      strokeShapeWidth = createDefaultAnimatableNumber 2.0 "Stroke Width",
      strokeShapeLineCap = LineCapRound,
      strokeShapeLineJoin = LineJoinRound,
      strokeShapeMiterLimit = 4.0,
      strokeShapeDashPattern =
        createDefaultAnimatableNumberArray [] "Dash Pattern",
      strokeShapeDashOffset = createDefaultAnimatableNumber 0.0 "Dash Offset",
      strokeShapeBlendMode = "normal",
      strokeShapeTaperEnabled = False,
      strokeShapeTaperStartLength =
        createDefaultAnimatableNumber 0.0 "Taper Start Length",
      strokeShapeTaperEndLength =
        createDefaultAnimatableNumber 0.0 "Taper End Length",
      strokeShapeTaperStartWidth =
        createDefaultAnimatableNumber 100.0 "Taper Start Width",
      strokeShapeTaperEndWidth =
        createDefaultAnimatableNumber 100.0 "Taper End Width",
      strokeShapeTaperStartEase =
        createDefaultAnimatableNumber 0.0 "Taper Start Ease",
      strokeShapeTaperEndEase =
        createDefaultAnimatableNumber 0.0 "Taper End Ease"
    }

-- | Create default gradient fill shape
createDefaultGradientFill :: GradientFillShape
createDefaultGradientFill =
  let gradientValue =
        GradientDef
          { gradientDefType = GradientTypeLinear,
            gradientDefStops =
              [ GradientStop
                  0.0
                  (ShapeColor 0.0 0.0 0.0 1.0),
                GradientStop
                  1.0
                  (ShapeColor 255.0 255.0 255.0 1.0)
              ],
            gradientDefStartPoint = Point2D 0.0 0.5,
            gradientDefEndPoint = Point2D 1.0 0.5,
            gradientDefHighlightLength = Nothing,
            gradientDefHighlightAngle = Nothing
          }
   in GradientFillShape
        { gradientFillShapeType = "gradientFill",
          gradientFillShapeName = "Gradient Fill",
          gradientFillShapeGradient =
            createAnimatableProperty
              "shape_prop_Gradient_enum"
              "Gradient"
              gradientValue
              PropertyTypeEnum
              Nothing,
          gradientFillShapeOpacity =
            createDefaultAnimatableNumber 100.0 "Opacity",
          gradientFillShapeFillRule = FillRuleNonzero,
          gradientFillShapeBlendMode = "normal"
        }

-- | Create default gradient stroke shape
createDefaultGradientStroke :: GradientStrokeShape
createDefaultGradientStroke =
  let gradientValue =
        GradientDef
          { gradientDefType = GradientTypeLinear,
            gradientDefStops =
              [ GradientStop
                  0.0
                  (ShapeColor 255.0 255.0 255.0 1.0),
                GradientStop
                  1.0
                  (ShapeColor 0.0 0.0 0.0 1.0)
              ],
            gradientDefStartPoint = Point2D 0.0 0.5,
            gradientDefEndPoint = Point2D 1.0 0.5,
            gradientDefHighlightLength = Nothing,
            gradientDefHighlightAngle = Nothing
          }
   in GradientStrokeShape
        { gradientStrokeShapeType = "gradientStroke",
          gradientStrokeShapeName = "Gradient Stroke",
          gradientStrokeShapeGradient =
            createAnimatableProperty
              "shape_prop_Gradient_enum"
              "Gradient"
              gradientValue
              PropertyTypeEnum
              Nothing,
          gradientStrokeShapeOpacity =
            createDefaultAnimatableNumber 100.0 "Opacity",
          gradientStrokeShapeWidth = createDefaultAnimatableNumber 2.0 "Width",
          gradientStrokeShapeLineCap = LineCapRound,
          gradientStrokeShapeLineJoin = LineJoinRound,
          gradientStrokeShapeMiterLimit = 4.0,
          gradientStrokeShapeDashPattern =
            createDefaultAnimatableNumberArray [] "Dash Pattern",
          gradientStrokeShapeDashOffset =
            createDefaultAnimatableNumber 0.0 "Dash Offset",
          gradientStrokeShapeBlendMode = "normal"
        }

-- ════════════════════════════════════════════════════════════════════════════
--                                             // path // operator // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default trim paths operator
createDefaultTrimPaths :: TrimPathsOperator
createDefaultTrimPaths =
  TrimPathsOperator
    { trimPathsOperatorType = "trimPaths",
      trimPathsOperatorName = "Trim Paths",
      trimPathsOperatorStart = createDefaultAnimatableNumber 0.0 "",
      trimPathsOperatorEnd = createDefaultAnimatableNumber 100.0 "",
      trimPathsOperatorOffset = createDefaultAnimatableNumber 0.0 "",
      trimPathsOperatorMode = TrimModeSimultaneously
    }

-- | Create default merge paths operator
createDefaultMergePaths :: MergePathsOperator
createDefaultMergePaths =
  MergePathsOperator
    { mergePathsOperatorType = "mergePaths",
      mergePathsOperatorName = "Merge Paths",
      mergePathsOperatorMode = MergeModeAdd
    }

-- | Create default offset paths operator
createDefaultOffsetPaths :: OffsetPathsOperator
createDefaultOffsetPaths =
  OffsetPathsOperator
    { offsetPathsOperatorType = "offsetPaths",
      offsetPathsOperatorName = "Offset Paths",
      offsetPathsOperatorAmount = createDefaultAnimatableNumber 0.0 "",
      offsetPathsOperatorLineJoin = OffsetJoinMiter,
      offsetPathsOperatorMiterLimit = createDefaultAnimatableNumber 4.0 "",
      offsetPathsOperatorCopies = createDefaultAnimatableNumber 1.0 "",
      offsetPathsOperatorCopyOffset = createDefaultAnimatableNumber 0.0 ""
    }

-- | Create default pucker bloat operator
createDefaultPuckerBloat :: PuckerBloatOperator
createDefaultPuckerBloat =
  PuckerBloatOperator
    { puckerBloatOperatorType = "puckerBloat",
      puckerBloatOperatorName = "Pucker & Bloat",
      puckerBloatOperatorAmount = createDefaultAnimatableNumber 0.0 ""
    }

-- | Create default wiggle paths operator
createDefaultWigglePaths :: WigglePathsOperator
createDefaultWigglePaths =
  WigglePathsOperator
    { wigglePathsOperatorType = "wigglePaths",
      wigglePathsOperatorName = "Wiggle Paths",
      wigglePathsOperatorSize = createDefaultAnimatableNumber 10.0 "",
      wigglePathsOperatorDetail = createDefaultAnimatableNumber 3.0 "",
      wigglePathsOperatorPoints = WigglePointTypeSmooth,
      wigglePathsOperatorCorrelation = createDefaultAnimatableNumber 50.0 "",
      wigglePathsOperatorTemporalPhase = createDefaultAnimatableNumber 0.0 "",
      wigglePathsOperatorSpatialPhase = createDefaultAnimatableNumber 0.0 "",
      wigglePathsOperatorRandomSeed = 12345.0
    }

-- | Create default zigzag operator
createDefaultZigZag :: ZigZagOperator
createDefaultZigZag =
  ZigZagOperator
    { zigZagOperatorType = "zigZag",
      zigZagOperatorName = "Zig Zag",
      zigZagOperatorSize = createDefaultAnimatableNumber 10.0 "",
      zigZagOperatorRidgesPerSegment = createDefaultAnimatableNumber 5.0 "",
      zigZagOperatorPoints = ZigZagPointTypeSmooth
    }

-- | Create default twist operator
createDefaultTwist :: TwistOperator
createDefaultTwist =
  TwistOperator
    { twistOperatorType = "twist",
      twistOperatorName = "Twist",
      twistOperatorAngle = createDefaultAnimatableNumber 0.0 "Angle",
      twistOperatorCenter = createDefaultAnimatablePoint "Center"
    }

-- | Create default rounded corners operator
createDefaultRoundedCorners :: RoundedCornersOperator
createDefaultRoundedCorners =
  RoundedCornersOperator
    { roundedCornersOperatorType = "roundedCorners",
      roundedCornersOperatorName = "Rounded Corners",
      roundedCornersOperatorRadius = createDefaultAnimatableNumber 10.0 ""
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                 // transform // and // repeater // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default shape transform
createDefaultShapeTransform :: ShapeTransform
createDefaultShapeTransform =
  ShapeTransform
    { shapeTransformType = "transform",
      shapeTransformName = "Transform",
      shapeTransformAnchorPoint = createDefaultAnimatablePoint "Anchor Point",
      shapeTransformPosition = createDefaultAnimatablePoint "Position",
      shapeTransformScale =
        createAnimatableProperty
          "shape_prop_Scale_point"
          "Scale"
          (Point2D 100.0 100.0)
          PropertyTypePosition
          Nothing,
      shapeTransformRotation = createDefaultAnimatableNumber 0.0 "Rotation",
      shapeTransformSkew = createDefaultAnimatableNumber 0.0 "Skew",
      shapeTransformSkewAxis = createDefaultAnimatableNumber 0.0 "Skew Axis",
      shapeTransformOpacity = createDefaultAnimatableNumber 100.0 "Opacity"
    }

-- | Create default repeater operator
createDefaultRepeater :: RepeaterOperator
createDefaultRepeater =
  let position =
        createAnimatableProperty
          "shape_prop_Position_point"
          "Position"
          (Point2D 100.0 0.0)
          PropertyTypePosition
          Nothing
      scale =
        createAnimatableProperty
          "shape_prop_Scale_point"
          "Scale"
          (Point2D 100.0 100.0)
          PropertyTypePosition
          Nothing
   in RepeaterOperator
        { repeaterOperatorType = "repeater",
          repeaterOperatorName = "Repeater",
          repeaterOperatorCopies = createDefaultAnimatableNumber 3.0 "Copies",
          repeaterOperatorOffset = createDefaultAnimatableNumber 0.0 "Offset",
          repeaterOperatorComposite = RepeaterCompositeBelow,
          repeaterOperatorTransform =
            RepeaterTransform
              { repeaterTransformAnchorPoint =
                  createDefaultAnimatablePoint "Anchor Point",
                repeaterTransformPosition = position,
                repeaterTransformScale = scale,
                repeaterTransformRotation =
                  createDefaultAnimatableNumber 0.0 "Rotation",
                repeaterTransformStartOpacity =
                  createDefaultAnimatableNumber 100.0 "Start Opacity",
                repeaterTransformEndOpacity =
                  createDefaultAnimatableNumber 100.0 "End Opacity"
              }
        }

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // group // factory
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default shape group
createDefaultGroup :: ShapeGroup
createDefaultGroup =
  ShapeGroup
    { shapeGroupType = "group",
      shapeGroupName = "Group",
      shapeGroupContents = [],
      shapeGroupTransform = createDefaultShapeTransform,
      shapeGroupBlendMode = "normal"
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                      // illustrator // operator // factories
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default extrude operator
createDefaultExtrude :: ExtrudeOperator
createDefaultExtrude =
  ExtrudeOperator
    { extrudeOperatorType = "extrude",
      extrudeOperatorName = "Extrude",
      extrudeOperatorDepth = createDefaultAnimatableNumber 50.0 "",
      extrudeOperatorBevelDepth = createDefaultAnimatableNumber 5.0 "",
      extrudeOperatorBevelSegments = 3.0,
      extrudeOperatorCapType = ExtrudeCapTypeFlat,
      extrudeOperatorMaterial =
        ExtrudeMaterial
          { extrudeMaterialFrontColor =
              createDefaultAnimatableColor 255.0 255.0 255.0 1.0 "",
            extrudeMaterialSideColor =
              createDefaultAnimatableColor 200.0 200.0 200.0 1.0 "",
            extrudeMaterialBevelColor =
              createDefaultAnimatableColor 180.0 180.0 180.0 1.0 ""
          }
    }

-- | Create default trace operator
createDefaultTrace :: TraceOperator
createDefaultTrace =
  TraceOperator
    { traceOperatorType = "trace",
      traceOperatorName = "Image Trace",
      traceOperatorMode = TraceModeBlackAndWhite,
      traceOperatorThreshold = createDefaultAnimatableNumber 128.0 "",
      traceOperatorColors = 16.0,
      traceOperatorCornerAngle = 20.0,
      traceOperatorPathFitting = createDefaultAnimatableNumber 2.0 "",
      traceOperatorNoiseReduction = createDefaultAnimatableNumber 25.0 "",
      traceOperatorSourceLayerId = Nothing,
      traceOperatorSourceFrame = Nothing
    }

-- | Create default simplify path operator
createDefaultSimplifyPath :: SimplifyPathOperator
createDefaultSimplifyPath =
  SimplifyPathOperator
    { simplifyPathOperatorType = "simplifyPath",
      simplifyPathOperatorName = "Simplify Path",
      simplifyPathOperatorTolerance = createDefaultAnimatableNumber 50.0 "",
      simplifyPathOperatorAngleTolerance =
        createDefaultAnimatableNumber 10.0 "",
      simplifyPathOperatorStraightLines = False
    }

-- | Create default smooth path operator
createDefaultSmoothPath :: SmoothPathOperator
createDefaultSmoothPath =
  SmoothPathOperator
    { smoothPathOperatorType = "smoothPath",
      smoothPathOperatorName = "Smooth Path",
      smoothPathOperatorAmount = createDefaultAnimatableNumber 50.0 ""
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // layer // data // factory
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default shape layer data
createDefaultShapeLayerData :: ShapeLayerData
createDefaultShapeLayerData =
  ShapeLayerData
    { shapeLayerDataContents = [],
      shapeLayerDataBlendMode = "normal",
      shapeLayerDataQuality = ShapeQualityNormal,
      shapeLayerDataGPUAccelerated = True
    }
