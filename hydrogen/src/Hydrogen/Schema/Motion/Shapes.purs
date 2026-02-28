-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // motion // shapes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape layer types and enums for vector graphics.
-- |
-- | Shapes are the fundamental drawing primitives for motion graphics.
-- | Shape layers can contain multiple shape contents including:
-- | - Generators: Rectangle, Ellipse, Polygon, Star, Path
-- | - Modifiers: Fill, Stroke, Gradient
-- | - Operators: Trim, Merge, Offset, Wiggle, ZigZag
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Shapes` from the Haskell backend.

module Hydrogen.Schema.Motion.Shapes
  ( -- * Fill/Stroke Enums
    FillRule(..)
  , fillRuleToString
  , fillRuleFromString
  
  , LineCap(..)
  , lineCapToString
  , lineCapFromString
  
  , LineJoin(..)
  , lineJoinToString
  , lineJoinFromString
  
  -- * Path Operator Enums
  , TrimMode(..)
  , trimModeToString
  , trimModeFromString
  
  , MergeMode(..)
  , mergeModeToString
  , mergeModeFromString
  
  , OffsetJoin(..)
  , offsetJoinToString
  , offsetJoinFromString
  
  , WigglePointType(..)
  , wigglePointTypeToString
  , wigglePointTypeFromString
  
  , ZigZagPointType(..)
  , zigZagPointTypeToString
  , zigZagPointTypeFromString
  
  -- * Repeater/Group
  , RepeaterComposite(..)
  , repeaterCompositeToString
  , repeaterCompositeFromString
  
  -- * Shape Content Type
  , ShapeContentType(..)
  , shapeContentTypeToString
  , shapeContentTypeFromString
  , isShapeContentTypeGenerator
  , isShapeContentTypeModifier
  , isShapeContentTypeOperator
  
  -- * Gradient
  , GradientType(..)
  , gradientTypeToString
  , gradientTypeFromString
  
  -- * Quality
  , ShapeQuality(..)
  , shapeQualityToString
  , shapeQualityFromString
  
  -- * Extrude
  , ExtrudeCapType(..)
  , extrudeCapTypeToString
  , extrudeCapTypeFromString
  
  -- * Trace
  , TraceMode(..)
  , traceModeToString
  , traceModeFromString
  
  -- * Path Direction
  , PathDirection(..)
  , pathDirectionToString
  , pathDirectionFromString
  , pathDirectionToInt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // fill // rule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill rule for determining inside/outside of paths.
data FillRule
  = FRNonzero   -- ^ Non-zero winding rule
  | FREvenodd   -- ^ Even-odd rule

derive instance eqFillRule :: Eq FillRule
derive instance ordFillRule :: Ord FillRule

instance showFillRule :: Show FillRule where
  show FRNonzero = "FRNonzero"
  show FREvenodd = "FREvenodd"

fillRuleToString :: FillRule -> String
fillRuleToString FRNonzero = "nonzero"
fillRuleToString FREvenodd = "evenodd"

fillRuleFromString :: String -> Maybe FillRule
fillRuleFromString "nonzero" = Just FRNonzero
fillRuleFromString "evenodd" = Just FREvenodd
fillRuleFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // line // cap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line cap style for stroke endpoints.
data LineCap
  = LCButt    -- ^ Flat end at endpoint
  | LCRound   -- ^ Rounded end
  | LCSquare  -- ^ Square end extending beyond endpoint

derive instance eqLineCap :: Eq LineCap
derive instance ordLineCap :: Ord LineCap

instance showLineCap :: Show LineCap where
  show LCButt = "LCButt"
  show LCRound = "LCRound"
  show LCSquare = "LCSquare"

lineCapToString :: LineCap -> String
lineCapToString LCButt = "butt"
lineCapToString LCRound = "round"
lineCapToString LCSquare = "square"

lineCapFromString :: String -> Maybe LineCap
lineCapFromString "butt" = Just LCButt
lineCapFromString "round" = Just LCRound
lineCapFromString "square" = Just LCSquare
lineCapFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // line // join
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line join style for stroke corners.
data LineJoin
  = LJMiter  -- ^ Sharp corner (may be clipped)
  | LJRound  -- ^ Rounded corner
  | LJBevel  -- ^ Beveled corner

derive instance eqLineJoin :: Eq LineJoin
derive instance ordLineJoin :: Ord LineJoin

instance showLineJoin :: Show LineJoin where
  show LJMiter = "LJMiter"
  show LJRound = "LJRound"
  show LJBevel = "LJBevel"

lineJoinToString :: LineJoin -> String
lineJoinToString LJMiter = "miter"
lineJoinToString LJRound = "round"
lineJoinToString LJBevel = "bevel"

lineJoinFromString :: String -> Maybe LineJoin
lineJoinFromString "miter" = Just LJMiter
lineJoinFromString "round" = Just LJRound
lineJoinFromString "bevel" = Just LJBevel
lineJoinFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // trim // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for Trim Paths operator.
data TrimMode
  = TMSimultaneously  -- ^ Trim all paths together
  | TMIndividually    -- ^ Trim each path separately

derive instance eqTrimMode :: Eq TrimMode
derive instance ordTrimMode :: Ord TrimMode

instance showTrimMode :: Show TrimMode where
  show TMSimultaneously = "TMSimultaneously"
  show TMIndividually = "TMIndividually"

trimModeToString :: TrimMode -> String
trimModeToString TMSimultaneously = "simultaneously"
trimModeToString TMIndividually = "individually"

trimModeFromString :: String -> Maybe TrimMode
trimModeFromString "simultaneously" = Just TMSimultaneously
trimModeFromString "individually" = Just TMIndividually
trimModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // merge // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for Merge Paths operator.
data MergeMode
  = MMAdd         -- ^ Union of paths
  | MMSubtract    -- ^ Subtract from first path
  | MMIntersect   -- ^ Intersection of paths
  | MMExclude     -- ^ Exclusive OR
  | MMMinusFront  -- ^ Subtract front from back
  | MMMinusBack   -- ^ Subtract back from front

derive instance eqMergeMode :: Eq MergeMode
derive instance ordMergeMode :: Ord MergeMode

instance showMergeMode :: Show MergeMode where
  show MMAdd = "MMAdd"
  show MMSubtract = "MMSubtract"
  show MMIntersect = "MMIntersect"
  show MMExclude = "MMExclude"
  show MMMinusFront = "MMMinusFront"
  show MMMinusBack = "MMMinusBack"

mergeModeToString :: MergeMode -> String
mergeModeToString MMAdd = "add"
mergeModeToString MMSubtract = "subtract"
mergeModeToString MMIntersect = "intersect"
mergeModeToString MMExclude = "exclude"
mergeModeToString MMMinusFront = "minus-front"
mergeModeToString MMMinusBack = "minus-back"

mergeModeFromString :: String -> Maybe MergeMode
mergeModeFromString "add" = Just MMAdd
mergeModeFromString "subtract" = Just MMSubtract
mergeModeFromString "intersect" = Just MMIntersect
mergeModeFromString "exclude" = Just MMExclude
mergeModeFromString "minus-front" = Just MMMinusFront
mergeModeFromString "minus-back" = Just MMMinusBack
mergeModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // offset // join
-- ═════════════════════════════════════════════════════════════════════════════

-- | Join type for Offset Paths operator.
data OffsetJoin
  = OJMiter  -- ^ Sharp corners
  | OJRound  -- ^ Rounded corners
  | OJBevel  -- ^ Beveled corners

derive instance eqOffsetJoin :: Eq OffsetJoin
derive instance ordOffsetJoin :: Ord OffsetJoin

instance showOffsetJoin :: Show OffsetJoin where
  show OJMiter = "OJMiter"
  show OJRound = "OJRound"
  show OJBevel = "OJBevel"

offsetJoinToString :: OffsetJoin -> String
offsetJoinToString OJMiter = "miter"
offsetJoinToString OJRound = "round"
offsetJoinToString OJBevel = "bevel"

offsetJoinFromString :: String -> Maybe OffsetJoin
offsetJoinFromString "miter" = Just OJMiter
offsetJoinFromString "round" = Just OJRound
offsetJoinFromString "bevel" = Just OJBevel
offsetJoinFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // wiggle // point // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point type for Wiggle Paths operator.
data WigglePointType
  = WPTCorner  -- ^ Sharp corners
  | WPTSmooth  -- ^ Smooth curves

derive instance eqWigglePointType :: Eq WigglePointType
derive instance ordWigglePointType :: Ord WigglePointType

instance showWigglePointType :: Show WigglePointType where
  show WPTCorner = "WPTCorner"
  show WPTSmooth = "WPTSmooth"

wigglePointTypeToString :: WigglePointType -> String
wigglePointTypeToString WPTCorner = "corner"
wigglePointTypeToString WPTSmooth = "smooth"

wigglePointTypeFromString :: String -> Maybe WigglePointType
wigglePointTypeFromString "corner" = Just WPTCorner
wigglePointTypeFromString "smooth" = Just WPTSmooth
wigglePointTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // zigzag // point // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point type for ZigZag operator.
data ZigZagPointType
  = ZZPTCorner  -- ^ Sharp corners
  | ZZPTSmooth  -- ^ Smooth curves

derive instance eqZigZagPointType :: Eq ZigZagPointType
derive instance ordZigZagPointType :: Ord ZigZagPointType

instance showZigZagPointType :: Show ZigZagPointType where
  show ZZPTCorner = "ZZPTCorner"
  show ZZPTSmooth = "ZZPTSmooth"

zigZagPointTypeToString :: ZigZagPointType -> String
zigZagPointTypeToString ZZPTCorner = "corner"
zigZagPointTypeToString ZZPTSmooth = "smooth"

zigZagPointTypeFromString :: String -> Maybe ZigZagPointType
zigZagPointTypeFromString "corner" = Just ZZPTCorner
zigZagPointTypeFromString "smooth" = Just ZZPTSmooth
zigZagPointTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // repeater // composite
-- ═════════════════════════════════════════════════════════════════════════════

-- | Composite order for Repeater operator.
data RepeaterComposite
  = RCAbove  -- ^ Copies appear above original
  | RCBelow  -- ^ Copies appear below original

derive instance eqRepeaterComposite :: Eq RepeaterComposite
derive instance ordRepeaterComposite :: Ord RepeaterComposite

instance showRepeaterComposite :: Show RepeaterComposite where
  show RCAbove = "RCAbove"
  show RCBelow = "RCBelow"

repeaterCompositeToString :: RepeaterComposite -> String
repeaterCompositeToString RCAbove = "above"
repeaterCompositeToString RCBelow = "below"

repeaterCompositeFromString :: String -> Maybe RepeaterComposite
repeaterCompositeFromString "above" = Just RCAbove
repeaterCompositeFromString "below" = Just RCBelow
repeaterCompositeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // shape // content // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of shape content item (26 variants).
-- |
-- | Shape layers contain a stack of content items that are processed
-- | in order to produce the final rendered shape.
data ShapeContentType
  -- Generators
  = SCTRectangle       -- ^ Rectangle generator
  | SCTEllipse         -- ^ Ellipse generator
  | SCTPolygon         -- ^ Polygon generator
  | SCTStar            -- ^ Star generator
  | SCTPath            -- ^ Bezier path generator
  -- Modifiers
  | SCTFill            -- ^ Solid fill
  | SCTStroke          -- ^ Solid stroke
  | SCTGradientFill    -- ^ Gradient fill
  | SCTGradientStroke  -- ^ Gradient stroke
  -- Operators
  | SCTTrimPaths       -- ^ Trim paths operator
  | SCTMergePaths      -- ^ Merge paths operator
  | SCTOffsetPaths     -- ^ Offset paths operator
  | SCTPuckerBloat     -- ^ Pucker/bloat operator
  | SCTWigglePaths     -- ^ Wiggle paths operator
  | SCTZigZag          -- ^ ZigZag operator
  | SCTTwist           -- ^ Twist operator
  | SCTRoundedCorners  -- ^ Rounded corners operator
  | SCTRepeater        -- ^ Repeater operator
  | SCTTransform       -- ^ Transform operator
  -- Group
  | SCTGroup           -- ^ Group container
  -- Illustrator-style
  | SCTSimplifyPath    -- ^ Simplify path operator
  | SCTSmoothPath      -- ^ Smooth path operator
  | SCTExtrude         -- ^ 3D extrusion
  | SCTTrace           -- ^ Image trace

derive instance eqShapeContentType :: Eq ShapeContentType
derive instance ordShapeContentType :: Ord ShapeContentType

instance showShapeContentType :: Show ShapeContentType where
  show SCTRectangle = "SCTRectangle"
  show SCTEllipse = "SCTEllipse"
  show SCTPolygon = "SCTPolygon"
  show SCTStar = "SCTStar"
  show SCTPath = "SCTPath"
  show SCTFill = "SCTFill"
  show SCTStroke = "SCTStroke"
  show SCTGradientFill = "SCTGradientFill"
  show SCTGradientStroke = "SCTGradientStroke"
  show SCTTrimPaths = "SCTTrimPaths"
  show SCTMergePaths = "SCTMergePaths"
  show SCTOffsetPaths = "SCTOffsetPaths"
  show SCTPuckerBloat = "SCTPuckerBloat"
  show SCTWigglePaths = "SCTWigglePaths"
  show SCTZigZag = "SCTZigZag"
  show SCTTwist = "SCTTwist"
  show SCTRoundedCorners = "SCTRoundedCorners"
  show SCTRepeater = "SCTRepeater"
  show SCTTransform = "SCTTransform"
  show SCTGroup = "SCTGroup"
  show SCTSimplifyPath = "SCTSimplifyPath"
  show SCTSmoothPath = "SCTSmoothPath"
  show SCTExtrude = "SCTExtrude"
  show SCTTrace = "SCTTrace"

shapeContentTypeToString :: ShapeContentType -> String
shapeContentTypeToString SCTRectangle = "rectangle"
shapeContentTypeToString SCTEllipse = "ellipse"
shapeContentTypeToString SCTPolygon = "polygon"
shapeContentTypeToString SCTStar = "star"
shapeContentTypeToString SCTPath = "path"
shapeContentTypeToString SCTFill = "fill"
shapeContentTypeToString SCTStroke = "stroke"
shapeContentTypeToString SCTGradientFill = "gradient-fill"
shapeContentTypeToString SCTGradientStroke = "gradient-stroke"
shapeContentTypeToString SCTTrimPaths = "trim-paths"
shapeContentTypeToString SCTMergePaths = "merge-paths"
shapeContentTypeToString SCTOffsetPaths = "offset-paths"
shapeContentTypeToString SCTPuckerBloat = "pucker-bloat"
shapeContentTypeToString SCTWigglePaths = "wiggle-paths"
shapeContentTypeToString SCTZigZag = "zigzag"
shapeContentTypeToString SCTTwist = "twist"
shapeContentTypeToString SCTRoundedCorners = "rounded-corners"
shapeContentTypeToString SCTRepeater = "repeater"
shapeContentTypeToString SCTTransform = "transform"
shapeContentTypeToString SCTGroup = "group"
shapeContentTypeToString SCTSimplifyPath = "simplify-path"
shapeContentTypeToString SCTSmoothPath = "smooth-path"
shapeContentTypeToString SCTExtrude = "extrude"
shapeContentTypeToString SCTTrace = "trace"

shapeContentTypeFromString :: String -> Maybe ShapeContentType
shapeContentTypeFromString "rectangle" = Just SCTRectangle
shapeContentTypeFromString "ellipse" = Just SCTEllipse
shapeContentTypeFromString "polygon" = Just SCTPolygon
shapeContentTypeFromString "star" = Just SCTStar
shapeContentTypeFromString "path" = Just SCTPath
shapeContentTypeFromString "fill" = Just SCTFill
shapeContentTypeFromString "stroke" = Just SCTStroke
shapeContentTypeFromString "gradient-fill" = Just SCTGradientFill
shapeContentTypeFromString "gradient-stroke" = Just SCTGradientStroke
shapeContentTypeFromString "trim-paths" = Just SCTTrimPaths
shapeContentTypeFromString "merge-paths" = Just SCTMergePaths
shapeContentTypeFromString "offset-paths" = Just SCTOffsetPaths
shapeContentTypeFromString "pucker-bloat" = Just SCTPuckerBloat
shapeContentTypeFromString "wiggle-paths" = Just SCTWigglePaths
shapeContentTypeFromString "zigzag" = Just SCTZigZag
shapeContentTypeFromString "twist" = Just SCTTwist
shapeContentTypeFromString "rounded-corners" = Just SCTRoundedCorners
shapeContentTypeFromString "repeater" = Just SCTRepeater
shapeContentTypeFromString "transform" = Just SCTTransform
shapeContentTypeFromString "group" = Just SCTGroup
shapeContentTypeFromString "simplify-path" = Just SCTSimplifyPath
shapeContentTypeFromString "smooth-path" = Just SCTSmoothPath
shapeContentTypeFromString "extrude" = Just SCTExtrude
shapeContentTypeFromString "trace" = Just SCTTrace
shapeContentTypeFromString _ = Nothing

-- | Check if shape content type is a generator.
isShapeContentTypeGenerator :: ShapeContentType -> Boolean
isShapeContentTypeGenerator SCTRectangle = true
isShapeContentTypeGenerator SCTEllipse = true
isShapeContentTypeGenerator SCTPolygon = true
isShapeContentTypeGenerator SCTStar = true
isShapeContentTypeGenerator SCTPath = true
isShapeContentTypeGenerator _ = false

-- | Check if shape content type is a modifier.
isShapeContentTypeModifier :: ShapeContentType -> Boolean
isShapeContentTypeModifier SCTFill = true
isShapeContentTypeModifier SCTStroke = true
isShapeContentTypeModifier SCTGradientFill = true
isShapeContentTypeModifier SCTGradientStroke = true
isShapeContentTypeModifier _ = false

-- | Check if shape content type is an operator.
isShapeContentTypeOperator :: ShapeContentType -> Boolean
isShapeContentTypeOperator SCTTrimPaths = true
isShapeContentTypeOperator SCTMergePaths = true
isShapeContentTypeOperator SCTOffsetPaths = true
isShapeContentTypeOperator SCTPuckerBloat = true
isShapeContentTypeOperator SCTWigglePaths = true
isShapeContentTypeOperator SCTZigZag = true
isShapeContentTypeOperator SCTTwist = true
isShapeContentTypeOperator SCTRoundedCorners = true
isShapeContentTypeOperator SCTRepeater = true
isShapeContentTypeOperator SCTTransform = true
isShapeContentTypeOperator SCTSimplifyPath = true
isShapeContentTypeOperator SCTSmoothPath = true
isShapeContentTypeOperator _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of gradient.
data GradientType
  = GTLinear  -- ^ Linear gradient
  | GTRadial  -- ^ Radial gradient

derive instance eqGradientType :: Eq GradientType
derive instance ordGradientType :: Ord GradientType

instance showGradientType :: Show GradientType where
  show GTLinear = "GTLinear"
  show GTRadial = "GTRadial"

gradientTypeToString :: GradientType -> String
gradientTypeToString GTLinear = "linear"
gradientTypeToString GTRadial = "radial"

gradientTypeFromString :: String -> Maybe GradientType
gradientTypeFromString "linear" = Just GTLinear
gradientTypeFromString "radial" = Just GTRadial
gradientTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shape // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rendering quality for shapes.
data ShapeQuality
  = SQDraft   -- ^ Fast preview
  | SQNormal  -- ^ Balanced
  | SQHigh    -- ^ Best quality

derive instance eqShapeQuality :: Eq ShapeQuality
derive instance ordShapeQuality :: Ord ShapeQuality

instance showShapeQuality :: Show ShapeQuality where
  show SQDraft = "SQDraft"
  show SQNormal = "SQNormal"
  show SQHigh = "SQHigh"

shapeQualityToString :: ShapeQuality -> String
shapeQualityToString SQDraft = "draft"
shapeQualityToString SQNormal = "normal"
shapeQualityToString SQHigh = "high"

shapeQualityFromString :: String -> Maybe ShapeQuality
shapeQualityFromString "draft" = Just SQDraft
shapeQualityFromString "normal" = Just SQNormal
shapeQualityFromString "high" = Just SQHigh
shapeQualityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // extrude // cap // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cap type for 3D extrusion.
data ExtrudeCapType
  = ECTFlat   -- ^ Flat cap
  | ECTRound  -- ^ Rounded cap
  | ECTBevel  -- ^ Beveled cap

derive instance eqExtrudeCapType :: Eq ExtrudeCapType
derive instance ordExtrudeCapType :: Ord ExtrudeCapType

instance showExtrudeCapType :: Show ExtrudeCapType where
  show ECTFlat = "ECTFlat"
  show ECTRound = "ECTRound"
  show ECTBevel = "ECTBevel"

extrudeCapTypeToString :: ExtrudeCapType -> String
extrudeCapTypeToString ECTFlat = "flat"
extrudeCapTypeToString ECTRound = "round"
extrudeCapTypeToString ECTBevel = "bevel"

extrudeCapTypeFromString :: String -> Maybe ExtrudeCapType
extrudeCapTypeFromString "flat" = Just ECTFlat
extrudeCapTypeFromString "round" = Just ECTRound
extrudeCapTypeFromString "bevel" = Just ECTBevel
extrudeCapTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // trace // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for image trace operation.
data TraceMode
  = TMBlackAndWhite  -- ^ Black and white tracing
  | TMGrayscale      -- ^ Grayscale tracing
  | TMColor          -- ^ Full color tracing

derive instance eqTraceMode :: Eq TraceMode
derive instance ordTraceMode :: Ord TraceMode

instance showTraceMode :: Show TraceMode where
  show TMBlackAndWhite = "TMBlackAndWhite"
  show TMGrayscale = "TMGrayscale"
  show TMColor = "TMColor"

traceModeToString :: TraceMode -> String
traceModeToString TMBlackAndWhite = "black-and-white"
traceModeToString TMGrayscale = "grayscale"
traceModeToString TMColor = "color"

traceModeFromString :: String -> Maybe TraceMode
traceModeFromString "black-and-white" = Just TMBlackAndWhite
traceModeFromString "grayscale" = Just TMGrayscale
traceModeFromString "color" = Just TMColor
traceModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // path // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Winding direction of a path.
data PathDirection
  = PDClockwise         -- ^ Clockwise winding
  | PDCounterClockwise  -- ^ Counter-clockwise winding

derive instance eqPathDirection :: Eq PathDirection
derive instance ordPathDirection :: Ord PathDirection

instance showPathDirection :: Show PathDirection where
  show PDClockwise = "PDClockwise"
  show PDCounterClockwise = "PDCounterClockwise"

pathDirectionToString :: PathDirection -> String
pathDirectionToString PDClockwise = "clockwise"
pathDirectionToString PDCounterClockwise = "counter-clockwise"

pathDirectionFromString :: String -> Maybe PathDirection
pathDirectionFromString "clockwise" = Just PDClockwise
pathDirectionFromString "counter-clockwise" = Just PDCounterClockwise
pathDirectionFromString _ = Nothing

-- | Convert path direction to integer multiplier.
-- | Useful for winding calculations.
pathDirectionToInt :: PathDirection -> Int
pathDirectionToInt PDClockwise = 1
pathDirectionToInt PDCounterClockwise = -1
