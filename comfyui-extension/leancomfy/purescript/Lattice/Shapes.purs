-- | Lattice.Shapes - Shape layer types and enums
-- |
-- | Source: leancomfy/lean/Lattice/Shapes.lean
-- | Consolidated from Lean4 Shapes/* submodules.

module Lattice.Shapes
  ( FillRule(..)
  , LineCap(..)
  , LineJoin(..)
  , TrimMode(..)
  , MergeMode(..)
  , OffsetJoin(..)
  , WigglePointType(..)
  , ZigZagPointType(..)
  , RepeaterComposite(..)
  , ShapeContentType(..)
  , GradientType(..)
  , ShapeQuality(..)
  , ExtrudeCapType(..)
  , TraceMode(..)
  , PathDirection(..)
  , pathDirectionToInt
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Fill/Stroke Enums
--------------------------------------------------------------------------------

data FillRule = FRNonzero | FREvenodd

derive instance Eq FillRule
derive instance Generic FillRule _
instance Show FillRule where show = genericShow

data LineCap = LCButt | LCRound | LCSquare

derive instance Eq LineCap
derive instance Generic LineCap _
instance Show LineCap where show = genericShow

data LineJoin = LJMiter | LJRound | LJBevel

derive instance Eq LineJoin
derive instance Generic LineJoin _
instance Show LineJoin where show = genericShow

--------------------------------------------------------------------------------
-- Path Operator Enums
--------------------------------------------------------------------------------

data TrimMode = TMSimultaneously | TMIndividually

derive instance Eq TrimMode
derive instance Generic TrimMode _
instance Show TrimMode where show = genericShow

data MergeMode
  = MMAdd | MMSubtract | MMIntersect | MMExclude | MMMinusFront | MMMinusBack

derive instance Eq MergeMode
derive instance Generic MergeMode _
instance Show MergeMode where show = genericShow

data OffsetJoin = OJMiter | OJRound | OJBevel

derive instance Eq OffsetJoin
derive instance Generic OffsetJoin _
instance Show OffsetJoin where show = genericShow

data WigglePointType = WPTCorner | WPTSmooth

derive instance Eq WigglePointType
derive instance Generic WigglePointType _
instance Show WigglePointType where show = genericShow

data ZigZagPointType = ZZPTCorner | ZZPTSmooth

derive instance Eq ZigZagPointType
derive instance Generic ZigZagPointType _
instance Show ZigZagPointType where show = genericShow

--------------------------------------------------------------------------------
-- Repeater/Group
--------------------------------------------------------------------------------

data RepeaterComposite = RCAbove | RCBelow

derive instance Eq RepeaterComposite
derive instance Generic RepeaterComposite _
instance Show RepeaterComposite where show = genericShow

--------------------------------------------------------------------------------
-- Shape Content Type
--------------------------------------------------------------------------------

data ShapeContentType
  -- Generators
  = SCTRectangle | SCTEllipse | SCTPolygon | SCTStar | SCTPath
  -- Modifiers
  | SCTFill | SCTStroke | SCTGradientFill | SCTGradientStroke
  -- Operators
  | SCTTrimPaths | SCTMergePaths | SCTOffsetPaths | SCTPuckerBloat
  | SCTWigglePaths | SCTZigZag | SCTTwist | SCTRoundedCorners
  | SCTRepeater | SCTTransform
  -- Group
  | SCTGroup
  -- Illustrator
  | SCTSimplifyPath | SCTSmoothPath | SCTExtrude | SCTTrace

derive instance Eq ShapeContentType
derive instance Generic ShapeContentType _
instance Show ShapeContentType where show = genericShow

--------------------------------------------------------------------------------
-- Gradient
--------------------------------------------------------------------------------

data GradientType = GTLinear | GTRadial

derive instance Eq GradientType
derive instance Generic GradientType _
instance Show GradientType where show = genericShow

--------------------------------------------------------------------------------
-- Quality
--------------------------------------------------------------------------------

data ShapeQuality = SQDraft | SQNormal | SQHigh

derive instance Eq ShapeQuality
derive instance Generic ShapeQuality _
instance Show ShapeQuality where show = genericShow

--------------------------------------------------------------------------------
-- Extrude
--------------------------------------------------------------------------------

data ExtrudeCapType = ECTFlat | ECTRound | ECTBevel

derive instance Eq ExtrudeCapType
derive instance Generic ExtrudeCapType _
instance Show ExtrudeCapType where show = genericShow

--------------------------------------------------------------------------------
-- Trace
--------------------------------------------------------------------------------

data TraceMode = TMBlackAndWhite | TMGrayscale | TMColor

derive instance Eq TraceMode
derive instance Generic TraceMode _
instance Show TraceMode where show = genericShow

--------------------------------------------------------------------------------
-- Path Direction
--------------------------------------------------------------------------------

data PathDirection = PDClockwise | PDCounterClockwise

derive instance Eq PathDirection
derive instance Generic PathDirection _
instance Show PathDirection where show = genericShow

pathDirectionToInt :: PathDirection -> Int
pathDirectionToInt PDClockwise = 1
pathDirectionToInt PDCounterClockwise = -1
