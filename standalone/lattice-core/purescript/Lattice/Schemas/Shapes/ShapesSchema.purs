-- | Lattice.Schemas.Shapes.ShapesSchema - Shape layer enums
-- |
-- | Shape layer enums for generators, modifiers, and path operators.
-- |
-- | Source: ui/src/schemas/layers/shapes-schema.ts

module Lattice.Schemas.Shapes.ShapesSchema
  ( -- Fill Rule
    FillRule(..)
  , fillRuleFromString
  , fillRuleToString
    -- Line Cap
  , LineCap(..)
  , lineCapFromString
  , lineCapToString
    -- Line Join
  , LineJoin(..)
  , lineJoinFromString
  , lineJoinToString
    -- Trim Mode
  , TrimMode(..)
  , trimModeFromString
  , trimModeToString
    -- Merge Mode
  , MergeMode(..)
  , mergeModeFromString
  , mergeModeToString
    -- Wiggle Point Type
  , WigglePointType(..)
  , wigglePointTypeFromString
  , wigglePointTypeToString
    -- Repeater Composite
  , RepeaterComposite(..)
  , repeaterCompositeFromString
  , repeaterCompositeToString
    -- Cap Type
  , CapType(..)
  , capTypeFromString
  , capTypeToString
    -- Trace Mode
  , TraceMode(..)
  , traceModeFromString
  , traceModeToString
    -- Shape Quality
  , ShapeQuality(..)
  , shapeQualityFromString
  , shapeQualityToString
    -- Shape Direction
  , ShapeDirection(..)
  , shapeDirectionFromInt
  , shapeDirectionToInt
    -- Constants
  , maxVerticesPerPath
  , minClosedPathVertices
  , maxGradientStops
  , minGradientStops
  , maxDashSegments
  , maxContentsPerGroup
  , maxBevelSegments
  , maxTraceColors
  , maxMiterLimit
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Fill Rule
-- ────────────────────────────────────────────────────────────────────────────

-- | Fill rule options
data FillRule
  = FillNonZero
  | FillEvenOdd

derive instance Eq FillRule
derive instance Generic FillRule _

instance Show FillRule where
  show = genericShow

fillRuleFromString :: String -> Maybe FillRule
fillRuleFromString = case _ of
  "nonzero" -> Just FillNonZero
  "evenodd" -> Just FillEvenOdd
  _ -> Nothing

fillRuleToString :: FillRule -> String
fillRuleToString = case _ of
  FillNonZero -> "nonzero"
  FillEvenOdd -> "evenodd"

-- ────────────────────────────────────────────────────────────────────────────
-- Line Cap
-- ────────────────────────────────────────────────────────────────────────────

-- | Line cap options
data LineCap
  = CapButt
  | CapRound
  | CapSquare

derive instance Eq LineCap
derive instance Generic LineCap _

instance Show LineCap where
  show = genericShow

lineCapFromString :: String -> Maybe LineCap
lineCapFromString = case _ of
  "butt" -> Just CapButt
  "round" -> Just CapRound
  "square" -> Just CapSquare
  _ -> Nothing

lineCapToString :: LineCap -> String
lineCapToString = case _ of
  CapButt -> "butt"
  CapRound -> "round"
  CapSquare -> "square"

-- ────────────────────────────────────────────────────────────────────────────
-- Line Join
-- ────────────────────────────────────────────────────────────────────────────

-- | Line join options
data LineJoin
  = JoinMiter
  | JoinRound
  | JoinBevel

derive instance Eq LineJoin
derive instance Generic LineJoin _

instance Show LineJoin where
  show = genericShow

lineJoinFromString :: String -> Maybe LineJoin
lineJoinFromString = case _ of
  "miter" -> Just JoinMiter
  "round" -> Just JoinRound
  "bevel" -> Just JoinBevel
  _ -> Nothing

lineJoinToString :: LineJoin -> String
lineJoinToString = case _ of
  JoinMiter -> "miter"
  JoinRound -> "round"
  JoinBevel -> "bevel"

-- ────────────────────────────────────────────────────────────────────────────
-- Trim Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Trim mode options
data TrimMode
  = TrimSimultaneously
  | TrimIndividually

derive instance Eq TrimMode
derive instance Generic TrimMode _

instance Show TrimMode where
  show = genericShow

trimModeFromString :: String -> Maybe TrimMode
trimModeFromString = case _ of
  "simultaneously" -> Just TrimSimultaneously
  "individually" -> Just TrimIndividually
  _ -> Nothing

trimModeToString :: TrimMode -> String
trimModeToString = case _ of
  TrimSimultaneously -> "simultaneously"
  TrimIndividually -> "individually"

-- ────────────────────────────────────────────────────────────────────────────
-- Merge Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Merge mode options (path boolean operations)
data MergeMode
  = MergeAdd
  | MergeSubtract
  | MergeIntersect
  | MergeExclude
  | MergeMinusFront
  | MergeMinusBack

derive instance Eq MergeMode
derive instance Generic MergeMode _

instance Show MergeMode where
  show = genericShow

mergeModeFromString :: String -> Maybe MergeMode
mergeModeFromString = case _ of
  "add" -> Just MergeAdd
  "subtract" -> Just MergeSubtract
  "intersect" -> Just MergeIntersect
  "exclude" -> Just MergeExclude
  "minusFront" -> Just MergeMinusFront
  "minusBack" -> Just MergeMinusBack
  _ -> Nothing

mergeModeToString :: MergeMode -> String
mergeModeToString = case _ of
  MergeAdd -> "add"
  MergeSubtract -> "subtract"
  MergeIntersect -> "intersect"
  MergeExclude -> "exclude"
  MergeMinusFront -> "minusFront"
  MergeMinusBack -> "minusBack"

-- ────────────────────────────────────────────────────────────────────────────
-- Wiggle Point Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Wiggle point type options
data WigglePointType
  = WiggleCorner
  | WiggleSmooth

derive instance Eq WigglePointType
derive instance Generic WigglePointType _

instance Show WigglePointType where
  show = genericShow

wigglePointTypeFromString :: String -> Maybe WigglePointType
wigglePointTypeFromString = case _ of
  "corner" -> Just WiggleCorner
  "smooth" -> Just WiggleSmooth
  _ -> Nothing

wigglePointTypeToString :: WigglePointType -> String
wigglePointTypeToString = case _ of
  WiggleCorner -> "corner"
  WiggleSmooth -> "smooth"

-- ────────────────────────────────────────────────────────────────────────────
-- Repeater Composite
-- ────────────────────────────────────────────────────────────────────────────

-- | Repeater composite options
data RepeaterComposite
  = CompositeAbove
  | CompositeBelow

derive instance Eq RepeaterComposite
derive instance Generic RepeaterComposite _

instance Show RepeaterComposite where
  show = genericShow

repeaterCompositeFromString :: String -> Maybe RepeaterComposite
repeaterCompositeFromString = case _ of
  "above" -> Just CompositeAbove
  "below" -> Just CompositeBelow
  _ -> Nothing

repeaterCompositeToString :: RepeaterComposite -> String
repeaterCompositeToString = case _ of
  CompositeAbove -> "above"
  CompositeBelow -> "below"

-- ────────────────────────────────────────────────────────────────────────────
-- Cap Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Cap type options for extrusion
data CapType
  = CapFlat
  | CapRoundCap
  | CapBevel

derive instance Eq CapType
derive instance Generic CapType _

instance Show CapType where
  show = genericShow

capTypeFromString :: String -> Maybe CapType
capTypeFromString = case _ of
  "flat" -> Just CapFlat
  "round" -> Just CapRoundCap
  "bevel" -> Just CapBevel
  _ -> Nothing

capTypeToString :: CapType -> String
capTypeToString = case _ of
  CapFlat -> "flat"
  CapRoundCap -> "round"
  CapBevel -> "bevel"

-- ────────────────────────────────────────────────────────────────────────────
-- Trace Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Trace mode options
data TraceMode
  = TraceBlackAndWhite
  | TraceGrayscale
  | TraceColor

derive instance Eq TraceMode
derive instance Generic TraceMode _

instance Show TraceMode where
  show = genericShow

traceModeFromString :: String -> Maybe TraceMode
traceModeFromString = case _ of
  "blackAndWhite" -> Just TraceBlackAndWhite
  "grayscale" -> Just TraceGrayscale
  "color" -> Just TraceColor
  _ -> Nothing

traceModeToString :: TraceMode -> String
traceModeToString = case _ of
  TraceBlackAndWhite -> "blackAndWhite"
  TraceGrayscale -> "grayscale"
  TraceColor -> "color"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Quality
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape quality options
data ShapeQuality
  = QualityDraft
  | QualityNormal
  | QualityHigh

derive instance Eq ShapeQuality
derive instance Generic ShapeQuality _

instance Show ShapeQuality where
  show = genericShow

shapeQualityFromString :: String -> Maybe ShapeQuality
shapeQualityFromString = case _ of
  "draft" -> Just QualityDraft
  "normal" -> Just QualityNormal
  "high" -> Just QualityHigh
  _ -> Nothing

shapeQualityToString :: ShapeQuality -> String
shapeQualityToString = case _ of
  QualityDraft -> "draft"
  QualityNormal -> "normal"
  QualityHigh -> "high"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Direction
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape direction (clockwise or counter-clockwise)
data ShapeDirection
  = DirectionClockwise       -- 1
  | DirectionCounterclockwise  -- -1

derive instance Eq ShapeDirection
derive instance Generic ShapeDirection _

instance Show ShapeDirection where
  show = genericShow

shapeDirectionFromInt :: Int -> Maybe ShapeDirection
shapeDirectionFromInt 1 = Just DirectionClockwise
shapeDirectionFromInt (-1) = Just DirectionCounterclockwise
shapeDirectionFromInt _ = Nothing

shapeDirectionToInt :: ShapeDirection -> Int
shapeDirectionToInt DirectionClockwise = 1
shapeDirectionToInt DirectionCounterclockwise = -1

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxVerticesPerPath :: Int
maxVerticesPerPath = 100000

minClosedPathVertices :: Int
minClosedPathVertices = 3

maxGradientStops :: Int
maxGradientStops = 100

minGradientStops :: Int
minGradientStops = 2

maxDashSegments :: Int
maxDashSegments = 1000

maxContentsPerGroup :: Int
maxContentsPerGroup = 1000

maxBevelSegments :: Int
maxBevelSegments = 100

maxTraceColors :: Int
maxTraceColors = 256

maxMiterLimit :: Number
maxMiterLimit = 100.0
