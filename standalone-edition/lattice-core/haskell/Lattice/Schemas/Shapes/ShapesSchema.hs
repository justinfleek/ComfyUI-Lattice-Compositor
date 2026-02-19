{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Shapes.ShapesSchema
Description : Shape layer enums for generators, modifiers, and path operators
Copyright   : (c) Lattice, 2026
License     : MIT

Shape layer enums for generators, modifiers, and path operators.

Source: ui/src/schemas/layers/shapes-schema.ts
-}

module Lattice.Schemas.Shapes.ShapesSchema
  ( -- * Fill Rule
    FillRule(..)
  , fillRuleFromText
  , fillRuleToText
    -- * Line Cap
  , LineCap(..)
  , lineCapFromText
  , lineCapToText
    -- * Line Join
  , LineJoin(..)
  , lineJoinFromText
  , lineJoinToText
    -- * Trim Mode
  , TrimMode(..)
  , trimModeFromText
  , trimModeToText
    -- * Merge Mode
  , MergeMode(..)
  , mergeModeFromText
  , mergeModeToText
    -- * Wiggle Point Type
  , WigglePointType(..)
  , wigglePointTypeFromText
  , wigglePointTypeToText
    -- * Repeater Composite
  , RepeaterComposite(..)
  , repeaterCompositeFromText
  , repeaterCompositeToText
    -- * Cap Type
  , CapType(..)
  , capTypeFromText
  , capTypeToText
    -- * Trace Mode
  , TraceMode(..)
  , traceModeFromText
  , traceModeToText
    -- * Shape Quality
  , ShapeQuality(..)
  , shapeQualityFromText
  , shapeQualityToText
    -- * Shape Direction
  , ShapeDirection(..)
  , shapeDirectionFromInt
  , shapeDirectionToInt
    -- * Constants
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

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Fill Rule
-- ────────────────────────────────────────────────────────────────────────────

-- | Fill rule options
data FillRule
  = FillNonZero
  | FillEvenOdd
  deriving stock (Eq, Show, Generic, Enum, Bounded)

fillRuleFromText :: Text -> Maybe FillRule
fillRuleFromText "nonzero" = Just FillNonZero
fillRuleFromText "evenodd" = Just FillEvenOdd
fillRuleFromText _ = Nothing

fillRuleToText :: FillRule -> Text
fillRuleToText FillNonZero = "nonzero"
fillRuleToText FillEvenOdd = "evenodd"

-- ────────────────────────────────────────────────────────────────────────────
-- Line Cap
-- ────────────────────────────────────────────────────────────────────────────

-- | Line cap options
data LineCap
  = CapButt
  | CapRound
  | CapSquare
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lineCapFromText :: Text -> Maybe LineCap
lineCapFromText "butt" = Just CapButt
lineCapFromText "round" = Just CapRound
lineCapFromText "square" = Just CapSquare
lineCapFromText _ = Nothing

lineCapToText :: LineCap -> Text
lineCapToText CapButt = "butt"
lineCapToText CapRound = "round"
lineCapToText CapSquare = "square"

-- ────────────────────────────────────────────────────────────────────────────
-- Line Join
-- ────────────────────────────────────────────────────────────────────────────

-- | Line join options
data LineJoin
  = JoinMiter
  | JoinRound
  | JoinBevel
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lineJoinFromText :: Text -> Maybe LineJoin
lineJoinFromText "miter" = Just JoinMiter
lineJoinFromText "round" = Just JoinRound
lineJoinFromText "bevel" = Just JoinBevel
lineJoinFromText _ = Nothing

lineJoinToText :: LineJoin -> Text
lineJoinToText JoinMiter = "miter"
lineJoinToText JoinRound = "round"
lineJoinToText JoinBevel = "bevel"

-- ────────────────────────────────────────────────────────────────────────────
-- Trim Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Trim mode options
data TrimMode
  = TrimSimultaneously
  | TrimIndividually
  deriving stock (Eq, Show, Generic, Enum, Bounded)

trimModeFromText :: Text -> Maybe TrimMode
trimModeFromText "simultaneously" = Just TrimSimultaneously
trimModeFromText "individually" = Just TrimIndividually
trimModeFromText _ = Nothing

trimModeToText :: TrimMode -> Text
trimModeToText TrimSimultaneously = "simultaneously"
trimModeToText TrimIndividually = "individually"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

mergeModeFromText :: Text -> Maybe MergeMode
mergeModeFromText "add" = Just MergeAdd
mergeModeFromText "subtract" = Just MergeSubtract
mergeModeFromText "intersect" = Just MergeIntersect
mergeModeFromText "exclude" = Just MergeExclude
mergeModeFromText "minusFront" = Just MergeMinusFront
mergeModeFromText "minusBack" = Just MergeMinusBack
mergeModeFromText _ = Nothing

mergeModeToText :: MergeMode -> Text
mergeModeToText MergeAdd = "add"
mergeModeToText MergeSubtract = "subtract"
mergeModeToText MergeIntersect = "intersect"
mergeModeToText MergeExclude = "exclude"
mergeModeToText MergeMinusFront = "minusFront"
mergeModeToText MergeMinusBack = "minusBack"

-- ────────────────────────────────────────────────────────────────────────────
-- Wiggle Point Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Wiggle point type options
data WigglePointType
  = WiggleCorner
  | WiggleSmooth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

wigglePointTypeFromText :: Text -> Maybe WigglePointType
wigglePointTypeFromText "corner" = Just WiggleCorner
wigglePointTypeFromText "smooth" = Just WiggleSmooth
wigglePointTypeFromText _ = Nothing

wigglePointTypeToText :: WigglePointType -> Text
wigglePointTypeToText WiggleCorner = "corner"
wigglePointTypeToText WiggleSmooth = "smooth"

-- ────────────────────────────────────────────────────────────────────────────
-- Repeater Composite
-- ────────────────────────────────────────────────────────────────────────────

-- | Repeater composite options
data RepeaterComposite
  = CompositeAbove
  | CompositeBelow
  deriving stock (Eq, Show, Generic, Enum, Bounded)

repeaterCompositeFromText :: Text -> Maybe RepeaterComposite
repeaterCompositeFromText "above" = Just CompositeAbove
repeaterCompositeFromText "below" = Just CompositeBelow
repeaterCompositeFromText _ = Nothing

repeaterCompositeToText :: RepeaterComposite -> Text
repeaterCompositeToText CompositeAbove = "above"
repeaterCompositeToText CompositeBelow = "below"

-- ────────────────────────────────────────────────────────────────────────────
-- Cap Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Cap type options for extrusion
data CapType
  = CapFlat
  | CapRoundCap
  | CapBevel
  deriving stock (Eq, Show, Generic, Enum, Bounded)

capTypeFromText :: Text -> Maybe CapType
capTypeFromText "flat" = Just CapFlat
capTypeFromText "round" = Just CapRoundCap
capTypeFromText "bevel" = Just CapBevel
capTypeFromText _ = Nothing

capTypeToText :: CapType -> Text
capTypeToText CapFlat = "flat"
capTypeToText CapRoundCap = "round"
capTypeToText CapBevel = "bevel"

-- ────────────────────────────────────────────────────────────────────────────
-- Trace Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Trace mode options
data TraceMode
  = TraceBlackAndWhite
  | TraceGrayscale
  | TraceColor
  deriving stock (Eq, Show, Generic, Enum, Bounded)

traceModeFromText :: Text -> Maybe TraceMode
traceModeFromText "blackAndWhite" = Just TraceBlackAndWhite
traceModeFromText "grayscale" = Just TraceGrayscale
traceModeFromText "color" = Just TraceColor
traceModeFromText _ = Nothing

traceModeToText :: TraceMode -> Text
traceModeToText TraceBlackAndWhite = "blackAndWhite"
traceModeToText TraceGrayscale = "grayscale"
traceModeToText TraceColor = "color"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Quality
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape quality options
data ShapeQuality
  = QualityDraft
  | QualityNormal
  | QualityHigh
  deriving stock (Eq, Show, Generic, Enum, Bounded)

shapeQualityFromText :: Text -> Maybe ShapeQuality
shapeQualityFromText "draft" = Just QualityDraft
shapeQualityFromText "normal" = Just QualityNormal
shapeQualityFromText "high" = Just QualityHigh
shapeQualityFromText _ = Nothing

shapeQualityToText :: ShapeQuality -> Text
shapeQualityToText QualityDraft = "draft"
shapeQualityToText QualityNormal = "normal"
shapeQualityToText QualityHigh = "high"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Direction
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape direction (clockwise or counter-clockwise)
data ShapeDirection
  = DirectionClockwise       -- 1
  | DirectionCounterclockwise  -- -1
  deriving stock (Eq, Show, Generic, Enum, Bounded)

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

maxMiterLimit :: Double
maxMiterLimit = 100.0
