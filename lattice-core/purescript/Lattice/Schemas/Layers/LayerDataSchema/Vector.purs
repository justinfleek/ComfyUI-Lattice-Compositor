-- | Lattice.Schemas.Layers.LayerDataSchema.Vector - Vector/Path layer enums
-- |
-- | Enums for Spline/Path and Text layers.

module Lattice.Schemas.Layers.LayerDataSchema.Vector
  ( -- Spline/Path
    ControlPointType(..), controlPointTypeFromString
  , GradientType(..), gradientTypeFromString
  , SplinePathEffectType(..), splinePathEffectTypeFromString
  , LineJoin(..), lineJoinFromString
  , LineCap(..), lineCapFromString
  , SplineLODMode(..), splineLODModeFromString
  , StrokeType(..), strokeTypeFromString
    -- Text Layer
  , TextAlign(..), textAlignFromString
  , TextBaseline(..), textBaselineFromString
  , TextDirection(..), textDirectionFromString
  , TextFontStyle(..), textFontStyleFromString
  , TextBasedOn(..), textBasedOnFromString
  , TextSelectorShape(..), textSelectorShapeFromString
  , TextSelectorMode(..), textSelectorModeFromString
  , TextAnchorGrouping(..), textAnchorGroupingFromString
  , TextCase(..), textCaseFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Spline/Path
-- ────────────────────────────────────────────────────────────────────────────

data ControlPointType = CpCorner | CpSmooth | CpSymmetric

derive instance Eq ControlPointType
derive instance Generic ControlPointType _
instance Show ControlPointType where show = genericShow

controlPointTypeFromString :: String -> Maybe ControlPointType
controlPointTypeFromString = case _ of
  "corner" -> Just CpCorner
  "smooth" -> Just CpSmooth
  "symmetric" -> Just CpSymmetric
  _ -> Nothing

data GradientType = GradLinear | GradRadial

derive instance Eq GradientType
derive instance Generic GradientType _
instance Show GradientType where show = genericShow

gradientTypeFromString :: String -> Maybe GradientType
gradientTypeFromString = case _ of
  "linear" -> Just GradLinear
  "radial" -> Just GradRadial
  _ -> Nothing

data SplinePathEffectType = SpeOffsetPath | SpeRoughen | SpeWiggle | SpeZigzag | SpeWave

derive instance Eq SplinePathEffectType
derive instance Generic SplinePathEffectType _
instance Show SplinePathEffectType where show = genericShow

splinePathEffectTypeFromString :: String -> Maybe SplinePathEffectType
splinePathEffectTypeFromString = case _ of
  "offsetPath" -> Just SpeOffsetPath
  "roughen" -> Just SpeRoughen
  "wiggle" -> Just SpeWiggle
  "zigzag" -> Just SpeZigzag
  "wave" -> Just SpeWave
  _ -> Nothing

data LineJoin = JoinMiter | JoinRound | JoinBevel

derive instance Eq LineJoin
derive instance Generic LineJoin _
instance Show LineJoin where show = genericShow

lineJoinFromString :: String -> Maybe LineJoin
lineJoinFromString = case _ of
  "miter" -> Just JoinMiter
  "round" -> Just JoinRound
  "bevel" -> Just JoinBevel
  _ -> Nothing

data LineCap = CapButt | CapRound | CapSquare

derive instance Eq LineCap
derive instance Generic LineCap _
instance Show LineCap where show = genericShow

lineCapFromString :: String -> Maybe LineCap
lineCapFromString = case _ of
  "butt" -> Just CapButt
  "round" -> Just CapRound
  "square" -> Just CapSquare
  _ -> Nothing

data SplineLODMode = LodZoom | LodPlayback | LodBoth

derive instance Eq SplineLODMode
derive instance Generic SplineLODMode _
instance Show SplineLODMode where show = genericShow

splineLODModeFromString :: String -> Maybe SplineLODMode
splineLODModeFromString = case _ of
  "zoom" -> Just LodZoom
  "playback" -> Just LodPlayback
  "both" -> Just LodBoth
  _ -> Nothing

data StrokeType = StrokeSolid | StrokeGradient

derive instance Eq StrokeType
derive instance Generic StrokeType _
instance Show StrokeType where show = genericShow

strokeTypeFromString :: String -> Maybe StrokeType
strokeTypeFromString = case _ of
  "solid" -> Just StrokeSolid
  "gradient" -> Just StrokeGradient
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Text Layer
-- ────────────────────────────────────────────────────────────────────────────

data TextAlign = AlignLeft | AlignCenter | AlignRight

derive instance Eq TextAlign
derive instance Generic TextAlign _
instance Show TextAlign where show = genericShow

textAlignFromString :: String -> Maybe TextAlign
textAlignFromString = case _ of
  "left" -> Just AlignLeft
  "center" -> Just AlignCenter
  "right" -> Just AlignRight
  _ -> Nothing

data TextBaseline = BaselineTop | BaselineMiddle | BaselineBottom

derive instance Eq TextBaseline
derive instance Generic TextBaseline _
instance Show TextBaseline where show = genericShow

textBaselineFromString :: String -> Maybe TextBaseline
textBaselineFromString = case _ of
  "top" -> Just BaselineTop
  "middle" -> Just BaselineMiddle
  "bottom" -> Just BaselineBottom
  _ -> Nothing

data TextDirection = DirLtr | DirRtl

derive instance Eq TextDirection
derive instance Generic TextDirection _
instance Show TextDirection where show = genericShow

textDirectionFromString :: String -> Maybe TextDirection
textDirectionFromString = case _ of
  "ltr" -> Just DirLtr
  "rtl" -> Just DirRtl
  _ -> Nothing

data TextFontStyle = StyleNormal | StyleItalic

derive instance Eq TextFontStyle
derive instance Generic TextFontStyle _
instance Show TextFontStyle where show = genericShow

textFontStyleFromString :: String -> Maybe TextFontStyle
textFontStyleFromString = case _ of
  "normal" -> Just StyleNormal
  "italic" -> Just StyleItalic
  _ -> Nothing

data TextBasedOn = BoCharacters | BoCharactersExSpaces | BoWords | BoLines

derive instance Eq TextBasedOn
derive instance Generic TextBasedOn _
instance Show TextBasedOn where show = genericShow

textBasedOnFromString :: String -> Maybe TextBasedOn
textBasedOnFromString = case _ of
  "characters" -> Just BoCharacters
  "characters_excluding_spaces" -> Just BoCharactersExSpaces
  "words" -> Just BoWords
  "lines" -> Just BoLines
  _ -> Nothing

data TextSelectorShape = ShapeSquare | ShapeRampUp | ShapeRampDown | ShapeTriangle | ShapeRound | ShapeSmooth

derive instance Eq TextSelectorShape
derive instance Generic TextSelectorShape _
instance Show TextSelectorShape where show = genericShow

textSelectorShapeFromString :: String -> Maybe TextSelectorShape
textSelectorShapeFromString = case _ of
  "square" -> Just ShapeSquare
  "ramp_up" -> Just ShapeRampUp
  "ramp_down" -> Just ShapeRampDown
  "triangle" -> Just ShapeTriangle
  "round" -> Just ShapeRound
  "smooth" -> Just ShapeSmooth
  _ -> Nothing

data TextSelectorMode = SmAdd | SmSubtract | SmIntersect | SmMin | SmMax | SmDifference

derive instance Eq TextSelectorMode
derive instance Generic TextSelectorMode _
instance Show TextSelectorMode where show = genericShow

textSelectorModeFromString :: String -> Maybe TextSelectorMode
textSelectorModeFromString = case _ of
  "add" -> Just SmAdd
  "subtract" -> Just SmSubtract
  "intersect" -> Just SmIntersect
  "min" -> Just SmMin
  "max" -> Just SmMax
  "difference" -> Just SmDifference
  _ -> Nothing

data TextAnchorGrouping = AgCharacter | AgWord | AgLine | AgAll

derive instance Eq TextAnchorGrouping
derive instance Generic TextAnchorGrouping _
instance Show TextAnchorGrouping where show = genericShow

textAnchorGroupingFromString :: String -> Maybe TextAnchorGrouping
textAnchorGroupingFromString = case _ of
  "character" -> Just AgCharacter
  "word" -> Just AgWord
  "line" -> Just AgLine
  "all" -> Just AgAll
  _ -> Nothing

data TextCase = CaseNormal | CaseUppercase | CaseLowercase | CaseSmallCaps

derive instance Eq TextCase
derive instance Generic TextCase _
instance Show TextCase where show = genericShow

textCaseFromString :: String -> Maybe TextCase
textCaseFromString = case _ of
  "normal" -> Just CaseNormal
  "uppercase" -> Just CaseUppercase
  "lowercase" -> Just CaseLowercase
  "smallCaps" -> Just CaseSmallCaps
  _ -> Nothing
