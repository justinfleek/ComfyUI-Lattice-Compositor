{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Shapes
Description : Shape layer types and enums
Copyright   : (c) Lattice, 2026
License     : MIT

Consolidated from Lean4 Shapes/* submodules.
-}

module Lattice.Shapes
  ( -- * Fill/Stroke Enums
    FillRule(..)
  , LineCap(..)
  , LineJoin(..)
    -- * Path Operator Enums
  , TrimMode(..)
  , MergeMode(..)
  , OffsetJoin(..)
  , WigglePointType(..)
  , ZigZagPointType(..)
    -- * Repeater/Group
  , RepeaterComposite(..)
    -- * Shape Content Type
  , ShapeContentType(..)
    -- * Gradient
  , GradientType(..)
    -- * Quality
  , ShapeQuality(..)
    -- * Extrude
  , ExtrudeCapType(..)
    -- * Trace
  , TraceMode(..)
    -- * Path Direction
  , PathDirection(..)
  , pathDirectionToInt
  ) where

import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Fill/Stroke Enums
--------------------------------------------------------------------------------

data FillRule = FRNonzero | FREvenodd
  deriving stock (Eq, Show, Generic)

data LineCap = LCButt | LCRound | LCSquare
  deriving stock (Eq, Show, Generic)

data LineJoin = LJMiter | LJRound | LJBevel
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Path Operator Enums
--------------------------------------------------------------------------------

data TrimMode = TMSimultaneously | TMIndividually
  deriving stock (Eq, Show, Generic)

data MergeMode
  = MMAdd | MMSubtract | MMIntersect | MMExclude | MMMinusFront | MMMinusBack
  deriving stock (Eq, Show, Generic)

data OffsetJoin = OJMiter | OJRound | OJBevel
  deriving stock (Eq, Show, Generic)

data WigglePointType = WPTCorner | WPTSmooth
  deriving stock (Eq, Show, Generic)

data ZigZagPointType = ZZPTCorner | ZZPTSmooth
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Repeater/Group
--------------------------------------------------------------------------------

data RepeaterComposite = RCAbove | RCBelow
  deriving stock (Eq, Show, Generic)

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
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Gradient
--------------------------------------------------------------------------------

data GradientType = GTLinear | GTRadial
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Quality
--------------------------------------------------------------------------------

data ShapeQuality = SQDraft | SQNormal | SQHigh
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Extrude
--------------------------------------------------------------------------------

data ExtrudeCapType = ECTFlat | ECTRound | ECTBevel
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Trace
--------------------------------------------------------------------------------

data TraceMode = TMBlackAndWhite | TMGrayscale | TMColor
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Path Direction
--------------------------------------------------------------------------------

data PathDirection = PDClockwise | PDCounterClockwise
  deriving stock (Eq, Show, Generic)

pathDirectionToInt :: PathDirection -> Int
pathDirectionToInt PDClockwise = 1
pathDirectionToInt PDCounterClockwise = -1
