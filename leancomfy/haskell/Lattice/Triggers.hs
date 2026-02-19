{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Triggers
Description : Layer 3: Triggers with proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Triggers.lean
-}

module Lattice.Triggers
  ( -- * Enumerations
    ComparisonOperator(..)
  , CompositeOperator(..)
    -- * Conditions
  , PropertyCondition(..)
  , FrameCondition(..)
  , AudioCondition(..)
  , TimeCondition(..)
    -- * Base Trigger
  , BaseTrigger(..)
    -- * Trigger Types
  , FrameTrigger(..)
  , PropertyTrigger(..)
  , AudioTrigger(..)
  , TimeTrigger(..)
  , ExpressionTrigger(..)
  , EventTrigger(..)
  , CompositeTrigger(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Comparison Operators
--------------------------------------------------------------------------------

data ComparisonOperator
  = COEquals | CONotEquals
  | COGreaterThan | COGreaterThanOrEqual
  | COLessThan | COLessThanOrEqual
  deriving stock (Eq, Show, Generic)

data CompositeOperator = COAnd | COOr
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Conditions
--------------------------------------------------------------------------------

data PropertyCondition = PropertyCondition
  { pcPropertyPath :: !NonEmptyString
  , pcOperator     :: !ComparisonOperator
  , pcValue        :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data FrameCondition = FrameCondition
  { fcFrame  :: !FrameNumber
  , fcRange  :: !(Maybe (FrameNumber, FrameNumber))
  , fcModulo :: !(Maybe FrameNumber)
  } deriving stock (Eq, Show, Generic)

data AudioCondition = AudioCondition
  { acBeatIndex     :: !(Maybe FrameNumber)
  , acPeakThreshold :: !UnitFloat
  , acFrequency     :: !(Maybe UnitFloat)
  } deriving stock (Eq, Show, Generic)

data TimeCondition = TimeCondition
  { tcTimecode :: !NonNegativeFloat
  , tcDuration :: !(Maybe NonNegativeFloat)
  , tcLoop     :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Base Trigger
--------------------------------------------------------------------------------

data BaseTrigger = BaseTrigger
  { btId            :: !NonEmptyString
  , btTriggerType   :: !NonEmptyString
  , btEnabled       :: !Bool
  , btCompositionId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Trigger Types
--------------------------------------------------------------------------------

data FrameTrigger = FrameTrigger
  { ftBase      :: !BaseTrigger
  , ftCondition :: !FrameCondition
  } deriving stock (Eq, Show, Generic)

data PropertyTrigger = PropertyTrigger
  { ptBase      :: !BaseTrigger
  , ptCondition :: !PropertyCondition
  , ptLayerId   :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data AudioTrigger = AudioTrigger
  { atBase      :: !BaseTrigger
  , atCondition :: !AudioCondition
  , atLayerId   :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data TimeTrigger = TimeTrigger
  { ttBase      :: !BaseTrigger
  , ttCondition :: !TimeCondition
  } deriving stock (Eq, Show, Generic)

data ExpressionTrigger = ExpressionTrigger
  { etBase       :: !BaseTrigger
  , etExpression :: !NonEmptyString
  , etLayerId    :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data EventTrigger = EventTrigger
  { evtBase      :: !BaseTrigger
  , evtEventType :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data CompositeTrigger = CompositeTrigger
  { ctBase     :: !BaseTrigger
  , ctOperator :: !CompositeOperator
  , ctTriggers :: !(Vector NonEmptyString)  -- Trigger IDs
  } deriving stock (Eq, Show, Generic)
