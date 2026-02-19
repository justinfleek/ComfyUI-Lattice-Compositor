-- | Lattice.Triggers - Layer 3: Triggers with proofs
-- |
-- | Source: lattice-core/lean/Lattice/Triggers.lean

module Lattice.Triggers
  ( ComparisonOperator(..)
  , CompositeOperator(..)
  , PropertyCondition
  , FrameCondition
  , AudioCondition
  , TimeCondition
  , BaseTrigger
  , FrameTrigger
  , PropertyTrigger
  , AudioTrigger
  , TimeTrigger
  , ExpressionTrigger
  , EventTrigger
  , CompositeTrigger
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Comparison Operators
--------------------------------------------------------------------------------

data ComparisonOperator
  = COEquals | CONotEquals
  | COGreaterThan | COGreaterThanOrEqual
  | COLessThan | COLessThanOrEqual

derive instance Eq ComparisonOperator
derive instance Generic ComparisonOperator _
instance Show ComparisonOperator where show = genericShow

data CompositeOperator = COAnd | COOr

derive instance Eq CompositeOperator
derive instance Generic CompositeOperator _
instance Show CompositeOperator where show = genericShow

--------------------------------------------------------------------------------
-- Conditions
--------------------------------------------------------------------------------

type PropertyCondition =
  { propertyPath :: NonEmptyString
  , operator     :: ComparisonOperator
  , value        :: String  -- JSON-encoded
  }

type FrameCondition =
  { frame  :: FrameNumber
  , range  :: Maybe { start :: FrameNumber, end :: FrameNumber }
  , modulo :: Maybe FrameNumber
  }

type AudioCondition =
  { beatIndex     :: Maybe FrameNumber
  , peakThreshold :: UnitFloat
  , frequency     :: Maybe UnitFloat
  }

type TimeCondition =
  { timecode :: NonNegativeFloat
  , duration :: Maybe NonNegativeFloat
  , loop     :: Boolean
  }

--------------------------------------------------------------------------------
-- Base Trigger
--------------------------------------------------------------------------------

type BaseTrigger =
  { id            :: NonEmptyString
  , triggerType   :: NonEmptyString
  , enabled       :: Boolean
  , compositionId :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Trigger Types
--------------------------------------------------------------------------------

type FrameTrigger =
  { base      :: BaseTrigger
  , condition :: FrameCondition
  }

type PropertyTrigger =
  { base      :: BaseTrigger
  , condition :: PropertyCondition
  , layerId   :: NonEmptyString
  }

type AudioTrigger =
  { base      :: BaseTrigger
  , condition :: AudioCondition
  , layerId   :: NonEmptyString
  }

type TimeTrigger =
  { base      :: BaseTrigger
  , condition :: TimeCondition
  }

type ExpressionTrigger =
  { base       :: BaseTrigger
  , expression :: NonEmptyString
  , layerId    :: NonEmptyString
  }

type EventTrigger =
  { base      :: BaseTrigger
  , eventType :: NonEmptyString
  }

type CompositeTrigger =
  { base     :: BaseTrigger
  , operator :: CompositeOperator
  , triggers :: Array NonEmptyString  -- Trigger IDs
  }
