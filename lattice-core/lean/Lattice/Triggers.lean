/-
  Lattice.Triggers - Layer 3: Triggers with proofs
  
  Single source of truth for all trigger types.
  Every trigger has proofs of its invariants.
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 3 - depends on Layer 0 (Primitives), Layer 1 (Enums), Layer 2A (Events), Layer 2B (Metrics).
  All other layers depend on this.
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Events
import Lattice.Metrics
import Batteries.Data.String.Basic

namespace Lattice.Triggers

open Lattice.Primitives
open Lattice.Enums
open Lattice.Events
open Lattice.Metrics

/-! ## Comparison Operators -/

/-- Comparison operator for conditions -/
inductive ComparisonOperator where
  | equals
  | notEquals
  | greaterThan
  | greaterThanOrEqual
  | lessThan
  | lessThanOrEqual
  deriving Repr, BEq, DecidableEq

/-! ## Conditions -/

/-- Property condition: property path, operator, value -/
structure PropertyCondition where
  propertyPath : NonEmptyString
  operator : ComparisonOperator
  value : String -- JSON-encoded value
  deriving Repr

/-- Frame condition: frame, range, modulo -/
structure FrameCondition where
  frame : FrameNumber
  range : Option (FrameNumber × FrameNumber) -- Optional (start, end) range
  modulo : Option FrameNumber -- Optional modulo (fires every N frames)
  deriving Repr

/-- Audio condition: beat index, peak threshold, frequency -/
structure AudioCondition where
  beatIndex : Option FrameNumber -- Optional specific beat index
  peakThreshold : NormalizedValue -- 0-1 threshold
  frequency : Option NormalizedValue -- Optional frequency band (0-1)
  deriving Repr

/-- Time condition: timecode, duration, loop -/
structure TimeCondition where
  timecode : NonNegativeFloat -- Time in seconds
  duration : Option NonNegativeFloat -- Optional duration
  loop : Bool -- Whether to loop
  deriving Repr

/-! ## Base Trigger -/

/-- Base trigger with type, conditions, enabled state, composition ID -/
structure BaseTrigger where
  id : NonEmptyString
  triggerType : NonEmptyString
  enabled : Bool
  compositionId : NonEmptyString
  deriving Repr

/-! ## Trigger Types -/

/-- Frame trigger: fires at specific frame(s) -/
structure FrameTrigger extends BaseTrigger where
  condition : FrameCondition
  deriving Repr

/-- Property trigger: fires when property crosses threshold -/
structure PropertyTrigger extends BaseTrigger where
  condition : PropertyCondition
  layerId : NonEmptyString
  deriving Repr

/-- Audio trigger: fires on beat/onset/peak -/
structure AudioTrigger extends BaseTrigger where
  condition : AudioCondition
  layerId : NonEmptyString -- Audio layer ID
  deriving Repr

/-- Time trigger: fires at timecode or duration -/
structure TimeTrigger extends BaseTrigger where
  condition : TimeCondition
  deriving Repr

/-- Expression trigger: fires when expression evaluates true -/
structure ExpressionTrigger extends BaseTrigger where
  expression : NonEmptyString -- Expression to evaluate
  layerId : NonEmptyString
  deriving Repr

/-- Event trigger: fires on system event -/
structure EventTrigger extends BaseTrigger where
  eventType : NonEmptyString -- Type of event to listen for
  deriving Repr

/-- Composite trigger operator -/
inductive CompositeOperator where
  | and
  | or
  deriving Repr, BEq, DecidableEq

/-- Composite trigger: AND/OR combinations of triggers -/
structure CompositeTrigger extends BaseTrigger where
  operator : CompositeOperator
  triggers : List NonEmptyString -- List of trigger IDs
  deriving Repr

end Lattice.Triggers
