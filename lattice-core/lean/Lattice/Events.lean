/-
  Lattice.Events - Layer 2A: Events with proofs
  
  Single source of truth for all event types.
  Every event has proofs of its invariants.
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 2A - depends on Layer 0 (Primitives) and Layer 1 (Enums).
  All other layers depend on this.
-/

import Lattice.Primitives
import Lattice.Enums
import Batteries.Data.String.Basic

namespace Lattice.Events

open Lattice.Primitives
open Lattice.Enums

/-! ## Base Event -/

/-- Base event with timestamp and event type -/
structure BaseEvent where
  id : NonEmptyString
  timestamp : PositiveFloat -- Unix timestamp in seconds
  eventType : NonEmptyString -- Type identifier for the event
  deriving Repr

/-! ## Composition Events -/

/-- Event: Composition was created -/
structure CompositionCreated extends BaseEvent where
  compositionId : NonEmptyString
  compositionName : NonEmptyString
  deriving Repr

/-- Event: Composition was deleted -/
structure CompositionDeleted extends BaseEvent where
  compositionId : NonEmptyString
  deriving Repr

/-- Event: Composition was rendered -/
structure CompositionRendered extends BaseEvent where
  compositionId : NonEmptyString
  frameNumber : FrameNumber
  duration : NonNegativeFloat -- Rendering duration in seconds
  deriving Repr

/-! ## Layer Events -/

/-- Event: Layer was created -/
structure LayerCreated extends BaseEvent where
  layerId : NonEmptyString
  compositionId : NonEmptyString
  layerType : LayerType
  deriving Repr

/-- Event: Layer was deleted -/
structure LayerDeleted extends BaseEvent where
  layerId : NonEmptyString
  compositionId : NonEmptyString
  deriving Repr

/-- Event: Layer was moved (reordered) -/
structure LayerMoved extends BaseEvent where
  layerId : NonEmptyString
  compositionId : NonEmptyString
  oldIndex : FrameNumber -- Previous position
  newIndex : FrameNumber -- New position
  deriving Repr

/-- Event: Layer was duplicated -/
structure LayerDuplicated extends BaseEvent where
  sourceLayerId : NonEmptyString
  newLayerId : NonEmptyString
  compositionId : NonEmptyString
  deriving Repr

/-- Event: Layer visibility changed -/
structure LayerVisibilityChanged extends BaseEvent where
  layerId : NonEmptyString
  compositionId : NonEmptyString
  visible : Bool
  deriving Repr

/-! ## Keyframe Events -/

/-- Event: Keyframe was added -/
structure KeyframeAdded extends BaseEvent where
  keyframeId : NonEmptyString
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  frameNumber : FrameNumber
  value : String -- JSON-encoded value
  deriving Repr

/-- Event: Keyframe was removed -/
structure KeyframeRemoved extends BaseEvent where
  keyframeId : NonEmptyString
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  frameNumber : FrameNumber
  deriving Repr

/-- Event: Keyframe was modified -/
structure KeyframeModified extends BaseEvent where
  keyframeId : NonEmptyString
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  frameNumber : FrameNumber
  oldValue : String -- JSON-encoded old value
  newValue : String -- JSON-encoded new value
  deriving Repr

/-- Event: Keyframe interpolation changed -/
structure KeyframeInterpolationChanged extends BaseEvent where
  keyframeId : NonEmptyString
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  oldInterpolation : InterpolationType
  newInterpolation : InterpolationType
  deriving Repr

/-! ## Property Events -/

/-- Event: Property was animated (keyframes added) -/
structure PropertyAnimated extends BaseEvent where
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  keyframeCount : PositiveInt
  deriving Repr

/-- Event: Property expression changed -/
structure PropertyExpressionChanged extends BaseEvent where
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  oldExpression : String
  newExpression : String
  deriving Repr

/-- Event: Property driver was added -/
structure PropertyDriverAdded extends BaseEvent where
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  driverPropertyPath : NonEmptyString -- Path to the property driving this one
  deriving Repr

/-! ## Effect Events -/

/-- Event: Effect was added to layer -/
structure EffectAdded extends BaseEvent where
  effectId : NonEmptyString
  layerId : NonEmptyString
  effectCategory : EffectCategory
  deriving Repr

/-- Event: Effect was removed from layer -/
structure EffectRemoved extends BaseEvent where
  effectId : NonEmptyString
  layerId : NonEmptyString
  deriving Repr

/-- Event: Effect parameter changed -/
structure EffectParameterChanged extends BaseEvent where
  effectId : NonEmptyString
  layerId : NonEmptyString
  parameterName : NonEmptyString
  oldValue : String -- JSON-encoded old value
  newValue : String -- JSON-encoded new value
  deriving Repr

/-! ## Export Events -/

/-- Event: Export started -/
structure ExportStarted extends BaseEvent where
  exportId : NonEmptyString
  compositionId : NonEmptyString
  exportFormat : ExportFormat
  exportTarget : ExportTarget
  deriving Repr

/-- Event: Export progress updated -/
structure ExportProgress extends BaseEvent where
  exportId : NonEmptyString
  compositionId : NonEmptyString
  progress : Percentage -- 0-100
  currentFrame : FrameNumber
  totalFrames : FrameNumber
  deriving Repr

/-- Event: Export completed successfully -/
structure ExportCompleted extends BaseEvent where
  exportId : NonEmptyString
  compositionId : NonEmptyString
  outputPath : NonEmptyString
  duration : NonNegativeFloat -- Export duration in seconds
  deriving Repr

/-- Event: Export failed -/
structure ExportFailed extends BaseEvent where
  exportId : NonEmptyString
  compositionId : NonEmptyString
  errorMessage : NonEmptyString
  deriving Repr

/-! ## Render Events -/

/-- Event: Render job queued -/
structure RenderJobQueued extends BaseEvent where
  jobId : NonEmptyString
  compositionId : NonEmptyString
  priority : PositiveInt
  deriving Repr

/-- Event: Render job completed -/
structure RenderJobCompleted extends BaseEvent where
  jobId : NonEmptyString
  compositionId : NonEmptyString
  duration : NonNegativeFloat -- Render duration in seconds
  deriving Repr

/-! ## System Events -/

/-- Event: Cache was cleared -/
structure CacheCleared extends BaseEvent where
  cacheType : NonEmptyString -- Type of cache cleared
  sizeBytes : FrameNumber -- Size of cache cleared
  deriving Repr

/-- Event: Error occurred -/
structure ErrorOccurred extends BaseEvent where
  severity : Severity
  errorMessage : NonEmptyString
  errorCode : NonEmptyString
  stackTrace : String -- May be empty
  deriving Repr

end Lattice.Events
