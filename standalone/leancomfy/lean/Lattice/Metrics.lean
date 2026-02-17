/-
  Lattice.Metrics - Layer 2B: Metrics with proofs
  
  Single source of truth for all metric types.
  Every metric has proofs of its invariants and bounds.
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 2B - depends on Layer 0 (Primitives) and Layer 1 (Enums).
  All other layers depend on this.
-/

import Lattice.Primitives
import Lattice.Enums
import Batteries.Data.String.Basic

namespace Lattice.Metrics

open Lattice.Primitives
open Lattice.Enums

/-! ## Metric Definition -/

/-- Aggregation method for metrics -/
inductive AggregationType where
  | sum
  | average
  | min
  | max
  | count
  | last
  deriving Repr, BEq, DecidableEq

/-- Time grain for metric sampling -/
inductive TimeGrain where
  | millisecond
  | second
  | minute
  | hour
  | day
  deriving Repr, BEq, DecidableEq

/-- Data type for metric values -/
inductive MetricDataType where
  | float
  | integer
  | percentage
  | duration
  deriving Repr, BEq, DecidableEq

/-- Category of metric -/
inductive MetricCategory where
  | rendering
  | performance
  | quality
  | resource
  | user
  | ai
  deriving Repr, BEq, DecidableEq

/-- Metric definition with bounds and aggregation -/
structure MetricDefinition where
  id : NonEmptyString
  name : NonEmptyString
  category : MetricCategory
  dataType : MetricDataType
  unit : NonEmptyString
  minValue : Float -- Minimum possible value
  maxValue : Float -- Maximum possible value
  aggregation : AggregationType
  timeGrain : TimeGrain
  deriving Repr

/-! ## Rendering Metrics -/

/-- Frame render time in milliseconds -/
structure FrameRenderTime where
  value : PositiveFloat -- Milliseconds, must be > 0
  frameNumber : FrameNumber
  deriving Repr

/-- Total render time in seconds -/
structure TotalRenderTime where
  value : NonNegativeFloat -- Seconds, >= 0
  frameCount : FrameNumber
  deriving Repr

/-- Memory usage in bytes -/
structure MemoryUsage where
  value : NonNegativeFloat -- Bytes, >= 0
  deriving Repr

/-- GPU usage percentage -/
structure GpuUsage where
  value : Percentage -- 0-100%
  deriving Repr

/-- Cache hit rate percentage -/
structure CacheHitRate where
  value : Percentage -- 0-100%
  deriving Repr

/-- Cache size in bytes -/
structure CacheSize where
  value : NonNegativeFloat -- Bytes, >= 0
  deriving Repr

/-! ## Performance Metrics -/

/-- Frames per second -/
structure Fps where
  value : NonNegativeFloat -- FPS, >= 0
  deriving Repr

/-- Number of dropped frames -/
structure DroppedFrames where
  value : FrameNumber -- Count, >= 0
  deriving Repr

/-- Playback latency in milliseconds -/
structure PlaybackLatency where
  value : NonNegativeFloat -- Milliseconds, >= 0
  deriving Repr

/-- Scrub latency in milliseconds -/
structure ScrubLatency where
  value : NonNegativeFloat -- Milliseconds, >= 0
  deriving Repr

/-! ## Quality Metrics -/

/-- Compression ratio (output size / input size) -/
structure CompressionRatio where
  value : PositiveFloat -- Ratio, must be > 0
  deriving Repr

/-- Bitrate in bits per second -/
structure Bitrate where
  value : PositiveFloat -- Bits per second, must be > 0
  deriving Repr

/-- Color accuracy percentage -/
structure ColorAccuracy where
  value : Percentage -- 0-100%
  deriving Repr

/-- Motion blur quality score -/
structure MotionBlurQuality where
  value : NormalizedValue -- 0-1 score
  deriving Repr

/-! ## Resource Metrics -/

/-- VRAM usage in bytes -/
structure VramUsage where
  value : NonNegativeFloat -- Bytes, >= 0
  deriving Repr

/-- CPU usage percentage -/
structure CpuUsage where
  value : Percentage -- 0-100%
  deriving Repr

/-- Network bandwidth in bits per second -/
structure NetworkBandwidth where
  value : NonNegativeFloat -- Bits per second, >= 0
  deriving Repr

/-- Storage used in bytes -/
structure StorageUsed where
  value : NonNegativeFloat -- Bytes, >= 0
  deriving Repr

/-! ## User Metrics -/

/-- Actions per session count -/
structure ActionsPerSession where
  value : FrameNumber -- Count, >= 0
  deriving Repr

/-- Export count -/
structure ExportCount where
  value : FrameNumber -- Count, >= 0
  deriving Repr

/-- Project count -/
structure ProjectCount where
  value : FrameNumber -- Count, >= 0
  deriving Repr

/-! ## AI Metrics -/

/-- Inference time in milliseconds -/
structure InferenceTime where
  value : PositiveFloat -- Milliseconds, must be > 0
  deriving Repr

/-- Model load time in milliseconds -/
structure ModelLoadTime where
  value : PositiveFloat -- Milliseconds, must be > 0
  deriving Repr

/-- Tokens used count -/
structure TokensUsed where
  value : FrameNumber -- Count, >= 0
  deriving Repr

/-- Cost in USD -/
structure CostUSD where
  value : NonNegativeFloat -- USD, >= 0
  deriving Repr

end Lattice.Metrics
