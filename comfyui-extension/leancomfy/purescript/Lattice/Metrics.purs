-- | Lattice.Metrics - Layer 2B: Metrics with proofs
-- |
-- | Source: leancomfy/lean/Lattice/Metrics.lean

module Lattice.Metrics
  ( AggregationType(..)
  , TimeGrain(..)
  , MetricDataType(..)
  , MetricCategory(..)
  , MetricDefinition
  , FrameRenderTime
  , TotalRenderTime
  , MemoryUsage
  , GpuUsage
  , CacheHitRate
  , CacheSize
  , Fps
  , DroppedFrames
  , PlaybackLatency
  , ScrubLatency
  , CompressionRatio
  , Bitrate
  , ColorAccuracy
  , MotionBlurQuality
  , VramUsage
  , CpuUsage
  , NetworkBandwidth
  , StorageUsed
  , InferenceTime
  , ModelLoadTime
  , TokensUsed
  , CostUSD
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data AggregationType = ATSum | ATAverage | ATMin | ATMax | ATCount | ATLast

derive instance Eq AggregationType
derive instance Generic AggregationType _
instance Show AggregationType where show = genericShow

data TimeGrain = TGMillisecond | TGSecond | TGMinute | TGHour | TGDay

derive instance Eq TimeGrain
derive instance Generic TimeGrain _
instance Show TimeGrain where show = genericShow

data MetricDataType = MDTFloat | MDTInteger | MDTPercentage | MDTDuration

derive instance Eq MetricDataType
derive instance Generic MetricDataType _
instance Show MetricDataType where show = genericShow

data MetricCategory
  = MCRendering | MCPerformance | MCQuality | MCResource | MCUser | MCAI

derive instance Eq MetricCategory
derive instance Generic MetricCategory _
instance Show MetricCategory where show = genericShow

--------------------------------------------------------------------------------
-- Metric Definition
--------------------------------------------------------------------------------

type MetricDefinition =
  { id          :: NonEmptyString
  , name        :: NonEmptyString
  , category    :: MetricCategory
  , dataType    :: MetricDataType
  , unit        :: NonEmptyString
  , minValue    :: FiniteFloat
  , maxValue    :: FiniteFloat
  , aggregation :: AggregationType
  , timeGrain   :: TimeGrain
  }

--------------------------------------------------------------------------------
-- Rendering Metrics
--------------------------------------------------------------------------------

type FrameRenderTime =
  { value       :: PositiveFloat
  , frameNumber :: FrameNumber
  }

type TotalRenderTime =
  { value      :: NonNegativeFloat
  , frameCount :: FrameNumber
  }

type MemoryUsage = { value :: NonNegativeFloat }
type GpuUsage = { value :: Percentage }
type CacheHitRate = { value :: Percentage }
type CacheSize = { value :: NonNegativeFloat }

--------------------------------------------------------------------------------
-- Performance Metrics
--------------------------------------------------------------------------------

type Fps = { value :: NonNegativeFloat }
type DroppedFrames = { value :: FrameNumber }
type PlaybackLatency = { value :: NonNegativeFloat }
type ScrubLatency = { value :: NonNegativeFloat }

--------------------------------------------------------------------------------
-- Quality Metrics
--------------------------------------------------------------------------------

type CompressionRatio = { value :: PositiveFloat }
type Bitrate = { value :: PositiveFloat }
type ColorAccuracy = { value :: Percentage }
type MotionBlurQuality = { value :: UnitFloat }

--------------------------------------------------------------------------------
-- Resource Metrics
--------------------------------------------------------------------------------

type VramUsage = { value :: NonNegativeFloat }
type CpuUsage = { value :: Percentage }
type NetworkBandwidth = { value :: NonNegativeFloat }
type StorageUsed = { value :: NonNegativeFloat }

--------------------------------------------------------------------------------
-- AI Metrics
--------------------------------------------------------------------------------

type InferenceTime = { value :: PositiveFloat }
type ModelLoadTime = { value :: PositiveFloat }
type TokensUsed = { value :: FrameNumber }
type CostUSD = { value :: NonNegativeFloat }
