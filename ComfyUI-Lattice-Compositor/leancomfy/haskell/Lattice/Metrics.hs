{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Metrics
Description : Layer 2B: Metrics with proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Metrics.lean
-}

module Lattice.Metrics
  ( -- * Enumerations
    AggregationType(..)
  , TimeGrain(..)
  , MetricDataType(..)
  , MetricCategory(..)
    -- * Metric Definition
  , MetricDefinition(..)
    -- * Rendering Metrics
  , FrameRenderTime(..)
  , TotalRenderTime(..)
  , MemoryUsage(..)
  , GpuUsage(..)
  , CacheHitRate(..)
  , CacheSize(..)
    -- * Performance Metrics
  , Fps(..)
  , DroppedFrames(..)
  , PlaybackLatency(..)
  , ScrubLatency(..)
    -- * Quality Metrics
  , CompressionRatio(..)
  , Bitrate(..)
  , ColorAccuracy(..)
  , MotionBlurQuality(..)
    -- * Resource Metrics
  , VramUsage(..)
  , CpuUsage(..)
  , NetworkBandwidth(..)
  , StorageUsed(..)
    -- * AI Metrics
  , InferenceTime(..)
  , ModelLoadTime(..)
  , TokensUsed(..)
  , CostUSD(..)
  ) where

import GHC.Generics (Generic)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data AggregationType = ATSum | ATAverage | ATMin | ATMax | ATCount | ATLast
  deriving stock (Eq, Show, Generic)

data TimeGrain = TGMillisecond | TGSecond | TGMinute | TGHour | TGDay
  deriving stock (Eq, Show, Generic)

data MetricDataType = MDTFloat | MDTInteger | MDTPercentage | MDTDuration
  deriving stock (Eq, Show, Generic)

data MetricCategory
  = MCRendering | MCPerformance | MCQuality | MCResource | MCUser | MCAI
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Metric Definition
--------------------------------------------------------------------------------

data MetricDefinition = MetricDefinition
  { mdId          :: !NonEmptyString
  , mdName        :: !NonEmptyString
  , mdCategory    :: !MetricCategory
  , mdDataType    :: !MetricDataType
  , mdUnit        :: !NonEmptyString
  , mdMinValue    :: !FiniteFloat
  , mdMaxValue    :: !FiniteFloat
  , mdAggregation :: !AggregationType
  , mdTimeGrain   :: !TimeGrain
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Rendering Metrics
--------------------------------------------------------------------------------

data FrameRenderTime = FrameRenderTime
  { frtValue       :: !PositiveFloat  -- Milliseconds
  , frtFrameNumber :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data TotalRenderTime = TotalRenderTime
  { trtValue      :: !NonNegativeFloat  -- Seconds
  , trtFrameCount :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data MemoryUsage = MemoryUsage
  { muValue :: !NonNegativeFloat  -- Bytes
  } deriving stock (Eq, Show, Generic)

data GpuUsage = GpuUsage
  { guValue :: !Percentage  -- 0-100%
  } deriving stock (Eq, Show, Generic)

data CacheHitRate = CacheHitRate
  { chrValue :: !Percentage  -- 0-100%
  } deriving stock (Eq, Show, Generic)

data CacheSize = CacheSize
  { csValue :: !NonNegativeFloat  -- Bytes
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Performance Metrics
--------------------------------------------------------------------------------

data Fps = Fps
  { fpsValue :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

data DroppedFrames = DroppedFrames
  { dfValue :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data PlaybackLatency = PlaybackLatency
  { plValue :: !NonNegativeFloat  -- Milliseconds
  } deriving stock (Eq, Show, Generic)

data ScrubLatency = ScrubLatency
  { slValue :: !NonNegativeFloat  -- Milliseconds
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Quality Metrics
--------------------------------------------------------------------------------

data CompressionRatio = CompressionRatio
  { crValue :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

data Bitrate = Bitrate
  { brValue :: !PositiveFloat  -- Bits per second
  } deriving stock (Eq, Show, Generic)

data ColorAccuracy = ColorAccuracy
  { caValue :: !Percentage  -- 0-100%
  } deriving stock (Eq, Show, Generic)

data MotionBlurQuality = MotionBlurQuality
  { mbqValue :: !UnitFloat  -- 0-1
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Resource Metrics
--------------------------------------------------------------------------------

data VramUsage = VramUsage
  { vuValue :: !NonNegativeFloat  -- Bytes
  } deriving stock (Eq, Show, Generic)

data CpuUsage = CpuUsage
  { cuValue :: !Percentage  -- 0-100%
  } deriving stock (Eq, Show, Generic)

data NetworkBandwidth = NetworkBandwidth
  { nbValue :: !NonNegativeFloat  -- Bits per second
  } deriving stock (Eq, Show, Generic)

data StorageUsed = StorageUsed
  { suValue :: !NonNegativeFloat  -- Bytes
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- AI Metrics
--------------------------------------------------------------------------------

data InferenceTime = InferenceTime
  { itValue :: !PositiveFloat  -- Milliseconds
  } deriving stock (Eq, Show, Generic)

data ModelLoadTime = ModelLoadTime
  { mltValue :: !PositiveFloat  -- Milliseconds
  } deriving stock (Eq, Show, Generic)

data TokensUsed = TokensUsed
  { tuValue :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

data CostUSD = CostUSD
  { cudValue :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)
