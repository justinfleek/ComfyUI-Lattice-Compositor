-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // time
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Musical time atoms for audio scheduling and synchronization.
-- |
-- | ## Musical Time vs Clock Time
-- | Musical applications often need to express time in beats and bars
-- | rather than absolute seconds. This module provides both.
-- |
-- | ## BPM and Time Signatures
-- | Beat-based time depends on tempo (BPM) and time signature.
-- | At 120 BPM, one beat = 500ms.
-- |
-- | ## Sample-Accurate Timing
-- | For precise audio scheduling, SampleCount provides sample-level accuracy.

module Hydrogen.Schema.Audio.Time
  ( -- * Types
    BeatTime(..)
  , BarTime(..)
  , SampleCount(..)
  , LatencyMs(..)
  , BPM(..)
  
  -- * Constructors
  , beatTime
  , barTime
  , sampleCount
  , latencyMs
  , bpm
  
  -- * Accessors
  , unwrapBeatTime
  , unwrapBarTime
  , unwrapSampleCount
  , unwrapLatencyMs
  , unwrapBPM
  
  -- * Predefined BPMs
  , bpm60
  , bpm90
  , bpm120
  , bpm140
  , bpm160
  
  -- * Conversions
  , beatsToMs
  , msToBeats
  , barsToBeats
  , beatsToSamples
  , samplesToMs
  , msToSamples
  
  -- * Operations
  , addBeats
  , subtractBeats
  , multiplyBeats
  
  -- * Bounds
  , beatTimeBounds
  , barTimeBounds
  , sampleCountBounds
  , latencyMsBounds
  , bpmBounds
  ) where

import Prelude

import Data.Int as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // beat time
-- ═════════════════════════════════════════════════════════════════════════════

-- | BeatTime - time measured in musical beats.
-- | Independent of tempo until converted to clock time.
-- | Supports fractional beats for sub-beat precision.
newtype BeatTime = BeatTime Number

derive instance eqBeatTime :: Eq BeatTime
derive instance ordBeatTime :: Ord BeatTime

instance showBeatTime :: Show BeatTime where
  show (BeatTime n) = show n <> " beats"

-- | Create a BeatTime value (clamped to non-negative)
beatTime :: Number -> BeatTime
beatTime n
  | n < 0.0 = BeatTime 0.0
  | otherwise = BeatTime n

unwrapBeatTime :: BeatTime -> Number
unwrapBeatTime (BeatTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // bar time
-- ═════════════════════════════════════════════════════════════════════════════

-- | BarTime - time measured in musical bars (measures).
-- | The number of beats per bar depends on the time signature.
-- | In 4/4 time, one bar = 4 beats.
newtype BarTime = BarTime Number

derive instance eqBarTime :: Eq BarTime
derive instance ordBarTime :: Ord BarTime

instance showBarTime :: Show BarTime where
  show (BarTime n) = show n <> " bars"

-- | Create a BarTime value (clamped to non-negative)
barTime :: Number -> BarTime
barTime n
  | n < 0.0 = BarTime 0.0
  | otherwise = BarTime n

unwrapBarTime :: BarTime -> Number
unwrapBarTime (BarTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sample count
-- ═════════════════════════════════════════════════════════════════════════════

-- | SampleCount - time measured in audio samples.
-- | For sample-accurate scheduling. The duration depends on sample rate.
-- | At 48kHz, 48000 samples = 1 second.
newtype SampleCount = SampleCount Int

derive instance eqSampleCount :: Eq SampleCount
derive instance ordSampleCount :: Ord SampleCount

instance showSampleCount :: Show SampleCount where
  show (SampleCount n) = show n <> " samples"

-- | Create a SampleCount value (clamped to non-negative)
sampleCount :: Int -> SampleCount
sampleCount n
  | n < 0 = SampleCount 0
  | otherwise = SampleCount n

unwrapSampleCount :: SampleCount -> Int
unwrapSampleCount (SampleCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // latency ms
-- ═════════════════════════════════════════════════════════════════════════════

-- | LatencyMs - latency measurement in milliseconds.
-- | Used for audio buffer latency, network delay, etc.
-- | Clamped to [0, 1000] covering practical audio latencies.
newtype LatencyMs = LatencyMs Number

derive instance eqLatencyMs :: Eq LatencyMs
derive instance ordLatencyMs :: Ord LatencyMs

instance showLatencyMs :: Show LatencyMs where
  show (LatencyMs n) = show n <> " ms latency"

-- | Create a LatencyMs value (clamped to 0-1000)
latencyMs :: Number -> LatencyMs
latencyMs n
  | n < 0.0 = LatencyMs 0.0
  | n > 1000.0 = LatencyMs 1000.0
  | otherwise = LatencyMs n

unwrapLatencyMs :: LatencyMs -> Number
unwrapLatencyMs (LatencyMs n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // bpm
-- ═════════════════════════════════════════════════════════════════════════════

-- | BPM - beats per minute (tempo).
-- | Standard musical tempo ranging from 20 (very slow) to 300 (very fast).
-- | Common tempos: 60 (slow), 120 (moderate), 180 (fast).
newtype BPM = BPM Number

derive instance eqBPM :: Eq BPM
derive instance ordBPM :: Ord BPM

instance showBPM :: Show BPM where
  show (BPM n) = show n <> " BPM"

-- | Create a BPM value (clamped to 20-300)
bpm :: Number -> BPM
bpm n
  | n < 20.0 = BPM 20.0
  | n > 300.0 = BPM 300.0
  | otherwise = BPM n

unwrapBPM :: BPM -> Number
unwrapBPM (BPM n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // predefined bpm
-- ═════════════════════════════════════════════════════════════════════════════

-- | 60 BPM - slow ballad tempo (1 beat per second)
bpm60 :: BPM
bpm60 = BPM 60.0

-- | 90 BPM - moderate tempo (hip-hop, R&B)
bpm90 :: BPM
bpm90 = BPM 90.0

-- | 120 BPM - standard dance tempo (house, techno)
bpm120 :: BPM
bpm120 = BPM 120.0

-- | 140 BPM - fast dance tempo (drum and bass)
bpm140 :: BPM
bpm140 = BPM 140.0

-- | 160 BPM - very fast tempo (hardcore, speedcore)
bpm160 :: BPM
bpm160 = BPM 160.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert beats to milliseconds at a given tempo.
-- | Formula: ms = (beats / bpm) * 60000
beatsToMs :: BPM -> BeatTime -> Number
beatsToMs (BPM tempo) (BeatTime beats) =
  (beats / tempo) * 60000.0

-- | Convert milliseconds to beats at a given tempo.
-- | Formula: beats = (ms * bpm) / 60000
msToBeats :: BPM -> Number -> BeatTime
msToBeats (BPM tempo) ms =
  beatTime ((ms * tempo) / 60000.0)

-- | Convert bars to beats given beats per bar.
-- | For 4/4 time, beatsPerBar = 4.
barsToBeats :: Number -> BarTime -> BeatTime
barsToBeats beatsPerBar (BarTime bars) =
  beatTime (bars * beatsPerBar)

-- | Convert beats to samples at a given tempo and sample rate.
-- | Formula: samples = (beats / bpm) * 60 * sampleRate
beatsToSamples :: BPM -> Int -> BeatTime -> SampleCount
beatsToSamples (BPM tempo) rate (BeatTime beats) =
  let seconds = beats / tempo * 60.0
      samples = seconds * Int.toNumber rate
  in sampleCount (Int.round samples)

-- | Convert samples to milliseconds at a given sample rate.
-- | Formula: ms = (samples / sampleRate) * 1000
samplesToMs :: Int -> SampleCount -> Number
samplesToMs rate (SampleCount samples)
  | rate <= 0 = 0.0
  | otherwise = (Int.toNumber samples / Int.toNumber rate) * 1000.0

-- | Convert milliseconds to samples at a given sample rate.
-- | Formula: samples = (ms / 1000) * sampleRate
msToSamples :: Int -> Number -> SampleCount
msToSamples rate ms
  | rate <= 0 = SampleCount 0
  | ms < 0.0 = SampleCount 0
  | otherwise = sampleCount (Int.round ((ms / 1000.0) * Int.toNumber rate))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two beat times.
addBeats :: BeatTime -> BeatTime -> BeatTime
addBeats (BeatTime a) (BeatTime b) = beatTime (a + b)

-- | Subtract beat times (clamped to 0).
subtractBeats :: BeatTime -> BeatTime -> BeatTime
subtractBeats (BeatTime a) (BeatTime b) = beatTime (a - b)

-- | Multiply beat time by a factor.
multiplyBeats :: Number -> BeatTime -> BeatTime
multiplyBeats factor (BeatTime beats) = beatTime (beats * factor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for BeatTime
-- |
-- | Min: 0.0
-- | Max: unbounded (finite)
beatTimeBounds :: Bounded.NumberBounds
beatTimeBounds = Bounded.numberBounds 0.0 10000.0 "beatTime" "Time in musical beats (0+)"

-- | Bounds for BarTime
-- |
-- | Min: 0.0
-- | Max: unbounded (finite)
barTimeBounds :: Bounded.NumberBounds
barTimeBounds = Bounded.numberBounds 0.0 1000.0 "barTime" "Time in musical bars (0+)"

-- | Bounds for SampleCount
-- |
-- | Min: 0
-- | Max: unbounded (finite)
sampleCountBounds :: Bounded.IntBounds
sampleCountBounds = Bounded.intBounds 0 2147483647 "sampleCount" "Audio sample count (0+)"

-- | Bounds for LatencyMs
-- |
-- | Min: 0.0
-- | Max: 1000.0 (1 second max practical latency)
latencyMsBounds :: Bounded.NumberBounds
latencyMsBounds = Bounded.numberBounds 0.0 1000.0 "latencyMs" "Audio latency in milliseconds (0-1000)"

-- | Bounds for BPM
-- |
-- | Min: 20.0 (very slow)
-- | Max: 300.0 (very fast)
bpmBounds :: Bounded.NumberBounds
bpmBounds = Bounded.numberBounds 20.0 300.0 "bpm" "Beats per minute (20-300)"
