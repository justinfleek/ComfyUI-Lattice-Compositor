-- |
-- Module      : Lattice.Services.LoopExpressions
-- Description : Pure loop expression functions for repeating animations
-- 
-- Migrated from ui/src/services/expressions/loopExpressions.ts
-- Pure calculations for repeatAfter and repeatBefore
-- Note: Keyframe interpolation handled separately (requires interpolation service)
--

module Lattice.Services.LoopExpressions
  ( -- Loop expressions
    repeatAfter
  , repeatBefore
  -- Types
  , LoopType(..)
  , LoopParams(..)
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Loop type for animation repetition
data LoopType
  = LoopCycle      -- Repeat from start
  | LoopPingpong   -- Alternate forward/backward
  | LoopOffset     -- Add cumulative offset each cycle
  | LoopContinue   -- Continue at last velocity
  deriving (Eq, Show)

-- | Parameters for loop expressions
-- Simplified from LoopExpressionContext - only what's needed for pure calculations
data LoopParams = LoopParams
  { loopParamsTime :: Double          -- Current time
  , loopParamsStartTime :: Double     -- Start time of loop range
  , loopParamsEndTime :: Double       -- End time of loop range
  , loopParamsValue :: [Double]       -- Current value (as array)
  , loopParamsVelocity :: [Double]    -- Current velocity (as array)
  , loopParamsStartValue :: [Double] -- Value at start of loop range
  , loopParamsEndValue :: [Double]   -- Value at end of loop range
  } deriving (Eq, Show)

-- | Safe array element access
safeGet :: [Double] -> Int -> Double
safeGet arr idx =
  let val = safeArrayGet arr idx 0.0
  in if isFinite val then val else 0.0

-- ============================================================================
-- LOOP EXPRESSIONS
-- ============================================================================

-- | Repeat After expression
-- Pure function: same inputs → same outputs
-- Repeats animation after last keyframe
-- Note: Returns cycle time and direction for interpolation - caller handles interpolation
repeatAfter ::
  LoopParams ->
  LoopType ->
  (Double, Bool)  -- (cycleTime, isReverse)
repeatAfter params loopType =
  let time = loopParamsTime params
      startTime = loopParamsStartTime params
      endTime = loopParamsEndTime params
      duration = endTime - startTime
      elapsed = time - endTime
  in if duration <= 0 || time <= endTime
       then (time, False)  -- Before end time, return current time
       else case loopType of
         LoopCycle ->
           let cycleTime = startTime + (elapsed - fromIntegral (floor (elapsed / duration)) * duration)
           in (cycleTime, False)
         LoopPingpong ->
           let cycles = floor (elapsed / duration) :: Int
               cycleProgress = (elapsed - fromIntegral cycles * duration) / duration
               isReverse = cycles `mod` 2 == 1
               t = if isReverse then 1 - cycleProgress else cycleProgress
               cycleTime = startTime + t * duration
           in (cycleTime, isReverse)
         LoopOffset ->
           let cycles = floor (elapsed / duration) :: Int
               cycleTime = startTime + (elapsed - fromIntegral cycles * duration)
           in (cycleTime, False)  -- Offset handled by caller
         LoopContinue ->
           (time, False)  -- Continue handled by caller with velocity

-- | Calculate offset for repeatAfter offset mode
-- Pure function: same inputs → same outputs
repeatAfterOffset ::
  LoopParams ->
  Double ->  -- elapsed time
  [Double]
repeatAfterOffset params elapsed =
  let startTime = loopParamsStartTime params
      endTime = loopParamsEndTime params
      duration = endTime - startTime
      cycles = floor (elapsed / duration) :: Int
      startValue = loopParamsStartValue params
      endValue = loopParamsEndValue params
      maxLen = max (length startValue) (length endValue)
      delta i = safeGet endValue i - safeGet startValue i
  in [safeGet startValue i + delta i * fromIntegral (cycles + 1) | i <- [0 .. maxLen - 1]]

-- | Calculate continue value for repeatAfter continue mode
-- Pure function: same inputs → same outputs
repeatAfterContinue ::
  LoopParams ->
  Double ->  -- elapsed time
  [Double]
repeatAfterContinue params elapsed =
  let valueArr = loopParamsValue params
      velocityArr = loopParamsVelocity params
      maxLen = max (length valueArr) (length velocityArr)
  in [safeGet valueArr i + safeGet velocityArr i * elapsed | i <- [0 .. maxLen - 1]]

-- | Repeat Before expression
-- Pure function: same inputs → same outputs
-- Repeats animation before first keyframe
-- Note: Returns cycle time and direction for interpolation - caller handles interpolation
repeatBefore ::
  LoopParams ->
  LoopType ->
  (Double, Bool)  -- (cycleTime, isReverse)
repeatBefore params loopType =
  let time = loopParamsTime params
      startTime = loopParamsStartTime params
      endTime = loopParamsEndTime params
      duration = endTime - startTime
      elapsed = startTime - time
  in if duration <= 0 || time >= startTime
       then (time, False)  -- After start time, return current time
       else case loopType of
         LoopCycle ->
           let cycleTime = endTime - (elapsed - fromIntegral (floor (elapsed / duration)) * duration)
           in (cycleTime, False)
         LoopPingpong ->
           let cycles = floor (elapsed / duration) :: Int
               cycleProgress = (elapsed - fromIntegral cycles * duration) / duration
               isReverse = cycles `mod` 2 == 1
               t = if isReverse then cycleProgress else 1 - cycleProgress
               cycleTime = startTime + t * duration
           in (cycleTime, isReverse)
         LoopOffset ->
           let cycles = floor (elapsed / duration) :: Int
               cycleTime = endTime - (elapsed - fromIntegral cycles * duration)
           in (cycleTime, False)  -- Offset handled by caller
         LoopContinue ->
           (time, False)  -- Continue handled by caller with velocity

-- | Calculate offset for repeatBefore offset mode
-- Pure function: same inputs → same outputs
repeatBeforeOffset ::
  LoopParams ->
  Double ->  -- elapsed time
  [Double]
repeatBeforeOffset params elapsed =
  let startTime = loopParamsStartTime params
      endTime = loopParamsEndTime params
      duration = endTime - startTime
      cycles = floor (elapsed / duration) :: Int
      startValue = loopParamsStartValue params
      endValue = loopParamsEndValue params
      maxLen = max (length startValue) (length endValue)
      delta i = safeGet startValue i - safeGet endValue i
  in [safeGet endValue i + delta i * fromIntegral (cycles + 1) | i <- [0 .. maxLen - 1]]

-- | Calculate continue value for repeatBefore continue mode
-- Pure function: same inputs → same outputs
repeatBeforeContinue ::
  LoopParams ->
  Double ->  -- elapsed time
  [Double]
repeatBeforeContinue params elapsed =
  let valueArr = loopParamsValue params
      velocityArr = loopParamsVelocity params
      maxLen = max (length valueArr) (length velocityArr)
  in [safeGet valueArr i - safeGet velocityArr i * elapsed | i <- [0 .. maxLen - 1]]
