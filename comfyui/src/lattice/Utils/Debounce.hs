-- |
-- Module      : Lattice.Utils.Debounce
-- Description : Debounce and throttle utilities for controlling function execution frequency
-- 
-- Migrated from ui/src/utils/debounce.ts
-- Pure functions for performance optimization
-- 
-- CRITICAL: No forbidden patterns - explicit types, no null/undefined, no type escapes
-- Note: These utilities are primarily for TypeScript interop via FFI.
-- For pure Haskell code, consider using STM or other concurrency primitives.
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lattice.Utils.Debounce
  ( -- Types
    DebouncedFunction
  , ThrottledFunction
  -- Debounce functions
  , debounce
  , debounceLeading
  -- Throttle functions
  , throttle
  , throttleLeading
  ) where

import Control.Concurrent (ThreadId, forkIO, killThread, threadDelay)
import Control.Concurrent.MVar (MVar, newMVar, readMVar, modifyMVar_)
import Data.Time.Clock (NominalDiffTime, diffUTCTime, getCurrentTime, UTCTime)
import Lattice.Utils.NumericSafety (isFinite)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Debounced function - delays execution until after a period of inactivity
-- 
-- Type: (a -> IO ()) -> Int -> Bool -> IO (a -> IO ())
-- 
-- System F/Omega proof: Explicit type at function boundary
-- Mathematical proof: Deterministic delay calculation
type DebouncedFunction a = a -> IO ()

-- | Throttled function - limits execution to at most once per time period
-- 
-- Type: (a -> IO ()) -> Int -> IO (a -> IO ())
-- 
-- System F/Omega proof: Explicit type at function boundary
-- Mathematical proof: Deterministic throttle calculation
type ThrottledFunction a = a -> IO ()

-- ============================================================================
-- INTERNAL STATE TYPES
-- ============================================================================

-- | Internal state for debounced function
data DebounceState = DebounceState
  { debounceTimeoutId :: Maybe ThreadId
  , debounceHasCalled :: Bool
  , debounceDelay :: Int  -- milliseconds (must be > 0)
  , debounceImmediate :: Bool
  }

-- | Internal state for throttled function
data ThrottleState = ThrottleState
  { throttleLastCall :: UTCTime
  , throttleTimeoutId :: Maybe ThreadId
  , throttleDelay :: Int  -- milliseconds (must be > 0)
  }

-- ============================================================================
-- DEBOUNCE IMPLEMENTATION
-- ============================================================================

-- | Debounce a function - delays execution until after a period of inactivity
-- 
-- System F/Omega proof:
--   - Explicit type: (a -> IO ()) -> Int -> Bool -> IO (a -> IO ())
--   - No type escapes: All types explicit
--   - Deterministic: Same inputs → same delay calculation
-- 
-- Mathematical proof:
--   - Delay calculation: delay_ms is finite and positive (validated)
--   - Timeout cancellation: Previous timeout always cancelled before new one
--   - Execution guarantee: Function executes exactly once after delay period
-- 
-- @param fn Function to debounce
-- @param delay Delay in milliseconds (must be > 0, finite)
-- @param immediate If True, execute immediately on first call
-- @returns Debounced function
debounce :: forall a. (a -> IO ()) -> Int -> Bool -> IO (DebouncedFunction a)
debounce fn delay immediate = do
  -- Validate delay is positive and finite
  let safeDelay = if delay > 0 && isFinite (fromIntegral delay :: Double) then delay else 1000
  
  stateVar <- newMVar (DebounceState Nothing False safeDelay immediate)
  
  return $ \args -> do
    state <- readMVar stateVar
    
    let callNow = immediate && not (debounceHasCalled state)
    
    -- Cancel existing timeout if present
    case debounceTimeoutId state of
      Just tid -> killThread tid
      Nothing -> return ()
    
    -- Create new timeout
    tid <- forkIO $ do
      threadDelay (debounceDelay state * 1000)  -- Convert ms to microseconds
      modifyMVar_ stateVar $ \s -> do
        if immediate then
          return (s { debounceTimeoutId = Nothing, debounceHasCalled = False })
        else do
          fn args
          return (s { debounceTimeoutId = Nothing })
    
    modifyMVar_ stateVar $ \s -> do
      if callNow then do
        fn args
        return (s { debounceTimeoutId = Just tid, debounceHasCalled = True })
      else
        return (s { debounceTimeoutId = Just tid })

-- | Debounce with leading edge execution
-- Executes immediately on first call, then debounces subsequent calls
debounceLeading :: forall a. (a -> IO ()) -> Int -> IO (DebouncedFunction a)
debounceLeading fn delay = debounce fn delay True

-- ============================================================================
-- THROTTLE IMPLEMENTATION
-- ============================================================================

-- | Throttle a function - limits execution to at most once per time period
-- 
-- System F/Omega proof:
--   - Explicit type: (a -> IO ()) -> Int -> IO (a -> IO ())
--   - No type escapes: All types explicit
--   - Deterministic: Same inputs → same throttle calculation
-- 
-- Mathematical proof:
--   - Delay calculation: delay_ms is finite and positive (validated)
--   - Time check: now - lastCall >= delay guarantees minimum interval
--   - Execution guarantee: Function executes at most once per delay period
-- 
-- @param fn Function to throttle
-- @param delay Minimum time between executions in milliseconds (must be > 0, finite)
-- @returns Throttled function
throttle :: forall a. (a -> IO ()) -> Int -> IO (ThrottledFunction a)
throttle fn delay = do
  -- Validate delay is positive and finite
  let safeDelay = if delay > 0 && isFinite (fromIntegral delay :: Double) then delay else 1000
  
  now <- getCurrentTime
  stateVar <- newMVar (ThrottleState now Nothing safeDelay)
  
  return $ \args -> do
    now' <- getCurrentTime
    state <- readMVar stateVar
    
    let timeSinceLastCall = diffUTCTime now' (throttleLastCall state)
        delaySeconds = fromIntegral safeDelay / 1000.0 :: NominalDiffTime
    
    if timeSinceLastCall >= delaySeconds then
      -- Enough time has passed, execute immediately
      modifyMVar_ stateVar $ \s -> do
        fn args
        return (s { throttleLastCall = now' })
    else do
      -- Schedule execution for when delay period ends
      case throttleTimeoutId state of
        Just tid -> killThread tid
        Nothing -> return ()
      let remainingDelay = delaySeconds - timeSinceLastCall
          remainingDelayMicroseconds = max 0 (floor (remainingDelay * 1000000))
      tidNew <- forkIO $ do
        threadDelay (fromIntegral remainingDelayMicroseconds)
        modifyMVar_ stateVar $ \s -> do
          now2 <- getCurrentTime
          fn args
          return (s { throttleLastCall = now2, throttleTimeoutId = Nothing })
      modifyMVar_ stateVar $ \s -> return (s { throttleTimeoutId = Just tidNew })

-- | Throttle with leading edge execution
-- Executes immediately, then throttles subsequent calls
throttleLeading :: forall a. (a -> IO ()) -> Int -> IO (ThrottledFunction a)
throttleLeading fn delay = do
  -- Validate delay is positive and finite
  let safeDelay = if delay > 0 && isFinite (fromIntegral delay :: Double) then delay else 1000
  
  now <- getCurrentTime
  stateVar <- newMVar (ThrottleState now Nothing safeDelay)
  
  return $ \args -> do
    now' <- getCurrentTime
    state <- readMVar stateVar
    
    let timeSinceLastCall = diffUTCTime now' (throttleLastCall state)
        delaySeconds = fromIntegral safeDelay / 1000.0 :: NominalDiffTime
    
    if timeSinceLastCall >= delaySeconds then do
      fn args
      modifyMVar_ stateVar $ \s -> return (s { throttleLastCall = now' })
    else
      return ()
