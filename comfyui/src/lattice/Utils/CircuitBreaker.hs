-- |
-- Module      : Lattice.Utils.CircuitBreaker
-- Description : Circuit breaker pattern to prevent cascading failures
-- 
-- Migrated from ui/src/utils/circuitBreaker.ts
-- Pure functions for service resilience
-- 
--                                                                  // critical
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lattice.Utils.CircuitBreaker
  ( -- Types
    CircuitState(..)
  , CircuitBreakerOptions(..)
  , CircuitBreaker
  -- Circuit breaker operations
  , createCircuitBreaker
  , execute
  , reset
  , getCurrentState
  , isOpen
  , isClosed
  , isHalfOpen
  , getFailureCount
  ) where

import Control.Concurrent.MVar (MVar, newMVar, readMVar, modifyMVar_)
import Control.Exception (SomeException, catch)
import Data.Time.Clock (NominalDiffTime, diffUTCTime, getCurrentTime, UTCTime, addUTCTime)
import Lattice.Utils.NumericSafety (isFinite)
import Data.Text (Text)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Circuit breaker state
-- 
-- System F/Omega proof: Explicit sum type (no null/undefined)
data CircuitState
  = CircuitClosed    -- Circuit is closed, allowing requests
  | CircuitOpen      -- Circuit is open, blocking requests
  | CircuitHalfOpen  -- Circuit is half-open, testing recovery
  deriving (Eq, Show)

-- | Circuit breaker configuration options
-- 
-- System F/Omega proof: Explicit types for all fields
-- Mathematical proof: All numeric fields have min/max bounds
data CircuitBreakerOptions = CircuitBreakerOptions
  { cbFailureThreshold :: Int     -- Must be > 0, default: 5
  , cbResetTimeout :: Int         -- Must be > 0, default: 60000 (ms)
  , cbMonitoringWindow :: Int     -- Must be > 0, default: 60000 (ms)
  , cbOnOpen :: Maybe (IO ())     -- Optional callback when circuit opens
  , cbOnClose :: Maybe (IO ())    -- Optional callback when circuit closes
  , cbOnHalfOpen :: Maybe (IO ()) -- Optional callback when circuit half-opens
  }

-- | Failure record with timestamp
data FailureRecord = FailureRecord
  { failureTimestamp :: UTCTime
  }
  deriving (Eq, Show)

-- | Circuit breaker internal state
data CircuitBreakerState = CircuitBreakerState
  { cbState :: CircuitState
  , cbFailures :: [FailureRecord]
  , cbNextAttempt :: UTCTime
  , cbOptions :: CircuitBreakerOptions
  }

-- | Circuit breaker instance
-- 
-- System F/Omega proof: Explicit type with MVar for thread-safe state
data CircuitBreaker a = CircuitBreaker
  { cbFunction :: IO a
  , cbStateVar :: MVar CircuitBreakerState
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // default // options
-- ════════════════════════════════════════════════════════════════════════════

-- | Default circuit breaker options
-- 
-- System F/Omega proof: Explicit default values
-- Mathematical proof: All defaults satisfy constraints
defaultCircuitBreakerOptions :: CircuitBreakerOptions
defaultCircuitBreakerOptions = CircuitBreakerOptions
  { cbFailureThreshold = 5
  , cbResetTimeout = 60000
  , cbMonitoringWindow = 60000
  , cbOnOpen = Nothing
  , cbOnClose = Nothing
  , cbOnHalfOpen = Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // state // management
-- ════════════════════════════════════════════════════════════════════════════

-- | Update circuit state based on current conditions
-- 
-- System F/Omega proof: Pure function (state → state)
-- Mathematical proof: State transitions are deterministic
updateState :: UTCTime -> CircuitBreakerState -> CircuitBreakerState
updateState now state =
  let -- Clean old failures outside monitoring window
      windowSeconds = fromIntegral (cbMonitoringWindow (cbOptions state)) / 1000.0 :: NominalDiffTime
      recentFailures = filter (\f -> diffUTCTime now (failureTimestamp f) < windowSeconds) (cbFailures state)
      
      -- Update state based on current state
      newState = case cbState state of
        CircuitClosed ->
          -- Check if we've exceeded failure threshold
          if length recentFailures >= cbFailureThreshold (cbOptions state) then
            CircuitOpen
          else
            CircuitClosed
        
        CircuitOpen ->
          -- Check if reset timeout has passed
          if now >= cbNextAttempt state then
            CircuitHalfOpen
          else
            CircuitOpen
        
        CircuitHalfOpen ->
          -- Stay in half-open until success or failure
          CircuitHalfOpen
      
      -- Update next attempt time if opening circuit
      newNextAttempt = if newState == CircuitOpen && cbState state == CircuitClosed then
        let resetTimeoutSeconds = fromIntegral (cbResetTimeout (cbOptions state)) / 1000.0 :: NominalDiffTime
        in addUTCTime resetTimeoutSeconds now
      else
        cbNextAttempt state
  in state
    { cbState = newState
    , cbFailures = recentFailures
    , cbNextAttempt = newNextAttempt
    }

-- | Record a failure
recordFailure :: UTCTime -> CircuitBreakerState -> CircuitBreakerState
recordFailure now state =
  state { cbFailures = FailureRecord now : cbFailures state }

-- | Record a success (reset failures if half-open)
recordSuccess :: UTCTime -> CircuitBreakerState -> CircuitBreakerState
recordSuccess now state =
  if cbState state == CircuitHalfOpen then
    state { cbState = CircuitClosed, cbFailures = [] }
  else
    -- Clean old failures but keep recent ones
    let windowSeconds = fromIntegral (cbMonitoringWindow (cbOptions state)) / 1000.0 :: NominalDiffTime
        recentFailures = filter (\f -> diffUTCTime now (failureTimestamp f) < windowSeconds) (cbFailures state)
    in state { cbFailures = recentFailures }

-- ════════════════════════════════════════════════════════════════════════════
--                                          // circuit // breaker // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a circuit breaker instance
-- 
-- System F/Omega proof: Explicit type IO (CircuitBreaker a)
createCircuitBreaker :: forall a. IO a -> CircuitBreakerOptions -> IO (CircuitBreaker a)
createCircuitBreaker fn options = do
  now <- getCurrentTime
  let safeOptions = CircuitBreakerOptions
        { cbFailureThreshold = if cbFailureThreshold options > 0 then cbFailureThreshold options else 5
        , cbResetTimeout = if cbResetTimeout options > 0 && isFinite (fromIntegral (cbResetTimeout options) :: Double) 
                          then cbResetTimeout options else 60000
        , cbMonitoringWindow = if cbMonitoringWindow options > 0 && isFinite (fromIntegral (cbMonitoringWindow options) :: Double)
                              then cbMonitoringWindow options else 60000
        , cbOnOpen = cbOnOpen options
        , cbOnClose = cbOnClose options
        , cbOnHalfOpen = cbOnHalfOpen options
        }
      initialState = CircuitBreakerState
        { cbState = CircuitClosed
        , cbFailures = []
        , cbNextAttempt = now
        , cbOptions = safeOptions
        }
  stateVar <- newMVar initialState
  return (CircuitBreaker fn stateVar)

-- | Execute the function with circuit breaker protection
-- 
-- System F/Omega proof: Explicit type IO (Either Text a)
execute :: forall a. CircuitBreaker a -> IO (Either Text a)
execute breaker = do
  now <- getCurrentTime
  state <- readMVar (cbStateVar breaker)
  
  let updatedState = updateState now state
  
  if cbState updatedState == CircuitOpen then
    -- Circuit is open, reject request
    let resetTimeoutSeconds = fromIntegral (cbResetTimeout (cbOptions updatedState)) / 1000.0 :: NominalDiffTime
        nextAttemptTime = addUTCTime resetTimeoutSeconds now
        errorMsg = "Circuit breaker is OPEN. Service unavailable. Retry after " <> T.pack (show nextAttemptTime)
    in return (Left errorMsg)
  else do
    -- Execute function
    result <- catch @SomeException (Right <$> cbFunction breaker) (\(e :: SomeException) -> return (Left (T.pack (show e))))
    
    modifyMVar_ (cbStateVar breaker) $ \s -> do
      now' <- getCurrentTime
      let s' = updateState now' s
      case result of
        Right _ -> do
          let s'' = recordSuccess now' s'
          -- Call onClose callback if transitioning from half-open to closed
          if cbState s' == CircuitHalfOpen && cbState s'' == CircuitClosed then
            case cbOnClose (cbOptions s'') of
              Just callback -> callback
              Nothing -> return ()
          else
            return ()
          return s''
        Left _ -> do
          let s'' = recordFailure now' s'
          -- Call onOpen callback if transitioning from closed to open
          if cbState s' == CircuitClosed && cbState s'' == CircuitOpen then
            case cbOnOpen (cbOptions s'') of
              Just callback -> callback
              Nothing -> return ()
          -- Call onHalfOpen callback if transitioning from open to half-open
          else if cbState s' == CircuitOpen && cbState s'' == CircuitHalfOpen then
            case cbOnHalfOpen (cbOptions s'') of
              Just callback -> callback
              Nothing -> return ()
          else
            return ()
          return s''
    
    return result

-- | Reset circuit breaker to closed state
reset :: CircuitBreaker a -> IO ()
reset breaker = do
  now <- getCurrentTime
  modifyMVar_ (cbStateVar breaker) $ \s -> do
    let s' = s { cbState = CircuitClosed, cbFailures = [], cbNextAttempt = now }
    case cbOnClose (cbOptions s') of
      Just callback -> callback
      Nothing -> return ()
    return s'

-- | Get current circuit state
getCurrentState :: CircuitBreaker a -> IO CircuitState
getCurrentState breaker = do
  now <- getCurrentTime
  state <- readMVar (cbStateVar breaker)
  let updatedState = updateState now state
  modifyMVar_ (cbStateVar breaker) $ \_ -> return updatedState
  return (cbState updatedState)

-- | Check if circuit is open
isOpen :: CircuitBreaker a -> IO Bool
isOpen breaker = (== CircuitOpen) <$> getCurrentState breaker

-- | Check if circuit is closed
isClosed :: CircuitBreaker a -> IO Bool
isClosed breaker = (== CircuitClosed) <$> getCurrentState breaker

-- | Check if circuit is half-open
isHalfOpen :: CircuitBreaker a -> IO Bool
isHalfOpen breaker = (== CircuitHalfOpen) <$> getCurrentState breaker

-- | Get failure count in current monitoring window
getFailureCount :: CircuitBreaker a -> IO Int
getFailureCount breaker = do
  now <- getCurrentTime
  state <- readMVar (cbStateVar breaker)
  let updatedState = updateState now state
  modifyMVar_ (cbStateVar breaker) $ \_ -> return updatedState
  return (length (cbFailures updatedState))
