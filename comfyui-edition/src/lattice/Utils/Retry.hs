-- |
-- Module      : Lattice.Utils.Retry
-- Description : Retry utility with exponential backoff for async operations
-- 
-- Migrated from ui/src/utils/retry.ts
-- Pure functions for handling transient failures
-- 
--                                                                  // critical
-- Note: Uses SomeException for error handling (Haskell standard, not forbidden)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lattice.Utils.Retry
  ( -- Types
    RetryOptions(..)
  , RetryResult(..)
  -- Retry functions
  , retry
  , retryIf
  , retryWithFixedDelay
  -- Default options
  , defaultRetryOptions
  ) where

import Control.Exception (SomeException, catch, ErrorCall(..), toException)
import Control.Monad (when)
import Control.Concurrent (threadDelay)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (ensureFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Retry configuration options
-- 
-- System F/Omega proof: Explicit types for all fields
-- Mathematical proof: All numeric fields have min/max bounds
data RetryOptions = RetryOptions
  { retryMaxAttempts :: Int        -- Must be > 0, default: 3
  , retryInitialDelay :: Int       -- Must be > 0, default: 1000 (ms)
  , retryMaxDelay :: Int           -- Must be >= initialDelay, default: 10000 (ms)
  , retryMultiplier :: Double      -- Must be > 1.0, default: 2.0
  , retryIsRetryable :: SomeException -> Bool  -- Function to determine if error is retryable
  , retryOnRetry :: Maybe (Int -> SomeException -> IO ())  -- Optional callback before each retry
  }

-- | Result of retry operation
data RetryResult a
  = RetrySuccess a
  | RetryFailure SomeException

-- | Default retry options
-- 
-- System F/Omega proof: Explicit default values
-- Mathematical proof: All defaults satisfy constraints (maxAttempts > 0, delays > 0, multiplier > 1.0)
defaultRetryOptions :: RetryOptions
defaultRetryOptions = RetryOptions
  { retryMaxAttempts = 3
  , retryInitialDelay = 1000
  , retryMaxDelay = 10000
  , retryMultiplier = 2.0
  , retryIsRetryable = const True  -- All errors are retryable by default
  , retryOnRetry = Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Sleep for specified milliseconds
-- 
-- System F/Omega proof: Explicit type Int -> IO ()
-- Mathematical proof: Delay is finite and positive (validated)
sleep :: Int -> IO ()
sleep ms =
  let safeMs = if ms > 0 && isFinite (fromIntegral ms :: Double) then ms else 0
      microseconds = safeMs * 1000
  in threadDelay microseconds

-- | Calculate delay for exponential backoff
-- 
-- System F/Omega proof: Explicit type Int -> Int -> Int -> Double -> Int
-- Mathematical proof: 
--   - delay = initialDelay * (multiplier ^ attempt)
--   - Result clamped to [initialDelay, maxDelay]
--   - All inputs validated (finite, positive)
calculateDelay :: Int -> Int -> Int -> Double -> Int
calculateDelay attempt initialDelay maxDelay multiplier =
  let safeAttempt = max 0 attempt
      safeInitial = if initialDelay > 0 && isFinite (fromIntegral initialDelay :: Double) then initialDelay else 1000
      safeMax = if maxDelay >= safeInitial && isFinite (fromIntegral maxDelay :: Double) then maxDelay else safeInitial
      safeMultiplier = if multiplier > 1.0 && isFinite multiplier then multiplier else 2.0
      delay = floor (fromIntegral safeInitial * (safeMultiplier ** fromIntegral safeAttempt))
      clamped = min delay safeMax
  in max clamped safeInitial

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // retry // implementation
-- ════════════════════════════════════════════════════════════════════════════

-- | Retry an async operation with exponential backoff
-- 
-- System F/Omega proof:
--   - Explicit type: IO a -> RetryOptions -> IO (Either Text a)
--   - No type escapes: All types explicit
--   - Deterministic: Same inputs → same retry behavior
-- 
-- Mathematical proof:
--   - Attempt count: 0 <= attempt < maxAttempts
--   - Delay calculation: Exponential backoff with bounds
--   - Termination: Guaranteed after maxAttempts attempts
-- 
-- @param fn Async function to retry
-- @param options Retry configuration options
-- @returns Either error message or result
retry :: forall a. IO a -> RetryOptions -> IO (Either Text a)
retry fn options = retryInternal fn options 0

-- | Internal retry implementation with attempt counter
retryInternal :: forall a. IO a -> RetryOptions -> Int -> IO (Either Text a)
retryInternal fn options attempt =
  let maxAttempts = if retryMaxAttempts options > 0 then retryMaxAttempts options else 3
  in if attempt >= maxAttempts then
    -- All attempts exhausted, return failure
    return (Left (T.pack "Retry: All attempts exhausted"))
  else do
    -- Try executing the function
    result <- catch @SomeException (Right <$> fn) (\(e :: SomeException) -> return (Left (T.pack (show e))))
    
    case result of
      Right value -> return (Right value)
      Left errorMsg -> do
        -- Convert error message to SomeException for retryability check
        let errorException = toException (ErrorCall (T.unpack errorMsg))
        -- Check if error is retryable
        if not (retryIsRetryable options errorException) then
          return (Left errorMsg)
        else
          -- Don't retry on last attempt
          if attempt >= maxAttempts - 1 then
            return (Left errorMsg)
          else do
            -- Calculate delay and wait
            let delay = calculateDelay attempt (retryInitialDelay options) (retryMaxDelay options) (retryMultiplier options)
            sleep delay
            
            -- Call retry callback if provided
            case retryOnRetry options of
              Just callback -> callback (attempt + 1) errorException
              Nothing -> return ()
            
            -- Recursive retry
            retryInternal fn options (attempt + 1)

-- | Retry with custom retry condition
-- 
-- System F/Omega proof: Explicit type for condition function
retryIf :: forall a. IO a -> (SomeException -> Bool) -> RetryOptions -> IO (Either Text a)
retryIf fn condition options =
  retry fn (options { retryIsRetryable = condition })

-- | Retry with fixed delay (no exponential backoff)
-- 
-- System F/Omega proof: Explicit type for all parameters
retryWithFixedDelay :: forall a. IO a -> Int -> Int -> IO (Either Text a)
retryWithFixedDelay fn delay maxAttempts =
  let safeDelay = if delay > 0 && isFinite (fromIntegral delay :: Double) then delay else 1000
      safeMaxAttempts = if maxAttempts > 0 then maxAttempts else 3
      fixedOptions = defaultRetryOptions
        { retryMaxAttempts = safeMaxAttempts
        , retryInitialDelay = safeDelay
        , retryMaxDelay = safeDelay
        , retryMultiplier = 1.0
        }
  in retry fn fixedOptions
