{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.RateLimitsSchema
Description : Rate limits schema
Copyright   : (c) Lattice, 2026
License     : MIT

Validates rate limit data stored in localStorage/sessionStorage.

Source: lattice-core/lean/Lattice/Schemas/Settings/RateLimitsSchema.lean
-}

module Lattice.Schemas.Settings.RateLimitsSchema
  ( -- * Constants
    maxCallsPerDay
  , maxCallsPerSession
  , maxVramCostMB
  , maxRateLimitKeys
    -- * Rate Limit Config
  , RateLimitConfig(..)
  , validateRateLimitConfig
    -- * Rate Limit Status
  , RateLimitStatus(..)
  , validateRateLimitStatus
    -- * Stored Rate Limits
  , StoredRateLimits(..)
  , validateStoredRateLimits
  , safeValidateStoredRateLimits
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (Maybe(..))

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateNonEmptyString, validateString
  , validatePositiveInt, validateNonNegativeInt
  , validatePositiveFloat, validateDateTime, validateDate
  )

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxCallsPerDay :: Int
maxCallsPerDay = 100000

maxCallsPerSession :: Int
maxCallsPerSession = 10000

maxVramCostMB :: Double
maxVramCostMB = 1000000  -- 1TB

maxRateLimitKeys :: Int
maxRateLimitKeys = 1000

--------------------------------------------------------------------------------
-- Rate Limit Config
--------------------------------------------------------------------------------

-- | Rate limit configuration for a tool
data RateLimitConfig = RateLimitConfig
  { rlcToolName :: !Text
  , rlcMaxPerDay :: !Int
  , rlcMaxPerSession :: !(Maybe Int)
  , rlcVramCostMB :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Validate RateLimitConfig
validateRateLimitConfig :: RateLimitConfig -> Either ValidationError RateLimitConfig
validateRateLimitConfig config = do
  _ <- validateNonEmptyString "toolName" maxNameLength (rlcToolName config)
  _ <- validatePositiveInt "maxPerDay" maxCallsPerDay (rlcMaxPerDay config)
  case rlcMaxPerSession config of
    Just maxSess -> do
      _ <- validatePositiveInt "maxPerSession" maxCallsPerSession maxSess
      pure ()
    Nothing -> pure ()
  case rlcVramCostMB config of
    Just cost -> do
      _ <- validatePositiveFloat "vramCostMB" maxVramCostMB cost
      pure ()
    Nothing -> pure ()
  Right config

--------------------------------------------------------------------------------
-- Rate Limit Status
--------------------------------------------------------------------------------

-- | Rate limit status for a tool
data RateLimitStatus = RateLimitStatus
  { rlsToolName :: !Text
  , rlsCallsToday :: !Int
  , rlsMaxPerDay :: !Int
  , rlsCallsThisSession :: !Int
  , rlsMaxPerSession :: !(Maybe Int)
  , rlsCanCall :: !Bool
  , rlsBlockedReason :: !(Maybe Text)
  , rlsResetsAt :: !Text  -- ISO timestamp
  , rlsResetsIn :: !Text  -- Human readable
  }
  deriving stock (Eq, Show, Generic)

-- | Validate status constraints
validateStatusConstraints :: RateLimitStatus -> Either ValidationError ()
validateStatusConstraints status
  | rlsCallsToday status > rlsMaxPerDay status =
      Left $ mkError "callsToday" "must be <= maxPerDay"
  | otherwise = case rlsMaxPerSession status of
      Just maxSess | rlsCallsThisSession status > maxSess ->
        Left $ mkError "callsThisSession" "must be <= maxPerSession"
      _ -> Right ()

-- | Validate RateLimitStatus
validateRateLimitStatus :: RateLimitStatus -> Either ValidationError RateLimitStatus
validateRateLimitStatus status = do
  _ <- validateNonEmptyString "toolName" maxNameLength (rlsToolName status)
  _ <- validateNonNegativeInt "callsToday" maxCallsPerDay (rlsCallsToday status)
  _ <- validatePositiveInt "maxPerDay" maxCallsPerDay (rlsMaxPerDay status)
  _ <- validateNonNegativeInt "callsThisSession" maxCallsPerSession (rlsCallsThisSession status)
  case rlsMaxPerSession status of
    Just maxSess -> do
      _ <- validatePositiveInt "maxPerSession" maxCallsPerSession maxSess
      pure ()
    Nothing -> pure ()
  case rlsBlockedReason status of
    Just reason -> do
      _ <- validateString "blockedReason" 500 reason
      pure ()
    Nothing -> pure ()
  _ <- validateDateTime "resetsAt" (rlsResetsAt status)
  _ <- validateString "resetsIn" 100 (rlsResetsIn status)
  validateStatusConstraints status
  Right status

--------------------------------------------------------------------------------
-- Stored Rate Limits
--------------------------------------------------------------------------------

-- | Rate limits stored in localStorage
data StoredRateLimits = StoredRateLimits
  { srlDate :: !Text  -- YYYY-MM-DD
  , srlCounts :: ![(Text, Int)]
  , srlLastReset :: !Text  -- ISO timestamp
  }
  deriving stock (Eq, Show, Generic)

-- | Validate StoredRateLimits
validateStoredRateLimits :: StoredRateLimits -> Either ValidationError StoredRateLimits
validateStoredRateLimits limits = do
  _ <- validateDate "date" (srlDate limits)
  _ <- validateDateTime "lastReset" (srlLastReset limits)
  if length (srlCounts limits) > maxRateLimitKeys
    then Left $ mkError "counts" $
      "must have at most " <> T.pack (show maxRateLimitKeys) <> " keys"
    else do
      mapM_ validateCount (srlCounts limits)
      Right limits
  where
    validateCount (key, count) = do
      _ <- validateString "counts.key" maxNameLength key
      _ <- validateNonNegativeInt "counts.value" maxCallsPerDay count
      pure ()

-- | Safe validation (returns Maybe)
safeValidateStoredRateLimits :: StoredRateLimits -> Maybe StoredRateLimits
safeValidateStoredRateLimits limits =
  case validateStoredRateLimits limits of
    Right l -> Just l
    Left _ -> Nothing
