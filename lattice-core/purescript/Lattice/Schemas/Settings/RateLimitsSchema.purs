-- | Lattice.Schemas.Settings.RateLimitsSchema - Rate limits schema
-- |
-- | Validates rate limit data stored in localStorage/sessionStorage.
-- |
-- | Source: lattice-core/lean/Lattice/Schemas/Settings/RateLimitsSchema.lean

module Lattice.Schemas.Settings.RateLimitsSchema
  ( -- Constants
    maxCallsPerDay
  , maxCallsPerSession
  , maxVramCostMB
  , maxRateLimitKeys
    -- Rate Limit Config
  , RateLimitConfig
  , validateRateLimitConfig
    -- Rate Limit Status
  , RateLimitStatus
  , validateRateLimitStatus
    -- Stored Rate Limits
  , StoredRateLimits
  , validateStoredRateLimits
  , safeValidateStoredRateLimits
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))

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

maxVramCostMB :: Number
maxVramCostMB = 1000000.0  -- 1TB

maxRateLimitKeys :: Int
maxRateLimitKeys = 1000

--------------------------------------------------------------------------------
-- Rate Limit Config
--------------------------------------------------------------------------------

-- | Rate limit configuration for a tool
type RateLimitConfig =
  { toolName :: String
  , maxPerDay :: Int
  , maxPerSession :: Maybe Int
  , vramCostMB :: Maybe Number
  }

-- | Validate RateLimitConfig
validateRateLimitConfig :: RateLimitConfig -> Either ValidationError RateLimitConfig
validateRateLimitConfig config = do
  _ <- validateNonEmptyString "toolName" maxNameLength config.toolName
  _ <- validatePositiveInt "maxPerDay" maxCallsPerDay config.maxPerDay
  case config.maxPerSession of
    Just maxSess -> do
      _ <- validatePositiveInt "maxPerSession" maxCallsPerSession maxSess
      pure unit
    Nothing -> pure unit
  case config.vramCostMB of
    Just cost -> do
      _ <- validatePositiveFloat "vramCostMB" maxVramCostMB cost
      pure unit
    Nothing -> pure unit
  pure config

--------------------------------------------------------------------------------
-- Rate Limit Status
--------------------------------------------------------------------------------

-- | Rate limit status for a tool
type RateLimitStatus =
  { toolName :: String
  , callsToday :: Int
  , maxPerDay :: Int
  , callsThisSession :: Int
  , maxPerSession :: Maybe Int
  , canCall :: Boolean
  , blockedReason :: Maybe String
  , resetsAt :: String  -- ISO timestamp
  , resetsIn :: String  -- Human readable
  }

-- | Validate status constraints
validateStatusConstraints :: RateLimitStatus -> Either ValidationError Unit
validateStatusConstraints status
  | status.callsToday > status.maxPerDay =
      Left $ mkError "callsToday" "must be <= maxPerDay"
  | otherwise = case status.maxPerSession of
      Just maxSess | status.callsThisSession > maxSess ->
        Left $ mkError "callsThisSession" "must be <= maxPerSession"
      _ -> Right unit

-- | Validate RateLimitStatus
validateRateLimitStatus :: RateLimitStatus -> Either ValidationError RateLimitStatus
validateRateLimitStatus status = do
  _ <- validateNonEmptyString "toolName" maxNameLength status.toolName
  _ <- validateNonNegativeInt "callsToday" maxCallsPerDay status.callsToday
  _ <- validatePositiveInt "maxPerDay" maxCallsPerDay status.maxPerDay
  _ <- validateNonNegativeInt "callsThisSession" maxCallsPerSession status.callsThisSession
  case status.maxPerSession of
    Just maxSess -> do
      _ <- validatePositiveInt "maxPerSession" maxCallsPerSession maxSess
      pure unit
    Nothing -> pure unit
  case status.blockedReason of
    Just reason -> do
      _ <- validateString "blockedReason" 500 reason
      pure unit
    Nothing -> pure unit
  _ <- validateDateTime "resetsAt" status.resetsAt
  _ <- validateString "resetsIn" 100 status.resetsIn
  validateStatusConstraints status
  pure status

--------------------------------------------------------------------------------
-- Stored Rate Limits
--------------------------------------------------------------------------------

-- | Rate limits stored in localStorage
type StoredRateLimits =
  { date :: String  -- YYYY-MM-DD
  , counts :: Array (Tuple String Int)
  , lastReset :: String  -- ISO timestamp
  }

-- | Validate StoredRateLimits
validateStoredRateLimits :: StoredRateLimits -> Either ValidationError StoredRateLimits
validateStoredRateLimits limits = do
  _ <- validateDate "date" limits.date
  _ <- validateDateTime "lastReset" limits.lastReset
  if Array.length limits.counts > maxRateLimitKeys
    then Left $ mkError "counts" $
      "must have at most " <> show maxRateLimitKeys <> " keys"
    else do
      traverse_ validateCount limits.counts
      pure limits
  where
    validateCount (Tuple key count) = do
      _ <- validateString "counts.key" maxNameLength key
      _ <- validateNonNegativeInt "counts.value" maxCallsPerDay count
      pure unit

-- | Safe validation (returns Maybe)
safeValidateStoredRateLimits :: StoredRateLimits -> Maybe StoredRateLimits
safeValidateStoredRateLimits limits =
  case validateStoredRateLimits limits of
    Right l -> Just l
    Left _ -> Nothing
