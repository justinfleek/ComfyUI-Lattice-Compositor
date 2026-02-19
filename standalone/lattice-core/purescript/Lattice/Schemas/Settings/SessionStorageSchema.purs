-- | Lattice.Schemas.Settings.SessionStorageSchema - Session storage validation
-- |
-- | Validates data stored in sessionStorage.
-- |
-- | Source: lattice-core/lean/Lattice/Schemas/Settings/SessionStorageSchema.lean

module Lattice.Schemas.Settings.SessionStorageSchema
  ( -- Constants
    maxSessionCountKeys
  , maxCallsPerSession
    -- Session Counts
  , SessionCounts
  , validateSessionCounts
  , safeValidateSessionCounts
    -- Audit Session ID
  , validateUUID
  , validateAuditSessionId
  , safeValidateAuditSessionId
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as SCU
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateString, validateNonNegativeInt
  )

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxSessionCountKeys :: Int
maxSessionCountKeys = 1000

maxCallsPerSession :: Int
maxCallsPerSession = 100000

--------------------------------------------------------------------------------
-- Session Counts
--------------------------------------------------------------------------------

-- | Session counts stored in sessionStorage
type SessionCounts =
  { counts :: Array (Tuple String Int)
  }

-- | Validate SessionCounts
validateSessionCounts :: SessionCounts -> Either ValidationError SessionCounts
validateSessionCounts sc
  | Array.length sc.counts > maxSessionCountKeys =
      Left $ mkError "counts" $
        "must have at most " <> show maxSessionCountKeys <> " keys"
  | otherwise = do
      traverse_ validateCount sc.counts
      pure sc
  where
    validateCount (Tuple key count) = do
      _ <- validateString "counts.key" maxNameLength key
      _ <- validateNonNegativeInt "counts.value" maxCallsPerSession count
      pure unit

-- | Safe validation
safeValidateSessionCounts :: SessionCounts -> Maybe SessionCounts
safeValidateSessionCounts sc =
  case validateSessionCounts sc of
    Right c -> Just c
    Left _ -> Nothing

--------------------------------------------------------------------------------
-- Audit Session ID
--------------------------------------------------------------------------------

-- | Check if character is hex digit
isHexDigit :: Char -> Boolean
isHexDigit c =
  (c >= '0' && c <= '9') ||
  (c >= 'a' && c <= 'f') ||
  (c >= 'A' && c <= 'F')

-- | Validate UUID format
validateUUID :: String -> String -> Either ValidationError String
validateUUID field value
  | String.length value /= 36 = Left $ mkError field "must be valid UUID format"
  | String.take 1 (String.drop 8 value) /= "-" ||
    String.take 1 (String.drop 13 value) /= "-" ||
    String.take 1 (String.drop 18 value) /= "-" ||
    String.take 1 (String.drop 23 value) /= "-" =
      Left $ mkError field "must be valid UUID format"
  | not (Array.all isHexDigit (Array.filter (_ /= '-') (SCU.toCharArray value))) =
      Left $ mkError field "must be valid UUID format"
  | otherwise = Right value

-- | Validate audit session ID
validateAuditSessionId :: String -> Either ValidationError String
validateAuditSessionId = validateUUID "auditSessionId"

-- | Safe validation
safeValidateAuditSessionId :: String -> Maybe String
safeValidateAuditSessionId value =
  case validateAuditSessionId value of
    Right v -> Just v
    Left _ -> Nothing
