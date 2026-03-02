{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.SessionStorageSchema
Description : Session storage validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates data stored in sessionStorage.

Source: lattice-core/lean/Lattice/Schemas/Settings/SessionStorageSchema.lean
-}

module Lattice.Schemas.Settings.SessionStorageSchema
  ( -- * Constants
    maxSessionCountKeys
  , maxCallsPerSession
    -- * Session Counts
  , SessionCounts(..)
  , validateSessionCounts
  , safeValidateSessionCounts
    -- * Audit Session ID
  , validateUUID
  , validateAuditSessionId
  , safeValidateAuditSessionId
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Char (isHexDigit)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateString, validateNonNegativeInt
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxSessionCountKeys :: Int
maxSessionCountKeys = 1000

maxCallsPerSession :: Int
maxCallsPerSession = 100000

-- ────────────────────────────────────────────────────────────────────────────
-- Session Counts
-- ────────────────────────────────────────────────────────────────────────────

-- | Session counts stored in sessionStorage
newtype SessionCounts = SessionCounts
  { sessionCounts :: [(Text, Int)]
  }
  deriving stock (Eq, Show, Generic)

-- | Validate SessionCounts
validateSessionCounts :: SessionCounts -> Either ValidationError SessionCounts
validateSessionCounts sc
  | length (sessionCounts sc) > maxSessionCountKeys =
      Left $ mkError "counts" $
        "must have at most " <> T.pack (show maxSessionCountKeys) <> " keys"
  | otherwise = do
      mapM_ validateCount (sessionCounts sc)
      Right sc
  where
    validateCount (key, count) = do
      _ <- validateString "counts.key" maxNameLength key
      _ <- validateNonNegativeInt "counts.value" maxCallsPerSession count
      pure ()

-- | Safe validation
safeValidateSessionCounts :: SessionCounts -> Maybe SessionCounts
safeValidateSessionCounts sc =
  case validateSessionCounts sc of
    Right c -> Just c
    Left _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Audit Session ID
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate UUID format
validateUUID :: Text -> Text -> Either ValidationError Text
validateUUID field value
  | T.length value /= 36 = Left $ mkError field "must be valid UUID format"
  | T.index value 8 /= '-' || T.index value 13 /= '-' ||
    T.index value 18 /= '-' || T.index value 23 /= '-' =
      Left $ mkError field "must be valid UUID format"
  | not (T.all isHexDigit (T.filter (/= '-') value)) =
      Left $ mkError field "must be valid UUID format"
  | otherwise = Right value

-- | Validate audit session ID
validateAuditSessionId :: Text -> Either ValidationError Text
validateAuditSessionId = validateUUID "auditSessionId"

-- | Safe validation
safeValidateAuditSessionId :: Text -> Maybe Text
safeValidateAuditSessionId value =
  case validateAuditSessionId value of
    Right v -> Just v
    Left _ -> Nothing
