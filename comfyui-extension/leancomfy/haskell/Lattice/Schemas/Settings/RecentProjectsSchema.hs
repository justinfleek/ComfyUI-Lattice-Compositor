{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.RecentProjectsSchema
Description : Recent projects validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates recent projects list stored in localStorage.

Source: leancomfy/lean/Lattice/Schemas/Settings/RecentProjectsSchema.lean
-}

module Lattice.Schemas.Settings.RecentProjectsSchema
  ( -- * Constants
    maxRecentProjects
  , maxThumbnailSize
  , maxTimestamp
    -- * Recent Project
  , RecentProject(..)
  , validateRecentProject
  , safeValidateRecentProject
    -- * Recent Projects Array
  , validateRecentProjects
  , safeValidateRecentProjects
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (Maybe(..))

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateEntityId, validateNonEmptyString, validateNonNegativeInt
  )

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxRecentProjects :: Int
maxRecentProjects = 100

maxThumbnailSize :: Int
maxThumbnailSize = 10 * 1024 * 1024  -- 10MB

maxTimestamp :: Int
maxTimestamp = 2147483647000  -- Year 2038

--------------------------------------------------------------------------------
-- Recent Project
--------------------------------------------------------------------------------

-- | A recent project entry
data RecentProject = RecentProject
  { rpId :: !Text
  , rpName :: !Text
  , rpThumbnail :: !(Maybe Text)
  , rpModifiedAt :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Validate RecentProject
validateRecentProject :: RecentProject -> Either ValidationError RecentProject
validateRecentProject rp = do
  _ <- validateEntityId "id" (rpId rp)
  _ <- validateNonEmptyString "name" maxNameLength (rpName rp)
  case rpThumbnail rp of
    Just thumb | T.length thumb > maxThumbnailSize ->
      Left $ mkError "thumbnail" $
        "must be at most " <> T.pack (show maxThumbnailSize) <> " characters"
    _ -> pure ()
  _ <- validateNonNegativeInt "modifiedAt" maxTimestamp (rpModifiedAt rp)
  Right rp

-- | Safe validation
safeValidateRecentProject :: RecentProject -> Maybe RecentProject
safeValidateRecentProject rp =
  case validateRecentProject rp of
    Right p -> Just p
    Left _ -> Nothing

--------------------------------------------------------------------------------
-- Recent Projects Array
--------------------------------------------------------------------------------

-- | Validate array of recent projects
validateRecentProjects :: [RecentProject] -> Either ValidationError [RecentProject]
validateRecentProjects projects
  | length projects > maxRecentProjects =
      Left $ mkError "recentProjects" $
        "must have at most " <> T.pack (show maxRecentProjects) <> " projects"
  | otherwise = do
      mapM_ validateRecentProject projects
      Right projects

-- | Safe validation
safeValidateRecentProjects :: [RecentProject] -> Maybe [RecentProject]
safeValidateRecentProjects projects =
  case validateRecentProjects projects of
    Right ps -> Just ps
    Left _ -> Nothing
