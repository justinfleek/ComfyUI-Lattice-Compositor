-- | Lattice.Schemas.Settings.RecentProjectsSchema - Recent projects validation
-- |
-- | Validates recent projects list stored in localStorage.
-- |
-- | Source: lattice-core/lean/Lattice/Schemas/Settings/RecentProjectsSchema.lean

module Lattice.Schemas.Settings.RecentProjectsSchema
  ( -- Constants
    maxRecentProjects
  , maxThumbnailSize
  , maxTimestamp
    -- Recent Project
  , RecentProject
  , validateRecentProject
  , safeValidateRecentProject
    -- Recent Projects Array
  , validateRecentProjects
  , safeValidateRecentProjects
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse_)

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
maxTimestamp = 2147483647  -- Max JS int for timestamp

--------------------------------------------------------------------------------
-- Recent Project
--------------------------------------------------------------------------------

-- | A recent project entry
type RecentProject =
  { id :: String
  , name :: String
  , thumbnail :: Maybe String
  , modifiedAt :: Int
  }

-- | Validate RecentProject
validateRecentProject :: RecentProject -> Either ValidationError RecentProject
validateRecentProject rp = do
  _ <- validateEntityId "id" rp.id
  _ <- validateNonEmptyString "name" maxNameLength rp.name
  case rp.thumbnail of
    Just thumb | String.length thumb > maxThumbnailSize ->
      Left $ mkError "thumbnail" $
        "must be at most " <> show maxThumbnailSize <> " characters"
    _ -> pure unit
  _ <- validateNonNegativeInt "modifiedAt" maxTimestamp rp.modifiedAt
  pure rp

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
validateRecentProjects :: Array RecentProject -> Either ValidationError (Array RecentProject)
validateRecentProjects projects
  | Array.length projects > maxRecentProjects =
      Left $ mkError "recentProjects" $
        "must have at most " <> show maxRecentProjects <> " projects"
  | otherwise = do
      traverse_ validateRecentProject projects
      pure projects

-- | Safe validation
safeValidateRecentProjects :: Array RecentProject -> Maybe (Array RecentProject)
safeValidateRecentProjects projects =
  case validateRecentProjects projects of
    Right ps -> Just ps
    Left _ -> Nothing
