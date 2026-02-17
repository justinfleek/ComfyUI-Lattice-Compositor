-- | Lattice.Schemas.DragDrop.ProjectItemSchema - Project item validation
-- |
-- | Validates project items for drag-drop operations.
-- |
-- | Source: ui/src/schemas/dragdrop/project-item-schema.ts

module Lattice.Schemas.DragDrop.ProjectItemSchema
  ( -- Constants
    maxDimension
    -- Project Item Type
  , ProjectItemType(..)
  , projectItemTypeFromString
  , projectItemTypeToString
    -- Project Item
  , ProjectItem
  , validateProjectItem
  , safeValidateProjectItem
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError
  , maxNameLength
  , validateEntityId, validateNonEmptyString
  )

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

--------------------------------------------------------------------------------
-- Project Item Type
--------------------------------------------------------------------------------

-- | Project item type options
data ProjectItemType
  = ItemComposition
  | ItemFootage
  | ItemSolid
  | ItemAudio
  | ItemFolder

derive instance Eq ProjectItemType
derive instance Generic ProjectItemType _

instance Show ProjectItemType where
  show = genericShow

projectItemTypeFromString :: String -> Maybe ProjectItemType
projectItemTypeFromString = case _ of
  "composition" -> Just ItemComposition
  "footage" -> Just ItemFootage
  "solid" -> Just ItemSolid
  "audio" -> Just ItemAudio
  "folder" -> Just ItemFolder
  _ -> Nothing

projectItemTypeToString :: ProjectItemType -> String
projectItemTypeToString = case _ of
  ItemComposition -> "composition"
  ItemFootage -> "footage"
  ItemSolid -> "solid"
  ItemAudio -> "audio"
  ItemFolder -> "folder"

--------------------------------------------------------------------------------
-- Project Item
--------------------------------------------------------------------------------

-- | Project item structure
type ProjectItem =
  { id :: String
  , name :: String
  , itemType :: ProjectItemType
  , width :: Maybe Int
  , height :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate ProjectItem
validateProjectItem :: ProjectItem -> Either ValidationError ProjectItem
validateProjectItem item = do
  _ <- validateEntityId "id" item.id
  _ <- validateNonEmptyString "name" maxNameLength item.name

  -- Validate width
  case item.width of
    Just w | w > maxDimension -> Left $ mkError "width" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  -- Validate height
  case item.height of
    Just h | h > maxDimension -> Left $ mkError "height" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  pure item

-- | Safe validation
safeValidateProjectItem :: ProjectItem -> Maybe ProjectItem
safeValidateProjectItem item =
  case validateProjectItem item of
    Right i -> Just i
    Left _ -> Nothing
