{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.DragDrop.ProjectItemSchema
Description : Project item validation for drag-drop
Copyright   : (c) Lattice, 2026
License     : MIT

Validates project items for drag-drop operations.

Source: ui/src/schemas/dragdrop/project-item-schema.ts
-}

module Lattice.Schemas.DragDrop.ProjectItemSchema
  ( -- * Constants
    maxDimension
    -- * Project Item Type
  , ProjectItemType(..)
  , projectItemTypeFromText
  , projectItemTypeToText
    -- * Project Item
  , ProjectItem(..)
  , validateProjectItem
  , safeValidateProjectItem
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

projectItemTypeFromText :: Text -> Maybe ProjectItemType
projectItemTypeFromText "composition" = Just ItemComposition
projectItemTypeFromText "footage" = Just ItemFootage
projectItemTypeFromText "solid" = Just ItemSolid
projectItemTypeFromText "audio" = Just ItemAudio
projectItemTypeFromText "folder" = Just ItemFolder
projectItemTypeFromText _ = Nothing

projectItemTypeToText :: ProjectItemType -> Text
projectItemTypeToText ItemComposition = "composition"
projectItemTypeToText ItemFootage = "footage"
projectItemTypeToText ItemSolid = "solid"
projectItemTypeToText ItemAudio = "audio"
projectItemTypeToText ItemFolder = "folder"

--------------------------------------------------------------------------------
-- Project Item
--------------------------------------------------------------------------------

-- | Project item structure
data ProjectItem = ProjectItem
  { piId :: !Text
  , piName :: !Text
  , piType :: !ProjectItemType
  , piWidth :: !(Maybe Int)
  , piHeight :: !(Maybe Int)
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate ProjectItem
validateProjectItem :: ProjectItem -> Either ValidationError ProjectItem
validateProjectItem item = do
  _ <- validateEntityId "id" (piId item)
  _ <- validateNonEmptyString "name" maxNameLength (piName item)

  -- Validate width
  case piWidth item of
    Just w | w > maxDimension -> Left $ mkError "width" $
             "must be at most " <> show maxDimension
    _ -> Right ()

  -- Validate height
  case piHeight item of
    Just h | h > maxDimension -> Left $ mkError "height" $
             "must be at most " <> show maxDimension
    _ -> Right ()

  Right item

-- | Safe validation
safeValidateProjectItem :: ProjectItem -> Maybe ProjectItem
safeValidateProjectItem item =
  case validateProjectItem item of
    Right i -> Just i
    Left _ -> Nothing
