-- |
-- Module      : Lattice.State.Preset
-- Description : Pure state management functions for preset store
-- 
-- Migrated from ui/src/stores/presetStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Preset
  ( -- Query functions
    allPresets
  , filterByCategory
  , filterParticlePresets
  , filterPathEffectPresets
  , filterCameraShakePresets
  , filterCameraTrajectoryPresets
  , filterTextStylePresets
  , filterAnimationPresets
  , searchPresets
  , filterUserPresets
  , getPresetById
  , createPresetCollection
  -- Types
  , PresetCategory(..)
  , Preset(..)
  , PresetCollection(..)
  ) where

import Data.Aeson.Types ((.!=))
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.List (find, filter)
import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

-- ============================================================================
-- PRESET CATEGORY
-- ============================================================================

-- | Preset category type
data PresetCategory
  = PresetCategoryParticle
  | PresetCategoryEffect
  | PresetCategoryAnimation
  | PresetCategoryCameraShake
  | PresetCategoryCameraTrajectory
  | PresetCategoryPathEffect
  | PresetCategoryTextStyle
  | PresetCategoryColorPalette
  deriving (Eq, Show, Generic)

instance ToJSON PresetCategory where
  toJSON PresetCategoryParticle = "particle"
  toJSON PresetCategoryEffect = "effect"
  toJSON PresetCategoryAnimation = "animation"
  toJSON PresetCategoryCameraShake = "camera-shake"
  toJSON PresetCategoryCameraTrajectory = "camera-trajectory"
  toJSON PresetCategoryPathEffect = "path-effect"
  toJSON PresetCategoryTextStyle = "text-style"
  toJSON PresetCategoryColorPalette = "color-palette"

instance FromJSON PresetCategory where
  parseJSON = withText "PresetCategory" $ \s ->
    case s of
      "particle" -> return PresetCategoryParticle
      "effect" -> return PresetCategoryEffect
      "animation" -> return PresetCategoryAnimation
      "camera-shake" -> return PresetCategoryCameraShake
      "camera-trajectory" -> return PresetCategoryCameraTrajectory
      "path-effect" -> return PresetCategoryPathEffect
      "text-style" -> return PresetCategoryTextStyle
      "color-palette" -> return PresetCategoryColorPalette
      _ -> fail "Invalid PresetCategory"

-- ============================================================================
-- PRESET (Minimal type for pure queries)
-- ============================================================================

-- | Preset with minimal fields for pure query functions
-- Full type definition will be migrated in schema phase
data Preset = Preset
  { presetId :: Text
  , presetName :: Text
  , presetCategory :: PresetCategory
  , presetDescription :: Maybe Text
  , presetTags :: Maybe [Text]
  , presetIsBuiltIn :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON Preset where
  toJSON (Preset id_ name category mDesc mTags isBuiltIn) =
    let
      baseFields = ["id" .= id_, "name" .= name, "category" .= category, "isBuiltIn" .= isBuiltIn]
      withDescription = case mDesc of
        Just d -> ("description" .= d) : baseFields
        Nothing -> baseFields
      withTags = case mTags of
        Just ts -> ("tags" .= ts) : withDescription
        Nothing -> withDescription
    in object withTags

instance FromJSON Preset where
  parseJSON = withObject "Preset" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    category <- o .: "category"
    mDesc <- o .:? "description"
    mTags <- o .:? "tags"
    isBuiltIn <- o .:? "isBuiltIn" .!= False
    return (Preset id_ name category mDesc mTags isBuiltIn)

-- ============================================================================
-- PRESET COLLECTION
-- ============================================================================

-- | Preset collection for import/export
data PresetCollection = PresetCollection
  { presetCollectionVersion :: Int
  , presetCollectionPresets :: [Preset]
  , presetCollectionExportedAt :: Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON PresetCollection where
  toJSON (PresetCollection version presets exportedAt) =
    object
      [ "version" .= version
      , "presets" .= presets
      , "exportedAt" .= exportedAt
      ]

instance FromJSON PresetCollection where
  parseJSON = withObject "PresetCollection" $ \o -> do
    version <- o .: "version"
    presets <- o .: "presets"
    exportedAt <- o .: "exportedAt"
    return (PresetCollection version presets exportedAt)

-- ============================================================================
-- QUERY FUNCTIONS
-- ============================================================================

-- | Get all presets including built-ins
-- Pure function: takes built-in particle presets, built-in path effect presets, and user presets, returns combined list
allPresets :: [Preset] -> [Preset] -> [Preset] -> [Preset]
allPresets builtInParticle builtInPathEffect userPresets =
  builtInParticle ++ builtInPathEffect ++ userPresets

-- | Filter presets by category
-- Pure function: takes category and preset list, returns filtered list
filterByCategory :: PresetCategory -> [Preset] -> [Preset]
filterByCategory category presets =
  filter (\p -> presetCategory p == category) presets

-- | Filter particle presets
-- Pure function: takes preset list, returns particle presets
filterParticlePresets :: [Preset] -> [Preset]
filterParticlePresets = filterByCategory PresetCategoryParticle

-- | Filter path effect presets
-- Pure function: takes preset list, returns path effect presets
filterPathEffectPresets :: [Preset] -> [Preset]
filterPathEffectPresets = filterByCategory PresetCategoryPathEffect

-- | Filter camera shake presets
-- Pure function: takes preset list, returns camera shake presets
filterCameraShakePresets :: [Preset] -> [Preset]
filterCameraShakePresets = filterByCategory PresetCategoryCameraShake

-- | Filter camera trajectory presets
-- Pure function: takes preset list, returns camera trajectory presets
filterCameraTrajectoryPresets :: [Preset] -> [Preset]
filterCameraTrajectoryPresets = filterByCategory PresetCategoryCameraTrajectory

-- | Filter text style presets
-- Pure function: takes preset list, returns text style presets
filterTextStylePresets :: [Preset] -> [Preset]
filterTextStylePresets = filterByCategory PresetCategoryTextStyle

-- | Filter animation presets
-- Pure function: takes preset list, returns animation presets
filterAnimationPresets :: [Preset] -> [Preset]
filterAnimationPresets = filterByCategory PresetCategoryAnimation

-- | Search presets by name, description, or tags
-- Pure function: takes query string, optional category, and preset list, returns filtered list
searchPresets :: Text -> Maybe PresetCategory -> [Preset] -> [Preset]
searchPresets query mCategory presets =
  let
    queryLower = T.toLower query
    
    -- Filter by category first if provided
    categoryFiltered = case mCategory of
      Nothing -> presets
      Just cat -> filterByCategory cat presets
    
    -- Search in name, description, or tags
    matchesQuery :: Preset -> Bool
    matchesQuery preset =
      let
        nameMatches = T.isInfixOf queryLower (T.toLower (presetName preset))
        descMatches = case presetDescription preset of
          Nothing -> False
          Just desc -> T.isInfixOf queryLower (T.toLower desc)
        tagsMatch = case presetTags preset of
          Nothing -> False
          Just tags -> any (\tag -> T.isInfixOf queryLower (T.toLower tag)) tags
      in
        nameMatches || descMatches || tagsMatch
  in
    filter matchesQuery categoryFiltered

-- | Filter user-created presets (excludes built-ins)
-- Pure function: takes preset list, returns user presets
filterUserPresets :: [Preset] -> [Preset]
filterUserPresets presets = filter (\p -> not (presetIsBuiltIn p)) presets

-- | Get preset by ID
-- Pure function: takes preset ID and preset list, returns preset or Nothing
getPresetById :: Text -> [Preset] -> Maybe Preset
getPresetById id_ presets = find (\p -> presetId p == id_) presets

-- | Create preset collection for export
-- Pure function: takes version, optional preset IDs, all presets, and timestamp, returns collection
-- If IDs provided, filters to those presets; otherwise uses user presets
createPresetCollection :: Int -> Maybe [Text] -> [Preset] -> Int -> PresetCollection
createPresetCollection version mPresetIds allPresets_ exportedAt =
  let
    presetsToExport = case mPresetIds of
      Nothing -> filterUserPresets allPresets_
      Just ids -> filter (\p -> presetId p `elem` ids) allPresets_
  in
    PresetCollection version presetsToExport exportedAt
