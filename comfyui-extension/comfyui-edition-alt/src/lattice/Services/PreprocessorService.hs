-- |
-- Module      : Lattice.Services.PreprocessorService
-- Description : Pure preprocessor lookup and validation functions
-- 
-- Migrated from ui/src/services/preprocessorService.ts
-- Pure lookup functions for preprocessor discovery and configuration
-- Note: Registry and IO functions deferred
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PreprocessorService
  ( -- Types
    PreprocessorCategory(..)
  , PreprocessorInputType(..)
  , PreprocessorInput(..)
  , PreprocessorInfo(..)
  -- Lookup functions
  , getPreprocessorsByCategory
  , getPreprocessorsForType
  , getDefaultPreprocessor
  -- Category mapping
  , typeToCategories
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (Maybe(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Preprocessor category
data PreprocessorCategory
  = CategoryDepth
  | CategoryNormal
  | CategoryPose
  | CategoryEdge
  | CategoryLineart
  | CategoryScribble
  | CategorySegmentation
  | CategoryVideo
  | CategoryOther
  deriving (Eq, Show, Ord)

-- | Preprocessor input type
data PreprocessorInputType
  = InputCombo
  | InputInt
  | InputFloat
  | InputBool
  | InputString
  deriving (Eq, Show)

-- | Preprocessor input configuration
data PreprocessorInput = PreprocessorInput
  { inputType :: PreprocessorInputType
  , inputDefault :: Either Text (Either Double Bool)  -- string | number | boolean
  , inputMin :: Maybe Double
  , inputMax :: Maybe Double
  , inputStep :: Maybe Double
  , inputOptions :: Maybe [Text]
  }
  deriving (Eq, Show)

-- | Preprocessor information
data PreprocessorInfo = PreprocessorInfo
  { preprocessorId :: Text
  , preprocessorDisplayName :: Text
  , preprocessorDescription :: Text
  , preprocessorCategory :: PreprocessorCategory
  , preprocessorInputs :: Map Text PreprocessorInput
  , preprocessorSource :: Maybe Text
  , preprocessorIsVideo :: Maybe Bool
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Map generation type to preprocessor categories
typeToCategories :: Text -> [PreprocessorCategory]
typeToCategories generationType = case generationType of
  "depth" -> [CategoryDepth]
  "normal" -> [CategoryNormal]
  "edge" -> [CategoryEdge, CategoryLineart, CategoryScribble]
  "segment" -> [CategorySegmentation]
  "pose" -> [CategoryPose, CategoryVideo]
  "video" -> [CategoryVideo, CategoryNormal]
  "custom" ->
    [ CategoryDepth
    , CategoryNormal
    , CategoryPose
    , CategoryEdge
    , CategoryLineart
    , CategoryScribble
    , CategorySegmentation
    , CategoryVideo
    , CategoryOther
    ]
  _ ->  -- Default to custom (all categories)
    [ CategoryDepth
    , CategoryNormal
    , CategoryPose
    , CategoryEdge
    , CategoryLineart
    , CategoryScribble
    , CategorySegmentation
    , CategoryVideo
    , CategoryOther
    ]

-- | Default preprocessors for each generation type
defaultPreprocessors :: Map Text Text
defaultPreprocessors = Map.fromList
  [ ("depth", "depth_anything_v2")
  , ("normal", "normal_bae")
  , ("edge", "canny")
  , ("segment", "oneformer_ade20k")
  , ("pose", "dwpose")
  , ("video", "normalcrafter")
  , ("custom", "depth_anything_v2")
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // lookup // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get preprocessors matching a category
-- Pure function: same inputs → same outputs
-- Note: Requires PREPROCESSOR_REGISTRY to be passed as parameter
getPreprocessorsByCategory ::
  PreprocessorCategory -> Map Text PreprocessorInfo -> [PreprocessorInfo]
getPreprocessorsByCategory category registry =
  filter (\info -> preprocessorCategory info == category) (Map.elems registry)

-- | Get preprocessors matching a generation type
-- Pure function: same inputs → same outputs
-- Note: Requires PREPROCESSOR_REGISTRY to be passed as parameter
getPreprocessorsForType ::
  Text -> Map Text PreprocessorInfo -> [PreprocessorInfo]
getPreprocessorsForType generationType registry =
  let categories = typeToCategories generationType
      allPreprocessors = Map.elems registry
  in filter (\info -> preprocessorCategory info `elem` categories) allPreprocessors

-- | Get default preprocessor for a generation type
-- Pure function: same inputs → same outputs
getDefaultPreprocessor :: Text -> Maybe Text
getDefaultPreprocessor generationType = Map.lookup generationType defaultPreprocessors
