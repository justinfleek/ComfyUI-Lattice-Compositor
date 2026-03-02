-- |
-- Module      : Lattice.State.Project
-- Description : Pure state management functions for project store
-- 
-- Migrated from ui/src/stores/projectStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Project
  ( -- Composition getters
    getOpenCompositions
  , getBreadcrumbPath
  , getActiveComposition
  , getActiveCompositionLayers
  -- Composition property getters
  , getWidth
  , getHeight
  , getFrameCount
  , getFps
  , getDuration
  , getBackgroundColor
  , getCurrentTime
  -- Project state queries
  , hasProject
  -- Asset utilities
  , findUsedAssetIds
  , getExtensionForAsset
  -- Project creation
  , createDefaultProject
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Maybe (maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Layer (LayerData(..))
import Lattice.Types.Project
  ( AssetReference(..)
  , AssetType(..)
  , Composition(..)
  , CompositionSettings(..)
  , LatticeProject(..)
  , ProjectMeta(..)
  , Layer(..)
  )
import Lattice.Types.LayerDataAsset
  ( ImageLayerData(..)
  , VideoData(..)
  , AudioLayerData(..)
  , DepthLayerData(..)
  , NormalLayerData(..)
  , NestedCompData(..)
  )
import Lattice.Types.LayerData3D
  ( ModelLayerData(..)
  , PointCloudLayerData(..)
  )
import Lattice.Types.LayerDataShapes
  ( ShapeLayerData(..)
  )

-- ============================================================================
-- COMPOSITION GETTERS
-- ============================================================================

-- | Get compositions that are currently open (in tabs)
-- Pure function: takes project and open composition IDs, returns compositions
getOpenCompositions ::
  LatticeProject ->
  [Text] ->
  [Composition]
getOpenCompositions project openIds =
  mapMaybe (\id_ -> HM.lookup id_ (latticeProjectCompositions project)) openIds
  where
    mapMaybe f = concatMap (maybeToList . f)

-- | Get breadcrumb path for nested composition navigation
-- Pure function: takes project and breadcrumb IDs, returns path with names
getBreadcrumbPath ::
  LatticeProject ->
  [Text] ->
  [(Text, Text)]  -- (id, name) pairs
getBreadcrumbPath project breadcrumbs =
  mapMaybe (\id_ -> do
    comp <- HM.lookup id_ (latticeProjectCompositions project)
    return (id_, compositionName comp)
  ) breadcrumbs
  where
    mapMaybe f = concatMap (maybeToList . f)

-- | Get active composition by ID
-- Pure function: takes project and active composition ID, returns composition or Nothing
getActiveComposition ::
  LatticeProject ->
  Text ->
  Maybe Composition
getActiveComposition project activeId =
  HM.lookup activeId (latticeProjectCompositions project)

-- | Get layers for active composition
-- Pure function: takes project and active composition ID, returns layers
getActiveCompositionLayers ::
  LatticeProject ->
  Text ->
  [Layer]
getActiveCompositionLayers project activeId =
  maybe [] compositionLayers (getActiveComposition project activeId)

-- ============================================================================
-- COMPOSITION PROPERTY GETTERS
-- ============================================================================

-- | Get composition width (default: 1024)
-- Pure function: takes project and active composition ID, returns width
getWidth ::
  LatticeProject ->
  Text ->
  Double
getWidth project activeId =
  maybe 1024.0 compositionSettingsWidth $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get composition height (default: 1024)
-- Pure function: takes project and active composition ID, returns height
getHeight ::
  LatticeProject ->
  Text ->
  Double
getHeight project activeId =
  maybe 1024.0 compositionSettingsHeight $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get composition frame count (default: 81)
-- Pure function: takes project and active composition ID, returns frame count
getFrameCount ::
  LatticeProject ->
  Text ->
  Double
getFrameCount project activeId =
  maybe 81.0 compositionSettingsFrameCount $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get composition FPS (default: 16)
-- Pure function: takes project and active composition ID, returns FPS
getFps ::
  LatticeProject ->
  Text ->
  Double
getFps project activeId =
  maybe 16.0 compositionSettingsFps $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get composition duration (default: 5)
-- Pure function: takes project and active composition ID, returns duration
getDuration ::
  LatticeProject ->
  Text ->
  Double
getDuration project activeId =
  maybe 5.0 compositionSettingsDuration $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get composition background color (default: "#050505")
-- Pure function: takes project and active composition ID, returns background color
getBackgroundColor ::
  LatticeProject ->
  Text ->
  Text
getBackgroundColor project activeId =
  maybe "#050505" compositionSettingsBackgroundColor $
    fmap compositionSettings (getActiveComposition project activeId)

-- | Get current time in seconds (currentFrame / fps)
-- Pure function: takes project and active composition ID, returns current time
getCurrentTime ::
  LatticeProject ->
  Text ->
  Double
getCurrentTime project activeId =
  case getActiveComposition project activeId of
    Nothing -> 0.0
    Just comp ->
      let fps = compositionSettingsFps (compositionSettings comp)
      in if fps > 0
        then compositionCurrentFrame comp / fps
        else 0.0

-- ============================================================================
-- PROJECT STATE QUERIES
-- ============================================================================

-- | Check if project has source image (hasProject)
-- Pure function: takes source image string, returns boolean
hasProject ::
  Maybe Text ->
  Bool
hasProject = maybe False (const True)

-- ============================================================================
-- ASSET UTILITIES
-- ============================================================================

-- | Find all asset IDs used in project
-- Pure function: traverses all compositions and layers, returns set of used asset IDs
findUsedAssetIds ::
  LatticeProject ->
  HashSet Text
findUsedAssetIds project =
  let
    -- Extract asset IDs from a layer's data
    extractAssetIds :: Layer -> HashSet Text
    extractAssetIds layer =
      case layerData layer of
        Nothing -> HS.empty
        Just (LayerDataImage d) ->
          let assetId = imageLayerDataAssetId d
          in if T.null assetId then HS.empty else HS.singleton assetId
        Just (LayerDataVideo d) ->
          maybe HS.empty HS.singleton (videoDataAssetId d)
        Just (LayerDataAudio d) ->
          maybe HS.empty HS.singleton (audioLayerDataAssetId d)
        Just (LayerDataDepth d) ->
          maybe HS.empty HS.singleton (depthLayerDataAssetId d)
        Just (LayerDataNormal d) ->
          maybe HS.empty HS.singleton (normalLayerDataAssetId d)
        -- NestedCompData uses compositionId, not assetId
        Just (LayerDataNestedComp _) -> HS.empty
        Just (LayerDataModel d) ->
          HS.singleton (modelLayerDataAssetId d)
        Just (LayerDataPointcloud d) ->
          HS.singleton (pointCloudLayerDataAssetId d)
        -- ShapeLayerData doesn't have assetId (vector-based)
        Just (LayerDataShape _) -> HS.empty
        -- TODO: Add more layer data types as needed (materials, textures, etc.)
        _ -> HS.empty
    
    -- Collect asset IDs from all layers in all compositions
    allAssetIds = HS.unions $
      concatMap (map extractAssetIds . compositionLayers) $
        HM.elems (latticeProjectCompositions project)
  in
    allAssetIds

-- | Get file extension for asset based on filename or type
-- Pure function: takes asset, returns extension string
getExtensionForAsset ::
  AssetReference ->
  Text
getExtensionForAsset asset =
  case assetReferenceFilename asset of
    Just filename ->
      let parts = T.splitOn "." filename
      in case reverse parts of
        [] -> defaultExtension
        (lastPart : remainingParts) -> T.toLower lastPart  -- Explicit pattern match
    Nothing -> defaultExtension
  where
    defaultExtension = case assetReferenceType asset of
      AssetTypeImage -> "png"
      AssetTypeVideo -> "mp4"
      AssetTypeAudio -> "mp3"
      AssetTypeModel -> "glb"
      AssetTypePointCloud -> "ply"
      AssetTypeDepthMap -> "png"
      AssetTypeTexture -> "png"
      AssetTypeMaterial -> "json"
      AssetTypeHDRI -> "hdr"
      AssetTypeSVG -> "svg"
      AssetTypeSprite -> "png"
      AssetTypeSpriteSheet -> "png"
      AssetTypeLUT -> "cube"
      _ -> "bin"

-- ============================================================================
-- PROJECT CREATION
-- ============================================================================

-- | Create default project structure
-- Pure function: creates a new project with default settings
createDefaultProject ::
  Text ->  -- Main composition ID
  LatticeProject
createDefaultProject mainCompId =
  LatticeProject
    { latticeProjectVersion = "1.0.0"
    , latticeProjectSchemaVersion = Just 1.0
    , latticeProjectMeta = ProjectMeta
        { projectMetaName = "Untitled Project"
        , projectMetaCreated = ""  -- Will be set by caller with current time
        , projectMetaModified = ""  -- Will be set by caller with current time
        , projectMetaAuthor = Nothing
        }
    , latticeProjectCompositions = HM.singleton mainCompId defaultComposition
    , latticeProjectMainCompositionId = mainCompId
    , latticeProjectComposition = defaultCompositionSettings
    , latticeProjectAssets = HM.empty
    , latticeProjectDataAssets = Nothing
    , latticeProjectLayers = []
    , latticeProjectCurrentFrame = 0.0
    , latticeProjectSnapConfig = Nothing
    , latticeProjectExportSettings = Nothing
    }
  where
    defaultCompositionSettings = CompositionSettings
      { compositionSettingsWidth = 1920.0
      , compositionSettingsHeight = 1080.0
      , compositionSettingsFrameCount = 81.0
      , compositionSettingsFps = 16.0
      , compositionSettingsDuration = 5.0625
      , compositionSettingsBackgroundColor = "#1a1a1a"
      , compositionSettingsAutoResizeToContent = False
      , compositionSettingsFrameBlendingEnabled = False
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
    defaultComposition = Composition
      { compositionId = mainCompId
      , compositionName = "Main Comp"
      , compositionSettings = defaultCompositionSettings
      , compositionLayers = []
      , compositionCurrentFrame = 0.0
      , compositionIsNestedComp = False
      , compositionParentCompositionId = Nothing
      , compositionWorkflowId = Nothing
      , compositionWorkflowInputs = Nothing
      , compositionWorkflowOutputs = Nothing
      , compositionTemplateConfig = Nothing
      , compositionGlobalLight = Nothing
      , compositionMarkers = Nothing
      }
