-- |
-- Module      : Lattice.Database.ModuleRegistry
-- Description : Database module registry for modular schema loading
-- 
-- Provides type-safe module registration and loading.
-- All operations are deterministic and total (no partial functions).
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Lattice.Database.ModuleRegistry
  ( ModuleId(..)
  , FeatureFlagName(..)
  , SqlFilePath(..)
  , TableName(..)
  , ModuleConfig(..)
  , ModuleRegistry(..)
  , ModuleLoadResult(..)
  , defaultRegistry
  , registerPluginModule
  , resolveLoadOrder
  , shouldLoadModule
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

-- | Module identifier
newtype ModuleId = ModuleId { unModuleId :: Text }
  deriving (Show, Eq, Ord)

-- | Feature flag name
newtype FeatureFlagName = FeatureFlagName { unFeatureFlagName :: Text }
  deriving (Show, Eq, Ord)

-- | SQL file path relative to scripts/database/
newtype SqlFilePath = SqlFilePath { unSqlFilePath :: Text }
  deriving (Show, Eq)

-- | Table name in database
newtype TableName = TableName { unTableName :: Text }
  deriving (Show, Eq)

-- | Module configuration
data ModuleConfig = ModuleConfig
  { configSqlFile :: SqlFilePath
  , configFeatureFlag :: Maybe FeatureFlagName  -- Nothing means always loaded (core)
  , configDependencies :: [ModuleId]
  , configTables :: [TableName]
  , configIsPlugin :: Bool
  }
  deriving (Show, Eq)

-- | Module registry
data ModuleRegistry = ModuleRegistry
  { registryModules :: Map ModuleId ModuleConfig
  }
  deriving (Show, Eq)

-- | Module load result
data ModuleLoadResult
  = LoadSuccess
  | LoadDependencyMissing ModuleId
  | LoadSqlFileNotFound SqlFilePath
  | LoadSqlError Text
  deriving (Show, Eq)

-- | Default module registry with core modules
defaultRegistry :: ModuleRegistry
defaultRegistry = ModuleRegistry $ Map.fromList
  [ (ModuleId "core", ModuleConfig
      { configSqlFile = SqlFilePath "00-core.sql"
      , configFeatureFlag = Nothing  -- Always loaded
      , configDependencies = []
      , configTables = 
          [ TableName "projects"
          , TableName "compositions"
          , TableName "layers"
          , TableName "keyframes"
          , TableName "expressions"
          , TableName "assets"
          , TableName "chat_messages"
          , TableName "feature_flags"
          , TableName "events"
          , TableName "metrics"
          , TableName "markers"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "effects", ModuleConfig
      { configSqlFile = SqlFilePath "modules/01-effects.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-effects-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "effects"
          , TableName "layer_styles"
          , TableName "layer_masks"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "animation", ModuleConfig
      { configSqlFile = SqlFilePath "modules/02-animation.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-animation-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "text_layers"
          , TableName "text_animators"
          , TableName "property_drivers"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "physics", ModuleConfig
      { configSqlFile = SqlFilePath "modules/03-physics.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-physics-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "physics_spaces"
          , TableName "physics_bodies"
          , TableName "physics_joints"
          , TableName "physics_rigid_bodies"
          , TableName "physics_cloth"
          , TableName "physics_ragdolls"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "particles", ModuleConfig
      { configSqlFile = SqlFilePath "modules/04-particles.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-particles-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "particle_systems"
          , TableName "particle_emitters"
          , TableName "particle_forces"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "audio", ModuleConfig
      { configSqlFile = SqlFilePath "modules/05-audio.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-audio-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "audio_tracks"
          , TableName "audio_analysis"
          , TableName "audio_reactivity"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "camera", ModuleConfig
      { configSqlFile = SqlFilePath "modules/06-camera.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-camera-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "cameras"
          , TableName "camera_paths"
          , TableName "camera_keyframes"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "export", ModuleConfig
      { configSqlFile = SqlFilePath "modules/07-export.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-export-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "export_jobs"
          , TableName "export_templates"
          , TableName "render_settings"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "ai", ModuleConfig
      { configSqlFile = SqlFilePath "modules/08-ai.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-ai-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "ai_models"
          , TableName "preprocessors"
          , TableName "segmentations"
          , TableName "vectorizations"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "templates", ModuleConfig
      { configSqlFile = SqlFilePath "modules/09-templates.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-templates-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "templates"
          , TableName "template_exposed_properties"
          , TableName "presets"
          ]
      , configIsPlugin = False
      })
  , (ModuleId "mesh-warp", ModuleConfig
      { configSqlFile = SqlFilePath "modules/10-mesh-warp.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-mesh-warp-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = 
          [ TableName "mesh_warp_pins"
          , TableName "mesh_warp_meshes"
          ]
      , configIsPlugin = False
      })
  ]

-- | Register a plugin module
registerPluginModule :: ModuleId -> ModuleConfig -> ModuleRegistry -> ModuleRegistry
registerPluginModule moduleId config (ModuleRegistry modules) =
  ModuleRegistry $ Map.insert moduleId config modules

-- | Resolve module load order based on dependencies (topological sort)
resolveLoadOrder :: ModuleRegistry -> [ModuleId] -> [ModuleId]
resolveLoadOrder (ModuleRegistry modules) moduleIds =
  let
    -- Build dependency graph
    deps :: Map ModuleId (Set ModuleId)
    deps = Map.fromList $ map (\(mid, cfg) -> (mid, Set.fromList $ configDependencies cfg)) $ Map.toList modules
    
    -- Topological sort
    visited :: Set ModuleId
    result :: [ModuleId]
    (visited, result) = topologicalSort deps moduleIds Set.empty []
  in
    reverse result
  where
    topologicalSort :: Map ModuleId (Set ModuleId) -> [ModuleId] -> Set ModuleId -> [ModuleId] -> (Set ModuleId, [ModuleId])
    topologicalSort _ [] visited result = (visited, result)
    topologicalSort deps (m:ms) visited result =
      if Set.member m visited then
        topologicalSort deps ms visited result
      else
        let
          moduleDeps = Map.findWithDefault Set.empty m deps
          (visited', result') = foldl (\acc dep -> topologicalSort deps [dep] (fst acc) (snd acc)) (visited, result) (Set.toList moduleDeps)
          visited'' = Set.insert m visited'
          result'' = m : result'
        in
          topologicalSort deps ms visited'' result''

-- | Check if module should be loaded based on feature flags
shouldLoadModule :: ModuleConfig -> [FeatureFlagName] -> Bool
shouldLoadModule config enabledFlags =
  case configFeatureFlag config of
    Nothing -> True  -- Core modules always load
    Just flag -> flag `elem` enabledFlags
