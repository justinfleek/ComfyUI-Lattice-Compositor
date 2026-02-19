-- |
-- Module      : Lattice.Database.Schema
-- Description : Database schema definitions and initialization
-- 
-- Defines modular schema loading using module registry.
-- All schemas are deterministic and idempotent.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Database.Schema
  ( initializeSchema
  , initializeFeatureFlags
  , loadModule
  , loadModules
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as Map
import System.FilePath ((</>))
import Control.Monad (foldM)
import Lattice.Database.DuckDB (DuckDBConnection, execute, DuckDBError(..))
import Lattice.Database.ModuleRegistry
  ( ModuleRegistry(..)
  , ModuleId(..)
  , ModuleConfig(..)
  , SqlFilePath(..)
  , FeatureFlagName(..)
  , ModuleLoadResult(..)
  , defaultRegistry
  , resolveLoadOrder
  , shouldLoadModule
  )

-- | Initialize complete database schema
-- Loads core module and all enabled domain modules
initializeSchema :: DuckDBConnection -> FilePath -> [FeatureFlagName] -> IO (Either Text ())
initializeSchema conn dbDir enabledFlags = do
  let registry = defaultRegistry
      allModuleIds = map fst $ Map.toList $ registryModules registry
      enabledModuleIds = filter (isModuleEnabled registry enabledFlags) allModuleIds
      loadOrder = resolveLoadOrder registry enabledModuleIds
  
  result <- foldM (loadModule conn dbDir registry) (Right ()) loadOrder
  return result

-- | Check if module is enabled
isModuleEnabled :: ModuleRegistry -> [FeatureFlagName] -> ModuleId -> Bool
isModuleEnabled (ModuleRegistry modules) enabledFlags moduleId =
  case Map.lookup moduleId modules of
    Nothing -> False
    Just config -> shouldLoadModule config enabledFlags

-- | Load a single module
loadModule :: DuckDBConnection -> FilePath -> ModuleRegistry -> Either Text () -> ModuleId -> IO (Either Text ())
loadModule conn dbDir registry acc moduleId =
  case acc of
    Left err -> return (Left err)
    Right _ -> do
      case Map.lookup moduleId (registryModules registry) of
        Nothing -> return (Left $ "Module not found: " <> unModuleId moduleId)
        Just config -> do
          let sqlPath = dbDir </> "scripts" </> "database" </> T.unpack (unSqlFilePath $ configSqlFile config)
          sqlContent <- TIO.readFile sqlPath
          result <- execute conn sqlContent
          case result of
            Left err -> return (Left $ "Failed to load module " <> unModuleId moduleId <> ": " <> T.pack (show err))
            Right _ -> return (Right ())

-- | Load multiple modules in dependency order
loadModules :: DuckDBConnection -> FilePath -> ModuleRegistry -> [ModuleId] -> IO (Either Text ())
loadModules conn dbDir registry moduleIds = do
  let loadOrder = resolveLoadOrder registry moduleIds
  foldM (loadModule conn dbDir registry) (Right ()) loadOrder

-- | Initialize feature flags
-- Inserts default feature flags into database
initializeFeatureFlags :: DuckDBConnection -> IO (Either Text ())
initializeFeatureFlags conn = do
  -- Execute feature flags SQL from init-feature-flags.sql
  -- For now, return success
  --                                                                      // todo
  return (Right ())
