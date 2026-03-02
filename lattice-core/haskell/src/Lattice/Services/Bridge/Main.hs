{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.Bridge.Main
Description : Main entry point for Lattice WebSocket bridge server
Copyright   : (c) Lattice, 2026
License     : MIT

Starts the WebSocket server that bridges PureScript UI to Haskell backend.
Initializes all handlers:
- Render (Hasktorch GPU)
- Storage (DuckDB)
- Export (FFmpeg)
- Math (exact bitwise)
-}

module Lattice.Services.Bridge.Main
  ( main
  , runBridge
  , BridgeConfig(..)
  , defaultBridgeConfig
  ) where

import Control.Exception (bracket)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment (getArgs, lookupEnv)
import System.FilePath ((</>))

import Lattice.Services.Bridge.Protocol
import Lattice.Services.Bridge.Server
import Lattice.Services.Bridge.Handlers.Math (mathHandler)
import Lattice.Services.Bridge.Handlers.Render (RenderContext, initRender, disposeRender, renderHandler)
import Lattice.Services.Bridge.Handlers.Storage (StorageContext, initStorage, closeStorage, storageHandler)
import Lattice.Services.Bridge.Handlers.Export (ExportContext, initExport, disposeExport, exportHandler)

-- ────────────────────────────────────────────────────────────────────────────
-- Configuration
-- ────────────────────────────────────────────────────────────────────────────

data BridgeConfig = BridgeConfig
  { bcHost :: !Text
  , bcPort :: !Int
  , bcDbPath :: !FilePath
  , bcTempDir :: !FilePath
  } deriving (Eq, Show)

defaultBridgeConfig :: BridgeConfig
defaultBridgeConfig = BridgeConfig
  { bcHost = "127.0.0.1"
  , bcPort = 9876
  , bcDbPath = "lattice.duckdb"
  , bcTempDir = "/tmp/lattice-export"
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Main
-- ────────────────────────────────────────────────────────────────────────────

main :: IO ()
main = do
  args <- getArgs
  
  -- Parse config from args/env
  host <- maybe "127.0.0.1" T.pack <$> lookupEnv "LATTICE_HOST"
  port <- maybe 9876 read <$> lookupEnv "LATTICE_PORT"
  dbPath <- maybe "lattice.duckdb" id <$> lookupEnv "LATTICE_DB"
  tempDir <- maybe "/tmp/lattice-export" id <$> lookupEnv "LATTICE_TEMP"
  
  let config = BridgeConfig
        { bcHost = host
        , bcPort = port
        , bcDbPath = dbPath
        , bcTempDir = tempDir
        }
  
  runBridge config

-- | Run the bridge server
runBridge :: BridgeConfig -> IO ()
runBridge config = do
  TIO.putStrLn "Initializing Lattice Bridge..."
  TIO.putStrLn $ "  Host: " <> bcHost config
  TIO.putStrLn $ "  Port: " <> T.pack (show $ bcPort config)
  TIO.putStrLn $ "  Database: " <> T.pack (bcDbPath config)
  TIO.putStrLn $ "  Temp Dir: " <> T.pack (bcTempDir config)
  
  -- Initialize all contexts
  bracket initContexts disposeContexts $ \(renderCtx, storageCtx, exportCtx) -> do
    TIO.putStrLn "All handlers initialized."
    
    -- Build handlers
    let handlers = Handlers
          { hRender = renderHandler renderCtx
          , hStorage = storageHandler storageCtx
          , hExport = exportHandler exportCtx
          , hMath = mathHandler
          }
    
    -- Build server config
    let serverConfig = ServerConfig
          { scHost = bcHost config
          , scPort = bcPort config
          , scPingInterval = 30
          , scMaxConnections = 100
          }
    
    -- Run server
    TIO.putStrLn "Starting WebSocket server..."
    runServer serverConfig handlers

-- ────────────────────────────────────────────────────────────────────────────
-- Context Management
-- ────────────────────────────────────────────────────────────────────────────

initContexts :: IO (RenderContext, StorageContext, ExportContext)
initContexts = do
  TIO.putStrLn "  Initializing Render (Hasktorch GPU)..."
  renderCtx <- initRender
  
  TIO.putStrLn "  Initializing Storage (DuckDB)..."
  storageCtx <- initStorage "lattice.duckdb"
  
  TIO.putStrLn "  Initializing Export (FFmpeg)..."
  exportCtx <- initExport "/tmp/lattice-export"
  
  pure (renderCtx, storageCtx, exportCtx)

disposeContexts :: (RenderContext, StorageContext, ExportContext) -> IO ()
disposeContexts (renderCtx, storageCtx, exportCtx) = do
  TIO.putStrLn "Shutting down..."
  disposeRender renderCtx
  closeStorage storageCtx
  disposeExport exportCtx
  TIO.putStrLn "Goodbye."
