{-# LANGUAGE OverloadedStrings #-}

-- | Setup DuckDB Database
-- Creates database directory and initializes schema
module Main where

import Aleph.Script
import qualified System.FilePath as FP

main :: IO ()
main = script $ do
  echo "Setting up DuckDB database..."
  
  -- Get project root (parent of scripts directory)
  script-dir <- pwd
  let project-root = FP.takeDirectory (FP.takeDirectory script-dir)
      db-dir = project-root </> ".lattice"
      db-path = db-dir </> "database.duckdb"
  
  -- Create database directory
  mkdirP db-dir
  
  -- Check if DuckDB CLI is available
  duckdb-cli <- which "duckdb"
  
  case duckdb-cli of
    Just duckdb-exe -> do
      echo "Using DuckDB CLI..."
      let init-sql = project-root </> "scripts" </> "init-database.sql"
          flags-sql = project-root </> "scripts" </> "init-feature-flags.sql"
      
      -- Run duckdb with SQL file input using bash redirection
      bash_ $ "duckdb " <> toText db-path <> " < " <> toText init-sql
      bash_ $ "duckdb " <> toText db-path <> " < " <> toText flags-sql
      echo "✅ Database initialized successfully"
    
    Nothing -> do
      -- Check if Node.js is available and duckdb package exists
      node-exe <- which "node"
      duckdb-node-modules <- test_d (project-root </> "node_modules" </> "duckdb")
      
      case (node-exe, duckdb-node-modules) of
        (Just node, True) -> do
          echo "Using Node.js DuckDB package..."
          cd (fromText $ pack project-root)
          
          -- Try to rebuild duckdb native bindings
          rebuild-result <- try $ run_ "npm" ["rebuild", "duckdb"]
          
          case rebuild-result of
            Left _ -> do
              echoErr "⚠️  DuckDB native bindings need to be rebuilt"
              echoErr "Run: npm rebuild duckdb"
              exit 1
            Right _ -> do
              let init-js = project-root </> "scripts" </> "init-database.js"
              run_ node [toText init-js]
              echo "✅ Database initialized successfully"
        
        _ -> do
          echoErr "❌ DuckDB not found. Install DuckDB CLI or Node.js package:"
          echoErr "  - CLI: https://duckdb.org/docs/installation/"
          echoErr "  - Node: npm install duckdb"
          exit 1
  
  echo $ "Database ready at: " <> toText db-path
