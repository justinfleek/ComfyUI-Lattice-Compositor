{-# LANGUAGE OverloadedStrings #-}

-- | SPA Development Server
-- Serves static files with SPA routing fallback (index.html for unmatched routes)
--                                                                    // spa-server
--
-- Usage: spa-server <public-dir> [port]
module Main where

import Aleph.Script
import System.Environment (getArgs)

-- | Default port for the SPA server
defaultPort :: Int
defaultPort = 8080

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> do
            putStrLn "Usage: spa-server <public-dir> [port]"
            putStrLn "       spa-server ../lattice-core/purescript/public 8080"
        [publicDir] -> runServer publicDir defaultPort
        [publicDir, portStr] -> case reads portStr of
            [(port, "")] -> runServer publicDir port
            _ -> putStrLn $ "Invalid port: " <> portStr
        _ -> putStrLn "Too many arguments"

-- | Run the SPA server using miniserve with --spa flag
runServer :: String -> Int -> IO ()
runServer publicDir port = script $ do
    echoErr $ ":: Starting SPA server on port " <> pack (show port)
    echoErr $ ":: Serving files from: " <> pack publicDir
    echoErr $ ":: SPA mode enabled (fallback to index.html)"
    echoErr ""
    
    -- Use miniserve with SPA mode
    -- miniserve is available in NixOS and supports --spa for SPA routing
    run_ "miniserve" 
        [ "--spa"                           -- SPA mode: serve index.html for 404s
        , "--index", "index.html"           -- Index file
        , "--port", pack (show port)        -- Port
        , "--interfaces", "127.0.0.1"       -- Bind to localhost only
        , pack publicDir                    -- Directory to serve
        ]
