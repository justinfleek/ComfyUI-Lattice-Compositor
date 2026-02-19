{-# LANGUAGE OverloadedStrings #-}

-- | Property-based tests for the Weyl Render API
-- Uses haskemathesis to generate valid requests from OpenAPI spec
-- and verify responses conform to the schema.
--
-- Run with: cabal test render-api-property
-- Or against live server: cabal run render-api-test -- --url https://sync.render.weyl.ai
module Main (main) where

import qualified Data.Map.Strict as Map
import Network.HTTP.Client (newManager)
import Network.HTTP.Client.TLS (tlsManagerSettings)
import System.Environment (getArgs, lookupEnv)
import Test.Hspec (hspec, describe, it, pendingWith)

import Haskemathesis.Auth.Config (AuthConfig (..), AuthValue (..))
import Haskemathesis.Check.Standard (allChecks)
import Haskemathesis.Config (TestConfig (..), defaultTestConfig, filterByTag)
import Haskemathesis.Execute.Http (executeHttp)
import Haskemathesis.Integration.Hspec (specForExecutor)
import Haskemathesis.OpenApi.Loader (loadOpenApiFile)
import Haskemathesis.OpenApi.Resolve (resolveOperations)

-- | Default spec path relative to project root
defaultSpecPath :: FilePath
defaultSpecPath = "specs/render.openapi.yaml"

-- | Parse command line arguments
parseArgs :: [String] -> (Maybe String, FilePath)
parseArgs args = go Nothing defaultSpecPath args
  where
    go url spec [] = (url, spec)
    go url spec ("--url":u:rest) = go (Just u) spec rest
    go url spec ("--spec":s:rest) = go url s rest
    go url spec (_:rest) = go url spec rest

main :: IO ()
main = do
    args <- getArgs
    let (mUrl, specPath) = parseArgs args
    
    -- Check for auth token in environment
    mToken <- lookupEnv "WEYL_API_TOKEN"
    
    specResult <- loadOpenApiFile specPath
    case specResult of
        Left err -> error $ "Failed to load OpenAPI spec: " <> show err
        Right spec -> case mUrl of
            Nothing -> do
                -- No URL provided - run spec validation only
                hspec $ describe "Render API OpenAPI Spec" $ do
                    it "loads and parses successfully" $ do
                        let ops = resolveOperations spec
                        length ops `shouldSatisfy` (> 0)
                    it "contains expected operations" $ do
                        pendingWith "Run with --url to test against live server"
            Just baseUrl -> do
                --                                                                       // url
                manager <- newManager tlsManagerSettings
                
                let authConfig = case mToken of
                        Nothing -> Nothing
                        Just token -> Just $ AuthConfig
                            (Map.fromList [("BearerAuth", AuthBearer token)])
                
                let config = defaultTestConfig
                        { tcAuthConfig = authConfig
                        , tcTestCount = 50  -- Start conservative
                        , tcOperationFilter = Just $ filterByTag "image"  -- Start with image ops
                        }
                
                hspec $ specForExecutor
                    (Just config)
                    allChecks
                    (executeHttp manager baseUrl)
                    (resolveOperations spec)

shouldSatisfy :: (Show a) => a -> (a -> Bool) -> IO ()
shouldSatisfy x p
    | p x = pure ()
    | otherwise = error $ "Expected predicate to hold for: " <> show x
