{-# LANGUAGE OverloadedStrings #-}

-- | Property-based tests for the Weyl Render API
-- Uses haskemathesis to generate valid requests from OpenAPI spec
-- and verify responses conform to the schema.
--
-- Run with: cabal test render-api-property
-- Or against live server: RENDER_API_URL=http://localhost:8081 cabal test render-api-property
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Network.HTTP.Client (newManager)
import Network.HTTP.Client.TLS (tlsManagerSettings)
import System.Environment (lookupEnv)
import Test.Hspec (hspec, describe, it, pendingWith)

import Haskemathesis.Auth.Config (AuthConfig (..), AuthValue (..))
import Haskemathesis.Config (TestConfig (..), defaultTestConfig)
import Haskemathesis.Execute.Http (executeHttp)
import Haskemathesis.Integration.Hspec (specForExecutorWithConfig)
import Haskemathesis.OpenApi.Loader (loadOpenApiFile)
import Haskemathesis.OpenApi.Resolve (resolveOperations)

-- | Default spec path relative to project root
defaultSpecPath :: FilePath
defaultSpecPath = "specs/render.openapi.yaml"

main :: IO ()
main = do
    -- Get URL and auth from environment variables
    mUrl <- lookupEnv "RENDER_API_URL"
    mToken <- lookupEnv "WEYL_API_TOKEN"
    
    specResult <- loadOpenApiFile defaultSpecPath
    case specResult of
        Left err -> Prelude.error $ "Failed to load OpenAPI spec: " <> show err
        Right spec -> case mUrl of
            Nothing -> do
                -- No URL provided - run spec validation only
                hspec $ describe "Render API OpenAPI Spec" $ do
                    it "loads and parses successfully" $ do
                        let ops = resolveOperations spec
                        length ops `shouldSatisfy` (> 0)
                    it "contains expected operations" $ do
                        pendingWith "Set RENDER_API_URL to test against live server"
            Just baseUrl -> do
                manager <- newManager tlsManagerSettings
                
                let authConfig = case mToken of
                        Nothing -> Nothing
                        Just token -> Just $ AuthConfig
                            (Map.fromList [("BearerAuth", AuthBearer (T.pack token))])
                
                let config = defaultTestConfig
                        { tcAuthConfig = authConfig
                        , tcPropertyCount = 50  -- Start conservative
                        -- Test all operations (no filter)
                        }
                
                hspec $ specForExecutorWithConfig
                    spec
                    config
                    (executeHttp manager (T.pack baseUrl))
                    (resolveOperations spec)

shouldSatisfy :: (Show a) => a -> (a -> Bool) -> IO ()
shouldSatisfy x p
    | p x = pure ()
    | otherwise = Prelude.error $ "Expected predicate to hold for: " <> show x
