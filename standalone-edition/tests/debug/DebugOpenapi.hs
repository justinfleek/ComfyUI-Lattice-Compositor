{-# LANGUAGE OverloadedStrings #-}
module Main where

import Haskemathesis.OpenApi.Loader
import Haskemathesis.OpenApi.Resolve
import Haskemathesis.OpenApi.Types

main :: IO ()
main = do
    spec <- loadOpenApiFile "specs/render.openapi.yaml"
    case spec of
        Left err -> print err
        Right s -> do
            let ops = resolveOperations s
            mapM_ printOp ops
  where
    printOp op = putStrLn $ "Op: " ++ show (roOperationId op) 
                          ++ " hasBody: " ++ show (fmap rbContentType (roRequestBody op))
