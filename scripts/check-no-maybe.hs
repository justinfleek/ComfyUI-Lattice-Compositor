#!/usr/bin/env runhaskell
-- |
-- Script: check-no-maybe.hs
-- Purpose: CI/CD check to prevent Maybe/Nothing in Haskell code
-- 
--                                                                    // banned
--                                                                  // required
--
-- Usage: runhaskell scripts/check-no-maybe.hs

{-# LANGUAGE OverloadedStrings #-}

import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

-- | Check if a line contains banned Maybe/Nothing patterns
-- Excludes: imports, comments, type signatures in comments
checkLine :: Int -> T.Text -> [(Int, T.Text)]
checkLine lineNum line =
  let
    stripped = T.strip line
    isComment = T.isPrefixOf "--" stripped || T.isPrefixOf "{-" stripped
    isImport = T.isPrefixOf "import" stripped
    -- Allow Maybe in imports and type signatures (we're migrating gradually)
    -- But ban Maybe in data constructors, function bodies, pattern matches
    hasBannedPattern =
      (T.isInfixOf ":: Maybe" line && not isComment && not isImport) ||
      (T.isInfixOf "Maybe " line && not isComment && not isImport && not (T.isInfixOf "import" line)) ||
      (T.isInfixOf " Nothing" line && not isComment) ||
      (T.isInfixOf "(Nothing" line && not isComment) ||
      (T.isInfixOf "= Nothing" line && not isComment) ||
      (T.isInfixOf " Just " line && not isComment && not isImport) ||
      (T.isInfixOf "(Just " line && not isComment) ||
      (T.isInfixOf "= Just" line && not isComment) ||
      (T.isInfixOf "case" line && T.isInfixOf "Nothing" line && not isComment) ||
      (T.isInfixOf "case" line && T.isInfixOf "Just" line && not isComment)
  in
    if hasBannedPattern && not isComment && not isImport
    then [(lineNum, line)]
    else []

-- | Check a file for banned patterns
checkFile :: FilePath -> IO [(Int, T.Text)]
checkFile filePath = do
  content <- TIO.readFile filePath
  let lines = T.lines content
      violations = concatMap (uncurry checkLine) (zip [1..] lines)
  return violations

-- | Main function
main :: IO ()
main = do
  -- Get Haskell source files
  let haskellFiles = [
        "src/lattice/State",
        "src/lattice/Services", 
        "src/lattice/Types",
        "src/lattice/Utils"
      ]
  
  -- For now, check specific critical files
  --                                                                      // todo
  let criticalFiles = [
        "src/lattice/State/Animation/Types.hs",
        "src/lattice/State/Expression.hs",
        "src/lattice/State/Layer/Types.hs",
        "src/lattice/State/Project.hs"
      ]
  
  allViolations <- mapM checkFile criticalFiles
  
  let violations = concat allViolations
  
  if null violations
  then do
    putStrLn "✅ No Maybe/Nothing violations found in critical files"
    exitSuccess
  else do
    hPutStrLn stderr "❌ BANNED PATTERN DETECTED: Maybe/Nothing found"
    hPutStrLn stderr ""
    hPutStrLn stderr "PROTOCOL VIOLATION: All values must have explicit defaults"
    hPutStrLn stderr ""
    hPutStrLn stderr "Violations:"
    mapM_ (\(lineNum, line) -> 
      hPutStrLn stderr $ "  Line " ++ show lineNum ++ ": " ++ T.unpack line
    ) violations
    hPutStrLn stderr ""
    hPutStrLn stderr "Fix: Replace Maybe with explicit default + Bool flag"
    hPutStrLn stderr "Example:"
    hPutStrLn stderr "  ❌ Maybe AudioBuffer"
    hPutStrLn stderr "  ✅ AudioBuffer + Bool audioBufferLoaded"
    exitFailure
