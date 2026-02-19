{-# LANGUAGE OverloadedStrings #-}

-- | Check Error Messages
-- Check that all error messages follow the explicit error pattern:
-- 1. What went wrong
-- 2. Where it happened
-- 3. How to fix it
module Main where

import Aleph.Script
import qualified Aleph.Script.Tools.Rg as Rg
import qualified System.FilePath as FP
import qualified Data.Text as T
import Data.Text (pack)

main :: IO ()
main = script $ do
  echo "🔍 Checking error messages for explicit format (What/Where/How to fix)..."
  
  scriptDir <- pwd
  let projectRoot = FP.takeDirectory (FP.takeDirectory scriptDir)
      leanDir = projectRoot </> "leancomfy" </> "lean"
      uiSrcDir = projectRoot </> "ui" </> "src"
      srcDir = projectRoot </> "src"
      testDir = projectRoot </> "test"
  
  errors <- do
    -- Lean 4: Check for throwError without "Fix:"
    echo ""
    echo "📋 Checking Lean 4 error messages..."
    (hasLeanErrors, leanMatches) <- checkPattern "throwError" [leanDir] (Just "lean") 
      ["Binary", "./", "Fix:", "fix:", ".lake"]
    when hasLeanErrors $ do
      echo "❌ ERROR: Found Lean error messages without 'Fix:' or 'fix:' directive"
      M.mapM_ echo leanMatches
    
    -- TypeScript: Check for throw new Error without "Fix:"
    echo ""
    echo "📋 Checking TypeScript error messages..."
    (hasTsErrors, tsMatches) <- checkPattern "throw new Error" [uiSrcDir] (Just "ts") 
      ["Binary", "./", "Fix:", "fix:", "How to fix", "how to fix"]
    when hasTsErrors $ do
      echo "❌ ERROR: Found TypeScript error messages without 'Fix:' directive"
      mapM_ echo tsMatches
    
    -- Haskell: Check for error calls without "Fix:"
    echo ""
    echo "📋 Checking Haskell error messages..."
    (hasHsErrors, hsMatches) <- checkPattern "error \"" [srcDir, testDir] (Just "hs") 
      ["Binary", "./", "Fix:", "fix:"]
    when hasHsErrors $ do
      echo "❌ ERROR: Found Haskell error messages without 'Fix:' directive"
      M.mapM_ echo hsMatches
    
    return $ (if hasLeanErrors then length leanMatches else 0) +
             (if hasTsErrors then length tsMatches else 0) +
             (if hasHsErrors then length hsMatches else 0)
  
  if errors == 0
    then do
      echo ""
      echo "✅ All error messages follow explicit format (What/Where/How to fix)"
      exit 0
    else do
      echo ""
      echo $ "❌ BANNED PATTERN DETECTED: " <> pack (show errors) <> " error messages without explicit format"
      exit 1

checkPattern :: Text -> [FilePath] -> Maybe Text -> [Text] -> Sh (Bool, [Text])
checkPattern pattern searchDirs fileType excludePatterns = do
  let rgOpts = Rg.defaults { Rg.lineNumber = True, Rg.type_ = fileType }
  result <- try $ Rg.rg rgOpts pattern searchDirs
  case result of
    Left _ -> return (False, [])
    Right output -> do
      let matches = T.lines output
          filtered = filter (\line -> 
            not (T.isPrefixOf "Binary" line) &&
            not (T.isPrefixOf "./" line) &&
            all (\exclude -> not (T.isInfixOf exclude line)) excludePatterns
          ) matches
      return (not (null filtered), filtered)
