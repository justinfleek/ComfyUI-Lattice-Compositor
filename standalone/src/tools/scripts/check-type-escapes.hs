{-# LANGUAGE OverloadedStrings #-}

-- | Check Type Escapes
-- Check for type escapes across the codebase
--                                                                    // banned
module Main where

import Aleph.Script
import qualified Aleph.Script.Tools.Rg as Rg
import qualified System.FilePath as FP
import qualified Data.Text as T
import Data.Text (pack)

main :: IO ()
main = script $ do
  echo "Checking for type escapes..."
  
  scriptDir <- pwd
  let projectRoot = FP.takeDirectory (FP.takeDirectory scriptDir)
      uiSrcDir = projectRoot </> "ui" </> "src"
      srcDir = projectRoot </> "src"
      testDir = projectRoot </> "test"
  
  violations <- do
    -- TypeScript: Check for 'any' type
    echo "Checking TypeScript files..."
    (hasAny, anyMatches) <- checkPattern ":\\s*any\\b|:\\s*any\\[\\]|<any>" [uiSrcDir] (Just "ts") ["Binary", "./", "//", "test"]
    when hasAny $ do
      echo "❌ ERROR: Found 'any' type in TypeScript code"
      M.mapM_ echo anyMatches
    
    -- TypeScript: Check for 'as any' or 'as unknown as'
    (hasAsAny, asAnyMatches) <- checkPattern "as\\s+any|as\\s+unknown\\s+as" [uiSrcDir] (Just "ts") ["Binary", "./", "//"]
    when hasAsAny $ do
      echo "❌ ERROR: Found 'as any' or 'as unknown as' (type assertions) in TypeScript code"
      M.mapM_ echo asAnyMatches
    
    -- TypeScript: Check for @ts-ignore or @ts-expect-error
    (hasTsIgnore, tsIgnoreMatches) <- checkPattern "@ts-ignore|@ts-expect-error" [uiSrcDir] (Just "ts") ["Binary", "./"]
    when hasTsIgnore $ do
      echo "❌ ERROR: Found '@ts-ignore' or '@ts-expect-error' in TypeScript code"
      M.mapM_ echo tsIgnoreMatches
    
    -- PureScript: Check for unsafeCoerce
    echo "Checking PureScript files..."
    (hasUnsafeCoerce, unsafeMatches) <- checkPattern "unsafeCoerce" [srcDir, testDir] (Just "purs") ["Binary", "./"]
    when hasUnsafeCoerce $ do
      echo "❌ ERROR: Found 'unsafeCoerce' in PureScript code"
      M.mapM_ echo unsafeMatches
    
    -- Haskell: Check for unsafeCoerce
    echo "Checking Haskell files..."
    (hasUnsafeCoerceHs, unsafeMatchesHs) <- checkPattern "unsafeCoerce" [srcDir, testDir] (Just "hs") ["Binary", "./"]
    when hasUnsafeCoerceHs $ do
      echo "❌ ERROR: Found 'unsafeCoerce' in Haskell code"
      M.mapM_ echo unsafeMatchesHs
    
    return $ (if hasAny then 1 else 0) + 
             (if hasAsAny then 1 else 0) + 
             (if hasTsIgnore then 1 else 0) + 
             (if hasUnsafeCoerce then 1 else 0) + 
             (if hasUnsafeCoerceHs then 1 else 0)
  
  if violations == 0
    then do
      echo "✅ No type escapes found"
      exit 0
    else do
      echo $ "❌ Found " <> pack (show violations) <> " violation(s)"
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
