{-# LANGUAGE OverloadedStrings #-}

-- | Check Banned Patterns
-- Check for banned patterns across the codebase
-- BANNED: undefined, error, head/tail, unsafeCoerce, ??/|| defaults, ! assertions
--
-- Exit code: 0 if no violations, 1 if violations found
module Main where

import Aleph.Script
import qualified Aleph.Script.Tools.Rg as Rg
import qualified System.FilePath as FP
import qualified Data.Text as T
import Data.Text (pack)

-- | Check pattern in files, excluding certain paths
checkPattern :: Text -> [FilePath] -> Maybe Text -> [Text] -> Sh (Bool, [Text])
checkPattern pattern searchDirs fileType excludePatterns = do
  let rgOpts = Rg.defaults
        { Rg.lineNumber = True
        , Rg.type_ = fileType
        }
  
  -- Run ripgrep
  result <- try $ Rg.rg rgOpts pattern searchDirs
  
  case result of
    Left _ -> return (False, [])  -- No matches or error
    Right output -> do
      let matches = T.lines output
          -- Filter out excluded patterns (Binary files, comments, etc.)
          filtered = filter (\line -> 
            not (T.isPrefixOf "Binary" line) &&
            not (T.isPrefixOf "./" line) &&
            all (\exclude -> not (T.isInfixOf exclude line)) excludePatterns
          ) matches
      
      if null filtered
        then return (False, [])
        else return (True, filtered)

main :: IO ()
main = script $ do
  echo "Checking for banned patterns..."
  
  scriptDir <- pwd
  let projectRoot = FP.takeDirectory (FP.takeDirectory scriptDir)
      srcDir = projectRoot </> "src"
      testDir = projectRoot </> "test"
      uiSrcDir = projectRoot </> "ui" </> "src"
  
  violations <- do
    -- ============================================================================
    -- HASKELL BANNED PATTERNS
    -- ============================================================================
    echo "Checking Haskell files..."
    
    -- Check for undefined
    (hasUndefined, undefinedMatches) <- checkPattern 
      "\\bundefined\\b" 
      [srcDir, testDir] 
      (Just "hs")
      ["Binary", "./"]
    
    when hasUndefined $ do
      echo "❌ ERROR: Found 'undefined' in Haskell code"
      M.mapM_ echo undefinedMatches
    
    -- Check for error
    (hasError, errorMatches) <- checkPattern 
      "\\berror\\s" 
      [srcDir, testDir] 
      (Just "hs")
      ["Binary", "./"]
    
    when hasError $ do
      echo "❌ ERROR: Found 'error' in Haskell code"
      M.mapM_ echo errorMatches
    
    -- Check for head/tail (partial functions)
    (hasHeadTail, headTailMatches) <- checkPattern 
      "\\bhead\\b|\\btail\\b" 
      [srcDir, testDir] 
      (Just "hs")
      ["Binary", "./", "import", "head", "tail"]
    
    when hasHeadTail $ do
      echo "❌ ERROR: Found 'head' or 'tail' (partial functions) in Haskell code"
      M.mapM_ echo headTailMatches
    
    -- ============================================================================
    -- PURESCRIPT BANNED PATTERNS
    -- ============================================================================
    echo "Checking PureScript files..."
    
    -- Check for unsafeCoerce
    (hasUnsafeCoerce, unsafeCoerceMatches) <- checkPattern 
      "unsafeCoerce" 
      [srcDir, testDir] 
      (Just "purs")
      ["Binary", "./"]
    
    when hasUnsafeCoerce $ do
      echo "❌ ERROR: Found 'unsafeCoerce' in PureScript code"
      M.mapM_ echo unsafeCoerceMatches
    
    -- ============================================================================
    -- TYPESCRIPT BANNED PATTERNS
    -- ============================================================================
    echo "Checking TypeScript files..."
    
    -- Check for ?? (nullish coalescing as default)
    (hasNullishCoalescing, nullishMatches) <- checkPattern 
      "\\?\\?" 
      [uiSrcDir] 
      (Just "ts")
      ["Binary", "./", "//", "test"]
    
    when hasNullishCoalescing $ do
      echo "❌ ERROR: Found '??' (nullish coalescing) in TypeScript code"
      M.mapM_ echo nullishMatches
    
    -- Check for || as default value (warning only)
    (hasOrDefault, _) <- checkPattern 
      "\\|\\|" 
      [uiSrcDir] 
      (Just "ts")
      ["Binary", "./", "//", "test", "if"]
    
    when hasOrDefault $ do
      echo "⚠️  WARNING: Found '||' (may be used as default) in TypeScript code"
    
    -- Check for ! (non-null assertions)
    (hasNonNullAssert, nonNullMatches) <- checkPattern 
      "!\\s*[a-zA-Z]" 
      [uiSrcDir] 
      (Just "ts")
      ["Binary", "./", "//", "test", "if"]
    
    when hasNonNullAssert $ do
      echo "❌ ERROR: Found '!' (non-null assertion) in TypeScript code"
      M.mapM_ echo nonNullMatches
    
    -- Count violations
    let violationCount = 
          (if hasUndefined then 1 else 0) +
          (if hasError then 1 else 0) +
          (if hasHeadTail then 1 else 0) +
          (if hasUnsafeCoerce then 1 else 0) +
          (if hasNullishCoalescing then 1 else 0) +
          (if hasNonNullAssert then 1 else 0)
    
    return violationCount
  
  if violations == 0
    then do
      echo "✅ No banned patterns found"
      exit 0
    else do
      echo $ "❌ Found " <> pack (show violations) <> " violation(s)"
      exit 1
