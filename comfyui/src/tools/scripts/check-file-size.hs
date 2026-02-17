{-# LANGUAGE OverloadedStrings #-}

-- | Check File Size
-- Checks that all files are under 500 lines
-- REQUIRED: All files <500 lines (enforced by architecture)
--
-- Exit code: 0 if no violations, 1 if violations found
module Main where

import Aleph.Script
import qualified Aleph.Script.Tools.Find as Find
import qualified System.FilePath as FP
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Data.Text (pack)

maxLines :: Int
maxLines = 500

-- | Count lines in a file
countLines :: FilePath -> Sh Int
countLines file = do
  result <- try $ run "wc" ["-l", toText file]
  case result of
    Left _ -> return 0  -- File doesn't exist or can't be read
    Right output -> do
      let linesList = T.lines output
          lineCountText = if null linesList then "0" else T.strip (head linesList)
      case TR.decimal lineCountText of
        Right (count, _) -> return count
        Left _ -> return 0

-- | Check files matching pattern in directory
checkFiles :: FilePath -> Text -> Text -> Sh Int
checkFiles baseDir pattern ext = do
  -- Use find to get files (handling .lake exclusion for Lean)
  output <- errExit False $ run "find" 
    [ toText baseDir
    , "-type", "f"
    , "-name", "*" <> ext
    , "!", "-path", "*/.lake/*"
    ]
  
  let files = filter (not . T.isInfixOf ".lake") (T.lines output)
  
  violations <- foldM (\acc fileText -> do
    let file = fromText fileText
    lineCount <- countLines file
    if lineCount > maxLines
      then do
        echo $ "❌ ERROR: " <> fileText <> " exceeds " <> 
               pack (show maxLines) <> " lines (" <> 
               pack (show lineCount) <> " lines)"
        return (acc + 1)
      else return acc
    ) 0 files
  
  return violations

main :: IO ()
main = script $ do
  echo $ "Checking file sizes (max " <> pack (show maxLines) <> " lines)..."
  
  scriptDir <- pwd
  let projectRoot = FP.takeDirectory (FP.takeDirectory scriptDir)
  
  violations <- do
    -- Check Haskell files
    echo "Checking Haskell files..."
    hsViolations <- checkFiles (projectRoot </> "src") "*.hs" ".hs"
    hsTestViolations <- checkFiles (projectRoot </> "test") "*.hs" ".hs"
    
    -- Check PureScript files
    echo "Checking PureScript files..."
    pursViolations <- checkFiles (projectRoot </> "src") "*.purs" ".purs"
    pursTestViolations <- checkFiles (projectRoot </> "test") "*.purs" ".purs"
    
    -- Check TypeScript files
    echo "Checking TypeScript files..."
    tsViolations <- checkFiles (projectRoot </> "ui" </> "src") "*.ts" ".ts"
    tsxViolations <- checkFiles (projectRoot </> "ui" </> "src") "*.tsx" ".tsx"
    
    -- Check Lean4 files
    echo "Checking Lean4 files..."
    leanViolations <- checkFiles (projectRoot </> "leancomfy" </> "lean") "*.lean" ".lean"
    
    return $ hsViolations + hsTestViolations + 
             pursViolations + pursTestViolations + 
             tsViolations + tsxViolations + 
             leanViolations
  
  if violations == 0
    then do
      echo $ "✅ All files are under " <> pack (show maxLines) <> " lines"
      exit 0
    else do
      echo $ "❌ Found " <> pack (show violations) <> " file(s) exceeding " <> 
             pack (show maxLines) <> " lines"
      echo ""
      echo "Suggestions:"
      echo "  - Split large files into smaller modules"
      echo "  - Extract helper functions to separate files"
      echo "  - Use type classes/protocols to reduce duplication"
      exit 1
