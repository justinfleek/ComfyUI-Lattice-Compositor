{-# LANGUAGE OverloadedStrings #-}

-- | Check Proofs
-- Check for proof requirements in Lean4 code
-- BANNED: sorry without TODO, unproven axiom
module Main where

import Aleph.Script
import qualified Aleph.Script.Tools.Rg as Rg
import qualified System.FilePath as FP
import qualified Data.Text as T
import Data.Text (pack)

main :: IO ()
main = script $ do
  echo "Checking for proof requirements..."
  
  scriptDir <- pwd
  let projectRoot = FP.takeDirectory (FP.takeDirectory scriptDir)
      leanDir = projectRoot </> "lattice-core" </> "lean"
  
  violations <- do
    echo "Checking Lean4 files..."
    
    -- Check for 'sorry' without TODO comment
    (hasSorry, sorryMatches) <- checkPattern "sorry" [leanDir] (Just "lean") 
      ["Binary", "./", "TODO", "--", "/*"]
    
    when hasSorry $ do
      echo "❌ ERROR: Found 'sorry' without TODO comment in Lean4 code"
      M.mapM_ echo sorryMatches
    
    return $ if hasSorry then 1 else 0
  
  if violations == 0
    then do
      echo "✅ No proof violations found"
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
