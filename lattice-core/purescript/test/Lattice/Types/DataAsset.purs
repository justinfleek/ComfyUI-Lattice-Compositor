-- | Port of ui/src/__tests__/types/dataAsset.property.test.ts
-- |
-- | Tests data asset type guards:
-- |   - isJSONAsset (json/mgjson types)
-- |   - isCSVAsset (csv/tsv types)
-- |   - isSupportedDataFile (file extension checking)
-- |   - getDataFileType (file type extraction)
-- |
-- | 16 tests across 4 describe blocks

module Test.Lattice.Types.DataAsset (spec) where

import Prelude

import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Foldable (for_)
import Data.String (toLower) as Str
import Data.String.CodeUnits (length, drop) as SCU
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.DataAsset (DataAssetType(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Utility functions (ported from TS types/dataAsset.ts)
-- These are simple type guards based on asset type / file extension
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a DataAssetType is a JSON-family type
isJSONAsset :: DataAssetType -> Boolean
isJSONAsset DAJson = true
isJSONAsset DAMgjson = true
isJSONAsset _ = false

-- | Check if a DataAssetType is a CSV-family type
isCSVAsset :: DataAssetType -> Boolean
isCSVAsset DACsv = true
isCSVAsset DATsv = true
isCSVAsset _ = false

-- | Check if a filename has a supported data file extension
isSupportedDataFile :: String -> Boolean
isSupportedDataFile filename =
  let lower = Str.toLower filename
  in endsWith ".json" lower
  || endsWith ".csv" lower
  || endsWith ".tsv" lower
  || endsWith ".mgjson" lower

-- | Get the DataAssetType from a filename, if supported
getDataFileType :: String -> Maybe DataAssetType
getDataFileType filename =
  let lower = Str.toLower filename
  in if endsWith ".mgjson" lower then Just DAMgjson
     else if endsWith ".json" lower then Just DAJson
     else if endsWith ".csv" lower then Just DACsv
     else if endsWith ".tsv" lower then Just DATsv
     else Nothing

-- | Check if a string ends with a suffix
endsWith :: String -> String -> Boolean
endsWith suffix str =
  let suffLen = SCU.length suffix
      strLen = SCU.length str
  in if strLen < suffLen
    then false
    else SCU.drop (strLen - suffLen) str == suffix

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "DataAsset - Type Tests" do
    isJSONAssetTests
    isCSVAssetTests
    isSupportedDataFileTests
    getDataFileTypeTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. isJSONAsset
-- ────────────────────────────────────────────────────────────────────────────

isJSONAssetTests :: Spec Unit
isJSONAssetTests = do
  describe "isJSONAsset" do

    it "should return true for JSON types" do
      isJSONAsset DAJson `shouldEqual` true
      isJSONAsset DAMgjson `shouldEqual` true

    it "should return false for non-JSON types" do
      isJSONAsset DACsv `shouldEqual` false
      isJSONAsset DATsv `shouldEqual` false

    it "should be mutually exclusive with isCSVAsset" do
      -- No type should be both JSON and CSV
      let allTypes = [DAJson, DACsv, DATsv, DAMgjson]
      for_ allTypes \t ->
        if isJSONAsset t && isCSVAsset t
          then fail ("Type " <> show t <> " is both JSON and CSV")
          else pure unit

-- ────────────────────────────────────────────────────────────────────────────
-- 2. isCSVAsset
-- ────────────────────────────────────────────────────────────────────────────

isCSVAssetTests :: Spec Unit
isCSVAssetTests = do
  describe "isCSVAsset" do

    it "should return true for CSV types" do
      isCSVAsset DACsv `shouldEqual` true
      isCSVAsset DATsv `shouldEqual` true

    it "should return false for non-CSV types" do
      isCSVAsset DAJson `shouldEqual` false
      isCSVAsset DAMgjson `shouldEqual` false

    it "should be mutually exclusive with isJSONAsset" do
      let allTypes = [DAJson, DACsv, DATsv, DAMgjson]
      for_ allTypes \t ->
        if isCSVAsset t && isJSONAsset t
          then fail ("Type " <> show t <> " is both CSV and JSON")
          else pure unit

-- ────────────────────────────────────────────────────────────────────────────
-- 3. isSupportedDataFile
-- ────────────────────────────────────────────────────────────────────────────

isSupportedDataFileTests :: Spec Unit
isSupportedDataFileTests = do
  describe "isSupportedDataFile" do

    it "should recognize .json files" do
      isSupportedDataFile "data.json" `shouldEqual` true
      isSupportedDataFile "path/to/file.json" `shouldEqual` true

    it "should recognize .csv files" do
      isSupportedDataFile "data.csv" `shouldEqual` true

    it "should recognize .tsv files" do
      isSupportedDataFile "data.tsv" `shouldEqual` true

    it "should recognize .mgjson files" do
      isSupportedDataFile "animation.mgjson" `shouldEqual` true

    it "should be case-insensitive" do
      isSupportedDataFile "data.JSON" `shouldEqual` true
      isSupportedDataFile "data.Csv" `shouldEqual` true
      isSupportedDataFile "DATA.TSV" `shouldEqual` true
      isSupportedDataFile "file.MGJSON" `shouldEqual` true

    it "should reject unsupported extensions" do
      isSupportedDataFile "image.png" `shouldEqual` false
      isSupportedDataFile "document.pdf" `shouldEqual` false
      isSupportedDataFile "script.js" `shouldEqual` false
      isSupportedDataFile "noextension" `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 4. getDataFileType
-- ────────────────────────────────────────────────────────────────────────────

getDataFileTypeTests :: Spec Unit
getDataFileTypeTests = do
  describe "getDataFileType" do

    it "should return correct type for supported files" do
      getDataFileType "data.json" `shouldEqual` Just DAJson
      getDataFileType "data.csv" `shouldEqual` Just DACsv
      getDataFileType "data.tsv" `shouldEqual` Just DATsv
      getDataFileType "anim.mgjson" `shouldEqual` Just DAMgjson

    it "should return Nothing for unsupported files" do
      isNothing (getDataFileType "image.png") `shouldEqual` true
      isNothing (getDataFileType "doc.pdf") `shouldEqual` true
      isNothing (getDataFileType "") `shouldEqual` true

    it "should be case-insensitive" do
      getDataFileType "DATA.JSON" `shouldEqual` Just DAJson
      getDataFileType "file.CSV" `shouldEqual` Just DACsv

    it "should be consistent with isSupportedDataFile" do
      let testFiles = ["data.json", "data.csv", "data.tsv", "anim.mgjson", "image.png", "nope"]
      for_ testFiles \f ->
        if isSupportedDataFile f
          then isJust (getDataFileType f) `shouldEqual` true
          else isNothing (getDataFileType f) `shouldEqual` true

    it "should prefer .mgjson over .json for double extension" do
      -- file.mgjson should be mgjson, not json
      getDataFileType "data.mgjson" `shouldEqual` Just DAMgjson
