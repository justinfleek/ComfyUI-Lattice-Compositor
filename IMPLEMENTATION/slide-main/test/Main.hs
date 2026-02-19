{- | Explicit test runner for Buck2
    
    Since Buck2 doesn't support GHC preprocessors like hspec-discover,
    we manually import and run all spec modules here.
-}
module Main where

import Test.Hspec (hspec, describe)

import qualified ChunkSpec
import qualified ConfigurationSpec
import qualified DecodeSpec
import qualified EncodeSpec
import qualified FrameSpec
import qualified HotTableSpec
import qualified ModelSpec
import qualified ParseSpec
import qualified RoundtripSpec
import qualified StressSpec
import qualified TokenizerFFISpec
import qualified ToolCallSpec
import qualified TypesSpec
import qualified VarintSpec

main :: IO ()
main = hspec $ do
    describe "ChunkSpec" ChunkSpec.spec
    describe "ConfigurationSpec" ConfigurationSpec.spec
    describe "DecodeSpec" DecodeSpec.spec
    describe "EncodeSpec" EncodeSpec.spec
    describe "FrameSpec" FrameSpec.spec
    describe "HotTableSpec" HotTableSpec.spec
    describe "ModelSpec" ModelSpec.spec
    describe "ParseSpec" ParseSpec.spec
    describe "RoundtripSpec" RoundtripSpec.spec
    describe "StressSpec" StressSpec.spec
    describe "TokenizerFFISpec" TokenizerFFISpec.spec
    describe "ToolCallSpec" ToolCallSpec.spec
    describe "TypesSpec" TypesSpec.spec
    describe "VarintSpec" VarintSpec.spec
