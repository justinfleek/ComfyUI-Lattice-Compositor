-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // qrcode // capacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Capacity table tests.

module Test.QRCode.Capacity (capacityTableTests) where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((<?>))
import Test.QuickCheck.Gen (chooseInt)

import Hydrogen.Element.Compound.QRCode.Types as Types
import Hydrogen.Element.Compound.QRCode.Encoding.Capacity as Cap
import Test.QRCode.Generators (genVersion, genEC)

capacityTableTests :: Spec Unit
capacityTableTests = describe "Capacity Table (160 configurations)" do
  
  describe "Block info sanity" do
    it "all configurations have positive EC per block" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ info.ecPerBlock > 0
    
    it "all configurations have at least one block" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ info.group1Blocks + info.group2Blocks >= 1
    
    it "group2 data = group1 data + 1 when group2 exists" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ (info.group2Blocks == 0) || (info.group2Data == info.group1Data + 1)
    
    it "total codewords increases with version" do
      Spec.quickCheck do
        v1 <- chooseInt 1 39
        let v2 = v1 + 1
        ec <- genEC
        let ver1 = Types.mkVersion v1
        let ver2 = Types.mkVersion v2
        let info1 = Cap.getBlockInfo ec ver1
        let info2 = Cap.getBlockInfo ec ver2
        let total1 = Cap.totalCodewords info1
        let total2 = Cap.totalCodewords info2
        pure $ total2 >= total1 <?>
          ("Version " <> show v2 <> " should have >= capacity than version " <> show v1)

  describe "Specific known values (ISO 18004 Table 9)" do
    it "Version 1-L: 19 data, 7 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECLow (Types.mkVersion 1)
      info.group1Data `shouldEqual` 19
      info.ecPerBlock `shouldEqual` 7
      info.group1Blocks `shouldEqual` 1
    
    it "Version 1-M: 16 data, 10 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECMedium (Types.mkVersion 1)
      info.group1Data `shouldEqual` 16
      info.ecPerBlock `shouldEqual` 10
    
    it "Version 1-Q: 13 data, 13 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECQuartile (Types.mkVersion 1)
      info.group1Data `shouldEqual` 13
      info.ecPerBlock `shouldEqual` 13
    
    it "Version 1-H: 9 data, 17 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECHigh (Types.mkVersion 1)
      info.group1Data `shouldEqual` 9
      info.ecPerBlock `shouldEqual` 17
    
    it "Version 40-L: multiple blocks totaling 2956 data codewords" do
      let info = Cap.getBlockInfo Types.ECLow (Types.mkVersion 40)
      let totalData = Cap.totalDataCodewords info
      totalData `shouldEqual` 2956
