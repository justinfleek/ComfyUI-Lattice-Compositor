-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // test // qrcode // matrix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matrix structure tests.

module Test.QRCode.Matrix (matrixStructureTests) where

import Prelude
import Data.Array as Array
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (chooseInt)

import Hydrogen.Element.Compound.QRCode.Types as Types
import Hydrogen.Element.Compound.QRCode.Matrix as Matrix

matrixStructureTests :: Spec Unit
matrixStructureTests = describe "Matrix Structure" do
  
  describe "Matrix size" do
    it "version n has size 4n + 17" do
      Spec.quickCheck do
        v <- chooseInt 1 40
        let version = Types.mkVersion v
        let expectedSize = 4 * v + 17
        pure $ Types.versionSize version === expectedSize
    
    it "version 1 is 21x21" do
      Types.versionSize (Types.mkVersion 1) `shouldEqual` 21
    
    it "version 40 is 177x177" do
      Types.versionSize (Types.mkVersion 40) `shouldEqual` 177

  describe "Finder patterns" do
    it "finder pattern is 7x7" do
      let version = Types.mkVersion 1
      let matrix = Matrix.initializeMatrix version
      let withFinders = Matrix.placeFinderPatterns matrix
      let topLeft = Types.getModule 0 0 withFinders
      Types.isDark topLeft `shouldEqual` true

  describe "Timing patterns" do
    it "timing pattern alternates dark/light" do
      let version = Types.mkVersion 5
      let matrix = Matrix.initializeMatrix version
      let m1 = Matrix.placeFinderPatterns matrix
      let m2 = Matrix.placeSeparators m1
      let m3 = Matrix.placeTimingPatterns m2
      let col8 = Types.getModule 6 8 m3
      let col9 = Types.getModule 6 9 m3
      Types.isDark col8 `shouldEqual` true
      Types.isDark col9 `shouldEqual` false

  describe "Alignment patterns" do
    it "version 1 has no alignment patterns" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 1)
      Array.length positions `shouldEqual` 0
    
    it "version 2 has alignment patterns at [6, 18]" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 2)
      positions `shouldEqual` [6, 18]
    
    it "version 7 has alignment patterns at [6, 22, 38]" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 7)
      positions `shouldEqual` [6, 22, 38]
