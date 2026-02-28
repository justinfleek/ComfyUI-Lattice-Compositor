-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // test // qrcode // segment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Segment encoding tests.

module Test.QRCode.Segment (segmentEncodingTests) where

import Prelude
import Data.String as String
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (suchThat)

import Hydrogen.Element.Compound.QRCode.Types as Types
import Hydrogen.Element.Compound.QRCode.Encoding.Segment as Seg
import Test.QRCode.Generators (genNumericString)

segmentEncodingTests :: Spec Unit
segmentEncodingTests = describe "Segment Encoding" do
  
  describe "Mode detection" do
    it "detects numeric mode for digit-only strings" do
      Spec.quickCheck do
        s <- genNumericString `suchThat` (\str -> String.length str > 0)
        pure $ Seg.detectOptimalMode s === Types.ModeNumeric
    
    it "detects alphanumeric for uppercase + digits" do
      let s = "HELLO WORLD 123"
      Seg.detectOptimalMode s `shouldEqual` Types.ModeAlphanumeric
    
    it "detects byte mode for lowercase" do
      let s = "hello"
      Seg.detectOptimalMode s `shouldEqual` Types.ModeByte

  describe "Character count bits" do
    it "returns correct bits for numeric mode" do
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeNumeric `shouldEqual` 10
      Seg.characterCountBits v10 Types.ModeNumeric `shouldEqual` 12
      Seg.characterCountBits v27 Types.ModeNumeric `shouldEqual` 14
    
    it "returns correct bits for alphanumeric mode" do
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeAlphanumeric `shouldEqual` 9
      Seg.characterCountBits v10 Types.ModeAlphanumeric `shouldEqual` 11
      Seg.characterCountBits v27 Types.ModeAlphanumeric `shouldEqual` 13
    
    it "returns correct bits for byte mode" do
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeByte `shouldEqual` 8
      Seg.characterCountBits v10 Types.ModeByte `shouldEqual` 16
      Seg.characterCountBits v27 Types.ModeByte `shouldEqual` 16

  describe "Alphanumeric encoding" do
    it "maps 0-9 to 0-9" do
      Seg.alphanumericValue '0' `shouldEqual` 0
      Seg.alphanumericValue '5' `shouldEqual` 5
      Seg.alphanumericValue '9' `shouldEqual` 9
    
    it "maps A-Z to 10-35" do
      Seg.alphanumericValue 'A' `shouldEqual` 10
      Seg.alphanumericValue 'Z' `shouldEqual` 35
    
    it "maps special chars correctly" do
      Seg.alphanumericValue ' ' `shouldEqual` 36
      Seg.alphanumericValue '$' `shouldEqual` 37
      Seg.alphanumericValue '%' `shouldEqual` 38
      Seg.alphanumericValue '*' `shouldEqual` 39
      Seg.alphanumericValue '+' `shouldEqual` 40
      Seg.alphanumericValue '-' `shouldEqual` 41
      Seg.alphanumericValue '.' `shouldEqual` 42
      Seg.alphanumericValue '/' `shouldEqual` 43
      Seg.alphanumericValue ':' `shouldEqual` 44
