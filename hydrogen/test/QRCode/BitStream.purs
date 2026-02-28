-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // qrcode // bitstream
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BitStream operation tests.

module Test.QRCode.BitStream (bitstreamTests) where

import Prelude
import Data.Array as Array
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (chooseInt, vectorOf)

import Hydrogen.Element.Compound.QRCode.Encoding.BitStream as BS

bitstreamTests :: Spec Unit
bitstreamTests = describe "BitStream Operations" do
  
  describe "Basic operations" do
    it "empty stream has length 0" do
      BS.length BS.empty `shouldEqual` 0
    
    it "fromInt produces correct number of bits" do
      Spec.quickCheck do
        val <- chooseInt 0 255
        numBits <- chooseInt 1 16
        let stream = BS.fromInt val numBits
        pure $ BS.length stream === numBits
    
    it "toBytes produces ceil(length/8) bytes" do
      Spec.quickCheck do
        numBits <- chooseInt 1 100
        bits <- vectorOf numBits (chooseInt 0 1)
        let stream = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits)
        let bytes = BS.toBytes stream
        let expectedBytes = (numBits + 7) / 8
        pure $ Array.length bytes === expectedBytes

  describe "Append" do
    it "length(a <> b) = length(a) + length(b)" do
      Spec.quickCheck do
        len1 <- chooseInt 0 50
        len2 <- chooseInt 0 50
        bits1 <- vectorOf len1 (chooseInt 0 1)
        bits2 <- vectorOf len2 (chooseInt 0 1)
        let s1 = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits1)
        let s2 = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits2)
        let combined = BS.append s1 s2
        pure $ BS.length combined === len1 + len2

  describe "Roundtrip" do
    it "toArray >>> fromBits = identity" do
      Spec.quickCheck do
        numBits <- chooseInt 1 100
        bits <- vectorOf numBits (chooseInt 0 1)
        let original = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits)
        let arr = BS.toArray original
        let restored = BS.fromBits arr
        pure $ BS.toArray restored === arr
