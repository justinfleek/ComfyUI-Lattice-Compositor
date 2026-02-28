-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // test // qrcode // mask
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Masking tests.

module Test.QRCode.Mask (maskingTests) where

import Prelude
import Data.Array.NonEmpty as NEA
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (chooseInt, elements)

import Hydrogen.Element.Compound.QRCode.Matrix as Matrix

maskingTests :: Spec Unit
maskingTests = describe "Masking" do
  
  describe "Mask patterns" do
    it "mask 0: (row + col) mod 2 == 0" do
      Matrix.shouldMaskModule Matrix.Mask0 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask0 0 1 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask0 1 0 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask0 1 1 `shouldEqual` true
    
    it "mask 1: row mod 2 == 0" do
      Matrix.shouldMaskModule Matrix.Mask1 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask1 0 5 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask1 1 0 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask1 1 5 `shouldEqual` false
    
    it "mask 2: col mod 3 == 0" do
      Matrix.shouldMaskModule Matrix.Mask2 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask2 0 3 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask2 0 1 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask2 0 2 `shouldEqual` false
    
    it "masking is self-inverse" do
      Spec.quickCheck do
        pattern <- elements $ NEA.cons' Matrix.Mask0 
          [Matrix.Mask1, Matrix.Mask2, Matrix.Mask3, 
           Matrix.Mask4, Matrix.Mask5, Matrix.Mask6, Matrix.Mask7]
        row <- chooseInt 0 100
        col <- chooseInt 0 100
        let shouldMask = Matrix.shouldMaskModule pattern row col
        pure $ (shouldMask == shouldMask) === true
