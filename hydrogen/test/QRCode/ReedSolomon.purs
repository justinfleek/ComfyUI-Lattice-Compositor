-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // test // qrcode // reedsolomon
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reed-Solomon error correction tests.

module Test.QRCode.ReedSolomon (reedSolomonTests) where

import Prelude
import Data.Array as Array
import Data.Foldable (all)
import Data.Maybe (fromMaybe)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===), (<?>))
import Test.QuickCheck.Gen (chooseInt, vectorOf)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon as RS
import Test.QRCode.Generators (genGFElement)

reedSolomonTests :: Spec Unit
reedSolomonTests = describe "Reed-Solomon Error Correction" do
  
  describe "Generator polynomial" do
    it "has correct degree" do
      Spec.quickCheck do
        numEC <- chooseInt 1 68
        let gen = RS.generatorPoly numEC
        pure $ Array.length gen === numEC + 1
    
    it "has leading coefficient 1" do
      Spec.quickCheck do
        numEC <- chooseInt 1 30
        let gen = RS.generatorPoly numEC
        pure $ fromMaybe 0 (Array.last gen) === 1
    
    it "has roots at α^0, α^1, ..., α^(n-1)" do
      Spec.quickCheck do
        numEC <- chooseInt 1 20
        rootIndex <- chooseInt 0 (numEC - 1)
        let gen = RS.generatorPoly numEC
        let root = RS.gfExp rootIndex
        let result = RS.polyEval gen root
        pure $ (result == 0) <?> 
          ("Generator poly should have root at α^" <> show rootIndex <> 
           " but evaluated to " <> show result)

  describe "EC codeword generation" do
    it "produces correct number of EC codewords" do
      Spec.quickCheck do
        numEC <- chooseInt 1 30
        dataLen <- chooseInt 1 50
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        pure $ Array.length ec === numEC
    
    it "EC codewords are in valid GF range" do
      Spec.quickCheck do
        numEC <- chooseInt 1 20
        dataLen <- chooseInt 1 30
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        pure $ all (\x -> x >= 0 && x <= 255) ec
    
    it "codeword polynomial evaluates to 0 at all roots" do
      Spec.quickCheck do
        numEC <- chooseInt 2 10
        dataLen <- chooseInt 2 20
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        let fullCodeword = dataBlock <> ec
        let fullPoly = Array.reverse fullCodeword
        rootIndex <- chooseInt 0 (numEC - 1)
        let root = RS.gfExp rootIndex
        let result = RS.polyEval fullPoly root
        pure $ (result == 0) <?>
          ("Full codeword should evaluate to 0 at α^" <> show rootIndex <>
           " but got " <> show result)
