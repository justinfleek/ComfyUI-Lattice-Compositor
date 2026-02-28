-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // test // qrcode // galoisfield
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Galois Field GF(2^8) arithmetic tests.

module Test.QRCode.GaloisField (galoisFieldTests) where

import Prelude
import Data.Array as Array
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (chooseInt)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon as RS
import Test.QRCode.Generators (genGFElement, genNonZeroGF)

galoisFieldTests :: Spec Unit
galoisFieldTests = describe "Galois Field GF(2^8)" do
  
  describe "Addition (XOR)" do
    it "is commutative: a + b = b + a" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        pure $ RS.gfAdd a b === RS.gfAdd b a
    
    it "is associative: (a + b) + c = a + (b + c)" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfAdd (RS.gfAdd a b) c === RS.gfAdd a (RS.gfAdd b c)
    
    it "has identity 0: a + 0 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfAdd a 0 === a
    
    it "is self-inverse: a + a = 0" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfAdd a a === 0

  describe "Multiplication" do
    it "is commutative: a * b = b * a" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        pure $ RS.gfMul a b === RS.gfMul b a
    
    it "is associative: (a * b) * c = a * (b * c)" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfMul (RS.gfMul a b) c === RS.gfMul a (RS.gfMul b c)
    
    it "has identity 1: a * 1 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfMul a 1 === a
    
    it "has absorbing element 0: a * 0 = 0" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfMul a 0 === 0
    
    it "distributes over addition: a * (b + c) = a*b + a*c" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfMul a (RS.gfAdd b c) === RS.gfAdd (RS.gfMul a b) (RS.gfMul a c)

  describe "Division" do
    it "is inverse of multiplication: (a * b) / b = a for b ≠ 0" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genNonZeroGF
        pure $ RS.gfDiv (RS.gfMul a b) b === a
    
    it "a / a = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfDiv a a === 1
    
    it "0 / a = 0 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfDiv 0 a === 0

  describe "Exponentiation" do
    it "a^0 = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfPow a 0 === 1
    
    it "a^1 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfPow a 1 === a
    
    it "a^2 = a * a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfPow a 2 === RS.gfMul a a
    
    it "a^(m+n) = a^m * a^n" do
      Spec.quickCheck do
        a <- genNonZeroGF
        m <- chooseInt 0 127
        n <- chooseInt 0 127
        pure $ RS.gfPow a (m + n) === RS.gfMul (RS.gfPow a m) (RS.gfPow a n)

  describe "Inverse" do
    it "a * inverse(a) = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfMul a (RS.gfInverse a) === 1
    
    it "inverse(inverse(a)) = a for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfInverse (RS.gfInverse a) === a

  describe "Exp/Log tables" do
    it "exp(log(a)) = a for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfExp (RS.gfLog a) === a
    
    it "log(exp(n)) = n mod 255 for n < 255" do
      Spec.quickCheck do
        n <- chooseInt 0 254
        pure $ RS.gfLog (RS.gfExp n) === n
    
    it "exp table has no duplicates in [0,254]" do
      let expValues = Array.mapWithIndex (\i _ -> RS.gfExp i) (Array.replicate 255 0)
      let unique = Array.nub expValues
      Array.length unique `shouldEqual` 255
