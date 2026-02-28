-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // test // qrcode // polynomial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Polynomial operation tests.

module Test.QRCode.Polynomial (polynomialTests) where

import Prelude
import Data.Array as Array
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (suchThat)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon as RS
import Test.QRCode.Generators (genPolynomial)

polynomialTests :: Spec Unit
polynomialTests = describe "Polynomial Operations" do
  
  describe "Polynomial addition" do
    it "is commutative" do
      Spec.quickCheck do
        p1 <- genPolynomial
        p2 <- genPolynomial
        pure $ RS.polyAdd p1 p2 === RS.polyAdd p2 p1
    
    it "has identity [0]" do
      Spec.quickCheck do
        p <- genPolynomial
        pure $ RS.polyAdd p [0] === p

  describe "Polynomial multiplication" do
    it "is commutative" do
      Spec.quickCheck do
        p1 <- genPolynomial `suchThat` (\p -> Array.length p <= 10)
        p2 <- genPolynomial `suchThat` (\p -> Array.length p <= 10)
        pure $ RS.polyMul p1 p2 === RS.polyMul p2 p1
    
    it "has identity [1]" do
      Spec.quickCheck do
        p <- genPolynomial
        pure $ RS.polyMul p [1] === p
    
    it "degree(p1 * p2) = degree(p1) + degree(p2) for non-zero polynomials" do
      Spec.quickCheck do
        p1 <- genPolynomial `suchThat` (\p -> Array.length p > 0 && Array.length p <= 10)
        p2 <- genPolynomial `suchThat` (\p -> Array.length p > 0 && Array.length p <= 10)
        let prod = RS.polyMul p1 p2
        pure $ Array.length prod === Array.length p1 + Array.length p2 - 1

  describe "Polynomial evaluation" do
    it "evaluating constant polynomial returns constant" do
      Spec.quickCheck \c x ->
        RS.polyEval [c] x === c
    
    it "evaluating [a, b] at x gives a + b*x" do
      Spec.quickCheck \a b x ->
        RS.polyEval [a, b] x === RS.gfAdd a (RS.gfMul b x)
