-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // qr-code // encoding // reed-solomon
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reed-Solomon Error Correction — Pure PureScript implementation.
-- |
-- | This is an orchestrating module that re-exports from:
-- | - `ReedSolomon.GF` — GF(2^8) field arithmetic
-- | - `ReedSolomon.Polynomial` — Polynomial operations
-- | - `ReedSolomon.EC` — Error correction computation
-- |
-- | This module adds validation and verification utilities.

module Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon
  ( module GF
  , module Polynomial
  , module EC
  , isValidGFElement
  , isValidPolynomial
  , polynomialsEqual
  , verifyGeneratorRoots
  , verifyTables
  , allGFElements
  ) where

import Prelude
  ( otherwise
  , (==)
  , (/=)
  , (>=)
  , (<=)
  , (+)
  , (&&)
  )

import Data.Array (length, index, (..))
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.GF
  ( GFElement(GFElement)
  , mkGFElement
  , gfElementValue
  , gfElementAdd
  , gfElementMul
  , gfAdd
  , gfSub
  , gfMul
  , gfDiv
  , gfPow
  , gfInverse
  , gfExp
  , gfLog
  , expTable
  , logTable
  , qrPolynomial
  , primitiveElement
  , gfMulSlow
  , highBit
  ) as GF

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.Polynomial
  ( Polynomial
  , polyMul
  , polyMulScalar
  , polyAdd
  , polyDivide
  , polyEval
  , polynomialDegree
  , showPolynomial
  ) as Polynomial

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.EC
  ( generatorPoly
  , generatorPolyCoeffs
  , computeECCodewords
  , computeECForData
  , ecCodewordsNeeded
  ) as EC

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

isValidGFElement :: Int -> Boolean
isValidGFElement n = n >= 0 && n <= 255

isValidPolynomial :: Polynomial.Polynomial -> Boolean
isValidPolynomial poly =
  let len = length poly
  in len >= 1 && allValid 0 poly
  where
    allValid :: Int -> Polynomial.Polynomial -> Boolean
    allValid i arr
      | i >= length arr = true
      | otherwise = case index arr i of
          Nothing -> false
          Just coeff -> isValidGFElement coeff && allValid (i + 1) arr

polynomialsEqual :: Polynomial.Polynomial -> Polynomial.Polynomial -> Boolean
polynomialsEqual p1 p2 =
  let
    len1 = length p1
    len2 = length p2
  in
    if len1 /= len2 then false
    else checkEqual 0 p1 p2
  where
    checkEqual :: Int -> Polynomial.Polynomial -> Polynomial.Polynomial -> Boolean
    checkEqual i a b
      | i >= length a = true
      | otherwise =
          let
            va = fromMaybe 0 (index a i)
            vb = fromMaybe 0 (index b i)
          in
            va == vb && checkEqual (i + 1) a b

verifyGeneratorRoots :: Int -> Boolean
verifyGeneratorRoots n =
  let gen = EC.generatorPoly n
  in if n <= 0 then true else checkRoots 0 n gen
  where
    checkRoots :: Int -> Int -> Polynomial.Polynomial -> Boolean
    checkRoots i numRoots poly
      | i >= numRoots = true
      | otherwise =
          let
            alphaI = GF.gfExp i
            evalResult = Polynomial.polyEval poly alphaI
          in
            evalResult == 0 && checkRoots (i + 1) numRoots poly

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // table verification
-- ═════════════════════════════════════════════════════════════════════════════

allGFElements :: Array Int
allGFElements = 0 .. 255

verifyTables :: Boolean
verifyTables =
  let
    expLogValid = checkExpLog 0
    logExpValid = checkLogExp 1
  in
    expLogValid && logExpValid
  where
    checkExpLog :: Int -> Boolean
    checkExpLog i
      | i >= 255 = true
      | otherwise =
          let
            expVal = fromMaybe 0 (index GF.expTable i)
            logVal = fromMaybe 0 (index GF.logTable expVal)
          in
            logVal == i && checkExpLog (i + 1)
    
    checkLogExp :: Int -> Boolean
    checkLogExp x
      | x >= 256 = true
      | otherwise =
          let
            logVal = fromMaybe 0 (index GF.logTable x)
            expVal = fromMaybe 0 (index GF.expTable logVal)
          in
            expVal == x && checkLogExp (x + 1)
