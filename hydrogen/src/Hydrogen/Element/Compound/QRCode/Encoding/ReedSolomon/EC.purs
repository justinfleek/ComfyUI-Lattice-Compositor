-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // element // qrcode // encoding // reedsolomon // ec
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Error Correction — Generator polynomials and EC codeword computation.
-- |
-- | The generator polynomial for n error correction codewords is:
-- |   G(x) = (x - α^0)(x - α^1)(x - α^2)...(x - α^(n-1))

module Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.EC
  ( generatorPoly
  , generatorPolyCoeffs
  , computeECCodewords
  , computeECForData
  , ecCodewordsNeeded
  ) where

import Prelude
  ( otherwise
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Array (length, replicate, reverse, take)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.GF (gfExp)
import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.Polynomial
  ( Polynomial
  , polyMul
  , polyDivide
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // generator polynomials
-- ═════════════════════════════════════════════════════════════════════════════

generatorPoly :: Int -> Polynomial
generatorPoly n
  | n <= 0 = [1]
  | otherwise = buildGenerator 0 [1]
  where
    buildGenerator :: Int -> Polynomial -> Polynomial
    buildGenerator i acc
      | i >= n = acc
      | otherwise =
          let
            alphaI = gfExp i
            factor = [alphaI, 1]
            newAcc = polyMul acc factor
          in
            buildGenerator (i + 1) newAcc

generatorPolyCoeffs :: Int -> Array Int
generatorPolyCoeffs n = reverse (generatorPoly n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // error correction
-- ═════════════════════════════════════════════════════════════════════════════

computeECCodewords :: Array Int -> Int -> Array Int
computeECCodewords dataCodewords numEC =
  let
    dataPoly = reverse dataCodewords
    shiftedPoly = replicate numEC 0 <> dataPoly
    genPoly = generatorPoly numEC
    remainder = polyDivide shiftedPoly genPoly
    paddedRemainder = padToLength numEC remainder
  in
    reverse paddedRemainder
  where
    padToLength :: Int -> Array Int -> Array Int
    padToLength targetLen arr =
      let currentLen = length arr
      in if currentLen >= targetLen then take targetLen arr
         else arr <> replicate (targetLen - currentLen) 0

computeECForData :: Array Int -> Int -> { dataCodewords :: Array Int, ecCodewords :: Array Int }
computeECForData dataCodewords numEC =
  { dataCodewords: dataCodewords
  , ecCodewords: computeECCodewords dataCodewords numEC
  }

ecCodewordsNeeded :: Int -> Int -> Int
ecCodewordsNeeded version ecLevel =
  let
    baseEC = case ecLevel of
      0 -> 7
      1 -> 10
      2 -> 13
      _ -> 17
  in
    baseEC + (version - 1) * 2
