-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--     // hydrogen // element // qrcode // encoding // reedsolomon // polynomial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Polynomial Operations — Polynomials over GF(2^8).
-- |
-- | Polynomials are represented as arrays of coefficients where:
-- | - Index 0 is the constant term (x^0)
-- | - Index n is the coefficient of x^n

module Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.Polynomial
  ( Polynomial
  , polyAdd
  , polyMulScalar
  , polyMul
  , polyDivide
  , polyEval
  , polynomialDegree
  , showPolynomial
  ) where

import Prelude
  ( show
  , otherwise
  , (==)
  , (/=)
  , (<)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (<>)
  )

import Data.Array (length, index, replicate, reverse, drop, foldl)
import Data.Array (zipWith, filter, mapWithIndex) as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.GF
  ( gfAdd
  , gfSub
  , gfMul
  , gfDiv
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // polynomial type
-- ═════════════════════════════════════════════════════════════════════════════

type Polynomial = Array Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // polynomial operations
-- ═════════════════════════════════════════════════════════════════════════════

polyAdd :: Polynomial -> Polynomial -> Polynomial
polyAdd p1 p2 =
  let
    len1 = length p1
    len2 = length p2
    maxLen = if len1 > len2 then len1 else len2
    padded1 = padRight maxLen p1
    padded2 = padRight maxLen p2
  in
    Array.zipWith gfAdd padded1 padded2
  where
    padRight :: Int -> Array Int -> Array Int
    padRight targetLen arr =
      let
        currentLen = length arr
        padding = replicate (targetLen - currentLen) 0
      in
        arr <> padding

polyMulScalar :: Int -> Polynomial -> Polynomial
polyMulScalar scalar poly = 
  Array.mapWithIndex (\_ c -> gfMul scalar c) poly

polyMul :: Polynomial -> Polynomial -> Polynomial
polyMul p1 p2 =
  let
    len1 = length p1
    len2 = length p2
    resultLen = len1 + len2 - 1
    initial = replicate resultLen 0
  in
    if len1 == 0 then []
    else if len2 == 0 then []
    else multiplyLoop 0 p1 p2 initial
  where
    multiplyLoop :: Int -> Polynomial -> Polynomial -> Polynomial -> Polynomial
    multiplyLoop i poly1 poly2 acc
      | i >= length poly1 = acc
      | otherwise =
          let
            coeff1 = fromMaybe 0 (index poly1 i)
            newAcc = addShifted i coeff1 poly2 acc
          in
            multiplyLoop (i + 1) poly1 poly2 newAcc
    
    addShifted :: Int -> Int -> Polynomial -> Polynomial -> Polynomial
    addShifted shift scalar poly acc =
      addShiftedLoop 0 shift scalar poly acc
    
    addShiftedLoop :: Int -> Int -> Int -> Polynomial -> Polynomial -> Polynomial
    addShiftedLoop j shift scalar poly acc
      | j >= length poly = acc
      | otherwise =
          let
            coeff = fromMaybe 0 (index poly j)
            product = gfMul scalar coeff
            targetIdx = shift + j
            oldVal = fromMaybe 0 (index acc targetIdx)
            newVal = gfAdd oldVal product
            newAcc = setAt targetIdx newVal acc
          in
            addShiftedLoop (j + 1) shift scalar poly newAcc
    
    setAt :: Int -> Int -> Array Int -> Array Int
    setAt idx val arr =
      Array.mapWithIndex (\i v -> if i == idx then val else v) arr

polyDivide :: Polynomial -> Polynomial -> Polynomial
polyDivide dividend divisor =
  let
    dividendLen = length dividend
    divisorLen = length divisor
  in
    if divisorLen == 0 then dividend
    else if dividendLen < divisorLen then dividend
    else divisionLoop (reverse dividend) (reverse divisor)
  where
    divisionLoop :: Polynomial -> Polynomial -> Polynomial
    divisionLoop currentDiv divisorRev =
      let
        currentLen = length currentDiv
        divLen = length divisorRev
        leadDiv = fromMaybe 0 (index divisorRev 0)
      in
        if currentLen < divLen then reverse (trimLeadingZeros currentDiv)
        else if leadDiv == 0 then reverse (trimLeadingZeros currentDiv)
        else
          let
            leadCurrent = fromMaybe 0 (index currentDiv 0)
          in
            if leadCurrent == 0 then
              divisionLoop (drop 1 currentDiv) divisorRev
            else
              let
                quotCoeff = gfDiv leadCurrent leadDiv
                subtracted = subtractScaledPoly quotCoeff divisorRev currentDiv
                reduced = drop 1 subtracted
              in
                divisionLoop reduced divisorRev
    
    subtractScaledPoly :: Int -> Polynomial -> Polynomial -> Polynomial
    subtractScaledPoly scalar divisorRev currentDiv =
      Array.mapWithIndex (\i val ->
        if i < length divisorRev then
          gfSub val (gfMul scalar (fromMaybe 0 (index divisorRev i)))
        else val
      ) currentDiv
    
    trimLeadingZeros :: Polynomial -> Polynomial
    trimLeadingZeros arr =
      let trimmed = dropWhileZero arr
      in if length trimmed == 0 then [0] else trimmed
    
    dropWhileZero :: Array Int -> Array Int
    dropWhileZero arr = case index arr 0 of
      Nothing -> []
      Just 0 -> dropWhileZero (drop 1 arr)
      Just _ -> arr

polyEval :: Polynomial -> Int -> Int
polyEval poly x =
  let reversed = reverse poly
  in foldl (\acc coeff -> gfAdd (gfMul acc x) coeff) 0 reversed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

polynomialDegree :: Polynomial -> Int
polynomialDegree poly =
  let
    len = length poly
    findDegree i
      | i < 0 = 0
      | otherwise = case index poly i of
          Just 0 -> findDegree (i - 1)
          Just _ -> i
          Nothing -> findDegree (i - 1)
  in
    findDegree (len - 1)

showPolynomial :: Polynomial -> String
showPolynomial poly =
  let
    terms = Array.filter (\t -> t.coeff /= 0) (Array.mapWithIndex (\i c -> { idx: i, coeff: c }) poly)
  in
    if length terms == 0 then "0"
    else foldl (\acc t ->
      let
        term = if t.idx == 0 then show t.coeff
               else if t.idx == 1 then show t.coeff <> "x"
               else show t.coeff <> "x^" <> show t.idx
      in
        if acc == "" then term else acc <> " + " <> term
    ) "" terms
