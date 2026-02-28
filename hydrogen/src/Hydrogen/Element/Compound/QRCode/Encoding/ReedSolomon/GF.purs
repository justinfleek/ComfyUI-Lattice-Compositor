-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // element // qrcode // encoding // reedsolomon // gf
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Galois Field GF(2^8) — Finite field arithmetic for Reed-Solomon.
-- |
-- | GF(2^8) is a finite field with 256 elements (0-255) where:
-- | - Addition is XOR
-- | - Multiplication uses the irreducible polynomial x^8 + x^4 + x^3 + x^2 + 1

module Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon.GF
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
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (==)
  , (<)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Array (index, replicate, snoc)
import Data.Array (mapWithIndex) as Array
import Data.EuclideanRing (mod)
import Data.Maybe (fromMaybe)
import Data.Int.Bits (xor, shl, shr, and)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gf element type
-- ═════════════════════════════════════════════════════════════════════════════

newtype GFElement = GFElement Int

derive instance eqGFElement :: Eq GFElement

instance showGFElement :: Show GFElement where
  show (GFElement n) = "GF(" <> show n <> ")"

mkGFElement :: Int -> GFElement
mkGFElement n
  | n < 0 = GFElement 0
  | n > 255 = GFElement (mod n 256)
  | otherwise = GFElement n

gfElementValue :: GFElement -> Int
gfElementValue (GFElement n) = n

gfElementAdd :: GFElement -> GFElement -> GFElement
gfElementAdd (GFElement a) (GFElement b) = GFElement (gfAdd a b)

gfElementMul :: GFElement -> GFElement -> GFElement
gfElementMul (GFElement a) (GFElement b) = GFElement (gfMul a b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

qrPolynomial :: Int
qrPolynomial = 0x11D

primitiveElement :: Int
primitiveElement = 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // lookup tables
-- ═════════════════════════════════════════════════════════════════════════════

expTable :: Array Int
expTable = buildExpTable 0 1 []
  where
    buildExpTable :: Int -> Int -> Array Int -> Array Int
    buildExpTable i val acc
      | i >= 256 = acc
      | otherwise =
          let
            newAcc = snoc acc val
            nextVal = val * primitiveElement
            reduced = if nextVal >= 256 then xor nextVal qrPolynomial else nextVal
          in
            buildExpTable (i + 1) reduced newAcc

logTable :: Array Int
logTable = buildLogTable 0 (replicate 256 0)
  where
    buildLogTable :: Int -> Array Int -> Array Int
    buildLogTable i acc
      | i >= 255 = acc
      | otherwise =
          let
            expVal = fromMaybe 0 (index expTable i)
            newAcc = Array.mapWithIndex (\idx v -> if idx == expVal then i else v) acc
          in
            buildLogTable (i + 1) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gf(2^8) arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

gfAdd :: Int -> Int -> Int
gfAdd a b = xor a b

gfSub :: Int -> Int -> Int
gfSub = gfAdd

gfMul :: Int -> Int -> Int
gfMul a b
  | a == 0 = 0
  | b == 0 = 0
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logB = fromMaybe 0 (index logTable b)
        logSum = mod (logA + logB) 255
      in
        fromMaybe 0 (index expTable logSum)

gfDiv :: Int -> Int -> Int
gfDiv a b
  | a == 0 = 0
  | b == 0 = 0
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logB = fromMaybe 0 (index logTable b)
        logDiff = mod (logA - logB + 255) 255
      in
        fromMaybe 0 (index expTable logDiff)

gfPow :: Int -> Int -> Int
gfPow a n
  | a == 0 = 0
  | n == 0 = 1
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logResult = mod (n * logA) 255
      in
        fromMaybe 0 (index expTable logResult)

gfInverse :: Int -> Int
gfInverse a
  | a == 0 = 0
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logInv = mod (255 - logA) 255
      in
        fromMaybe 0 (index expTable logInv)

gfExp :: Int -> Int
gfExp i = fromMaybe 0 (index expTable (mod i 255))

gfLog :: Int -> Int
gfLog x
  | x == 0 = 0
  | otherwise = fromMaybe 0 (index logTable x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bit operations
-- ═════════════════════════════════════════════════════════════════════════════

gfMulSlow :: Int -> Int -> Int
gfMulSlow a b = mulLoop a b 0
  where
    mulLoop :: Int -> Int -> Int -> Int
    mulLoop x y acc
      | y == 0 = acc
      | otherwise =
          let
            newAcc = if and y 1 == 1 then xor acc x else acc
            xShifted = shl x 1
            xReduced = if and xShifted 0x100 == 0 then xShifted else xor xShifted qrPolynomial
            yShifted = shr y 1
          in
            mulLoop xReduced yShifted newAcc

highBit :: Int -> Int
highBit n = findHighBit n 0
  where
    findHighBit :: Int -> Int -> Int
    findHighBit x pos
      | x == 0 = pos - 1
      | otherwise = findHighBit (shr x 1) (pos + 1)
