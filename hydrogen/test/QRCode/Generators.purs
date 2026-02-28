-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // test // qrcode // generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QuickCheck generators for QR Code property tests.

module Test.QRCode.Generators
  ( genGFElement
  , genNonZeroGF
  , genVersion
  , genEC
  , genNumericString
  , genAlphanumericString
  , genAlphanumericChar
  , genByteString
  , genByteChar
  , genURLString
  , genAdversarialString
  , genPolynomial
  , genDataBlock
  , toEnum
  ) where

import Prelude
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Char (fromCharCode)
import Data.Maybe (fromMaybe)
import Data.String as String
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (Tuple(Tuple))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf, vectorOf)

import Hydrogen.Element.Compound.QRCode.Types as Types

genGFElement :: Gen Int
genGFElement = chooseInt 0 255

genNonZeroGF :: Gen Int
genNonZeroGF = chooseInt 1 255

genVersion :: Gen Types.QRVersion
genVersion = do
  v <- frequency $ NEA.cons'
    (Tuple 20.0 (pure 1))
    [ Tuple 15.0 (chooseInt 2 5)
    , Tuple 10.0 (chooseInt 6 9)
    , Tuple 10.0 (pure 10)
    , Tuple 10.0 (chooseInt 11 26)
    , Tuple 10.0 (pure 27)
    , Tuple 10.0 (chooseInt 27 39)
    , Tuple 15.0 (pure 40)
    ]
  pure (Types.mkVersion v)

genEC :: Gen Types.ErrorCorrection
genEC = elements $ NEA.cons'
  Types.ECLow
  [ Types.ECMedium
  , Types.ECQuartile
  , Types.ECHigh
  ]

genNumericString :: Gen String
genNumericString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))
    [ Tuple 10.0 (pure 1)
    , Tuple 10.0 (pure 2)
    , Tuple 10.0 (pure 3)
    , Tuple 20.0 (chooseInt 4 20)
    , Tuple 20.0 (chooseInt 21 100)]
  digits <- vectorOf len (chooseInt 0 9)
  pure (String.joinWith "" (Array.mapWithIndex (\_ d -> show d) digits))

genAlphanumericString :: Gen String
genAlphanumericString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))
    [ Tuple 10.0 (pure 1)
    , Tuple 10.0 (pure 2)
    , Tuple 25.0 (chooseInt 3 50)
    , Tuple 25.0 (chooseInt 51 200)]
  chars <- vectorOf len genAlphanumericChar
  pure (fromCharArray chars)

genAlphanumericChar :: Gen Char
genAlphanumericChar = 
  let
    digits = NEA.cons' '0' ['1','2','3','4','5','6','7','8','9']
    letters = NEA.cons' 'A' ['B','C','D','E','F','G','H','I','J','K','L','M',
                             'N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
    specials = NEA.cons' '$' ['%','*','+','-','.','/',':']
  in
    frequency $ NEA.cons'
      (Tuple 40.0 (elements digits))
      [ Tuple 40.0 (elements letters)
      , Tuple 10.0 (pure ' ')
      , Tuple 10.0 (elements specials)
      ]

genByteString :: Gen String
genByteString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))
    [ Tuple 20.0 (chooseInt 1 20)
    , Tuple 30.0 (chooseInt 21 100)
    , Tuple 20.0 (chooseInt 101 500)]
  chars <- vectorOf len genByteChar
  pure (fromCharArray chars)

genByteChar :: Gen Char
genByteChar = do
  code <- frequency $ NEA.cons'
    (Tuple 70.0 (chooseInt 32 126))
    [ Tuple 10.0 (chooseInt 0 31)
    , Tuple 10.0 (chooseInt 127 255)
    , Tuple 10.0 (pure 0)]
  pure (toEnum code)

genURLString :: Gen String
genURLString = do
  protocol <- elements $ NEA.cons' "https://" ["http://"]
  domain <- genDomain
  path <- genPath
  pure (protocol <> domain <> path)

genDomain :: Gen String
genDomain = do
  parts <- chooseInt 1 3
  segments <- vectorOf parts genDomainSegment
  tld <- elements $ NEA.cons' ".com" [".org", ".net", ".io", ".dev"]
  pure (String.joinWith "." segments <> tld)

genDomainSegment :: Gen String
genDomainSegment = do
  len <- chooseInt 3 12
  chars <- vectorOf len (elements $ NEA.cons' 'a' 
    ['b','c','d','e','f','g','h','i','j','k','l','m',
     'n','o','p','q','r','s','t','u','v','w','x','y','z'])
  pure (fromCharArray chars)

genPath :: Gen String
genPath = frequency $ NEA.cons'
  (Tuple 50.0 (pure ""))
  [ Tuple 50.0 (do
      segs <- chooseInt 1 4
      parts <- vectorOf segs genPathSegment
      hasQuery <- frequency $ NEA.cons' (Tuple 60.0 (pure false)) [Tuple 40.0 (pure true)]
      if hasQuery 
        then do
          query <- genQueryString
          pure ("/" <> String.joinWith "/" parts <> query)
        else pure ("/" <> String.joinWith "/" parts))
  ]

genPathSegment :: Gen String
genPathSegment = do
  len <- chooseInt 2 15
  chars <- vectorOf len (elements $ NEA.cons' 'a' 
    ['b','c','d','e','f','g','h','i','j','k','l','m',
     'n','o','p','q','r','s','t','u','v','w','x','y','z',
     '0','1','2','3','4','5','6','7','8','9','-','_'])
  pure (fromCharArray chars)

genQueryString :: Gen String
genQueryString = do
  params <- chooseInt 1 5
  pairs <- vectorOf params genQueryParam
  pure ("?" <> String.joinWith "&" pairs)

genQueryParam :: Gen String
genQueryParam = do
  key <- genPathSegment
  val <- genPathSegment
  pure (key <> "=" <> val)

genAdversarialString :: Gen String
genAdversarialString = oneOf $ NEA.cons'
  (pure "")
  [ pure "\x00"
  , pure "\x00\x00\x00"
  , pure (String.joinWith "" (Array.replicate 3000 "A"))
  , pure "https://x.com/\x00/y"
  , do len <- chooseInt 100 500
       bytes <- vectorOf len (chooseInt 0 255)
       pure (fromCharArray (Array.mapWithIndex (\_ b -> toEnum b) bytes))
  , pure "HELLO WORLD"
  , pure "12345678901234567890"
  , pure "AC-42"
  ]

genPolynomial :: Gen (Array Int)
genPolynomial = do
  degree <- frequency $ NEA.cons'
    (Tuple 10.0 (pure 0))
    [ Tuple 20.0 (pure 1)
    , Tuple 30.0 (chooseInt 2 10)
    , Tuple 30.0 (chooseInt 11 30)
    , Tuple 10.0 (chooseInt 31 68)]
  vectorOf (degree + 1) genGFElement

genDataBlock :: Gen (Array Int)
genDataBlock = do
  len <- frequency $ NEA.cons'
    (Tuple 10.0 (pure 1))
    [ Tuple 30.0 (chooseInt 2 20)
    , Tuple 40.0 (chooseInt 21 100)
    , Tuple 20.0 (chooseInt 101 200)]
  vectorOf len genGFElement

toEnum :: Int -> Char
toEnum n = fromMaybe '?' (fromCharCode n)
