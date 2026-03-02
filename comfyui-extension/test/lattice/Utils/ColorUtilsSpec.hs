-- |
-- Test suite for Lattice.Utils.ColorUtils
--

module Lattice.Utils.ColorUtilsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.ColorUtils
import qualified Data.Text as T

spec :: TestTree
spec = testGroup "Lattice.Utils.ColorUtils"
  [ testGroup "HSV Conversions"
    [ testCase "hsvToRgb - red" $ do
        let (r, g, b) = hsvToRgb 0 1 1
        r @?= 255.0
        g @?= 0.0
        b @?= 0.0
    , testCase "hsvToRgb - green" $ do
        let (r, g, b) = hsvToRgb 120 1 1
        r @?= 0.0
        g @?= 255.0
        b @?= 0.0
    , testCase "rgbToHsv - red" $ do
        let (h, s, v) = rgbToHsv 255 0 0
        h @?= 0.0
        s @?= 1.0
        v @?= 1.0
    ]
  , testGroup "HSL Conversions"
    [ testCase "hslToRgb - red" $ do
        let (r, g, b) = hslToRgb 0 1 0.5
        r @?= 255.0
        g @?= 0.0
        b @?= 0.0
    , testCase "rgbToHsl - red" $ do
        let (h, s, l) = rgbToHsl 255 0 0
        h @?= 0.0
        s @?= 1.0
    ]
  , testGroup "Hex Conversions"
    [ testCase "hexToRgb - #FF0000" $ do
        case hexToRgb "#FF0000" of
          Right (r, g, b) -> do
            r @?= 255.0
            g @?= 0.0
            b @?= 0.0
          Left _ -> assertFailure "Should parse #FF0000"
    , testCase "hexToRgb - #RGB format" $ do
        case hexToRgb "#F00" of
          Right (r, g, b) -> do
            r @?= 255.0
            g @?= 0.0
            b @?= 0.0
          Left _ -> assertFailure "Should parse #F00"
    , testCase "rgbToHex - red" $
        rgbToHex 255 0 0 @?= T.pack "#ff0000"
    , testCase "hexToRgb roundtrip" $ do
        let original = (255.0, 128.0, 64.0)
            hex = rgbToHex (fst original) (snd original) (snd (snd original, fst original))
        case hexToRgb hex of
          Right result -> result @?= original
          Left _ -> assertFailure "Should roundtrip"
    ]
  , testGroup "Color Parsing"
    [ testCase "parseColor - hex" $ do
        case parseColor (T.pack "#FF0000") of
          Right (r, g, b) -> do
            r @?= 255.0
            g @?= 0.0
            b @?= 0.0
          Left _ -> assertFailure "Should parse hex"
    , testCase "parseColor - rgb()" $ do
        case parseColor (T.pack "rgb(255, 0, 0)") of
          Right (r, g, b) -> do
            r @?= 255.0
            g @?= 0.0
            b @?= 0.0
          Left _ -> assertFailure "Should parse rgb()"
    ]
  , testGroup "Color Operations"
    [ testCase "lerpColor - red to blue" $ do
        case lerpColor (T.pack "#ff0000") (T.pack "#0000ff") 0.5 of
          Right result -> result @?= T.pack "#800080"  -- Purple
          Left _ -> assertFailure "Should interpolate"
    , testCase "getContrastColor - white background" $ do
        case getContrastColor (T.pack "#ffffff") of
          Right result -> result @?= T.pack "#000000"  -- Black text
          Left _ -> assertFailure "Should return black"
    , testCase "getContrastColor - black background" $ do
        case getContrastColor (T.pack "#000000") of
          Right result -> result @?= T.pack "#ffffff"  -- White text
          Left _ -> assertFailure "Should return white"
    ]
  ]
