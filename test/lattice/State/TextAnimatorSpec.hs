-- |
-- Module      : Lattice.State.TextAnimatorSpec
-- Description : Test suite for text animator state management
--

module Lattice.State.TextAnimatorSpec (spec) where

import Data.Text (Text)
import Lattice.State.TextAnimator
  ( getTextContent
  , hasTextAnimators
  , getTextAnimators
  , getTextAnimator
  , getTextPathConfig
  , hasTextPath
  , rgbaObjectToHex
  , hexToRgbaObject
  , isRgbaObject
  , RGBA(..)
  , TextAnimator(..)
  , TextData(..)
  , TextPathConfig(..)
  , Layer(..)
  , LayerType(..)
  )
import Data.Aeson (Value(..), object, (.=))
import Data.HashMap.Strict (fromList)
import Data.Scientific (scientific)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // helpers
-- ════════════════════════════════════════════════════════════════════════════

createTestLayer :: LayerType -> Maybe TextData -> Layer
createTestLayer type_ mData = Layer "layer1" type_ mData

createTestTextData :: Maybe Text -> Maybe [TextAnimator] -> Maybe TextPathConfig -> TextData
createTestTextData mText mAnimators mPathConfig = TextData mText mAnimators mPathConfig

createTestAnimator :: Text -> Text -> Bool -> TextAnimator
createTestAnimator id_ name enabled = TextAnimator id_ name enabled

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.TextAnimator"
    [ testGroup
        "getTextContent"
        [ testCase "getTextContent - returns text from text layer" $ do
            let textData = createTestTextData (Just "Hello World") Nothing Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextContent layer
            assertEqual "Should return text" (Just "Hello World") result
        , testCase "getTextContent - returns Nothing for non-text layer" $ do
            let layer = createTestLayer LayerTypeImage Nothing
            let result = getTextContent layer
            assertEqual "Should return Nothing" Nothing result
        , testCase "getTextContent - returns Nothing when text is missing" $ do
            let textData = createTestTextData Nothing Nothing Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextContent layer
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "hasTextAnimators"
        [ testCase "hasTextAnimators - returns True when animators exist" $ do
            let animators = [createTestAnimator "a1" "Animator 1" True]
            let textData = createTestTextData (Just "Text") (Just animators) Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = hasTextAnimators layer
            assertBool "Should return True" result
        , testCase "hasTextAnimators - returns False when no animators" $ do
            let textData = createTestTextData (Just "Text") (Just []) Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = hasTextAnimators layer
            assertBool "Should return False" (not result)
        , testCase "hasTextAnimators - returns False for non-text layer" $ do
            let layer = createTestLayer LayerTypeImage Nothing
            let result = hasTextAnimators layer
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "getTextAnimators"
        [ testCase "getTextAnimators - returns animators list" $ do
            let animators = [createTestAnimator "a1" "Animator 1" True, createTestAnimator "a2" "Animator 2" False]
            let textData = createTestTextData (Just "Text") (Just animators) Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextAnimators layer
            assertEqual "Should return 2 animators" 2 (length result)
        , testCase "getTextAnimators - returns empty list for non-text layer" $ do
            let layer = createTestLayer LayerTypeImage Nothing
            let result = getTextAnimators layer
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "getTextAnimator"
        [ testCase "getTextAnimator - returns animator when exists" $ do
            let animator = createTestAnimator "a1" "Animator 1" True
            let animators = [animator]
            let textData = createTestTextData (Just "Text") (Just animators) Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextAnimator "a1" layer
            assertEqual "Should return animator" (Just animator) result
        , testCase "getTextAnimator - returns Nothing for non-existent ID" $ do
            let animators = [createTestAnimator "a1" "Animator 1" True]
            let textData = createTestTextData (Just "Text") (Just animators) Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextAnimator "nonexistent" layer
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "getTextPathConfig"
        [ testCase "getTextPathConfig - returns path config when exists" $ do
            let pathConfig = TextPathConfig [] False False False False 0.0 0.0 0.0 "left"
            let textData = createTestTextData (Just "Text") Nothing (Just pathConfig)
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextPathConfig layer
            assertBool "Should return path config" (result == Just pathConfig)
        , testCase "getTextPathConfig - returns Nothing when missing" $ do
            let textData = createTestTextData (Just "Text") Nothing Nothing
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = getTextPathConfig layer
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "hasTextPath"
        [ testCase "hasTextPath - returns True when path has 2+ points" $ do
            let pathConfig = TextPathConfig [String "point1", String "point2"] False False False False 0.0 0.0 0.0 "left"
            let textData = createTestTextData (Just "Text") Nothing (Just pathConfig)
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = hasTextPath layer
            assertBool "Should return True" result
        , testCase "hasTextPath - returns False when path has < 2 points" $ do
            let pathConfig = TextPathConfig [String "point1"] False False False False 0.0 0.0 0.0 "left"
            let textData = createTestTextData (Just "Text") Nothing (Just pathConfig)
            let layer = createTestLayer LayerTypeText (Just textData)
            let result = hasTextPath layer
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "rgbaObjectToHex"
        [ testCase "rgbaObjectToHex - converts RGBA to hex" $ do
            let rgba = RGBA 255.0 200.0 100.0 255.0
            let result = rgbaObjectToHex rgba
            assertBool "Should produce hex string" (not (null (show result)))
            case T.uncons result of
              Nothing -> assertBool "Should not be empty" False
              Just (firstChar, _) -> assertBool "Should start with #" (firstChar == '#')
        ]
    , testGroup
        "hexToRgbaObject"
        [ testCase "hexToRgbaObject - converts valid hex to RGBA" $ do
            let result = hexToRgbaObject "#ffc864"
            assertEqual "Should have correct R" 255.0 (rgbaR result)
            assertEqual "Should have correct G" 200.0 (rgbaG result)
            assertEqual "Should have correct B" 100.0 (rgbaB result)
        , testCase "hexToRgbaObject - returns default for invalid hex" $ do
            let result = hexToRgbaObject "invalid"
            assertEqual "Should return black" 0.0 (rgbaR result)
            assertEqual "Should return black" 0.0 (rgbaG result)
            assertEqual "Should return black" 0.0 (rgbaB result)
        ]
    , testGroup
        "isRgbaObject"
        [ testCase "isRgbaObject - returns True for valid RGBA object" $ do
            let value = object [("r", Number (scientific 255 0)), ("g", Number (scientific 200 0)), ("b", Number (scientific 100 0))]
            let result = isRgbaObject value
            assertBool "Should return True" result
        , testCase "isRgbaObject - returns False for invalid object" $ do
            let value = String "not an object"
            let result = isRgbaObject value
            assertBool "Should return False" (not result)
        ]
    ]
