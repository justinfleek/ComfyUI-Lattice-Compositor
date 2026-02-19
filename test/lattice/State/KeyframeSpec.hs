-- |
-- Module      : Lattice.State.KeyframeSpec
-- Description : Test suite for keyframe state management
--

module Lattice.State.KeyframeSpec (spec) where

import Data.Aeson (Value(..), Number)
import Data.Scientific (scientific)
import Data.Text (Text)
import Lattice.State.Keyframe
  ( safeFrame
  , findPropertyByPath
  , findSurroundingKeyframes
  , hasKeyframesInClipboard
  , hasPositionSeparated
  , hasScaleSeparated
  , AnimatableProperty(..)
  , Keyframe(..)
  , Layer(..)
  , LayerTransform(..)
  , ClipboardKeyframe(..)
  , SeparateDimensions(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // helpers
-- ════════════════════════════════════════════════════════════════════════════

createTestKeyframe :: Int -> Value -> Keyframe Value
createTestKeyframe frame value = Keyframe "kf1" frame value

createTestProperty :: Text -> Text -> Bool -> [Keyframe Value] -> AnimatableProperty Value
createTestProperty id_ name animated keyframes = AnimatableProperty id_ name animated keyframes

createTestTransform :: Maybe SeparateDimensions -> LayerTransform
createTestTransform mSepDims = LayerTransform Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing mSepDims

createTestLayer :: Text -> LayerTransform -> Maybe (AnimatableProperty Value) -> [AnimatableProperty Value] -> Layer
createTestLayer id_ transform opacity properties = Layer id_ transform opacity properties

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Keyframe"
    [ testGroup
        "safeFrame"
        [ testCase "safeFrame - returns frame when valid" $ do
            let result = safeFrame (Just 10.0) 0.0
            assertEqual "Should return 10.0" 10.0 result
        , testCase "safeFrame - returns fallback when Nothing" $ do
            let result = safeFrame Nothing 5.0
            assertEqual "Should return fallback" 5.0 result
        , testCase "safeFrame - returns fallback when Infinity" $ do
            let result = safeFrame (Just (1/0)) 5.0
            assertEqual "Should return fallback" 5.0 result
        ]
    , testGroup
        "findPropertyByPath"
        [ testCase "findPropertyByPath - finds position property" $ do
            let position = createTestProperty "pos" "position" False []
            let transform = LayerTransform (Just position) Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing
            let layer = createTestLayer "layer1" transform Nothing []
            let result = findPropertyByPath layer "position"
            assertBool "Should return position property" (result == Just position)
        , testCase "findPropertyByPath - finds opacity property" $ do
            let opacity = createTestProperty "op" "opacity" False []
            let layer = createTestLayer "layer1" (createTestTransform Nothing) (Just opacity) []
            let result = findPropertyByPath layer "opacity"
            assertBool "Should return opacity property" (result == Just opacity)
        , testCase "findPropertyByPath - returns Nothing for non-existent property" $ do
            let layer = createTestLayer "layer1" (createTestTransform Nothing) Nothing []
            let result = findPropertyByPath layer "nonexistent"
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "findSurroundingKeyframes"
        [ testCase "findSurroundingKeyframes - finds before and after keyframes" $ do
            let kf1 = createTestKeyframe 10 (Number (scientific 100 0))
            let kf2 = createTestKeyframe 20 (Number (scientific 200 0))
            let kf3 = createTestKeyframe 30 (Number (scientific 300 0))
            let property = createTestProperty "prop1" "test" True [kf1, kf2, kf3]
            let (before, after) = findSurroundingKeyframes property 15
            assertBool "Should have before keyframe" (before == Just kf1)
            assertBool "Should have after keyframe" (after == Just kf2)
        , testCase "findSurroundingKeyframes - returns Nothing when no keyframes" $ do
            let property = createTestProperty "prop1" "test" False []
            let (before, after) = findSurroundingKeyframes property 15
            assertEqual "Should return Nothing for before" Nothing before
            assertEqual "Should return Nothing for after" Nothing after
        ]
    , testGroup
        "hasKeyframesInClipboard"
        [ testCase "hasKeyframesInClipboard - returns True when clipboard has keyframes" $ do
            let clipboard = [ClipboardKeyframe "layer1" "position" []]
            let result = hasKeyframesInClipboard clipboard
            assertBool "Should return True" result
        , testCase "hasKeyframesInClipboard - returns False when clipboard is empty" $ do
            let result = hasKeyframesInClipboard []
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "hasPositionSeparated"
        [ testCase "hasPositionSeparated - returns True when position is separated" $ do
            let sepDims = SeparateDimensions True False
            let transform = createTestTransform (Just sepDims)
            let layer = createTestLayer "layer1" transform Nothing []
            let result = hasPositionSeparated layer
            assertBool "Should return True" result
        , testCase "hasPositionSeparated - returns False when position is not separated" $ do
            let sepDims = SeparateDimensions False False
            let transform = createTestTransform (Just sepDims)
            let layer = createTestLayer "layer1" transform Nothing []
            let result = hasPositionSeparated layer
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "hasScaleSeparated"
        [ testCase "hasScaleSeparated - returns True when scale is separated" $ do
            let sepDims = SeparateDimensions False True
            let transform = createTestTransform (Just sepDims)
            let layer = createTestLayer "layer1" transform Nothing []
            let result = hasScaleSeparated layer
            assertBool "Should return True" result
        , testCase "hasScaleSeparated - returns False when scale is not separated" $ do
            let sepDims = SeparateDimensions False False
            let transform = createTestTransform (Just sepDims)
            let layer = createTestLayer "layer1" transform Nothing []
            let result = hasScaleSeparated layer
            assertBool "Should return False" (not result)
        ]
    ]
