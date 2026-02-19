-- |
-- Module      : Lattice.State.AudioSyncSpec
-- Description : Test suite for audio synchronization state management
--

module Lattice.State.AudioSyncSpec (spec) where

import Data.Text (Text)
import Lattice.State.AudioSync
  ( checkAudioStateSync
  , AudioState(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.AudioSync"
    [ testGroup
        "checkAudioStateSync"
        [ testCase "checkAudioStateSync - returns True for identical states" $ do
            let stateA = AudioState (Just "buffer1") (Just "file1")
            let stateB = AudioState (Just "buffer1") (Just "file1")
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return True" result
        , testCase "checkAudioStateSync - returns False for different buffers" $ do
            let stateA = AudioState (Just "buffer1") (Just "file1")
            let stateB = AudioState (Just "buffer2") (Just "file1")
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return False" (not result)
        , testCase "checkAudioStateSync - returns False for different files" $ do
            let stateA = AudioState (Just "buffer1") (Just "file1")
            let stateB = AudioState (Just "buffer1") (Just "file2")
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return False" (not result)
        , testCase "checkAudioStateSync - returns True when both buffers are null" $ do
            let stateA = AudioState Nothing (Just "file1")
            let stateB = AudioState Nothing (Just "file1")
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return True" result
        , testCase "checkAudioStateSync - returns False when one buffer is null" $ do
            let stateA = AudioState (Just "buffer1") (Just "file1")
            let stateB = AudioState Nothing (Just "file1")
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return False" (not result)
        , testCase "checkAudioStateSync - returns True when both files are null" $ do
            let stateA = AudioState (Just "buffer1") Nothing
            let stateB = AudioState (Just "buffer1") Nothing
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return True" result
        , testCase "checkAudioStateSync - returns False when one file is null" $ do
            let stateA = AudioState (Just "buffer1") (Just "file1")
            let stateB = AudioState (Just "buffer1") Nothing
            let result = checkAudioStateSync stateA stateB
            assertBool "Should return False" (not result)
        ]
    ]
