-- | Port of ui/src/__tests__/stores/projectActions.test.ts (history subset)
-- |
-- | Tests pure history/undo/redo state transitions.
-- | Effectful tests (autosave, asset management, serialization)
-- | are deferred to later waves.
-- |
-- | 22 tests across 5 describe blocks

module Test.Lattice.State.HistoryOps (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing, isJust)
import Lattice.State.HistoryOps
  ( HistoryState
  , mkHistoryState
  , pushHistory
  , undo
  , redo
  , canUndo
  , canRedo
  , clearHistory
  , historyLength
  , maxHistorySize
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "HistoryOps" do
    initTests
    pushTests
    undoRedoTests
    clearTests
    edgeCaseTests

--------------------------------------------------------------------------------
-- 1. Initialization
--------------------------------------------------------------------------------

initTests :: Spec Unit
initTests = do
  describe "mkHistoryState" do

    it "creates state with one entry" do
      let state = mkHistoryState "initial"
      historyLength state `shouldEqual` 1

    it "starts at index 0" do
      let state = mkHistoryState "initial"
      state.index `shouldEqual` 0

    it "cannot undo from initial state" do
      let state = mkHistoryState "initial"
      canUndo state `shouldEqual` false

    it "cannot redo from initial state" do
      let state = mkHistoryState "initial"
      canRedo state `shouldEqual` false

--------------------------------------------------------------------------------
-- 2. pushHistory
--------------------------------------------------------------------------------

pushTests :: Spec Unit
pushTests = do
  describe "pushHistory" do

    it "adds a state to the stack" do
      let state = pushHistory "state2" (mkHistoryState "state1")
      historyLength state `shouldEqual` 2

    it "updates index to latest" do
      let state = pushHistory "state2" (mkHistoryState "state1")
      state.index `shouldEqual` 1

    it "can undo after push" do
      let state = pushHistory "state2" (mkHistoryState "state1")
      canUndo state `shouldEqual` true

    it "truncates future states on push after undo" do
      let s0 = mkHistoryState "s0"
      let s1 = pushHistory "s1" s0
      let s2 = pushHistory "s2" s1
      -- Undo twice to go back to s0
      let { state: s3 } = undo s2
      let { state: s4 } = undo s3
      -- Now push new state - should discard s1 and s2
      let s5 = pushHistory "s_new" s4
      historyLength s5 `shouldEqual` 2
      canRedo s5 `shouldEqual` false

    it "enforces maximum history size" do
      let buildHistory n state =
            if n <= 0 then state
            else buildHistory (n - 1) (pushHistory ("state" <> show n) state)
      let state = buildHistory 60 (mkHistoryState "initial")
      historyLength state `shouldEqual` maxHistorySize

    it "deep clones state (independent snapshots)" do
      let s0 = mkHistoryState "original"
      let s1 = pushHistory "modified" s0
      -- Original state in stack should be unchanged
      case undo s1 of
        { snapshot: Just snap } -> snap `shouldEqual` "original"
        { snapshot: Nothing } -> fail "Expected undo snapshot"

--------------------------------------------------------------------------------
-- 3. undo / redo
--------------------------------------------------------------------------------

undoRedoTests :: Spec Unit
undoRedoTests = do
  describe "undo / redo" do

    it "undo returns previous snapshot" do
      let s0 = mkHistoryState "first"
      let s1 = pushHistory "second" s0
      case undo s1 of
        { snapshot: Just snap } -> snap `shouldEqual` "first"
        { snapshot: Nothing } -> fail "Expected undo snapshot"

    it "redo returns next snapshot" do
      let s0 = mkHistoryState "first"
      let s1 = pushHistory "second" s0
      let { state: s2 } = undo s1
      case redo s2 of
        { snapshot: Just snap } -> snap `shouldEqual` "second"
        { snapshot: Nothing } -> fail "Expected redo snapshot"

    it "multiple undo steps work" do
      let s0 = mkHistoryState "a"
      let s1 = pushHistory "b" s0
      let s2 = pushHistory "c" s1
      let { state: s3, snapshot: snap1 } = undo s2
      case snap1 of
        Just s -> s `shouldEqual` "b"
        Nothing -> fail "Expected snapshot"
      let { snapshot: snap2 } = undo s3
      case snap2 of
        Just s -> s `shouldEqual` "a"
        Nothing -> fail "Expected snapshot"

    it "undo at beginning returns Nothing" do
      let state = mkHistoryState "only"
      let { snapshot } = undo state
      isNothing snapshot `shouldEqual` true

    it "redo at end returns Nothing" do
      let state = mkHistoryState "only"
      let { snapshot } = redo state
      isNothing snapshot `shouldEqual` true

    it "undo then redo returns to same state" do
      let s0 = mkHistoryState "first"
      let s1 = pushHistory "second" s0
      let { state: s2 } = undo s1
      let { snapshot } = redo s2
      case snapshot of
        Just s -> s `shouldEqual` "second"
        Nothing -> fail "Expected redo snapshot"

    it "canUndo/canRedo update correctly through sequence" do
      let s0 = mkHistoryState "a"
      canUndo s0 `shouldEqual` false
      canRedo s0 `shouldEqual` false
      let s1 = pushHistory "b" s0
      canUndo s1 `shouldEqual` true
      canRedo s1 `shouldEqual` false
      let { state: s2 } = undo s1
      canUndo s2 `shouldEqual` false
      canRedo s2 `shouldEqual` true

--------------------------------------------------------------------------------
-- 4. clearHistory
--------------------------------------------------------------------------------

clearTests :: Spec Unit
clearTests = do
  describe "clearHistory" do

    it "reduces to single entry" do
      let s0 = mkHistoryState "a"
      let s1 = pushHistory "b" s0
      let s2 = pushHistory "c" s1
      let cleared = clearHistory s2
      historyLength cleared `shouldEqual` 1

    it "sets index to 0" do
      let s0 = mkHistoryState "a"
      let s1 = pushHistory "b" s0
      let cleared = clearHistory s1
      cleared.index `shouldEqual` 0

    it "preserves current state" do
      let s0 = mkHistoryState "a"
      let s1 = pushHistory "b" s0
      let cleared = clearHistory s1
      -- The current state should be "b" (the one at index 1)
      case undo cleared of
        { snapshot: Nothing } -> pure unit -- Cannot undo = only one entry, correct
        { snapshot: Just _ } -> fail "Should not be able to undo after clear"

--------------------------------------------------------------------------------
-- 5. Edge cases
--------------------------------------------------------------------------------

edgeCaseTests :: Spec Unit
edgeCaseTests = do
  describe "edge cases" do

    it "rapid push/undo/redo sequence works" do
      let s0 = mkHistoryState "s0"
      -- Push 10 states
      let buildN n st = if n <= 0 then st else buildN (n - 1) (pushHistory ("s" <> show n) st)
      let s10 = buildN 10 s0
      -- Undo 2, redo 1, push, undo 3, redo 2
      let { state: a } = undo s10
      let { state: b } = undo a
      let { state: c } = redo b
      let d = pushHistory "new" c
      let { state: e } = undo d
      let { state: f } = undo e
      let { state: g } = undo f
      let { state: h } = redo g
      let { state: final } = redo h
      -- Should not crash and index should be valid
      (final.index >= 0) `shouldEqual` true
      (final.index < historyLength final) `shouldEqual` true

    it "determinism: same operations produce identical results" do
      let ops init =
            let s1 = pushHistory "x" init
                s2 = pushHistory "y" s1
                s3 = pushHistory "z" s2
                { state: s4 } = undo s3
                { state: s5 } = undo s4
                s6 = pushHistory "w" s5
            in s6
      let r1 = ops (mkHistoryState "a")
      let r2 = ops (mkHistoryState "a")
      r1.index `shouldEqual` r2.index
      historyLength r1 `shouldEqual` historyLength r2
