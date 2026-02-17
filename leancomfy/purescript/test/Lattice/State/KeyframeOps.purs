-- | Port of ui/src/__tests__/stores/keyframeActions.test.ts
-- |        + keyframeStore.property.test.ts
-- |        + keyframeActions.property.test.ts (pure invariant subset)
-- |
-- | Tests pure keyframe CRUD, query, and timing operations.
-- | Store-coupled tests (findPropertyByPath, dimension separation,
-- | advanced systems, all-layers, mesh-warp-pose, timewarp-text-audio)
-- | are deferred to later waves requiring state infrastructure.
-- |
-- | 45 tests across 9 describe blocks

module Test.Lattice.State.KeyframeOps (spec) where

import Prelude

import Data.Array (length, index, all, sort)
import Data.Maybe (Maybe(..), isNothing, isJust)
import Effect.Aff (Aff)
import Lattice.Primitives (FiniteFloat(..), FrameNumber(..), NonEmptyString(..), mkNonEmptyString)
import Lattice.Entities (Keyframe, ControlMode(..), BezierHandle)
import Lattice.Enums (InterpolationType(..))
import Lattice.State.KeyframeOps
  ( addKeyframe
  , removeKeyframe
  , clearKeyframes
  , moveKeyframe
  , moveKeyframes
  , setKeyframeValue
  , setKeyframeInterpolation
  , getKeyframesAtFrame
  , getAllKeyframeFrames
  , findNextKeyframeFrame
  , findPrevKeyframeFrame
  , findSurroundingKeyframes
  , scaleKeyframeTiming
  , timeReverseKeyframes
  , sortKeyframes
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

nes :: String -> NonEmptyString
nes s = case mkNonEmptyString s of
  Just v -> v
  Nothing -> NonEmptyString "error"

ff :: Number -> FiniteFloat
ff = FiniteFloat

defaultHandle :: BezierHandle
defaultHandle = { frame: ff 0.0, value: ff 0.0, enabled: true }

mkKf :: String -> Int -> String -> Keyframe
mkKf id frame value =
  { id: nes id
  , frame: FrameNumber frame
  , value: value
  , interpolation: ITLinear
  , inHandle: defaultHandle
  , outHandle: defaultHandle
  , controlMode: CMSmooth
  }

mkKfInterp :: String -> Int -> String -> InterpolationType -> Keyframe
mkKfInterp id frame value interp =
  { id: nes id
  , frame: FrameNumber frame
  , value: value
  , interpolation: interp
  , inHandle: defaultHandle
  , outHandle: defaultHandle
  , controlMode: CMSmooth
  }

assertSorted :: Array Keyframe -> Aff Unit
assertSorted kfs = do
  let frames = map (\k -> let FrameNumber f = k.frame in f) kfs
  assertFramesSorted frames 0

assertFramesSorted :: Array Int -> Int -> Aff Unit
assertFramesSorted frames idx =
  case { curr: index frames idx, next: index frames (idx + 1) } of
    { curr: Just a, next: Just b } ->
      if a <= b then assertFramesSorted frames (idx + 1)
      else fail ("Keyframes not sorted: frame " <> show a <> " > " <> show b <> " at index " <> show idx)
    _ -> pure unit

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "KeyframeOps" do
    addKeyframeTests
    removeKeyframeTests
    clearKeyframesTests
    moveKeyframeTests
    moveKeyframesTests
    setValueTests
    queryTests
    timingTests
    propertyInvariantTests

--------------------------------------------------------------------------------
-- 1. addKeyframe
--------------------------------------------------------------------------------

addKeyframeTests :: Spec Unit
addKeyframeTests = do
  describe "addKeyframe" do

    it "adds a keyframe to empty array" do
      let kf = mkKf "kf1" 10 "hello"
      let result = addKeyframe kf []
      length result `shouldEqual` 1

    it "keeps keyframes sorted by frame" do
      let kf1 = mkKf "kf1" 30 "a"
      let kf2 = mkKf "kf2" 10 "b"
      let kf3 = mkKf "kf3" 20 "c"
      let result = addKeyframe kf3 (addKeyframe kf2 (addKeyframe kf1 []))
      assertSorted result
      length result `shouldEqual` 3

    it "replaces keyframe at same frame" do
      let kf1 = mkKf "kf1" 10 "original"
      let kf2 = mkKf "kf2" 10 "replacement"
      let result = addKeyframe kf2 [kf1]
      length result `shouldEqual` 1
      case index result 0 of
        Just k -> k.value `shouldEqual` "replacement"
        Nothing -> fail "Expected one keyframe"

    it "handles multiple keyframes at different frames" do
      let kfs = addKeyframe (mkKf "kf5" 50 "e")
              $ addKeyframe (mkKf "kf4" 40 "d")
              $ addKeyframe (mkKf "kf3" 30 "c")
              $ addKeyframe (mkKf "kf2" 20 "b")
              $ addKeyframe (mkKf "kf1" 10 "a") []
      length kfs `shouldEqual` 5
      assertSorted kfs

    it "preserves interpolation type" do
      let kf = mkKfInterp "kf1" 10 "v" ITBezier
      let result = addKeyframe kf []
      case index result 0 of
        Just k -> k.interpolation `shouldEqual` ITBezier
        Nothing -> fail "Expected one keyframe"

--------------------------------------------------------------------------------
-- 2. removeKeyframe
--------------------------------------------------------------------------------

removeKeyframeTests :: Spec Unit
removeKeyframeTests = do
  describe "removeKeyframe" do

    it "removes keyframe by ID" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      case removeKeyframe (nes "kf2") kfs of
        Just result -> do
          length result `shouldEqual` 2
        Nothing -> fail "Expected removal to succeed"

    it "returns Nothing when ID not found" do
      let kfs = [mkKf "kf1" 10 "a"]
      isNothing (removeKeyframe (nes "nonexistent") kfs) `shouldEqual` true

    it "handles empty array" do
      isNothing (removeKeyframe (nes "kf1") []) `shouldEqual` true

    it "removes last keyframe" do
      let kfs = [mkKf "kf1" 10 "a"]
      case removeKeyframe (nes "kf1") kfs of
        Just result -> length result `shouldEqual` 0
        Nothing -> fail "Expected removal to succeed"

    it "preserves other keyframes" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      case removeKeyframe (nes "kf2") kfs of
        Just result -> do
          case index result 0 of
            Just k -> k.value `shouldEqual` "a"
            Nothing -> fail "Expected first keyframe"
          case index result 1 of
            Just k -> k.value `shouldEqual` "c"
            Nothing -> fail "Expected second keyframe"
        Nothing -> fail "Expected removal to succeed"

--------------------------------------------------------------------------------
-- 3. clearKeyframes
--------------------------------------------------------------------------------

clearKeyframesTests :: Spec Unit
clearKeyframesTests = do
  describe "clearKeyframes" do

    it "clears all keyframes" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      length (clearKeyframes kfs) `shouldEqual` 0

    it "handles empty array" do
      length (clearKeyframes []) `shouldEqual` 0

--------------------------------------------------------------------------------
-- 4. moveKeyframe
--------------------------------------------------------------------------------

moveKeyframeTests :: Spec Unit
moveKeyframeTests = do
  describe "moveKeyframe" do

    it "moves keyframe to new frame" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let result = moveKeyframe (nes "kf1") (FrameNumber 15) kfs
      assertSorted result
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 15
        Nothing -> fail "Expected keyframe"

    it "clamps to frame 0" do
      let kfs = [mkKf "kf1" 10 "a"]
      let result = moveKeyframe (nes "kf1") (FrameNumber (-5)) kfs
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 0
        Nothing -> fail "Expected keyframe"

    it "returns unchanged if ID not found" do
      let kfs = [mkKf "kf1" 10 "a"]
      let result = moveKeyframe (nes "nonexistent") (FrameNumber 20) kfs
      length result `shouldEqual` 1
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected keyframe"

    it "maintains sort order after move" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      let result = moveKeyframe (nes "kf1") (FrameNumber 25) kfs
      assertSorted result

    it "preserves value when moving" do
      let kfs = [mkKf "kf1" 10 "original_value"]
      let result = moveKeyframe (nes "kf1") (FrameNumber 20) kfs
      case index result 0 of
        Just k -> k.value `shouldEqual` "original_value"
        Nothing -> fail "Expected keyframe"

--------------------------------------------------------------------------------
-- 5. moveKeyframes (batch)
--------------------------------------------------------------------------------

moveKeyframesTests :: Spec Unit
moveKeyframesTests = do
  describe "moveKeyframes (batch)" do

    it "moves multiple keyframes by delta" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      let moves = [{ id: nes "kf1", delta: 5 }, { id: nes "kf2", delta: 5 }]
      let result = moveKeyframes moves kfs
      assertSorted result
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 15
        Nothing -> fail "Expected keyframe"

    it "clamps negative frames to 0" do
      let kfs = [mkKf "kf1" 5 "a", mkKf "kf2" 10 "b"]
      let moves = [{ id: nes "kf1", delta: -10 }, { id: nes "kf2", delta: -10 }]
      let result = moveKeyframes moves kfs
      -- Both should be clamped to 0
      let allNonNeg = all (\k -> let FrameNumber f = k.frame in f >= 0) result
      allNonNeg `shouldEqual` true

    it "ignores moves for non-existent IDs" do
      let kfs = [mkKf "kf1" 10 "a"]
      let moves = [{ id: nes "nonexistent", delta: 5 }]
      let result = moveKeyframes moves kfs
      length result `shouldEqual` 1
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected keyframe"

    it "delta of 0 preserves frames" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let moves = [{ id: nes "kf1", delta: 0 }, { id: nes "kf2", delta: 0 }]
      let result = moveKeyframes moves kfs
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected first keyframe"
      case index result 1 of
        Just k -> k.frame `shouldEqual` FrameNumber 20
        Nothing -> fail "Expected second keyframe"

--------------------------------------------------------------------------------
-- 6. setKeyframeValue / setKeyframeInterpolation
--------------------------------------------------------------------------------

setValueTests :: Spec Unit
setValueTests = do
  describe "setKeyframeValue / setKeyframeInterpolation" do

    it "updates value by ID" do
      let kfs = [mkKf "kf1" 10 "old"]
      let result = setKeyframeValue (nes "kf1") "new" kfs
      case index result 0 of
        Just k -> k.value `shouldEqual` "new"
        Nothing -> fail "Expected keyframe"

    it "does not affect other keyframes" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let result = setKeyframeValue (nes "kf1") "updated" kfs
      case index result 1 of
        Just k -> k.value `shouldEqual` "b"
        Nothing -> fail "Expected second keyframe"

    it "updates interpolation type" do
      let kfs = [mkKf "kf1" 10 "a"]
      let result = setKeyframeInterpolation (nes "kf1") ITBezier kfs
      case index result 0 of
        Just k -> k.interpolation `shouldEqual` ITBezier
        Nothing -> fail "Expected keyframe"

    it "can set to hold interpolation" do
      let kfs = [mkKf "kf1" 10 "a"]
      let result = setKeyframeInterpolation (nes "kf1") ITHold kfs
      case index result 0 of
        Just k -> k.interpolation `shouldEqual` ITHold
        Nothing -> fail "Expected keyframe"

--------------------------------------------------------------------------------
-- 7. Queries
--------------------------------------------------------------------------------

queryTests :: Spec Unit
queryTests = do
  describe "queries" do

    it "getKeyframesAtFrame returns matching keyframes" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 10 "b", mkKf "kf3" 20 "c"]
      let result = getKeyframesAtFrame (FrameNumber 10) kfs
      length result `shouldEqual` 2

    it "getKeyframesAtFrame returns empty for no match" do
      let kfs = [mkKf "kf1" 10 "a"]
      let result = getKeyframesAtFrame (FrameNumber 99) kfs
      length result `shouldEqual` 0

    it "getAllKeyframeFrames returns sorted unique frames" do
      let kfs = [mkKf "kf1" 30 "a", mkKf "kf2" 10 "b", mkKf "kf3" 10 "c", mkKf "kf4" 20 "d"]
      let result = getAllKeyframeFrames kfs
      length result `shouldEqual` 3
      case index result 0 of
        Just f -> f `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected first frame"
      case index result 2 of
        Just f -> f `shouldEqual` FrameNumber 30
        Nothing -> fail "Expected last frame"

    it "findNextKeyframeFrame finds next frame" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      findNextKeyframeFrame (FrameNumber 15) kfs `shouldEqual` Just (FrameNumber 20)

    it "findNextKeyframeFrame returns Nothing at end" do
      let kfs = [mkKf "kf1" 10 "a"]
      findNextKeyframeFrame (FrameNumber 10) kfs `shouldEqual` Nothing

    it "findPrevKeyframeFrame finds previous frame" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      findPrevKeyframeFrame (FrameNumber 25) kfs `shouldEqual` Just (FrameNumber 20)

    it "findPrevKeyframeFrame returns Nothing at start" do
      let kfs = [mkKf "kf1" 10 "a"]
      findPrevKeyframeFrame (FrameNumber 10) kfs `shouldEqual` Nothing

    it "findSurroundingKeyframes finds both neighbors" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      let result = findSurroundingKeyframes (FrameNumber 15) kfs
      isJust result.before `shouldEqual` true
      isJust result.after `shouldEqual` true
      case result.before of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected before"
      case result.after of
        Just k -> k.frame `shouldEqual` FrameNumber 20
        Nothing -> fail "Expected after"

    it "findSurroundingKeyframes returns Nothing when no neighbors" do
      let result = findSurroundingKeyframes (FrameNumber 10) []
      isNothing result.before `shouldEqual` true
      isNothing result.after `shouldEqual` true

--------------------------------------------------------------------------------
-- 8. Timing
--------------------------------------------------------------------------------

timingTests :: Spec Unit
timingTests = do
  describe "timing" do

    it "scaleKeyframeTiming scales frames around anchor" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b", mkKf "kf3" 30 "c"]
      let result = scaleKeyframeTiming 2.0 (FrameNumber 10) kfs
      -- kf1 stays at 10 (anchor), kf2 goes to 30, kf3 goes to 50
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected first keyframe"
      case index result 1 of
        Just k -> k.frame `shouldEqual` FrameNumber 30
        Nothing -> fail "Expected second keyframe"
      case index result 2 of
        Just k -> k.frame `shouldEqual` FrameNumber 50
        Nothing -> fail "Expected third keyframe"

    it "scaleKeyframeTiming clamps to 0" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      -- Scale by -1 around frame 0: 10 -> -10 -> clamp to 0
      let result = scaleKeyframeTiming (-1.0) (FrameNumber 0) kfs
      let allNonNeg = all (\k -> let FrameNumber f = k.frame in f >= 0) result
      allNonNeg `shouldEqual` true

    it "scaleKeyframeTiming with factor 1.0 preserves frames" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let result = scaleKeyframeTiming 1.0 (FrameNumber 0) kfs
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected first keyframe"
      case index result 1 of
        Just k -> k.frame `shouldEqual` FrameNumber 20
        Nothing -> fail "Expected second keyframe"

    it "timeReverseKeyframes reverses values but keeps frames" do
      let kfs = [mkKf "kf1" 10 "first", mkKf "kf2" 20 "second", mkKf "kf3" 30 "third"]
      let result = timeReverseKeyframes kfs
      -- Frames stay: 10, 20, 30 but values reverse: third, second, first
      case index result 0 of
        Just k -> do
          k.frame `shouldEqual` FrameNumber 10
          k.value `shouldEqual` "third"
        Nothing -> fail "Expected first keyframe"
      case index result 1 of
        Just k -> do
          k.frame `shouldEqual` FrameNumber 20
          k.value `shouldEqual` "second"
        Nothing -> fail "Expected second keyframe"
      case index result 2 of
        Just k -> do
          k.frame `shouldEqual` FrameNumber 30
          k.value `shouldEqual` "first"
        Nothing -> fail "Expected third keyframe"

    it "timeReverseKeyframes handles empty array" do
      length (timeReverseKeyframes []) `shouldEqual` 0

    it "timeReverseKeyframes handles single keyframe" do
      let kfs = [mkKf "kf1" 10 "only"]
      let result = timeReverseKeyframes kfs
      length result `shouldEqual` 1
      case index result 0 of
        Just k -> k.value `shouldEqual` "only"
        Nothing -> fail "Expected keyframe"

--------------------------------------------------------------------------------
-- 9. Property-based invariants (deterministic assertions)
--------------------------------------------------------------------------------

propertyInvariantTests :: Spec Unit
propertyInvariantTests = do
  describe "property invariants" do

    it "addKeyframe always produces sorted output" do
      -- Build up keyframes in reverse order
      let kfs = addKeyframe (mkKf "kf1" 50 "e")
              $ addKeyframe (mkKf "kf2" 40 "d")
              $ addKeyframe (mkKf "kf3" 30 "c")
              $ addKeyframe (mkKf "kf4" 20 "b")
              $ addKeyframe (mkKf "kf5" 10 "a") []
      assertSorted kfs

    it "moveKeyframes preserves values" do
      let kfs = [mkKf "kf1" 10 "val_a", mkKf "kf2" 20 "val_b", mkKf "kf3" 30 "val_c"]
      let moves = [{ id: nes "kf1", delta: 5 }, { id: nes "kf2", delta: 5 }, { id: nes "kf3", delta: 5 }]
      let result = moveKeyframes moves kfs
      -- All values should be preserved
      let vals = sort (map _.value result)
      vals `shouldEqual` ["val_a", "val_b", "val_c"]

    it "moveKeyframes always produces non-negative frames" do
      let kfs = [mkKf "kf1" 5 "a", mkKf "kf2" 10 "b", mkKf "kf3" 100 "c"]
      let moves = [{ id: nes "kf1", delta: -100 }, { id: nes "kf2", delta: -100 }, { id: nes "kf3", delta: -100 }]
      let result = moveKeyframes moves kfs
      let allNonNeg = all (\k -> let FrameNumber f = k.frame in f >= 0) result
      allNonNeg `shouldEqual` true

    it "moveKeyframes with delta 0 is identity" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let moves = [{ id: nes "kf1", delta: 0 }, { id: nes "kf2", delta: 0 }]
      let result = moveKeyframes moves kfs
      length result `shouldEqual` 2
      case index result 0 of
        Just k -> k.frame `shouldEqual` FrameNumber 10
        Nothing -> fail "Expected first keyframe"
      case index result 1 of
        Just k -> k.frame `shouldEqual` FrameNumber 20
        Nothing -> fail "Expected second keyframe"

    it "sortKeyframes is idempotent" do
      let kfs = [mkKf "kf1" 30 "a", mkKf "kf2" 10 "b", mkKf "kf3" 20 "c"]
      let sorted1 = sortKeyframes kfs
      let sorted2 = sortKeyframes sorted1
      length sorted1 `shouldEqual` length sorted2
      case { a: index sorted1 0, b: index sorted2 0 } of
        { a: Just a, b: Just b } -> a.frame `shouldEqual` b.frame
        _ -> fail "Expected keyframes"

    it "clearKeyframes then add produces single keyframe" do
      let kfs = [mkKf "kf1" 10 "a", mkKf "kf2" 20 "b"]
      let cleared = clearKeyframes kfs
      let result = addKeyframe (mkKf "kf3" 15 "new") cleared
      length result `shouldEqual` 1

    it "determinism: same operations produce identical results" do
      let ops kfs = addKeyframe (mkKf "kf3" 25 "c")
                  $ addKeyframe (mkKf "kf2" 15 "b")
                  $ addKeyframe (mkKf "kf1" 5 "a") kfs
      let result1 = ops []
      let result2 = ops []
      length result1 `shouldEqual` length result2
      case { a: index result1 0, b: index result2 0 } of
        { a: Just a, b: Just b } -> do
          a.frame `shouldEqual` b.frame
          a.value `shouldEqual` b.value
        _ -> fail "Expected keyframes"
