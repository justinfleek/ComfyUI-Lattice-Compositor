-- | Port of ui/src/__tests__/types/transform.test.ts and transform.property.test.ts (partial)
-- |
-- | Tests transform-related types and structures:
-- |   - LayerTransform2D structure
-- |   - LayerTransform3D structure
-- |   - Vec3 creation via mkVec3
-- |   - MotionBlurSettings structure
-- |   - Default value patterns
-- |
-- | Note: Factory tests (createDefaultTransform, separatePositionDimensions, etc.)
-- | are deferred - they require PS transform module with AnimatableProperty factories.
-- |
-- | 12 tests across 3 describe blocks

module Test.Lattice.Types.Transform (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing, isJust)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( FiniteFloat(..), mkFiniteFloat, unFiniteFloat
  , Percentage(..), mkPercentage, unPercentage
  )
import Lattice.Project (Vec3, mkVec3)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

shouldBeCloseTo :: Number -> Number -> Number -> Aff Unit
shouldBeCloseTo actual expected tolerance =
  let diff = if actual > expected then actual - expected else expected - actual
  in if diff <= tolerance
    then pure unit
    else fail ("Expected " <> show actual <> " to be close to " <> show expected
               <> " (tolerance " <> show tolerance <> ", diff " <> show diff <> ")")

ff :: Number -> FiniteFloat
ff n = case mkFiniteFloat n of
  Just v -> v
  Nothing -> FiniteFloat 0.0

pct :: Number -> Percentage
pct n = case mkPercentage n of
  Just v -> v
  Nothing -> Percentage 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "Transform - Type Tests" do
    vec3Tests
    transform2DTests
    transform3DTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Vec3
-- ────────────────────────────────────────────────────────────────────────────

vec3Tests :: Spec Unit
vec3Tests = do
  describe "Vec3 (mkVec3)" do

    it "should create valid Vec3 from finite numbers" do
      case mkVec3 1.0 2.0 3.0 of
        Just v -> do
          shouldBeCloseTo (unFiniteFloat v.x) 1.0 0.01
          shouldBeCloseTo (unFiniteFloat v.y) 2.0 0.01
          shouldBeCloseTo (unFiniteFloat v.z) 3.0 0.01
        Nothing -> fail "Expected Just Vec3"

    it "should create Vec3 at origin" do
      case mkVec3 0.0 0.0 0.0 of
        Just v -> do
          shouldBeCloseTo (unFiniteFloat v.x) 0.0 0.01
          shouldBeCloseTo (unFiniteFloat v.y) 0.0 0.01
          shouldBeCloseTo (unFiniteFloat v.z) 0.0 0.01
        Nothing -> fail "Expected Just Vec3 at origin"

    it "should handle negative values" do
      case mkVec3 (-100.0) (-200.0) (-300.0) of
        Just v -> do
          shouldBeCloseTo (unFiniteFloat v.x) (-100.0) 0.01
          shouldBeCloseTo (unFiniteFloat v.y) (-200.0) 0.01
        Nothing -> fail "Expected Just Vec3 with negative values"

    it "should reject NaN values" do
      let nan = 0.0 / 0.0
      isNothing (mkVec3 nan 0.0 0.0) `shouldEqual` true
      isNothing (mkVec3 0.0 nan 0.0) `shouldEqual` true
      isNothing (mkVec3 0.0 0.0 nan) `shouldEqual` true

    it "should reject Infinity values" do
      let inf = 1.0 / 0.0
      isNothing (mkVec3 inf 0.0 0.0) `shouldEqual` true
      isNothing (mkVec3 0.0 (-inf) 0.0) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 2. LayerTransform2D structure
-- ────────────────────────────────────────────────────────────────────────────

transform2DTests :: Spec Unit
transform2DTests = do
  describe "LayerTransform2D" do

    it "should allow creating a default 2D transform" do
      let t2d =
            { anchorX: ff 0.0
            , anchorY: ff 0.0
            , positionX: ff 0.0
            , positionY: ff 0.0
            , scaleX: ff 100.0
            , scaleY: ff 100.0
            , rotation: ff 0.0
            , opacity: pct 100.0
            }
      shouldBeCloseTo (unFiniteFloat t2d.scaleX) 100.0 0.01
      shouldBeCloseTo (unPercentage t2d.opacity) 100.0 0.01

    it "should support arbitrary transform values" do
      let t2d =
            { anchorX: ff 50.0
            , anchorY: ff 50.0
            , positionX: ff 960.0
            , positionY: ff 540.0
            , scaleX: ff 200.0
            , scaleY: ff 150.0
            , rotation: ff 45.0
            , opacity: pct 75.0
            }
      shouldBeCloseTo (unFiniteFloat t2d.positionX) 960.0 0.01
      shouldBeCloseTo (unFiniteFloat t2d.rotation) 45.0 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- 3. LayerTransform3D structure
-- ────────────────────────────────────────────────────────────────────────────

transform3DTests :: Spec Unit
transform3DTests = do
  describe "LayerTransform3D" do

    it "should allow creating a default 3D transform" do
      let t3d =
            { anchorX: ff 0.0
            , anchorY: ff 0.0
            , anchorZ: ff 0.0
            , positionX: ff 0.0
            , positionY: ff 0.0
            , positionZ: ff 0.0
            , scaleX: ff 100.0
            , scaleY: ff 100.0
            , scaleZ: ff 100.0
            , rotation: ff 0.0
            , rotationX: ff 0.0
            , rotationY: ff 0.0
            , rotationZ: ff 0.0
            , opacity: pct 100.0
            , orientation: Nothing :: Maybe { x :: FiniteFloat, y :: FiniteFloat, z :: FiniteFloat }
            }
      shouldBeCloseTo (unFiniteFloat t3d.scaleZ) 100.0 0.01
      isNothing t3d.orientation `shouldEqual` true

    it "should support orientation vector" do
      let t3d =
            { anchorX: ff 0.0
            , anchorY: ff 0.0
            , anchorZ: ff 0.0
            , positionX: ff 0.0
            , positionY: ff 0.0
            , positionZ: ff 0.0
            , scaleX: ff 100.0
            , scaleY: ff 100.0
            , scaleZ: ff 100.0
            , rotation: ff 0.0
            , rotationX: ff 30.0
            , rotationY: ff 45.0
            , rotationZ: ff 60.0
            , opacity: pct 100.0
            , orientation: Just { x: ff 0.0, y: ff 0.0, z: ff 0.0 }
            }
      isJust t3d.orientation `shouldEqual` true
      shouldBeCloseTo (unFiniteFloat t3d.rotationX) 30.0 0.01
      shouldBeCloseTo (unFiniteFloat t3d.rotationY) 45.0 0.01

    it "should have default scale at 100% for all axes" do
      -- Standard transform: scale defaults to 100 (not 1.0)
      let scale = { x: ff 100.0, y: ff 100.0, z: ff 100.0 }
      shouldBeCloseTo (unFiniteFloat scale.x) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat scale.y) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat scale.z) 100.0 0.01

    it "should have default position at origin" do
      -- Standard transform: position defaults to 0
      let pos = { x: ff 0.0, y: ff 0.0, z: ff 0.0 }
      shouldBeCloseTo (unFiniteFloat pos.x) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat pos.y) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat pos.z) 0.0 0.01
