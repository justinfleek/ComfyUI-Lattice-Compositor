-- | Port of ui/src/__tests__/types/transform.property.test.ts (partial)
-- |
-- | Tests transform type properties:
-- |   - LayerTransform2D structure defaults
-- |   - LayerTransform3D structure defaults
-- |   - Vec3 creation properties
-- |   - Transform determinism
-- |
-- | Note: Dimension separation/linking tests (separatePositionDimensions,
-- | linkPositionDimensions, etc.) are deferred - they require PS transform
-- | module with AnimatableProperty mutation equivalents.
-- |
-- | 15 tests across 3 describe blocks

module Test.Lattice.Types.TransformProps (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing, isJust)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( FiniteFloat(..), Percentage(..)
  , mkFiniteFloat, mkPercentage
  , unFiniteFloat, unPercentage
  )
import Lattice.Project (Vec3, mkVec3)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Default transform constructors (pure, no AnimatableProperty)
--------------------------------------------------------------------------------

defaultTransform2D
  :: { anchorX :: FiniteFloat, anchorY :: FiniteFloat
     , positionX :: FiniteFloat, positionY :: FiniteFloat
     , scaleX :: FiniteFloat, scaleY :: FiniteFloat
     , rotation :: FiniteFloat, opacity :: Percentage
     }
defaultTransform2D =
  { anchorX: ff 0.0, anchorY: ff 0.0
  , positionX: ff 0.0, positionY: ff 0.0
  , scaleX: ff 100.0, scaleY: ff 100.0
  , rotation: ff 0.0, opacity: pct 100.0
  }

defaultTransform3D
  :: { anchorX :: FiniteFloat, anchorY :: FiniteFloat, anchorZ :: FiniteFloat
     , positionX :: FiniteFloat, positionY :: FiniteFloat, positionZ :: FiniteFloat
     , scaleX :: FiniteFloat, scaleY :: FiniteFloat, scaleZ :: FiniteFloat
     , rotation :: FiniteFloat
     , rotationX :: FiniteFloat, rotationY :: FiniteFloat, rotationZ :: FiniteFloat
     , opacity :: Percentage
     , orientation :: Maybe { x :: FiniteFloat, y :: FiniteFloat, z :: FiniteFloat }
     }
defaultTransform3D =
  { anchorX: ff 0.0, anchorY: ff 0.0, anchorZ: ff 0.0
  , positionX: ff 0.0, positionY: ff 0.0, positionZ: ff 0.0
  , scaleX: ff 100.0, scaleY: ff 100.0, scaleZ: ff 100.0
  , rotation: ff 0.0
  , rotationX: ff 0.0, rotationY: ff 0.0, rotationZ: ff 0.0
  , opacity: pct 100.0
  , orientation: Nothing
  }

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Transform Properties" do
    transform2DPropertyTests
    transform3DPropertyTests
    vec3PropertyTests

--------------------------------------------------------------------------------
-- 1. LayerTransform2D properties
--------------------------------------------------------------------------------

transform2DPropertyTests :: Spec Unit
transform2DPropertyTests = do
  describe "LayerTransform2D properties" do
    let t = defaultTransform2D

    it "default anchor is at origin" do
      shouldBeCloseTo (unFiniteFloat t.anchorX) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat t.anchorY) 0.0 0.01

    it "default position is at origin" do
      shouldBeCloseTo (unFiniteFloat t.positionX) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat t.positionY) 0.0 0.01

    it "default scale is 100%" do
      shouldBeCloseTo (unFiniteFloat t.scaleX) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat t.scaleY) 100.0 0.01

    it "default rotation is 0" do
      shouldBeCloseTo (unFiniteFloat t.rotation) 0.0 0.01

    it "default opacity is 100%" do
      shouldBeCloseTo (unPercentage t.opacity) 100.0 0.01

    it "is deterministic" do
      let t1 = defaultTransform2D
      let t2 = defaultTransform2D
      unFiniteFloat t1.scaleX `shouldEqual` unFiniteFloat t2.scaleX
      unPercentage t1.opacity `shouldEqual` unPercentage t2.opacity

--------------------------------------------------------------------------------
-- 2. LayerTransform3D properties
--------------------------------------------------------------------------------

transform3DPropertyTests :: Spec Unit
transform3DPropertyTests = do
  describe "LayerTransform3D properties" do
    let t = defaultTransform3D

    it "default 3D anchor includes Z at 0" do
      shouldBeCloseTo (unFiniteFloat t.anchorZ) 0.0 0.01

    it "default 3D position includes Z at 0" do
      shouldBeCloseTo (unFiniteFloat t.positionZ) 0.0 0.01

    it "default 3D scale is 100% for all axes" do
      shouldBeCloseTo (unFiniteFloat t.scaleX) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat t.scaleY) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat t.scaleZ) 100.0 0.01

    it "default rotations are all 0" do
      shouldBeCloseTo (unFiniteFloat t.rotationX) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat t.rotationY) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat t.rotationZ) 0.0 0.01

    it "default orientation is Nothing" do
      isNothing t.orientation `shouldEqual` true

    it "supports setting orientation" do
      let t3d = defaultTransform3D { orientation = Just { x: ff 0.0, y: ff 0.0, z: ff 0.0 } }
      isJust t3d.orientation `shouldEqual` true

    it "is deterministic" do
      let t1 = defaultTransform3D
      let t2 = defaultTransform3D
      unFiniteFloat t1.scaleZ `shouldEqual` unFiniteFloat t2.scaleZ

--------------------------------------------------------------------------------
-- 3. Vec3 property tests
--------------------------------------------------------------------------------

vec3PropertyTests :: Spec Unit
vec3PropertyTests = do
  describe "Vec3 properties" do

    it "mkVec3 round-trips through finite check" do
      case mkVec3 42.0 (-17.5) 100.0 of
        Just v -> do
          shouldBeCloseTo (unFiniteFloat v.x) 42.0 0.01
          shouldBeCloseTo (unFiniteFloat v.y) (-17.5) 0.01
          shouldBeCloseTo (unFiniteFloat v.z) 100.0 0.01
        Nothing -> fail "Expected valid Vec3"

    it "mkVec3 is deterministic" do
      let v1 = mkVec3 1.0 2.0 3.0
      let v2 = mkVec3 1.0 2.0 3.0
      case v1, v2 of
        Just a, Just b -> do
          unFiniteFloat a.x `shouldEqual` unFiniteFloat b.x
          unFiniteFloat a.y `shouldEqual` unFiniteFloat b.y
          unFiniteFloat a.z `shouldEqual` unFiniteFloat b.z
        _, _ -> fail "Both should be Just"
