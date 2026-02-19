-- | Port of ui/src/__tests__/types/project.property.test.ts
-- |
-- | Tests project factory functions:
-- |   - createDefaultEffectLayerData
-- |   - createDefaultLightLayerData
-- |   - createDefaultSolidLayerData
-- |   - createDefaultNullLayerData
-- |   - createDefaultPoseLayerData
-- |   - createEmptyProject
-- |   - BLEND_MODE_CATEGORIES (via blendModeCategory)
-- |
-- | Note: createDefaultProceduralMatteData and normalizeLayerTiming are deferred
-- | (require AnimatableProperty-based parameters and migration logic)
-- |
-- | 30 tests across 7 describe blocks

module Test.Lattice.Types.ProjectProps (spec) where

import Prelude

import Data.Array (length, all)
import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( NonEmptyString(..), FrameNumber(..)
  , mkNonEmptyString
  , unNonEmptyString, unHexColor, unPositiveFloat
  , unPercentage, unNonNegativeFloat, unUnitFloat
  )
import Lattice.LayerData
  ( createDefaultEffectLayerData
  , createDefaultLightLayerData
  , createDefaultSolidLayerData
  , createDefaultNullLayerData
  , createDefaultPoseLayerData
  , LightType(..)
  , FalloffType(..)
  , PoseFormat(..)
  )
import Lattice.Project (createEmptyProject)
import Lattice.BlendModes as BM
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

nes :: String -> NonEmptyString
nes s = case mkNonEmptyString s of
  Just v -> v
  Nothing -> NonEmptyString "error"

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "Project Properties" do
    effectLayerDataTests
    lightLayerDataTests
    solidLayerDataTests
    nullLayerDataTests
    poseLayerDataTests
    emptyProjectTests
    blendModeCategoryTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. createDefaultEffectLayerData
-- ────────────────────────────────────────────────────────────────────────────

effectLayerDataTests :: Spec Unit
effectLayerDataTests = do
  describe "createDefaultEffectLayerData" do
    let eld = createDefaultEffectLayerData

    it "effectLayer is true" do
      eld.effectLayer `shouldEqual` true

    it "adjustmentLayer is true (backwards compat)" do
      eld.adjustmentLayer `shouldEqual` true

    it "color is #FF6B6B (red)" do
      unHexColor eld.color `shouldEqual` "#FF6B6B"

    it "is deterministic" do
      let e1 = createDefaultEffectLayerData
      let e2 = createDefaultEffectLayerData
      e1.effectLayer `shouldEqual` e2.effectLayer
      unHexColor e1.color `shouldEqual` unHexColor e2.color

-- ────────────────────────────────────────────────────────────────────────────
-- 2. createDefaultLightLayerData
-- ────────────────────────────────────────────────────────────────────────────

lightLayerDataTests :: Spec Unit
lightLayerDataTests = do
  describe "createDefaultLightLayerData" do
    let lld = createDefaultLightLayerData

    it "lightType is point" do
      lld.lightType `shouldEqual` LightPoint

    it "color is white" do
      unHexColor lld.color `shouldEqual` "#ffffff"

    it "intensity is 100" do
      shouldBeCloseTo (unPercentage lld.intensity) 100.0 0.01

    it "radius is 500" do
      shouldBeCloseTo (unPositiveFloat lld.radius) 500.0 0.01

    it "falloff is none" do
      lld.falloff `shouldEqual` FONone

    it "castShadows is false" do
      lld.castShadows `shouldEqual` false

    it "is deterministic" do
      let l1 = createDefaultLightLayerData
      let l2 = createDefaultLightLayerData
      l1.lightType `shouldEqual` l2.lightType
      l1.castShadows `shouldEqual` l2.castShadows

-- ────────────────────────────────────────────────────────────────────────────
-- 3. createDefaultSolidLayerData
-- ────────────────────────────────────────────────────────────────────────────

solidLayerDataTests :: Spec Unit
solidLayerDataTests = do
  describe "createDefaultSolidLayerData" do
    let sld = createDefaultSolidLayerData 1920 1080

    it "color is mid-gray (#808080)" do
      unHexColor sld.color `shouldEqual` "#808080"

    it "width matches parameter" do
      sld.width `shouldEqual` 1920

    it "height matches parameter" do
      sld.height `shouldEqual` 1080

    it "shadowCatcher is false" do
      sld.shadowCatcher `shouldEqual` false

    it "is deterministic" do
      let s1 = createDefaultSolidLayerData 1920 1080
      let s2 = createDefaultSolidLayerData 1920 1080
      unHexColor s1.color `shouldEqual` unHexColor s2.color
      s1.width `shouldEqual` s2.width

-- ────────────────────────────────────────────────────────────────────────────
-- 4. createDefaultNullLayerData
-- ────────────────────────────────────────────────────────────────────────────

nullLayerDataTests :: Spec Unit
nullLayerDataTests = do
  describe "createDefaultNullLayerData" do
    let nld = createDefaultNullLayerData

    it "size is 40" do
      nld.size `shouldEqual` 40

    it "is deterministic" do
      let n1 = createDefaultNullLayerData
      let n2 = createDefaultNullLayerData
      n1.size `shouldEqual` n2.size

-- ────────────────────────────────────────────────────────────────────────────
-- 5. createDefaultPoseLayerData
-- ────────────────────────────────────────────────────────────────────────────

poseLayerDataTests :: Spec Unit
poseLayerDataTests = do
  describe "createDefaultPoseLayerData" do
    let pld = createDefaultPoseLayerData

    it "has 18 keypoints" do
      length pld.keypoints `shouldEqual` 18

    it "format is coco" do
      pld.format `shouldEqual` PFCoco

    it "all keypoints have confidence 1.0" do
      let allConf = all (\kp -> unUnitFloat kp.confidence >= 0.99) pld.keypoints
      allConf `shouldEqual` true

    it "lineWidth is 4" do
      shouldBeCloseTo (unPositiveFloat pld.lineWidth) 4.0 0.01

    it "showConfidence is false" do
      pld.showConfidence `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 6. createEmptyProject
-- ────────────────────────────────────────────────────────────────────────────

emptyProjectTests :: Spec Unit
emptyProjectTests = do
  describe "createEmptyProject" do
    let proj = createEmptyProject 1920 1080 (nes "2024-01-01T00:00:00Z")

    it "version is 1.0.0" do
      unNonEmptyString proj.version `shouldEqual` "1.0.0"

    it "schemaVersion is 2" do
      proj.schemaVersion `shouldEqual` 2

    it "meta name is Untitled" do
      proj.meta.name `shouldEqual` "Untitled"

    it "has one composition" do
      length proj.compositions `shouldEqual` 1

    it "mainCompositionId is 'main'" do
      unNonEmptyString proj.mainCompositionId `shouldEqual` "main"

    it "has no assets" do
      length proj.assets `shouldEqual` 0

    it "currentFrame is 0" do
      proj.currentFrame `shouldEqual` FrameNumber 0

    it "is deterministic" do
      let p1 = createEmptyProject 1920 1080 (nes "2024-01-01T00:00:00Z")
      let p2 = createEmptyProject 1920 1080 (nes "2024-01-01T00:00:00Z")
      unNonEmptyString p1.version `shouldEqual` unNonEmptyString p2.version
      p1.schemaVersion `shouldEqual` p2.schemaVersion

-- ────────────────────────────────────────────────────────────────────────────
-- 7. blendModeCategory
-- ────────────────────────────────────────────────────────────────────────────

blendModeCategoryTests :: Spec Unit
blendModeCategoryTests = do
  describe "blendModeCategory" do

    it "Normal is in Normal category" do
      BM.blendModeCategory BM.BMNormal `shouldEqual` BM.BMCNormal

    it "Multiply is in Darken category" do
      BM.blendModeCategory BM.BMMultiply `shouldEqual` BM.BMCDarken

    it "Screen is in Lighten category" do
      BM.blendModeCategory BM.BMScreen `shouldEqual` BM.BMCLighten
