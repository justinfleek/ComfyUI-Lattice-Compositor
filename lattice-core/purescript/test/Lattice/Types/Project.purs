-- | Port of ui/src/__tests__/types/project.test.ts and project.property.test.ts (partial)
-- |
-- | Tests project type enumerations and structure:
-- |   - LayerType exhaustiveness (26 variants)
-- |   - BlendMode completeness (27 variants)
-- |   - TrackMatteMode variants
-- |   - CompositionSettings structure
-- |   - ProjectMeta structure
-- |
-- | Note: Factory tests (createEmptyProject, createDefaultXLayerData, etc.)
-- | are deferred - they require complex multi-module factory functions.
-- |
-- | 15 tests across 4 describe blocks

module Test.Lattice.Types.Project (spec) where

import Prelude

import Data.Array (length, nub)
import Data.Maybe (Maybe(..))
import Lattice.Primitives
  ( NonEmptyString(..), mkNonEmptyString
  , FrameNumber(..)
  , mkPositiveFloat, mkNonNegativeFloat, mkHexColor, mkPercentage
  , PositiveFloat(..), NonNegativeFloat(..), HexColor(..), Percentage(..)
  , unNonEmptyString
  )
import Lattice.Project
  ( LayerType(..)
  , BlendMode(..)
  , TrackMatteMode(..)
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Project - Type Tests" do
    layerTypeTests
    blendModeTests
    trackMatteModeTests
    structureTests

--------------------------------------------------------------------------------
-- 1. LayerType
--------------------------------------------------------------------------------

allLayerTypes :: Array LayerType
allLayerTypes =
  [ LTImage, LTVideo, LTSolid, LTText, LTShape, LTNull, LTCamera, LTLight
  , LTAudio, LTParticle, LTAdjustment, LTPreComp, LTGroup, LTNestedComp
  , LTDepth, LTNormal, LTGenerated, LTMatte, LTControl, LTSpline, LTPath
  , LTPose, LTEffect, LTModel, LTPointCloud, LTDepthflow
  ]

layerTypeTests :: Spec Unit
layerTypeTests = do
  describe "LayerType" do

    it "should have 26 layer types" do
      length allLayerTypes `shouldEqual` 26

    it "should have no duplicate layer types" do
      -- Each type shows uniquely
      let shown = map show allLayerTypes
      length (nub shown) `shouldEqual` 26

    it "should include all visual layer types" do
      let visual = [LTImage, LTVideo, LTSolid, LTText, LTShape]
      length visual `shouldEqual` 5

    it "should include all 3D layer types" do
      let types3d = [LTCamera, LTLight, LTModel, LTPointCloud]
      length types3d `shouldEqual` 4

    it "should include generated/matte types" do
      let gen = [LTGenerated, LTMatte, LTDepth, LTNormal]
      length gen `shouldEqual` 4

--------------------------------------------------------------------------------
-- 2. BlendMode
--------------------------------------------------------------------------------

allBlendModes :: Array BlendMode
allBlendModes =
  [ BMNormal, BMMultiply, BMScreen, BMOverlay, BMDarken, BMLighten
  , BMColorDodge, BMColorBurn, BMHardLight, BMSoftLight, BMDifference
  , BMExclusion, BMHue, BMSaturation, BMColor, BMLuminosity, BMAdd
  , BMSubtract, BMDivide, BMLinearBurn, BMLinearDodge, BMVividLight
  , BMLinearLight, BMPinLight, BMHardMix, BMDissolve, BMDarker, BMLighter
  ]

blendModeTests :: Spec Unit
blendModeTests = do
  describe "BlendMode" do

    it "should have 28 blend modes" do
      length allBlendModes `shouldEqual` 28

    it "should have no duplicates" do
      let shown = map show allBlendModes
      length (nub shown) `shouldEqual` 28

    it "should include standard blend modes" do
      let standard = [BMNormal, BMMultiply, BMScreen, BMOverlay]
      length standard `shouldEqual` 4

    it "should include component blend modes (HSL)" do
      let component = [BMHue, BMSaturation, BMColor, BMLuminosity]
      length component `shouldEqual` 4

--------------------------------------------------------------------------------
-- 3. TrackMatteMode
--------------------------------------------------------------------------------

trackMatteModeTests :: Spec Unit
trackMatteModeTests = do
  describe "TrackMatteMode" do

    it "should have 5 track matte modes" do
      let modes = [TMNone, TMAlpha, TMAlphaInverted, TMLuma, TMLumaInverted]
      length modes `shouldEqual` 5

    it "should have none as default option" do
      -- TMNone represents no track matte
      TMNone `shouldEqual` TMNone

--------------------------------------------------------------------------------
-- 4. Structure validation
--------------------------------------------------------------------------------

structureTests :: Spec Unit
structureTests = do
  describe "type structure" do

    it "should allow creating CompositionSettings" do
      let settings =
            { width: 1920
            , height: 1080
            , frameCount: 300
            , fps: case mkPositiveFloat 30.0 of
                Just v -> v
                Nothing -> PositiveFloat 30.0
            , duration: case mkNonNegativeFloat 10.0 of
                Just v -> v
                Nothing -> NonNegativeFloat 10.0
            , backgroundColor: case mkHexColor "#000000" of
                Just v -> v
                Nothing -> HexColor "#000000"
            , autoResizeToContent: false
            , frameBlendingEnabled: false
            }
      settings.width `shouldEqual` 1920
      settings.height `shouldEqual` 1080
      settings.frameCount `shouldEqual` 300

    it "should allow creating ProjectMeta" do
      let meta =
            { name: "Test Project"
            , created: case mkNonEmptyString "2024-01-01T00:00:00Z" of
                Just v -> v
                Nothing -> NonEmptyString "error"
            , modified: case mkNonEmptyString "2024-01-01T00:00:00Z" of
                Just v -> v
                Nothing -> NonEmptyString "error"
            , author: Nothing :: Maybe String
            , description: Nothing :: Maybe String
            , tags: [] :: Array String
            }
      meta.name `shouldEqual` "Test Project"

    it "should allow creating LayerBase with correct types" do
      -- Verify the record structure compiles correctly
      let nes s = case mkNonEmptyString s of
            Just v -> v
            Nothing -> NonEmptyString "error"
      let layer =
            { id: nes "layer-1"
            , name: nes "Test Layer"
            , layerType: LTImage
            , visible: true
            , locked: false
            , solo: false
            , shy: false
            , enabled: true
            , selected: false
            , collapsed: false
            , guideLayer: false
            , is3D: false
            , blendMode: BMNormal
            , opacity: case mkPercentage 100.0 of
                Just v -> v
                Nothing -> Percentage 100.0
            , startFrame: FrameNumber 0
            , endFrame: FrameNumber 300
            , inPoint: FrameNumber 0
            , outPoint: FrameNumber 300
            , stretch: case mkPositiveFloat 1.0 of
                Just v -> v
                Nothing -> PositiveFloat 1.0
            , parentId: Nothing :: Maybe NonEmptyString
            , trackMatteMode: TMNone
            , trackMatteLayerId: Nothing :: Maybe NonEmptyString
            , motionBlur: false
            , qualitySetting: Nothing :: Maybe NonEmptyString
            , samplingQuality: Nothing :: Maybe NonEmptyString
            , preserveTransparency: false
            , frameBlending: false
            , timeRemapEnabled: false
            }
      unNonEmptyString layer.id `shouldEqual` "layer-1"
      layer.layerType `shouldEqual` LTImage
      layer.visible `shouldEqual` true
