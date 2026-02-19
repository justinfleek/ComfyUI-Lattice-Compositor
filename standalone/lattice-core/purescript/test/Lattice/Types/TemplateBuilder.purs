-- | Port of ui/src/__tests__/types/templateBuilder.property.test.ts (partial)
-- |
-- | Tests createDefaultTemplateConfig, createPropertyGroup, createTemplateComment:
-- |   - All required properties present
-- |   - Default values correct
-- |   - Export settings defaults
-- |
-- | 14 tests across 3 describe blocks

module Test.Lattice.Types.TemplateBuilder (spec) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..), isNothing)
import Lattice.Primitives (NonEmptyString(..), FrameNumber(..), mkNonEmptyString, unNonEmptyString)
import Lattice.TemplateBuilder
  ( PosterQuality(..)
  , createDefaultTemplateConfig
  , createPropertyGroup
  , createTemplateComment
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

nes :: String -> NonEmptyString
nes s = case mkNonEmptyString s of
  Just v -> v
  Nothing -> NonEmptyString "error"

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "TemplateBuilder - Type Tests" do
    templateConfigTests
    propertyGroupTests
    templateCommentTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. createDefaultTemplateConfig
-- ────────────────────────────────────────────────────────────────────────────

templateConfigTests :: Spec Unit
templateConfigTests = do
  describe "createDefaultTemplateConfig" do

    it "should set name from input" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      unNonEmptyString config.name `shouldEqual` "My Comp"

    it "should set masterCompositionId from input" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      unNonEmptyString config.masterCompositionId `shouldEqual` "comp-1"

    it "should start with empty exposed properties" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      length config.exposedProperties `shouldEqual` 0

    it "should start with empty groups" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      length config.groups `shouldEqual` 0

    it "should start with empty comments" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      length config.comments `shouldEqual` 0

    it "should have posterFrame 0" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      config.posterFrame `shouldEqual` FrameNumber 0

    it "should have correct export settings" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      config.exportSettings.includeFonts `shouldEqual` true
      config.exportSettings.includeMedia `shouldEqual` true
      config.exportSettings.allowDurationChange `shouldEqual` false
      config.exportSettings.posterQuality `shouldEqual` PQHigh

    it "should set created and modified timestamps" do
      let ts = nes "2024-01-01T00:00:00Z"
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") ts
      config.created `shouldEqual` ts
      config.modified `shouldEqual` ts

    it "should have no description by default" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      isNothing config.description `shouldEqual` true

    it "should have no author by default" do
      let config = createDefaultTemplateConfig (nes "comp-1") (nes "My Comp") (nes "2024-01-01T00:00:00Z")
      isNothing config.author `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 2. createPropertyGroup
-- ────────────────────────────────────────────────────────────────────────────

propertyGroupTests :: Spec Unit
propertyGroupTests = do
  describe "createPropertyGroup" do

    it "should set id and name correctly" do
      let group = createPropertyGroup (nes "grp_1") (nes "Transform") 0
      unNonEmptyString group.id `shouldEqual` "grp_1"
      unNonEmptyString group.name `shouldEqual` "Transform"

    it "should default expanded to true" do
      let group = createPropertyGroup (nes "grp_1") (nes "Transform") 0
      group.expanded `shouldEqual` true

    it "should set order correctly" do
      let group = createPropertyGroup (nes "grp_1") (nes "Transform") 5
      group.order `shouldEqual` 5

-- ────────────────────────────────────────────────────────────────────────────
-- 3. createTemplateComment
-- ────────────────────────────────────────────────────────────────────────────

templateCommentTests :: Spec Unit
templateCommentTests = do
  describe "createTemplateComment" do

    it "should set id and text correctly" do
      let comment = createTemplateComment (nes "cmt_1") "Hello world" 0
      unNonEmptyString comment.id `shouldEqual` "cmt_1"
      comment.text `shouldEqual` "Hello world"

    it "should set order correctly" do
      let comment = createTemplateComment (nes "cmt_1") "Hello" 3
      comment.order `shouldEqual` 3

    it "should have no groupId by default" do
      let comment = createTemplateComment (nes "cmt_1") "Hello" 0
      isNothing comment.groupId `shouldEqual` true
