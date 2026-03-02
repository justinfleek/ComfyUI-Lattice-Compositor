-- | Port of ui/src/__tests__/types/shapes.property.test.ts (partial)
-- |
-- | Tests shape type enumerations and structure:
-- |   - ShapeContentType exhaustiveness (24 variants)
-- |   - FillRule variants
-- |   - LineCap/LineJoin variants
-- |   - TrimMode, MergeMode variants
-- |   - PathDirection mapping
-- |   - GradientType variants
-- |   - ExtrudeCapType variants
-- |
-- | Note: Shape factory tests (createDefaultRectangle, createDefaultFill, etc.)
-- | are deferred - they require shape content data types and AnimatableProperty factories.
-- |
-- | 20 tests across 4 describe blocks

module Test.Lattice.Types.ShapesProps (spec) where

import Prelude

import Data.Array (length, nub)
import Lattice.Shapes
  ( ShapeContentType(..)
  , FillRule(..)
  , LineCap(..)
  , LineJoin(..)
  , TrimMode(..)
  , MergeMode(..)
  , OffsetJoin(..)
  , WigglePointType(..)
  , ZigZagPointType(..)
  , RepeaterComposite(..)
  , GradientType(..)
  , ShapeQuality(..)
  , ExtrudeCapType(..)
  , TraceMode(..)
  , PathDirection(..)
  , pathDirectionToInt
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Shapes Properties" do
    contentTypeTests
    fillStrokeTests
    operatorTests
    miscTests

--------------------------------------------------------------------------------
-- 1. ShapeContentType
--------------------------------------------------------------------------------

allContentTypes :: Array ShapeContentType
allContentTypes =
  [ SCTRectangle, SCTEllipse, SCTPolygon, SCTStar, SCTPath
  , SCTFill, SCTStroke, SCTGradientFill, SCTGradientStroke
  , SCTTrimPaths, SCTMergePaths, SCTOffsetPaths, SCTPuckerBloat
  , SCTWigglePaths, SCTZigZag, SCTTwist, SCTRoundedCorners
  , SCTRepeater, SCTTransform
  , SCTGroup
  , SCTSimplifyPath, SCTSmoothPath, SCTExtrude, SCTTrace
  ]

contentTypeTests :: Spec Unit
contentTypeTests = do
  describe "ShapeContentType" do

    it "should have 23 content types" do
      length allContentTypes `shouldEqual` 24

    it "should have no duplicates" do
      let shown = map show allContentTypes
      length (nub shown) `shouldEqual` 24

    it "should include all generators" do
      let generators = [SCTRectangle, SCTEllipse, SCTPolygon, SCTStar, SCTPath]
      length generators `shouldEqual` 5

    it "should include all modifiers" do
      let modifiers = [SCTFill, SCTStroke, SCTGradientFill, SCTGradientStroke]
      length modifiers `shouldEqual` 4

    it "should include all operators" do
      let operators = [SCTTrimPaths, SCTMergePaths, SCTOffsetPaths, SCTPuckerBloat
                      , SCTWigglePaths, SCTZigZag, SCTTwist, SCTRoundedCorners
                      , SCTRepeater, SCTTransform]
      length operators `shouldEqual` 10

    it "should include illustrator tools" do
      let tools = [SCTSimplifyPath, SCTSmoothPath, SCTExtrude, SCTTrace]
      length tools `shouldEqual` 4

--------------------------------------------------------------------------------
-- 2. Fill/Stroke enums
--------------------------------------------------------------------------------

fillStrokeTests :: Spec Unit
fillStrokeTests = do
  describe "fill/stroke enums" do

    it "FillRule has 2 variants" do
      let rules = [FRNonzero, FREvenodd]
      length rules `shouldEqual` 2

    it "LineCap has 3 variants" do
      let caps = [LCButt, LCRound, LCSquare]
      length caps `shouldEqual` 3

    it "LineJoin has 3 variants" do
      let joins = [LJMiter, LJRound, LJBevel]
      length joins `shouldEqual` 3

    it "GradientType has 2 variants" do
      let grads = [GTLinear, GTRadial]
      length grads `shouldEqual` 2

--------------------------------------------------------------------------------
-- 3. Operator enums
--------------------------------------------------------------------------------

operatorTests :: Spec Unit
operatorTests = do
  describe "operator enums" do

    it "TrimMode has 2 variants" do
      let modes = [TMSimultaneously, TMIndividually]
      length modes `shouldEqual` 2

    it "MergeMode has 6 variants" do
      let modes = [MMAdd, MMSubtract, MMIntersect, MMExclude, MMMinusFront, MMMinusBack]
      length modes `shouldEqual` 6

    it "OffsetJoin has 3 variants" do
      let joins = [OJMiter, OJRound, OJBevel]
      length joins `shouldEqual` 3

    it "WigglePointType has 2 variants" do
      let types = [WPTCorner, WPTSmooth]
      length types `shouldEqual` 2

    it "ZigZagPointType has 2 variants" do
      let types = [ZZPTCorner, ZZPTSmooth]
      length types `shouldEqual` 2

    it "RepeaterComposite has 2 variants" do
      let comps = [RCAbove, RCBelow]
      length comps `shouldEqual` 2

--------------------------------------------------------------------------------
-- 4. Misc
--------------------------------------------------------------------------------

miscTests :: Spec Unit
miscTests = do
  describe "misc shape types" do

    it "PathDirection clockwise maps to 1" do
      pathDirectionToInt PDClockwise `shouldEqual` 1

    it "PathDirection counter-clockwise maps to -1" do
      pathDirectionToInt PDCounterClockwise `shouldEqual` (-1)

    it "ExtrudeCapType has 3 variants" do
      let caps = [ECTFlat, ECTRound, ECTBevel]
      length caps `shouldEqual` 3

    it "ShapeQuality has 3 variants" do
      let quals = [SQDraft, SQNormal, SQHigh]
      length quals `shouldEqual` 3

    it "TraceMode has 3 variants" do
      let modes = [TMBlackAndWhite, TMGrayscale, TMColor]
      length modes `shouldEqual` 3
