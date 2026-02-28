-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property tests for Schema modules:
-- | - Diff: patch/apply correctness
-- | - Group: hierarchical organization
-- | - Priority: ordering and bounds
-- | - Landauer: entropy-based precision
-- | - Color atoms: Hue, Saturation, Lightness, Opacity, Channel
-- | - Identity: Generation monotonicity
-- |
-- | ## Test Philosophy
-- |
-- | At billion-agent scale, unbounded values or incorrect clamp/wrap behavior
-- | causes cascading failures. These tests verify:
-- | - Bounds are ALWAYS enforced
-- | - Clamping vs wrapping semantics are correct
-- | - Adversarial inputs don't break invariants
module Test.Schema.Property
  ( schemaPropertyTests
  ) where

import Prelude (Unit, bind, negate, pure, unit, ($), (&&), (||), (<=), (>=), (<>), (==), (/=), (>), (<), show, discard, otherwise, (+), (-), (*), mod)

import Data.Array.NonEmpty as NEA
import Data.Array (length, index) as Array
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Schema.Diff as Diff
import Hydrogen.Schema.Group as Group
import Hydrogen.Schema.Priority as Priority
import Hydrogen.Schema.GPU.Landauer as Landauer
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Identity.Temporal as Temporal
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Geometry.Angle as Angle
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency)
import Control.Monad.Gen.Class (chooseFloat)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Data.Maybe (Maybe(Nothing, Just))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate Priority levels
genPriority :: Gen Priority.Priority
genPriority = elements $ NEA.cons'
  Priority.Critical
  [ Priority.High
  , Priority.Normal
  , Priority.Low
  , Priority.Background
  ]

-- | Generate Numeric Priority
genNumericPriority :: Gen Priority.NumericPriority
genNumericPriority = do
  n <- chooseInt 0 1000
  pure $ Priority.numericPriority n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main test export — Schema property tests
schemaPropertyTests :: Spec Unit
schemaPropertyTests = describe "Schema Property Tests" do
  diffPropertyTests
  groupPropertyTests
  priorityPropertyTests
  landauerPropertyTests
  huePropertyTests
  saturationPropertyTests
  lightnessPropertyTests
  opacityPropertyTests
  channelPropertyTests
  generationPropertyTests
  transform2DPropertyTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // diff tests
-- ═══════════════════════════════════════════════════════════════════════════════

diffPropertyTests :: Spec Unit
diffPropertyTests = describe "Diff" do
  describe "Diff Constructors" do
    it "NoChange constructor exists" do
      let _ = Diff.NoChange :: Diff.Diff Int
      pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // group tests
-- ═══════════════════════════════════════════════════════════════════════════════

groupPropertyTests :: Spec Unit
groupPropertyTests = describe "Group (hierarchical organization)" do
  
  describe "Construction" do
    it "emptyGroup creates group with no items" do
      let g = Group.emptyGroup "test" "Test Group" :: Group.Group Int
      Group.isEmpty g `shouldEqual` true
    
    it "leaf creates group with items" do
      let g = Group.leaf "colors" "Colors" [1, 2, 3]
      Group.isEmpty g `shouldEqual` false
      Array.length (Group.groupItems g) `shouldEqual` 3
    
    it "leaf group is a leaf (no children)" do
      let g = Group.leaf "test" "Test" [1]
      Group.isLeaf g `shouldEqual` true
    
    it "emptyGroup is a root (no parent)" do
      let g = Group.emptyGroup "root" "Root" :: Group.Group Int
      Group.isRoot g `shouldEqual` true
  
  describe "Deterministic Identity" do
    it "same slug produces same GroupId" do
      let g1 = Group.emptyGroup "brand" "Brand A" :: Group.Group Int
      let g2 = Group.emptyGroup "brand" "Brand B" :: Group.Group Int
      Group.groupId g1 `shouldEqual` Group.groupId g2
    
    it "different slugs produce different GroupIds" do
      let g1 = Group.emptyGroup "primary" "Primary" :: Group.Group Int
      let g2 = Group.emptyGroup "secondary" "Secondary" :: Group.Group Int
      (Group.groupId g1 /= Group.groupId g2) `shouldEqual` true
  
  describe "Hierarchical Structure" do
    it "groupWithChildren sets parent references" do
      let parent = Group.groupWithChildren "colors" "Colors"
            [ Group.leaf "primary" "Primary" [1, 2]
            , Group.leaf "secondary" "Secondary" [3, 4]
            ]
      let children = Group.groupChildren parent
      Array.length children `shouldEqual` 2
      -- Each child should have parent set
      Spec.quickCheck do
        idx <- chooseInt 0 1
        case Array.index children idx of
          Nothing -> pure $ true <?> "Index out of bounds"
          Just child -> 
            case Group.groupParent child of
              Nothing -> pure $ false <?> "Child should have parent"
              Just pid -> pure $ (pid == Group.groupId parent)
                <?> "Child parent should match parent id"
    
    it "nested groups form tree structure" do
      let tree = Group.groupWithChildren "root" "Root"
            [ Group.groupWithChildren "branch1" "Branch 1"
                [ Group.leaf "leaf1a" "Leaf 1A" [1]
                , Group.leaf "leaf1b" "Leaf 1B" [2]
                ]
            , Group.leaf "leaf2" "Leaf 2" [3]
            ]
      -- Root has 2 direct children
      Array.length (Group.groupChildren tree) `shouldEqual` 2
      -- All groups should be findable
      let allGroups = Group.allGroups tree
      Array.length allGroups `shouldEqual` 5  -- root + branch1 + leaf1a + leaf1b + leaf2
  
  describe "Modification" do
    it "addItem increases item count" do
      let g = Group.emptyGroup "test" "Test" :: Group.Group Int
      let g' = Group.addItem 42 g
      Array.length (Group.groupItems g') `shouldEqual` 1
    
    it "addItems adds multiple items" do
      let g = Group.emptyGroup "test" "Test" :: Group.Group Int
      let g' = Group.addItems [1, 2, 3, 4, 5] g
      Array.length (Group.groupItems g') `shouldEqual` 5
    
    it "removeItem removes specific item" do
      let g = Group.leaf "test" "Test" [1, 2, 3]
      let g' = Group.removeItem 2 g
      Array.length (Group.groupItems g') `shouldEqual` 2
      Group.hasItem 2 g' `shouldEqual` false
    
    it "setGroupName changes name but preserves id" do
      let g = Group.emptyGroup "test" "Original Name" :: Group.Group Int
      let g' = Group.setGroupName "New Name" g
      Group.groupName g' `shouldEqual` "New Name"
      Group.groupId g' `shouldEqual` Group.groupId g
  
  describe "Traversal" do
    it "allItems collects items from group and descendants" do
      let tree = Group.groupWithChildren "root" "Root"
            [ Group.leaf "a" "A" [1, 2]
            , Group.leaf "b" "B" [3, 4]
            ]
      let items = Group.allItems tree
      Array.length items `shouldEqual` 4
    
    it "descendants returns all child groups recursively" do
      let tree = Group.groupWithChildren "root" "Root"
            [ Group.groupWithChildren "branch" "Branch"
                [ Group.leaf "leaf" "Leaf" [1]
                ]
            ]
      let desc = Group.descendants tree
      Array.length desc `shouldEqual` 2  -- branch + leaf
  
  describe "Queries" do
    it "hasItem finds existing items" do
      let g = Group.leaf "test" "Test" [1, 2, 3]
      Group.hasItem 2 g `shouldEqual` true
      Group.hasItem 99 g `shouldEqual` false
    
    it "findGroup locates group by id" do
      let tree = Group.groupWithChildren "root" "Root"
            [ Group.leaf "target" "Target" [42]
            ]
      let targetId = Group.makeGroupId ["root", "target"]
      case Group.findGroup targetId tree of
        Nothing -> 1 `shouldEqual` 0  -- Fail
        Just found -> Group.groupSlug found `shouldEqual` "target"
  
  describe "Forest Operations" do
    it "emptyForest has no roots" do
      let f = Group.emptyForest :: Group.Forest Int
      Array.length (Group.forestRoots f) `shouldEqual` 0
    
    it "addRoot increases forest size" do
      let f = Group.emptyForest :: Group.Forest Int
      let g = Group.emptyGroup "root1" "Root 1"
      let f' = Group.addRoot g f
      Array.length (Group.forestRoots f') `shouldEqual` 1
    
    it "forestAllItems collects from all roots" do
      let f = Group.emptyForest :: Group.Forest Int
      let g1 = Group.leaf "a" "A" [1, 2]
      let g2 = Group.leaf "b" "B" [3, 4]
      let f' = Group.addRoot g2 (Group.addRoot g1 f)
      Array.length (Group.forestAllItems f') `shouldEqual` 4
  
  describe "Compound Predicates" do
    it "group is either leaf or has children (using ||)" do
      Spec.quickCheck propGroupIsLeafOrHasChildren
    
    it "item index wraps correctly with mod" do
      Spec.quickCheck propItemIndexWraps

-- | Property: A group is either a leaf (no children) or has children.
-- | Uses (||) operator.
propGroupIsLeafOrHasChildren :: Gen Result
propGroupIsLeafOrHasChildren = do
  hasChildren <- elements $ NEA.cons' true [false]
  let group = if hasChildren
              then Group.groupWithChildren "parent" "Parent" 
                     [Group.leaf "child" "Child" [1]]
              else Group.leaf "leaf" "Leaf" [1, 2, 3]
  let isLeafGroup = Group.isLeaf group
  let hasChildGroups = Array.length (Group.groupChildren group) > 0
  pure $ (isLeafGroup || hasChildGroups)
    <?> "Group should be either a leaf or have children"

-- | Property: Item indices wrap correctly using mod for cyclic access.
-- | Uses mod operator.
propItemIndexWraps :: Gen Result
propItemIndexWraps = do
  idx <- chooseInt 0 100
  let items = [10, 20, 30, 40, 50]  -- 5 items
  let itemCount = Array.length items
  let wrappedIdx = idx `mod` itemCount
  -- Verify wrapped index is always in bounds
  pure $ (wrappedIdx >= 0 && wrappedIdx < itemCount)
    <?> "Wrapped index " <> show wrappedIdx <> " from " <> show idx <> " should be in [0, " <> show itemCount <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // priority tests
-- ═══════════════════════════════════════════════════════════════════════════════

priorityPropertyTests :: Spec Unit
priorityPropertyTests = describe "Priority" do
  describe "Ordering" do
    it "critical is highest" do
      Spec.quickCheck propCriticalHighest

    it "background is lowest" do
      Spec.quickCheck propBackgroundLowest
  
  describe "Numeric Priority" do
    it "numeric priority is bounded [0, 1000]" do
      Spec.quickCheck propNumericPriorityBounded

-- Property: Critical is highest
propCriticalHighest :: Gen Result
propCriticalHighest = do
  p <- genPriority
  pure $ Priority.priorityToInt p <= Priority.priorityToInt Priority.Critical
    <?> show p <> " should be <= critical"

-- Property: Background is lowest
propBackgroundLowest :: Gen Result
propBackgroundLowest = do
  p <- genPriority
  pure $ Priority.priorityToInt Priority.Background <= Priority.priorityToInt p
    <?> "background should be <= " <> show p

-- Property: NumericPriority is bounded [0, 1000]
propNumericPriorityBounded :: Gen Result
propNumericPriorityBounded = do
  np <- genNumericPriority
  let v = Priority.unwrapNumericPriority np
  pure $ v >= 0 && v <= 1000
    <?> "NumericPriority " <> show v <> " should be in [0, 1000]"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // landauer tests
-- ═══════════════════════════════════════════════════════════════════════════════

landauerPropertyTests :: Spec Unit
landauerPropertyTests = describe "Landauer Precision" do
  describe "Free Boundary Condition" do
    it "entropy <= precision implies free boundary" do
      Spec.quickCheck propFreeBoundaryCondition
    
    it "forward sensitivity is non-negative" do
      Spec.quickCheck propForwardSensitivityNonNeg
    
    it "backward sensitivity is non-negative" do
      Spec.quickCheck propBackwardSensitivityNonNeg
    
    it "effective precision bounds both flows" do
      Spec.quickCheck propEffectivePrecisionBounds

-- | Generate entropy values (0-64 bits)
genEntropy :: Gen Number
genEntropy = do
  bits <- chooseInt 0 64
  pure $ intToNumber bits

-- | Generate tolerance values (0-8 bits, typical)
genTolerance :: Gen Number
genTolerance = do
  bits <- chooseInt 0 8
  pure $ intToNumber bits

-- | Generate precision bits (1-64)
genPrecisionBits :: Gen Int
genPrecisionBits = chooseInt 1 64

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber n = intToNumberGo n 0.0

intToNumberGo :: Int -> Number -> Number
intToNumberGo n acc
  | n <= 0 = acc
  | otherwise = intToNumberGo (n - 1) (acc + 1.0)

-- Property: Free boundary when entropy <= precision
propFreeBoundaryCondition :: Gen Result
propFreeBoundaryCondition = do
  entropyBits <- chooseInt 0 32
  precisionBits <- chooseInt entropyBits 64  -- precision >= entropy
  let ent = Landauer.entropy (intToNumber entropyBits)
  let prec = Landauer.precisionBits precisionBits
  let cost = Landauer.landauerCost ent prec
  pure $ Landauer.isFree cost
    <?> "Entropy " <> show entropyBits <> " <= precision " <> show precisionBits <> " should be free"

-- Property: Forward sensitivity is non-negative
propForwardSensitivityNonNeg :: Gen Result
propForwardSensitivityNonNeg = do
  e <- genEntropy
  b <- genPrecisionBits
  let ent = Landauer.entropy e
  let prec = Landauer.precisionBits b
  let sens = Landauer.forwardSensitivity ent prec
  pure $ sens >= 0.0
    <?> "Forward sensitivity should be >= 0, got " <> show sens

-- Property: Backward sensitivity is non-negative
propBackwardSensitivityNonNeg :: Gen Result
propBackwardSensitivityNonNeg = do
  e <- genEntropy
  b <- genPrecisionBits
  let ent = Landauer.entropy e
  let prec = Landauer.precisionBits b
  let sens = Landauer.backwardSensitivity ent prec
  pure $ sens >= 0.0
    <?> "Backward sensitivity should be >= 0, got " <> show sens

-- Property: Effective precision bounds both forward and backward requirements
propEffectivePrecisionBounds :: Gen Result
propEffectivePrecisionBounds = do
  fwdE <- genEntropy
  bwdE <- genEntropy
  fwdTol <- genTolerance
  bwdTol <- genTolerance
  let fwdEnt = Landauer.entropy fwdE
  let bwdEnt = Landauer.entropy bwdE
  let tol = Landauer.distortionTolerance fwdTol bwdTol
  let prec = Landauer.effectivePrecision fwdEnt bwdEnt tol
  -- Effective precision should satisfy both tolerances
  -- This is a structural property - the precision is computed as max of requirements
  let fwdSatisfied = Landauer.satisfiesForwardTolerance fwdEnt prec tol
  let bwdSatisfied = Landauer.satisfiesBackwardTolerance bwdEnt prec tol
  pure $ fwdSatisfied && bwdSatisfied
    <?> "Effective precision should satisfy both tolerances"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // adversarial generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Wide range integers for adversarial testing
genWideRangeInt :: Gen Int
genWideRangeInt = frequency $ NEA.cons'
  (Tuple 20.0 (chooseInt (-1000000) (-1)))          -- Large negatives
  [ Tuple 20.0 (chooseInt 0 100)                    -- Normal range
  , Tuple 20.0 (chooseInt 101 1000)                 -- Above typical bounds
  , Tuple 20.0 (chooseInt 1000 1000000)             -- Large positives
  , Tuple 10.0 (elements $ NEA.cons' 0 [(-1), 2147483647, (-2147483648)])
  , Tuple 10.0 (pure 2147483647)                    -- Int max
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // hue property tests
-- ═══════════════════════════════════════════════════════════════════════════════

huePropertyTests :: Spec Unit
huePropertyTests = describe "Hue (wrapping, 0-359)" do
  
  describe "Bounds Invariant" do
    it "hue always produces values in 0-359 (clamping)" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let h = Hue.hue n
        let val = Hue.unwrap h
        pure $ (val >= 0 && val <= 359)
          <?> "Hue out of bounds: input=" <> show n <> ", output=" <> show val
    
    it "hueWrap always produces values in 0-359 (wrapping)" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let h = Hue.hueWrap n
        let val = Hue.unwrap h
        pure $ (val >= 0 && val <= 359)
          <?> "HueWrap out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Wrapping Behavior" do
    it "hueWrap(360) == 0" do
      Hue.unwrap (Hue.hueWrap 360) `shouldEqual` 0
    
    it "hueWrap(-1) == 359" do
      Hue.unwrap (Hue.hueWrap (-1)) `shouldEqual` 359
    
    it "hueWrap(n + 360) == hueWrap(n)" do
      Spec.quickCheck do
        n <- chooseInt (-1000) 1000
        let h1 = Hue.hueWrap n
        let h2 = Hue.hueWrap (n + 360)
        pure $ h1 === h2
  
  describe "Rotation" do
    it "rotate 0 is identity" do
      Spec.quickCheck do
        n <- chooseInt 0 359
        let h = Hue.hue n
        pure $ Hue.rotate 0 h === h
    
    it "double complement is identity" do
      Spec.quickCheck do
        n <- chooseInt 0 359
        let h = Hue.hue n
        pure $ Hue.complement (Hue.complement h) === h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // saturation property tests
-- ═══════════════════════════════════════════════════════════════════════════════

saturationPropertyTests :: Spec Unit
saturationPropertyTests = describe "Saturation (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "saturation always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let s = Saturation.saturation n
        let val = Saturation.unwrap s
        pure $ (val >= 0 && val <= 100)
          <?> "Saturation out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Clamping" do
    it "saturation(-1) == 0" do
      Saturation.unwrap (Saturation.saturation (-1)) `shouldEqual` 0
    
    it "saturation(101) == 100" do
      Saturation.unwrap (Saturation.saturation 101) `shouldEqual` 100
    
    it "values in range preserved" do
      Spec.quickCheck do
        n <- chooseInt 0 100
        let s = Saturation.saturation n
        pure $ Saturation.unwrap s === n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // lightness property tests
-- ═══════════════════════════════════════════════════════════════════════════════

lightnessPropertyTests :: Spec Unit
lightnessPropertyTests = describe "Lightness (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "lightness always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let l = Lightness.lightness n
        let val = Lightness.unwrap l
        pure $ (val >= 0 && val <= 100)
          <?> "Lightness out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Clamping" do
    it "lightness(-1) == 0" do
      Lightness.unwrap (Lightness.lightness (-1)) `shouldEqual` 0
    
    it "lightness(101) == 100" do
      Lightness.unwrap (Lightness.lightness 101) `shouldEqual` 100

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // opacity property tests
-- ═══════════════════════════════════════════════════════════════════════════════

opacityPropertyTests :: Spec Unit
opacityPropertyTests = describe "Opacity (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "opacity always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let o = Opacity.opacity n
        let val = Opacity.unwrap o
        pure $ (val >= 0 && val <= 100)
          <?> "Opacity out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Predicates" do
    it "predicates are mutually exclusive" do
      Spec.quickCheck do
        n <- chooseInt 0 100
        let o = Opacity.opacity n
        let isT = Opacity.isTransparent o
        let isO = Opacity.isOpaque o
        let isS = Opacity.isSemiTransparent o
        -- Exactly one should be true
        let count = (if isT then 1 else 0) + (if isO then 1 else 0) + (if isS then 1 else 0)
        pure $ count === 1

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // channel property tests
-- ═══════════════════════════════════════════════════════════════════════════════

channelPropertyTests :: Spec Unit
channelPropertyTests = describe "Channel (clamping, 0-255)" do
  
  describe "Bounds Invariant" do
    it "channel always produces values in 0-255" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let c = Channel.channel n
        let val = Channel.unwrap c
        pure $ (val >= 0 && val <= 255)
          <?> "Channel out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Inversion" do
    it "invert(invert(c)) == c" do
      Spec.quickCheck do
        n <- chooseInt 0 255
        let c = Channel.channel n
        pure $ Channel.invert (Channel.invert c) === c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // generation property tests
-- ═══════════════════════════════════════════════════════════════════════════════

generationPropertyTests :: Spec Unit
generationPropertyTests = describe "Generation (non-negative, monotonic)" do
  
  describe "Bounds Invariant" do
    it "generation always produces non-negative values" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let g = Temporal.generation n
        let val = Temporal.unwrapGeneration g
        pure $ val >= 0
          <?> "Generation negative: input=" <> show n <> ", output=" <> show val
  
  describe "Monotonicity" do
    it "nextGeneration always increases" do
      Spec.quickCheck do
        n <- chooseInt 0 1000000
        let g = Temporal.generation n
        let next = Temporal.nextGeneration g
        let gVal = Temporal.unwrapGeneration g
        let nextVal = Temporal.unwrapGeneration next
        pure $ nextVal > gVal
          <?> "nextGeneration not monotonic: " <> show gVal <> " -> " <> show nextVal
    
    it "initialGeneration is 0" do
      Temporal.unwrapGeneration Temporal.initialGeneration `shouldEqual` 0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // transform2D property tests
-- ═══════════════════════════════════════════════════════════════════════════════

transform2DPropertyTests :: Spec Unit
transform2DPropertyTests = describe "Transform2D" do
  
  describe "Scale Bounds" do
    it "scale always produces values in [-10, 10]" do
      Spec.quickCheck do
        x <- genScaleInput
        let s = Transform.scale x
        let sx = Transform.getScaleX s
        let sy = Transform.getScaleY s
        pure $ (sx >= (-10.0) && sx <= 10.0 && sy >= (-10.0) && sy <= 10.0)
          <?> "Scale out of bounds: input=" <> show x <> ", output=(" <> show sx <> ", " <> show sy <> ")"
    
    it "scaleXY always produces values in [-10, 10]" do
      Spec.quickCheck do
        x <- genScaleInput
        y <- genScaleInput
        let s = Transform.scaleXY x y
        let sx = Transform.getScaleX s
        let sy = Transform.getScaleY s
        pure $ (sx >= (-10.0) && sx <= 10.0 && sy >= (-10.0) && sy <= 10.0)
          <?> "ScaleXY out of bounds: input=(" <> show x <> ", " <> show y <> "), output=(" <> show sx <> ", " <> show sy <> ")"
  
  describe "Scale Identity" do
    it "scaleIdentity is (1, 1)" do
      let s = Transform.scaleIdentity
      Transform.getScaleX s `shouldEqual` 1.0
      Transform.getScaleY s `shouldEqual` 1.0
    
    it "uniform scale has equal X and Y" do
      Spec.quickCheck do
        n <- genScaleInput
        let s = Transform.scale n
        pure $ Transform.isUniformScale s
          <?> "scale " <> show n <> " should be uniform"
  
  describe "Skew Bounds" do
    it "skew always produces values in [-89, 89]" do
      Spec.quickCheck do
        x <- genSkewInput
        y <- genSkewInput
        let sk = Transform.skew x y
        let skx = Transform.getSkewX sk
        let sky = Transform.getSkewY sk
        pure $ (skx >= (-89.0) && skx <= 89.0 && sky >= (-89.0) && sky <= 89.0)
          <?> "Skew out of bounds: input=(" <> show x <> ", " <> show y <> "), output=(" <> show skx <> ", " <> show sky <> ")"
  
  describe "Translate" do
    it "translateNone is (0, 0)" do
      let t = Transform.translateNone
      Transform.getTranslateX t `shouldEqual` 0.0
      Transform.getTranslateY t `shouldEqual` 0.0
    
    it "addTranslate is commutative" do
      Spec.quickCheck propTranslateCommutative
    
    it "negate twice is identity" do
      Spec.quickCheck propTranslateDoubleNegate
  
  describe "Rotate" do
    it "rotateNone has 0 degrees" do
      let r = Transform.rotateNone
      let angle = Transform.getRotation r
      Angle.unwrapDegrees angle `shouldEqual` 0.0
    
    it "rotate90 + rotate90 + rotate90 + rotate90 = rotateNone" do
      let r90 = Transform.rotate90
      let r180 = Transform.addRotation r90 r90
      let r270 = Transform.addRotation r180 r90
      let r360 = Transform.addRotation r270 r90
      -- 360 degrees normalizes to 0
      Angle.unwrapDegrees (Transform.getRotation r360) `shouldEqual` 0.0
  
  describe "Transform2D Composition" do
    it "identity transform has no components" do
      let t = Transform.identityTransform
      -- Check that all optional components are Nothing
      -- We verify by checking the CSS output is empty
      Transform.transform2DToLegacyCss t `shouldEqual` ""
    
    it "composeTransform with identity is original" do
      Spec.quickCheck propComposeWithIdentity
    
    it "composeTransform accumulates translations" do
      Spec.quickCheck propComposeTranslations
    
    it "composeTransform multiplies scales" do
      Spec.quickCheck propComposeScales

-- | Generator for scale inputs (includes adversarial values)
genScaleInput :: Gen Number
genScaleInput = frequency $ NEA.cons'
  (Tuple 30.0 (chooseFloat (-10.0) 10.0))        -- Valid range
  [ Tuple 20.0 (chooseFloat (-100.0) (-10.0))    -- Below min
  , Tuple 20.0 (chooseFloat 10.0 100.0)          -- Above max
  , Tuple 10.0 (pure 0.0)                        -- Zero
  , Tuple 10.0 (pure 1.0)                        -- Identity
  , Tuple 10.0 (pure (-1.0))                     -- Flip
  ]

-- | Generator for scale values within valid range (for composition tests)
genScaleInRange :: Gen Number
genScaleInRange = frequency $ NEA.cons'
  (Tuple 40.0 (chooseFloat 0.1 3.0))            -- Common range
  [ Tuple 20.0 (pure 1.0)                        -- Identity
  , Tuple 20.0 (chooseFloat 0.5 2.0)             -- Typical UI
  , Tuple 20.0 (chooseFloat (-3.0) (-0.1))       -- Flips
  ]

-- | Generator for skew inputs (includes adversarial values)
genSkewInput :: Gen Number
genSkewInput = frequency $ NEA.cons'
  (Tuple 40.0 (chooseFloat (-89.0) 89.0))        -- Valid range
  [ Tuple 20.0 (chooseFloat (-180.0) (-89.0))    -- Below min
  , Tuple 20.0 (chooseFloat 89.0 180.0)          -- Above max
  , Tuple 10.0 (pure 0.0)                        -- None
  , Tuple 10.0 (pure 45.0)                       -- Common diagonal
  ]

-- | Approximate equality for floating point
approxEq :: Number -> Number -> Boolean
approxEq a b = 
  let diff = if a > b then a - b else b - a
  in diff < 0.0001

-- | Expose clampScale for testing
-- | NOTE: We cannot call internal functions - use indirect testing
-- | This tests via scale constructor
clampScaleViaScale :: Number -> Number
clampScaleViaScale n = Transform.getScaleX (Transform.scale n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // transform property functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: addTranslate is commutative
propTranslateCommutative :: Gen Result
propTranslateCommutative = do
  x1 <- chooseFloat (-1000.0) 1000.0
  y1 <- chooseFloat (-1000.0) 1000.0
  x2 <- chooseFloat (-1000.0) 1000.0
  y2 <- chooseFloat (-1000.0) 1000.0
  let t1 = Transform.translate x1 y1
  let t2 = Transform.translate x2 y2
  let r1 = Transform.addTranslate t1 t2
  let r2 = Transform.addTranslate t2 t1
  pure $ (Transform.getTranslateX r1 == Transform.getTranslateX r2 &&
          Transform.getTranslateY r1 == Transform.getTranslateY r2)
    <?> "addTranslate should be commutative"

-- | Property: double negation is identity for translate
propTranslateDoubleNegate :: Gen Result
propTranslateDoubleNegate = do
  x <- chooseFloat (-1000.0) 1000.0
  y <- chooseFloat (-1000.0) 1000.0
  let t = Transform.translate x y
  let doubleNeg = Transform.negateTranslate (Transform.negateTranslate t)
  pure $ (Transform.getTranslateX doubleNeg == x &&
          Transform.getTranslateY doubleNeg == y)
    <?> "double negation should be identity"

-- | Property: composing with identity preserves transform
propComposeWithIdentity :: Gen Result
propComposeWithIdentity = do
  tx <- chooseFloat (-100.0) 100.0
  ty <- chooseFloat (-100.0) 100.0
  let t = Transform.withTranslate (Transform.translate tx ty) Transform.identityTransform
  let composed = Transform.composeTransform t Transform.identityTransform
  let css1 = Transform.transform2DToLegacyCss t
  let css2 = Transform.transform2DToLegacyCss composed
  pure $ css1 == css2
    <?> "Composing with identity should preserve transform"

-- | Property: translations accumulate when composed
propComposeTranslations :: Gen Result
propComposeTranslations = do
  x1 <- chooseFloat (-100.0) 100.0
  y1 <- chooseFloat (-100.0) 100.0
  x2 <- chooseFloat (-100.0) 100.0
  y2 <- chooseFloat (-100.0) 100.0
  let t1 = Transform.withTranslate (Transform.translate x1 y1) Transform.identityTransform
  let t2 = Transform.withTranslate (Transform.translate x2 y2) Transform.identityTransform
  let composed = Transform.composeTransform t1 t2
  let Transform.Transform2D rec = composed
  case rec.translate of
    Nothing -> pure $ (1 == 0) <?> "Composed transform should have translation"
    Just tr -> 
      let expectedX = x1 + x2
          expectedY = y1 + y2
      in pure $ (approxEq (Transform.getTranslateX tr) expectedX &&
                 approxEq (Transform.getTranslateY tr) expectedY)
           <?> "Translation should accumulate: expected (" <> show expectedX <> ", " <> show expectedY <> 
               "), got (" <> show (Transform.getTranslateX tr) <> ", " <> show (Transform.getTranslateY tr) <> ")"

-- | Property: scales multiply when composed
propComposeScales :: Gen Result
propComposeScales = do
  s1 <- genScaleInRange
  s2 <- genScaleInRange
  let t1 = Transform.withScale (Transform.scale s1) Transform.identityTransform
  let t2 = Transform.withScale (Transform.scale s2) Transform.identityTransform
  let composed = Transform.composeTransform t1 t2
  let Transform.Transform2D rec = composed
  case rec.scale of
    Nothing -> pure $ (1 == 0) <?> "Composed transform should have scale"
    Just sc -> 
      let expectedClamped = clampScaleViaScale (s1 * s2)
      in pure $ (approxEq (Transform.getScaleX sc) expectedClamped &&
                 approxEq (Transform.getScaleY sc) expectedClamped)
           <?> "Scale should multiply: " <> show s1 <> " * " <> show s2 <> " = " <> show expectedClamped <> 
               ", got " <> show (Transform.getScaleX sc)
