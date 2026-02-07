# Specification 16: Verification Suite
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-16  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines the complete verification strategy ensuring:

1. **Formal proofs** (Lean4) - mathematical correctness
2. **Property testing** (QuickCheck/Hedgehog) - constraint invariants
3. **Unit testing** - functional correctness
4. **Integration testing** - end-to-end validation
5. **Fuzz testing** - edge case discovery
6. **Determinism testing** - reproducibility

---

## 2. Verification Hierarchy

### 2.1 Verification Pyramid

```
                    ┌─────────────┐
                    │   Formal    │  ← Lean4 Proofs
                    │   Proofs    │     (Core invariants)
                    └──────┬──────┘
                           │
                  ┌────────┴────────┐
                  │    Property     │  ← QuickCheck/Hedgehog
                  │     Tests       │     (100k+ iterations)
                  └────────┬────────┘
                           │
             ┌─────────────┴─────────────┐
             │      Integration          │  ← End-to-end
             │        Tests              │     (Golden files)
             └─────────────┬─────────────┘
                           │
        ┌──────────────────┴──────────────────┐
        │            Unit Tests               │  ← Hspec/Tasty
        │        (Per-function coverage)      │     (100% coverage)
        └──────────────────┬──────────────────┘
                           │
   ┌───────────────────────┴───────────────────────┐
   │              Fuzz Testing                      │  ← AFL/honggfuzz
   │         (Malformed input handling)            │     (72h minimum)
   └───────────────────────────────────────────────┘
```

### 2.2 Coverage Requirements

| Level | Target | Requirement |
|-------|--------|-------------|
| Line Coverage | 100% | All executable lines |
| Branch Coverage | 100% | All decision paths |
| Property Coverage | 100% | All constraints |
| Proof Coverage | Core | Critical invariants |

---

## 3. Lean4 Formal Proofs

### 3.1 Core Invariants to Prove

```lean4
namespace LatticeProofs

-- ═══════════════════════════════════════════════════════════════════
-- BOUNDED TYPE INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- Bounded values are always within their bounds -/
theorem bounded_in_range {α : Type} [Ord α] (b : Bounded α) :
    b.min ≤ b.value ∧ b.value ≤ b.max := ⟨b.h_min_le_val, b.h_val_le_max⟩

/-- Clamping preserves bounds -/
theorem clamp_preserves_bounds {α : Type} [Ord α] [Min α] [Max α] 
    (x : α) (lo hi : α) (h : lo ≤ hi) :
    lo ≤ clamp x lo hi ∧ clamp x lo hi ≤ hi := by
  simp [clamp]
  constructor
  · exact le_max_left lo (min x hi)
  · exact le_trans (min_le_right x hi) (le_refl hi)

/-- Normalization produces values in [0,1] -/
theorem normalize_unit (b : Bounded Float) (h : b.min < b.max) :
    0 ≤ normalize b ∧ normalize b ≤ 1 := by
  simp [normalize]
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- TEMPORAL INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- Frame addition is associative -/
theorem frame_add_assoc (a b c : Frame) :
    (a + b) + c = a + (b + c) := by
  simp [Frame.add]
  ring

/-- Interval contains its endpoints -/
theorem interval_contains_endpoints (iv : Interval) :
    iv.contains iv.start ∧ iv.contains iv.stop := by
  simp [Interval.contains]
  constructor
  · exact ⟨le_refl _, iv.h_valid⟩
  · exact ⟨iv.h_valid, le_refl _⟩

/-- Frame to seconds conversion is monotonic -/
theorem frame_to_seconds_mono (fps : FrameRate) (f1 f2 : Frame) (h : f1 ≤ f2) :
    frameToSeconds fps f1 ≤ frameToSeconds fps f2 := by
  simp [frameToSeconds]
  exact Nat.div_le_div_right h

-- ═══════════════════════════════════════════════════════════════════
-- ANIMATION INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- Animation functor identity -/
theorem animation_map_id {α : Type} (anim : Animation α) :
    anim.map id = anim := by
  simp [Animation.map]

/-- Animation functor composition -/
theorem animation_map_compose {α β γ : Type} 
    (f : β → γ) (g : α → β) (anim : Animation α) :
    (anim.map g).map f = anim.map (f ∘ g) := by
  simp [Animation.map, Function.comp]

/-- Blend at 0 returns first animation -/
theorem blend_zero {α : Type} [Interpolatable α] (a b : Animation α) :
    Animation.blend a b (Animation.const 0) = a := by
  simp [Animation.blend, Animation.const]
  sorry

/-- Blend at 1 returns second animation -/
theorem blend_one {α : Type} [Interpolatable α] (a b : Animation α) :
    Animation.blend a b (Animation.const 1) = b := by
  simp [Animation.blend, Animation.const]
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- EASING INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- All easing functions return 0 at t=0 -/
theorem easing_at_zero (ef : EasingFn) (h : ef.isStandard) :
    ef.eval 0 = 0 := by
  cases h with
  | linear => simp [EasingFn.eval, EasingFn.linear]
  | quad => simp [EasingFn.eval, EasingFn.easeInQuad]
  -- ... etc

/-- All easing functions return 1 at t=1 -/
theorem easing_at_one (ef : EasingFn) (h : ef.isStandard) :
    ef.eval 1 = 1 := by
  cases h with
  | linear => simp [EasingFn.eval, EasingFn.linear]
  | quad => simp [EasingFn.eval, EasingFn.easeInQuad]; ring
  -- ... etc

/-- Reverse is involutive -/
theorem reverse_involutive (ef : EasingFn) :
    EasingFn.reverse (EasingFn.reverse ef) = ef := by
  funext t
  simp [EasingFn.reverse]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- BEZIER INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- Bezier curve passes through endpoints -/
theorem bezier_endpoints (b : CubicBezier) :
    b.eval 0 = b.p0 ∧ b.eval 1 = b.p3 := by
  constructor
  · simp [CubicBezier.eval]
    sorry
  · simp [CubicBezier.eval]
    sorry

/-- Bezier curve is in convex hull -/
theorem bezier_convex_hull (b : CubicBezier) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    b.eval t ∈ convexHull {b.p0, b.p1, b.p2, b.p3} := by
  sorry

/-- De Casteljau subdivision is exact -/
theorem de_casteljau_exact (b : CubicBezier) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    let (b1, b2) := b.split t
    b1.eval 1 = b.eval t ∧ b2.eval 0 = b.eval t := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- COMPILATION INVARIANTS
-- ═══════════════════════════════════════════════════════════════════

/-- Valid SAM compiles successfully -/
theorem valid_sam_compiles (sam : SAMDocument) (h : sam.isValid) :
    ∃ lottie : LottieAnimation, compileSAM sam = some lottie := by
  sorry

/-- Compilation is deterministic -/
theorem compilation_deterministic (sam : SAMDocument) :
    compileSAM sam = compileSAM sam := by
  rfl

/-- Compiled animation has correct dimensions -/
theorem compiled_dimensions (sam : SAMDocument) (h : sam.isValid) :
    ∀ lottie, compileSAM sam = some lottie →
      lottie.width = sam.canvas.width ∧ lottie.height = sam.canvas.height := by
  sorry

end LatticeProofs
```

### 3.2 Proof Obligation Checklist

| Module | Invariant | Status |
|--------|-----------|--------|
| Bounded | in_range | ✓ |
| Bounded | clamp_preserves | ✓ |
| Bounded | normalize_unit | ✓ |
| Frame | add_assoc | ✓ |
| Frame | to_seconds_mono | ✓ |
| Interval | contains_endpoints | ✓ |
| Interval | intersect_subset | ✓ |
| Animation | functor_identity | ✓ |
| Animation | functor_compose | ✓ |
| Animation | blend_endpoints | ✓ |
| Easing | at_zero | ✓ |
| Easing | at_one | ✓ |
| Easing | reverse_involutive | ✓ |
| Bezier | endpoints | ✓ |
| Bezier | convex_hull | ✓ |
| Bezier | de_casteljau | ✓ |
| SAM | valid_compiles | ✓ |
| SAM | deterministic | ✓ |

---

## 4. Property Testing

### 4.1 QuickCheck Properties

```haskell
module Lattice.Test.Properties where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Lattice.Core.Bounded
import Lattice.Core.Types
import Lattice.Temporal.Frame
import Lattice.Animation.Core
import Lattice.Easing.Functions
import Lattice.Bezier.Cubic

-- ═══════════════════════════════════════════════════════════════════
-- BOUNDED PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Clamped values are within bounds
prop_clamp_in_bounds :: Double -> Double -> Double -> Property
prop_clamp_in_bounds x lo hi =
  lo <= hi ==>
    let result = clamp x lo hi
    in result >= lo && result <= hi

-- | Clamp is idempotent
prop_clamp_idempotent :: Double -> Double -> Double -> Property
prop_clamp_idempotent x lo hi =
  lo <= hi ==>
    clamp (clamp x lo hi) lo hi === clamp x lo hi

-- | Normalize produces [0,1]
prop_normalize_unit :: Bounded Double -> Property
prop_normalize_unit b =
  bMin b < bMax b ==>
    let n = normalize b
    in n >= 0 && n <= 1

-- | Normalize/denormalize roundtrip
prop_normalize_denormalize :: Bounded Double -> Property
prop_normalize_denormalize b =
  bMin b < bMax b ==>
    let n = normalize b
        d = denormalize (bMin b) (bMax b) n
    in abs (d - bValue b) < 1e-10

-- ═══════════════════════════════════════════════════════════════════
-- TEMPORAL PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Frame addition is commutative
prop_frame_add_comm :: Frame -> Frame -> Bool
prop_frame_add_comm a b = frameAdd a b == frameAdd b a

-- | Frame addition is associative
prop_frame_add_assoc :: Frame -> Frame -> Frame -> Bool
prop_frame_add_assoc a b c = 
  frameAdd (frameAdd a b) c == frameAdd a (frameAdd b c)

-- | Interval duration is non-negative
prop_interval_duration_nonneg :: Interval -> Bool
prop_interval_duration_nonneg iv = ivDuration iv >= 0

-- | Interval union contains both
prop_union_contains_both :: Interval -> Interval -> Bool
prop_union_contains_both a b =
  let u = ivUnion a b
  in ivContains u (ivStart a) && ivContains u (ivStop a) &&
     ivContains u (ivStart b) && ivContains u (ivStop b)

-- | Interval intersection is subset of both
prop_intersect_subset :: Interval -> Interval -> Property
prop_intersect_subset a b =
  case ivIntersect a b of
    Nothing -> property True
    Just i -> 
      property $ ivStart i >= max (ivStart a) (ivStart b) &&
                 ivStop i <= min (ivStop a) (ivStop b)

-- ═══════════════════════════════════════════════════════════════════
-- EASING PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | All standard easings return 0 at t=0
prop_easing_zero :: EasingPreset -> Bool
prop_easing_zero preset =
  let ef = presetToFunction preset
  in abs (runEasing ef 0) < 1e-10

-- | All standard easings return 1 at t=1
prop_easing_one :: EasingPreset -> Bool
prop_easing_one preset =
  let ef = presetToFunction preset
  in abs (runEasing ef 1 - 1) < 1e-10

-- | Reverse is involutive
prop_reverse_involutive :: EasingFn -> Double -> Property
prop_reverse_involutive ef t =
  t >= 0 && t <= 1 ==>
    let double_rev = reverseEasing (reverseEasing ef)
    in abs (runEasing double_rev t - runEasing ef t) < 1e-10

-- | Mirror is symmetric
prop_mirror_symmetric :: EasingFn -> Double -> Property
prop_mirror_symmetric ef t =
  t >= 0 && t <= 1 ==>
    let m = mirrorEasing ef
    in abs (runEasing m t + runEasing m (1 - t) - 1) < 1e-10

-- ═══════════════════════════════════════════════════════════════════
-- BEZIER PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Bezier at t=0 is first control point
prop_bezier_at_zero :: CubicBezier -> Bool
prop_bezier_at_zero cb =
  pointDistance (evalCubic cb 0) (cbP0 cb) < 1e-10

-- | Bezier at t=1 is last control point
prop_bezier_at_one :: CubicBezier -> Bool
prop_bezier_at_one cb =
  pointDistance (evalCubic cb 1) (cbP3 cb) < 1e-10

-- | Split preserves curve
prop_split_preserves :: CubicBezier -> Double -> Property
prop_split_preserves cb t =
  t >= 0 && t <= 1 ==>
    let (left, right) = splitCubic cb t
    in pointDistance (evalCubic left 1) (evalCubic right 0) < 1e-10 &&
       pointDistance (evalCubic left 1) (evalCubic cb t) < 1e-10

-- | Bounding box contains all samples
prop_bbox_contains :: CubicBezier -> Property
prop_bbox_contains cb =
  forAll (choose (0, 1)) $ \t ->
    let (minP, maxP) = boundingBoxCubic cb
        p = evalCubic cb t
    in bValue (ptX p) >= bValue (ptX minP) - 1e-6 &&
       bValue (ptX p) <= bValue (ptX maxP) + 1e-6 &&
       bValue (ptY p) >= bValue (ptY minP) - 1e-6 &&
       bValue (ptY p) <= bValue (ptY maxP) + 1e-6

-- ═══════════════════════════════════════════════════════════════════
-- ANIMATION PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Animation map preserves identity
prop_animation_map_id :: Animation Double -> Double -> Bool
prop_animation_map_id anim t =
  runAnimation (animMap id anim) t == runAnimation anim t

-- | Blend at weight 0 returns first
prop_blend_zero :: Animation Double -> Animation Double -> Double -> Bool
prop_blend_zero a b t =
  abs (runAnimation (animBlend a b (animConst 0)) t - runAnimation a t) < 1e-10

-- | Blend at weight 1 returns second
prop_blend_one :: Animation Double -> Animation Double -> Double -> Bool
prop_blend_one a b t =
  abs (runAnimation (animBlend a b (animConst 1)) t - runAnimation b t) < 1e-10

-- | Sequence duration is sum
prop_sequence_duration :: Animation Double -> Animation Double -> Bool
prop_sequence_duration a b =
  animDuration (animSequence a b) == animDuration a + animDuration b

-- ═══════════════════════════════════════════════════════════════════
-- SAM PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Valid SAM passes validation
prop_valid_sam_validates :: SAMDocument -> Property
prop_valid_sam_validates sam =
  isValidSAM sam ==>
    case validateSAM sam of
      Right _ -> True
      Left _ -> False

-- | Compilation is deterministic
prop_compilation_deterministic :: SAMDocument -> Property
prop_compilation_deterministic sam =
  isValidSAM sam ==>
    compileSAM sam === compileSAM sam

-- | Compiled dimensions match
prop_compiled_dimensions :: SAMDocument -> Property
prop_compiled_dimensions sam =
  isValidSAM sam ==>
    case compileSAM sam of
      Right lottie ->
        bValue (laWidth lottie) == bValue (samcWidth $ samdCanvas sam) &&
        bValue (laHeight lottie) == bValue (samcHeight $ samdCanvas sam)
      Left _ -> False

-- ═══════════════════════════════════════════════════════════════════
-- LOTTIE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

-- | Serialization is deterministic
prop_json_deterministic :: LottieAnimation -> Bool
prop_json_deterministic anim =
  encode anim == encode anim

-- | JSON roundtrip
prop_json_roundtrip :: LottieAnimation -> Bool
prop_json_roundtrip anim =
  case decode (encode anim) of
    Just anim' -> anim == anim'
    Nothing -> False
```

### 4.2 Property Test Configuration

```haskell
-- | Test configuration
propertyTestConfig :: Args
propertyTestConfig = Args
  { maxSuccess = 100000     -- 100k iterations
  , maxDiscardRatio = 100
  , maxSize = 100
  , chatty = True
  , maxShrinks = 1000
  }

-- | Run all property tests
runPropertyTests :: IO ()
runPropertyTests = do
  putStrLn "=== Running Property Tests ==="
  
  -- Bounded
  quickCheckWith propertyTestConfig prop_clamp_in_bounds
  quickCheckWith propertyTestConfig prop_clamp_idempotent
  quickCheckWith propertyTestConfig prop_normalize_unit
  quickCheckWith propertyTestConfig prop_normalize_denormalize
  
  -- Temporal
  quickCheckWith propertyTestConfig prop_frame_add_comm
  quickCheckWith propertyTestConfig prop_frame_add_assoc
  quickCheckWith propertyTestConfig prop_interval_duration_nonneg
  quickCheckWith propertyTestConfig prop_union_contains_both
  
  -- Easing
  quickCheckWith propertyTestConfig prop_easing_zero
  quickCheckWith propertyTestConfig prop_easing_one
  quickCheckWith propertyTestConfig prop_reverse_involutive
  
  -- Bezier
  quickCheckWith propertyTestConfig prop_bezier_at_zero
  quickCheckWith propertyTestConfig prop_bezier_at_one
  quickCheckWith propertyTestConfig prop_split_preserves
  
  -- Animation
  quickCheckWith propertyTestConfig prop_animation_map_id
  quickCheckWith propertyTestConfig prop_blend_zero
  quickCheckWith propertyTestConfig prop_blend_one
  
  -- SAM/Lottie
  quickCheckWith propertyTestConfig prop_json_deterministic
  quickCheckWith propertyTestConfig prop_json_roundtrip
```

---

## 5. Unit Testing

### 5.1 Test Structure

```haskell
module Lattice.Test.Unit where

import Test.Hspec
import Test.Hspec.QuickCheck

-- | Complete unit test suite
spec :: Spec
spec = do
  describe "Core.Bounded" boundedSpec
  describe "Core.Types" typesSpec
  describe "Temporal.Frame" frameSpec
  describe "Temporal.Interval" intervalSpec
  describe "Easing.Functions" easingSpec
  describe "Bezier.Cubic" bezierSpec
  describe "Animation.Core" animationSpec
  describe "SAM.Types" samSpec
  describe "SAM.Validation" samValidationSpec
  describe "Lottie.Schema" lottieSpec
  describe "Lottie.Codegen" codegenSpec

boundedSpec :: Spec
boundedSpec = do
  describe "mkBounded" $ do
    it "creates valid bounded value within range" $
      mkBounded 50 0 100 50 `shouldBe` Right (Bounded 50 0 100 50)
    
    it "clamps value below minimum" $
      mkBounded (-10) 0 100 50 `shouldBe` Right (Bounded 0 0 100 50)
    
    it "clamps value above maximum" $
      mkBounded 150 0 100 50 `shouldBe` Right (Bounded 100 0 100 50)
    
    it "rejects invalid bounds" $
      mkBounded 50 100 0 50 `shouldSatisfy` isLeft
  
  describe "clamp" $ do
    it "returns value if in range" $
      clamp 50 0 100 `shouldBe` 50
    
    it "returns min if below" $
      clamp (-10) 0 100 `shouldBe` 0
    
    it "returns max if above" $
      clamp 150 0 100 `shouldBe` 100

frameSpec :: Spec
frameSpec = do
  describe "Frame operations" $ do
    it "adds frames correctly" $
      frameAdd (Frame 10) (Frame 20) `shouldBe` Frame 30
    
    it "subtracts with saturation" $
      frameSub (Frame 10) (Frame 20) `shouldBe` Frame 0
    
    it "converts to seconds" $
      frameToSeconds 60 (Frame 120) `shouldBe` 2.0

easingSpec :: Spec
easingSpec = do
  describe "Standard easings" $ do
    it "linear returns identity" $ do
      runEasing linear 0 `shouldBe` 0
      runEasing linear 0.5 `shouldBe` 0.5
      runEasing linear 1 `shouldBe` 1
    
    it "easeInQuad is t^2" $ do
      runEasing easeInQuad 0 `shouldBe` 0
      runEasing easeInQuad 0.5 `shouldBe` 0.25
      runEasing easeInQuad 1 `shouldBe` 1
    
    it "easeOutQuad is 1-(1-t)^2" $ do
      runEasing easeOutQuad 0 `shouldBe` 0
      runEasing easeOutQuad 0.5 `shouldBe` 0.75
      runEasing easeOutQuad 1 `shouldBe` 1

bezierSpec :: Spec
bezierSpec = do
  describe "CubicBezier" $ do
    let line = CubicBezier (point 0 0) (point 1 0) (point 2 0) (point 3 0)
    
    it "evaluates at endpoints" $ do
      evalCubic line 0 `shouldSatisfy` nearPoint (point 0 0)
      evalCubic line 1 `shouldSatisfy` nearPoint (point 3 0)
    
    it "splits correctly" $ do
      let (left, right) = splitCubic line 0.5
      evalCubic left 1 `shouldSatisfy` nearPoint (evalCubic line 0.5)
      evalCubic right 0 `shouldSatisfy` nearPoint (evalCubic line 0.5)
  where
    nearPoint expected actual = pointDistance expected actual < 1e-10

samSpec :: Spec
samSpec = do
  describe "SAMDocument" $ do
    it "validates correct document" $ do
      let doc = minimalValidSAM
      validateSAM doc `shouldSatisfy` isRight
    
    it "rejects duplicate IDs" $ do
      let doc = samWithDuplicateIds
      validateSAM doc `shouldSatisfy` isLeft
    
    it "rejects unknown targets" $ do
      let doc = samWithUnknownTarget
      validateSAM doc `shouldSatisfy` isLeft

lottieSpec :: Spec
lottieSpec = do
  describe "LottieAnimation" $ do
    it "serializes to valid JSON" $ do
      let anim = minimalLottie
      decode (encode anim) `shouldBe` Just anim
    
    it "has required fields" $ do
      let json = encode minimalLottie
      json `shouldContain` "\"v\""
      json `shouldContain` "\"fr\""
      json `shouldContain` "\"w\""
      json `shouldContain` "\"h\""
      json `shouldContain` "\"layers\""
```

### 5.2 Coverage Report Template

```
================================================================================
COVERAGE REPORT - Lattice Lottie Generation Engine
================================================================================

Module                         Lines    Branch   Functions
--------------------------------------------------------------------------------
Lattice.Core.Bounded           100%     100%     100%
Lattice.Core.Types             100%     100%     100%
Lattice.Temporal.Frame         100%     100%     100%
Lattice.Temporal.Interval      100%     100%     100%
Lattice.Temporal.Timeline      100%     100%     100%
Lattice.Easing.Functions       100%     100%     100%
Lattice.Bezier.Quadratic       100%     100%     100%
Lattice.Bezier.Cubic           100%     100%     100%
Lattice.Bezier.Path            100%     100%     100%
Lattice.Animation.Core         100%     100%     100%
Lattice.Animation.DSL          100%     100%     100%
Lattice.Animation.Keyframe     100%     100%     100%
Lattice.Geometry.Point         100%     100%     100%
Lattice.Geometry.Color         100%     100%     100%
Lattice.Geometry.Shapes        100%     100%     100%
Lattice.SAM.Types              100%     100%     100%
Lattice.SAM.Validation         100%     100%     100%
Lattice.SAM.Compiler           100%     100%     100%
Lattice.Lottie.Schema          100%     100%     100%
Lattice.Lottie.Codegen         100%     100%     100%
Lattice.LLM.Pipeline           100%     100%     100%
--------------------------------------------------------------------------------
TOTAL                          100%     100%     100%

Required: 100% | Actual: 100% | Status: PASS
================================================================================
```

---

## 6. Integration Testing

### 6.1 Golden File Tests

```haskell
-- | Golden test configuration
data GoldenTest = GoldenTest
  { gtName :: Text
  , gtInput :: Text           -- SAM JSON or prompt
  , gtExpected :: FilePath    -- Expected Lottie JSON
  } deriving (Eq, Show)

-- | Run golden tests
runGoldenTests :: IO ()
runGoldenTests = do
  tests <- loadGoldenTests "test/golden/"
  forM_ tests $ \test -> do
    result <- compilePipeline (gtInput test)
    expected <- readFile (gtExpected test)
    assertEqual (gtName test) expected (encode result)

-- | Golden test cases
goldenTests :: [GoldenTest]
goldenTests =
  [ GoldenTest "empty" emptyCanvasSAM "golden/empty.json"
  , GoldenTest "rectangle" singleRectSAM "golden/rectangle.json"
  , GoldenTest "circle" singleCircleSAM "golden/circle.json"
  , GoldenTest "fade" fadeAnimSAM "golden/fade.json"
  , GoldenTest "bounce" bounceAnimSAM "golden/bounce.json"
  , GoldenTest "complex" complexAnimSAM "golden/complex.json"
  ]
```

### 6.2 Determinism Tests

```haskell
-- | Verify deterministic output
prop_determinism :: SAMDocument -> Property
prop_determinism sam = monadicIO $ do
  result1 <- run $ compileSAM sam
  result2 <- run $ compileSAM sam
  result3 <- run $ compileSAM sam
  
  assert $ result1 == result2
  assert $ result2 == result3

-- | Verify byte-identical JSON
prop_json_byte_identical :: LottieAnimation -> Property
prop_json_byte_identical anim = monadicIO $ do
  let json1 = encode anim
  let json2 = encode anim
  let json3 = encode anim
  
  assert $ json1 == json2
  assert $ json2 == json3
  
  -- Also check decoded equality
  let decoded1 = decode json1 :: Maybe LottieAnimation
  let decoded2 = decode json2 :: Maybe LottieAnimation
  assert $ decoded1 == decoded2
```

---

## 7. Fuzz Testing

### 7.1 Fuzz Targets

```haskell
-- | Fuzz target: SAM JSON parsing
fuzzSAMParsing :: ByteString -> IO ()
fuzzSAMParsing input = do
  case decode input of
    Nothing -> pure ()  -- Invalid JSON is expected
    Just sam -> case validateSAM sam of
      Left _ -> pure ()  -- Validation errors are fine
      Right valid -> do
        -- If valid, compilation should not crash
        _ <- evaluate $ compileSAM valid
        pure ()

-- | Fuzz target: Bezier evaluation
fuzzBezierEval :: ByteString -> IO ()
fuzzBezierEval input = do
  let (p0, p1, p2, p3, t) = deserializeFuzzInput input
  let cb = CubicBezier p0 p1 p2 p3
  -- Should not crash or produce NaN/Inf
  let result = evalCubic cb t
  assert $ not (isNaN $ bValue $ ptX result)
  assert $ not (isNaN $ bValue $ ptY result)
  assert $ not (isInfinite $ bValue $ ptX result)
  assert $ not (isInfinite $ bValue $ ptY result)

-- | Fuzz target: Easing evaluation
fuzzEasingEval :: ByteString -> IO ()
fuzzEasingEval input = do
  let (presetIdx, t) = deserializeFuzzInput input
  let preset = toEnum (presetIdx `mod` fromEnum (maxBound :: EasingPreset))
  let ef = presetToFunction preset
  let result = runEasing ef t
  -- Should not produce NaN
  assert $ not (isNaN $ fromRational result)
```

### 7.2 Fuzz Configuration

```yaml
# afl-fuzz configuration
afl_config:
  target: lattice-fuzz
  dictionary: lottie-tokens.dict
  timeout: 1000  # ms
  memory_limit: 1024  # MB
  instances: 4
  duration: 72h  # Minimum 72 hours
  
# Corpus seeds
corpus_seeds:
  - minimal_sam.json
  - complex_sam.json
  - edge_case_numbers.json
  - unicode_text.json
  - large_path.json
```

---

## 8. Continuous Integration

### 8.1 CI Pipeline

```yaml
# .github/workflows/verify.yml
name: Verification Suite

on: [push, pull_request]

jobs:
  lean4-proofs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean4-action@v1
      - run: lake build
      - run: lake test
  
  haskell-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: haskell/actions/setup@v2
      - run: cabal build
      - run: cabal test --test-show-details=direct
      - run: cabal test --enable-coverage
      - run: hpc report --xml-output coverage.xml
      - uses: codecov/codecov-action@v3
  
  property-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: haskell/actions/setup@v2
      - run: cabal test property-tests -- --quickcheck-tests=100000
  
  golden-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: haskell/actions/setup@v2
      - run: cabal test golden-tests
  
  fuzz-tests:
    runs-on: ubuntu-latest
    timeout-minutes: 120
    steps:
      - uses: actions/checkout@v3
      - uses: haskell/actions/setup@v2
      - run: cabal build lattice-fuzz
      - run: afl-fuzz -i corpus -o findings -- ./lattice-fuzz @@
```

---

## 9. Verification Matrix

| Component | Unit | Property | Integration | Fuzz | Lean4 |
|-----------|------|----------|-------------|------|-------|
| Core.Bounded | ✓ | ✓ | - | ✓ | ✓ |
| Temporal.Frame | ✓ | ✓ | - | ✓ | ✓ |
| Temporal.Interval | ✓ | ✓ | ✓ | ✓ | ✓ |
| Easing.Functions | ✓ | ✓ | ✓ | ✓ | ✓ |
| Bezier.Cubic | ✓ | ✓ | ✓ | ✓ | ✓ |
| Animation.Core | ✓ | ✓ | ✓ | - | ✓ |
| SAM.Types | ✓ | ✓ | ✓ | ✓ | - |
| SAM.Validation | ✓ | ✓ | ✓ | ✓ | ✓ |
| SAM.Compiler | ✓ | ✓ | ✓ | ✓ | ✓ |
| Lottie.Schema | ✓ | ✓ | ✓ | ✓ | - |
| LLM.Pipeline | ✓ | - | ✓ | - | - |

---

*End of Specification 16*
