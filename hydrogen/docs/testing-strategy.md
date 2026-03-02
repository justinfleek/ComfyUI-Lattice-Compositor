-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // docs // testing strategy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# HYDROGEN TESTING STRATEGY

**Date**: 2026-02-26
**Purpose**: Comprehensive testing strategy for production readiness
**Current Coverage**: 2.4% (22 test files for 911 source files)
**Target Coverage**: 80%+

---

## EXECUTIVE SUMMARY

The Hydrogen testing infrastructure has **excellent foundations** (property-based testing,
algebraic law verification) but **extremely limited coverage**. This document outlines
a systematic approach to achieving production-grade testing.

---

## CURRENT STATE ASSESSMENT

### What Exists (Strong)

| Area | Quality | Notes |
|------|---------|-------|
| QuickCheck integration | Excellent | Full property-based testing framework |
| Algebraic law tests | Excellent | Functor, Applicative, Monad laws verified |
| RemoteData tests | Excellent | All monad laws, comprehensive edge cases |
| QRCode tests | Excellent | GF arithmetic, Reed-Solomon, full spec coverage |
| Color edge cases | Good | Black, white, primaries, out-of-gamut |
| Division by zero | Good | Widget.purs handles adversarial inputs |

### What's Missing (Critical)

| Gap | Impact | Priority |
|-----|--------|----------|
| JSON roundtrip tests | Cannot verify serialization | CRITICAL |
| Browser/DOM tests | Rendering unverified | CRITICAL |
| Schema atom coverage | Core types untested | CRITICAL |
| Visual regression | UI changes undetected | HIGH |
| Performance benchmarks | Regressions undetected | MEDIUM |
| E2E/integration tests | User flows unverified | MEDIUM |

---

## TEST CATEGORIES

### 1. Property-Based Tests (QuickCheck)

**Purpose**: Verify algebraic properties hold for all inputs.

**Key Properties for Bounded Atoms**:

```purescript
-- Every bounded atom should satisfy these properties:

-- 1. Clamping is idempotent
prop_clamp_idempotent :: Atom -> Result
prop_clamp_idempotent x = construct (unwrap x) === x

-- 2. Values are within bounds
prop_within_bounds :: Atom -> Result
prop_within_bounds x =
  let v = toNumber x
      b = bounds
  in (v >= b.min && v <= b.max) <?> "Value within bounds"

-- 3. Lerp stays in bounds
prop_lerp_bounded :: Atom -> Atom -> Number -> Result
prop_lerp_bounded from to t =
  let result = lerp from to (clamp 0.0 1.0 t)
  in withinBounds result <?> "Lerp in bounds"

-- 4. Blend is symmetric at t=0.5
prop_blend_symmetric :: Atom -> Atom -> Result
prop_blend_symmetric a b =
  blend 0.5 a b === blend 0.5 b a <?> "Blend symmetric"

-- 5. Lerp endpoints
prop_lerp_endpoints :: Atom -> Atom -> Result
prop_lerp_endpoints a b =
  (lerp a b 0.0 === a) && (lerp a b 1.0 === b)
```

**Key Properties for ADTs**:

```purescript
-- Every ADT should satisfy:

-- 1. all* array contains all constructors
prop_all_complete :: forall a. Bounded a => Enum a => Array a -> Result
prop_all_complete all = length all === (fromEnum top - fromEnum bottom + 1)

-- 2. Show/Read roundtrip (if applicable)
prop_show_parse :: forall a. Show a => Parse a => a -> Result
prop_show_parse x = parse (show x) === Just x
```

### 2. Roundtrip Tests

**Purpose**: Verify encode/decode preserves values exactly.

```purescript
-- JSON roundtrip
prop_json_roundtrip :: forall a. Eq a => EncodeJson a => DecodeJson a => a -> Result
prop_json_roundtrip x = decodeJson (encodeJson x) === Right x

-- Canonical string roundtrip (for identity)
prop_canonical_roundtrip :: forall a. Identifiable a => a -> Result
prop_canonical_roundtrip x = fromCanonical (toCanonical x) === Just x

-- Binary roundtrip (for GPU types)
prop_binary_roundtrip :: DrawCommand -> Result
prop_binary_roundtrip cmd = deserialize (serialize cmd) === Right cmd
```

### 3. Unit Tests (spec)

**Purpose**: Verify specific behaviors and edge cases.

```purescript
-- Predicate tests
describe "Hue predicates" do
  it "isWarm returns true for red" do
    isWarm (hue 0) `shouldEqual` true
  it "isWarm returns true for yellow" do
    isWarm (hue 60) `shouldEqual` true
  it "isWarm returns false for cyan" do
    isWarm (hue 180) `shouldEqual` false

-- Edge case tests
describe "Hue edge cases" do
  it "wraps 360 to 0" do
    hueWrap 360 `shouldEqual` hue 0
  it "handles negative values" do
    hueWrap (-30) `shouldEqual` hue 330
  it "complement is involutive" do
    complement (complement (hue 45)) `shouldEqual` hue 45
```

### 4. Browser Tests (Puppeteer/Playwright)

**Purpose**: Verify actual rendering in browsers.

```javascript
// test/Browser/Render.spec.js
describe('Element Rendering', () => {
  test('Rectangle renders with correct dimensions', async () => {
    await page.goto('/test/rectangle');
    const dimensions = await page.evaluate(() => {
      const canvas = document.querySelector('canvas');
      const ctx = canvas.getContext('2d');
      // Measure rendered rectangle
      return measureRectangle(ctx);
    });
    expect(dimensions.width).toBe(200);
    expect(dimensions.height).toBe(100);
  });

  test('Text renders with correct font', async () => {
    await page.goto('/test/text');
    const fontUsed = await page.evaluate(() => {
      // Check rendered font metrics
    });
    expect(fontUsed.family).toBe('Inter');
    expect(fontUsed.size).toBe(16);
  });
});
```

### 5. Visual Regression Tests

**Purpose**: Detect unintended visual changes.

```javascript
// test/Visual/Regression.spec.js
describe('Visual Regression', () => {
  test('ColorPicker matches baseline', async () => {
    await page.goto('/components/colorpicker');
    const screenshot = await page.screenshot();
    expect(screenshot).toMatchImageSnapshot({
      failureThreshold: 0.01,
      failureThresholdType: 'percent'
    });
  });
});
```

### 6. Performance Tests

**Purpose**: Establish baselines and detect regressions.

```purescript
-- bench/Render.purs
benchmark "Render 1000 rectangles" do
  let elements = Array.replicate 1000 testRectangle
  measureTime $ render elements

benchmark "Diff 10000 element tree" do
  let old = generateTree 10000
  let new = modifyRandom old
  measureTime $ diff old new

benchmark "JSON encode 100 colors" do
  let colors = Array.replicate 100 testColor
  measureTime $ traverse encodeJson colors
```

---

## TEST FILE STRUCTURE

```
test/
├── Main.purs                     -- Test runner entry point
├── Property/
│   ├── BoundedAtoms.purs         -- Generic bounded type properties
│   ├── Serialization.purs        -- JSON/binary roundtrips
│   └── Laws.purs                 -- Algebraic laws (Functor, Monad, etc.)
├── Schema/
│   ├── Color/
│   │   ├── Atoms.purs            -- Hue, Channel, Saturation, etc.
│   │   ├── Molecules.purs        -- RGB, HSL, OKLCH, etc.
│   │   ├── Predicates.purs       -- isWarm, isGrayscale, etc.
│   │   └── Conversion.purs       -- Color space roundtrips
│   ├── Dimension/
│   │   ├── Atoms.purs            -- Pixel, AspectRatio, etc.
│   │   └── Molecules.purs        -- Size2D, Rect, etc.
│   ├── Typography/
│   │   ├── Atoms.purs            -- FontSize, FontWeight, etc.
│   │   └── Scale.purs            -- Type scale calculations
│   ├── Geometry/
│   │   ├── Vector.purs           -- Vec2, Vec3, Vec4 ops
│   │   ├── Matrix.purs           -- Matrix3, Matrix4 ops
│   │   └── Quaternion.purs       -- Rotation composition
│   ├── Temporal/
│   │   ├── Duration.purs         -- Duration arithmetic
│   │   └── Easing.purs           -- Easing curve properties
│   ├── Spatial/
│   │   └── PBR.purs              -- Metallic, Roughness, IOR
│   └── Audio/
│       └── Frequency.purs        -- Hertz, MidiNote conversions
├── Element/
│   ├── Pure.purs                 -- Pure Element properties
│   ├── Diff.purs                 -- Diffing algorithm
│   └── Render.purs               -- Render output verification
├── Integration/
│   ├── Playground.purs           -- Full playground flow
│   └── ColorPicker.purs          -- ColorPicker component
├── Browser/                      -- JavaScript test files
│   ├── Render.spec.js            -- Puppeteer rendering tests
│   ├── Events.spec.js            -- Mouse/keyboard events
│   └── Visual.spec.js            -- Screenshot regression
└── Benchmark/
    ├── Render.purs               -- Render timing
    ├── Diff.purs                 -- Diff timing
    └── Serialization.purs        -- JSON encode/decode timing
```

---

## PRIORITY IMPLEMENTATION ORDER

### Phase 1: Foundation (Weeks 1-2)

**Goal**: Test infrastructure and critical paths

1. **Set up test organization**
   - Create directory structure above
   - Configure spago for test dependencies
   - Set up CI test running

2. **Property test templates**
   ```purescript
   -- test/Property/BoundedAtoms.purs
   module Test.Property.BoundedAtoms where
   
   class BoundedAtom a where
     construct :: Number -> a
     unwrap :: a -> Number
     bounds :: Bounds
   
   prop_clamp_idempotent :: forall a. BoundedAtom a => a -> Result
   prop_within_bounds :: forall a. BoundedAtom a => a -> Result
   prop_lerp_bounded :: forall a. BoundedAtom a => a -> a -> Number -> Result
   ```

3. **JSON roundtrip tests for Color atoms**
   - Hue, Channel, Saturation, Lightness, Opacity
   - RGB, HSL, OKLCH molecules

### Phase 2: Schema Coverage (Weeks 3-4)

**Goal**: All bounded atoms have property tests

4. **Complete Dimension pillar tests**
5. **Complete Typography pillar tests**
6. **Complete Geometry pillar tests**
7. **Complete Temporal pillar tests**
8. **Complete remaining pillars**

### Phase 3: Browser Testing (Weeks 5-6)

**Goal**: Rendering verification

9. **Set up Puppeteer/Playwright**
10. **Basic rendering tests**
    - Rectangle, Circle, Text rendering
    - Color accuracy
    - Font metrics

11. **Visual regression baseline**
    - Capture baseline screenshots
    - Configure diff thresholds

### Phase 4: Integration & Performance (Weeks 7-8)

**Goal**: Full system verification

12. **Integration tests**
    - ColorPicker component flow
    - Form validation flow
    - Router navigation

13. **Performance benchmarks**
    - Render timing baselines
    - Diff algorithm timing
    - Serialization throughput

---

## SPECIFIC TEST IMPLEMENTATIONS

### Test: Hue Atom Properties

```purescript
-- test/Schema/Color/Atoms.purs

module Test.Schema.Color.Atoms where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (Result, (===), (<?>), arbitrary)
import Hydrogen.Schema.Color.Hue as Hue

hueSpec :: Spec Unit
hueSpec = describe "Hue atom" do
  describe "bounds" do
    quickCheck "values are 0-359" \(n :: Int) ->
      let h = Hue.hue n
          v = Hue.unwrap h
      in (v >= 0 && v <= 359) <?> "Hue in bounds"

  describe "wrapping" do
    quickCheck "360 wraps to 0" \_ ->
      Hue.hueWrap 360 === Hue.hue 0

    quickCheck "negative wraps correctly" \(n :: Int) ->
      let h = Hue.hueWrap (negate (abs n `mod` 360))
          v = Hue.unwrap h
      in (v >= 0 && v <= 359) <?> "Negative wrap in bounds"

  describe "rotation" do
    quickCheck "rotate 0 is identity" \h ->
      Hue.rotate 0 h === h

    quickCheck "rotate 360 is identity" \h ->
      Hue.rotate 360 h === h

    quickCheck "rotate is associative" \h d1 d2 ->
      Hue.rotate d1 (Hue.rotate d2 h) === Hue.rotate (d1 + d2) h

  describe "complement" do
    quickCheck "complement is involutive" \h ->
      Hue.complement (Hue.complement h) === h

    quickCheck "complement differs by 180" \h ->
      abs (Hue.unwrap h - Hue.unwrap (Hue.complement h)) === 180

  describe "predicates" do
    it "red is warm" do
      Hue.isWarm Hue.red `shouldEqual` true

    it "cyan is cool" do
      Hue.isCool Hue.cyan `shouldEqual` true

    it "warm and cool are not both true" do
      quickCheck \h ->
        not (Hue.isWarm h && Hue.isCool h) <?> "Mutual exclusion"

  describe "blend" do
    quickCheck "blend 0.0 returns first" \a b ->
      Hue.blend 0.0 a b === a

    quickCheck "blend 1.0 returns second" \a b ->
      Hue.blend 1.0 a b === b

    quickCheck "blendShortestPath takes short route" \_ ->
      -- 350 to 10 should go through 0, not through 180
      let result = Hue.blendShortestPath 0.5 (Hue.hue 350) (Hue.hue 10)
      in Hue.unwrap result === 0 <?> "Shortest path through 0"
```

### Test: JSON Roundtrip

```purescript
-- test/Property/Serialization.purs

module Test.Property.Serialization where

import Prelude
import Data.Either (Either(..))
import Data.Argonaut (encodeJson, decodeJson)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (Result, (===))

import Hydrogen.Codec.Json.Color as JsonColor

jsonRoundtripSpec :: Spec Unit
jsonRoundtripSpec = describe "JSON roundtrip" do
  describe "Color atoms" do
    quickCheck "Hue roundtrips" \h ->
      decodeJson (encodeJson h) === Right (h :: Hue)

    quickCheck "Channel roundtrips" \c ->
      decodeJson (encodeJson c) === Right (c :: Channel)

    quickCheck "RGB roundtrips" \rgb ->
      decodeJson (encodeJson rgb) === Right (rgb :: RGB)

    quickCheck "HSL roundtrips" \hsl ->
      decodeJson (encodeJson hsl) === Right (hsl :: HSL)

    quickCheck "OKLCH roundtrips" \oklch ->
      decodeJson (encodeJson oklch) === Right (oklch :: OKLCH)

  describe "Spatial atoms" do
    quickCheck "Metallic roundtrips" \m ->
      decodeJson (encodeJson m) === Right (m :: Metallic)

    quickCheck "Roughness roundtrips" \r ->
      decodeJson (encodeJson r) === Right (r :: Roughness)
```

### Test: Color Conversion Accuracy

```purescript
-- test/Schema/Color/Conversion.purs

module Test.Schema.Color.Conversion where

import Prelude
import Test.Spec (Spec, describe)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (Result, (<?>))

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Conversion as Convert

conversionSpec :: Spec Unit
conversionSpec = describe "Color conversion" do
  describe "RGB <-> HSL" do
    quickCheck "roundtrip preserves value" \rgb ->
      let hsl = Convert.rgbToHsl rgb
          rgb' = Convert.hslToRgb hsl
      in closeEnough rgb rgb' <?> "RGB->HSL->RGB roundtrip"

  describe "RGB <-> OKLCH" do
    quickCheck "roundtrip preserves value" \rgb ->
      let oklch = Convert.rgbToOklch rgb
          rgb' = Convert.oklchToRgb oklch
      in closeEnough rgb rgb' <?> "RGB->OKLCH->RGB roundtrip"

  describe "Edge cases" do
    it "pure black converts correctly" do
      let black = RGB.rgb 0 0 0
          hsl = Convert.rgbToHsl black
      HSL.lightness hsl `shouldSatisfy` \l -> l < 1

    it "pure white converts correctly" do
      let white = RGB.rgb 255 255 255
          hsl = Convert.rgbToHsl white
      HSL.lightness hsl `shouldSatisfy` \l -> l > 99

-- Helper: colors are "close enough" within rounding tolerance
closeEnough :: RGB -> RGB -> Boolean
closeEnough a b =
  let diff = abs (RGB.red a - RGB.red b)
           + abs (RGB.green a - RGB.green b)
           + abs (RGB.blue a - RGB.blue b)
  in diff <= 3  -- Allow 1 per channel for rounding
```

---

## GENERATOR PATTERNS

For QuickCheck to work, atoms need `Arbitrary` instances:

```purescript
-- test/Generators.purs

module Test.Generators where

import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (chooseInt, choose)

import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Spatial.Metallic as Metallic

instance arbitraryHue :: Arbitrary Hue where
  arbitrary = Hue.hue <$> chooseInt 0 359

instance arbitraryChannel :: Arbitrary Channel where
  arbitrary = Channel.channel <$> chooseInt 0 255

instance arbitraryMetallic :: Arbitrary Metallic where
  arbitrary = Metallic.metallic <$> choose 0.0 1.0

instance arbitraryRGB :: Arbitrary RGB where
  arbitrary = RGB.rgb <$> arbitrary <*> arbitrary <*> arbitrary
```

---

## CI INTEGRATION

### GitHub Actions Workflow

```yaml
# .github/workflows/test.yml
name: Test
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      
      - name: Build
        run: nix develop --command spago build
        
      - name: Test
        run: nix develop --command spago test
        
      - name: Browser Tests
        run: |
          nix develop --command npm install
          nix develop --command npm run test:browser
          
      - name: Upload Coverage
        uses: codecov/codecov-action@v3
```

---

## METRICS & GOALS

### Coverage Targets

| Milestone | Target | Date |
|-----------|--------|------|
| Baseline | 10% | Week 2 |
| Foundation | 30% | Week 4 |
| Solid | 50% | Week 6 |
| Production | 80% | Week 12 |

### Quality Metrics

| Metric | Current | Target |
|--------|---------|--------|
| Property test count | ~20 | 500+ |
| Unit test count | ~50 | 1000+ |
| Browser test count | 0 | 100+ |
| Visual regression baselines | 0 | 50+ |
| Performance benchmarks | 0 | 20+ |

---

*Last updated: 2026-02-26*
