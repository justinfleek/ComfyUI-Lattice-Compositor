-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // docs // remediation tracker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# HYDROGEN REMEDIATION TRACKER

**Purpose**: Track all issues identified in the Production Readiness Audit.
**Last Updated**: 2026-02-26

---

## STATUS LEGEND

- [ ] Not started
- [~] In progress
- [x] Complete
- [!] Blocked

---

## 1. ADT COMPLETENESS - Missing `all*` Arrays

**Priority**: Medium
**Effort**: 2-3 hours total
**Pattern**: Add `all<TypeName> :: Array <TypeName>` export with all constructors

### Tasks

- [x] `SwipeDirection` → Add `allSwipeDirections`
  - File: `src/Hydrogen/Schema/Gestural/Gesture/Swipe.purs`
  - Constructors: `SwipeUp`, `SwipeDown`, `SwipeLeft`, `SwipeRight`
  - **COMPLETED**: 2026-02-26

- [x] `AnimationDirection` → Add `allAnimationDirections`
  - File: `src/Hydrogen/Schema/Motion/KeyframeAnimation.purs`
  - Constructors: `DirectionNormal`, `DirectionReverse`, `DirectionAlternate`, `DirectionAlternateReverse`
  - **COMPLETED**: 2026-02-26

- [x] `AnimationFillMode` → Add `allAnimationFillModes`
  - File: `src/Hydrogen/Schema/Motion/KeyframeAnimation.purs`
  - Constructors: `FillNone`, `FillForwards`, `FillBackwards`, `FillBoth`
  - **COMPLETED**: 2026-02-26

- [x] `AnimationPlayState` → Add `allAnimationPlayStates`
  - File: `src/Hydrogen/Schema/Motion/KeyframeAnimation.purs`
  - Constructors: `PlayStatePlaying`, `PlayStatePaused`
  - **COMPLETED**: 2026-02-26

- [~] `Easing` → N/A (not a simple enumeration)
  - File: `src/Hydrogen/Schema/Temporal/Easing.purs`
  - Note: `Easing` is a sum type with data-carrying constructors (CubicBezier, Steps, Spring, Procedural). 
    An `all*` array doesn't make sense here — variants carry parameters.
  - **SKIPPED**: Not applicable to parameterized ADTs

- [x] `FullInterpolationType` → Add `allFullInterpolationTypes`
  - File: `src/Hydrogen/Schema/Motion/Interpolation.purs`
  - Note: 33 constructors - all enumerated
  - **COMPLETED**: 2026-02-26

- [x] `ControlMode` → Add `allControlModes`
  - File: `src/Hydrogen/Schema/Motion/Interpolation.purs`
  - Constructors: `CMSymmetric`, `CMSmooth`, `CMCorner`
  - **COMPLETED**: 2026-02-26

- [x] `NoteName` → Add `allNoteNames`
  - File: `src/Hydrogen/Schema/Audio/Frequency.purs`
  - Constructors: C, CSharp, D, DSharp, E, F, FSharp, G, GSharp, A, ASharp, B (12 total)
  - **COMPLETED**: 2026-02-26

- [x] `GesturePhase` → Add `allGesturePhases`
  - File: `src/Hydrogen/Schema/Gestural/Gesture/Phase.purs`
  - Constructors: `Possible`, `Began`, `Changed`, `Ended`, `Cancelled`, `Failed`
  - **COMPLETED**: 2026-02-26

### Template

```purescript
-- Add to module exports:
, all<TypeName>

-- Add to module body:
-- | All <TypeName> values for UI enumeration.
all<TypeName> :: Array <TypeName>
all<TypeName> = [Constructor1, Constructor2, ...]
```

---

## 2. FILE SIZE VIOLATIONS - Files Over 500 Lines

**Priority**: High
**Effort**: 2 weeks total

### Critical (>1000 lines) - MUST SPLIT

- [x] `Motion/Effects.purs` (1524 lines → 8 files, all <500 lines)
  - Split into: `Effects/Core.purs`, `Effects/Blur.purs`, `Effects/Distortion.purs`,
    `Effects/Glow.purs`, `Effects/Noise.purs`, `Effects/Time.purs`,
    `Effects/Mesh.purs`, `Effects/Stylize.purs`
  - Created leader module: `Effects.purs` with re-exports
  - **COMPLETED**: 2026-02-26
  - Added `all*` arrays to all ADTs during split

- [ ] `Geometry/Path.purs` (1217 lines)
  - Split into: `Path/Commands.purs`, `Path/Operations.purs`, `Path/Query.purs`
  - Create leader module: `Path.purs` with re-exports

- [ ] `Brand/Logo.purs` (1209 lines)
  - Split into: `Logo/Types.purs`, `Logo/Operations.purs`, `Logo/Validation.purs`
  - Create leader module: `Logo.purs` with re-exports

- [ ] `Geometry/Spline.purs` (1153 lines)
  - Split into: `Spline/Types.purs`, `Spline/Evaluation.purs`, `Spline/Algorithms.purs`

- [ ] `Motion/Camera3D.purs` (1120 lines)
  - Split into: `Camera3D/Types.purs`, `Camera3D/Operations.purs`, `Camera3D/Animation.purs`

- [ ] `Sensation/Compounds.purs` (1063 lines)
  - Split into: `Compounds/Comfort.purs`, `Compounds/Safety.purs`, `Compounds/Flow.purs`

- [ ] `Physics/Collision.purs` (966 lines)
  - Split into: `Collision/Detection.purs`, `Collision/Response.purs`, `Collision/Types.purs`

- [ ] `Geometry/Nurbs.purs` (963 lines)
  - Split into: `Nurbs/Types.purs`, `Nurbs/Evaluation.purs`, `Nurbs/Operations.purs`

### Severe (>800 lines) - Should Split

- [ ] `Color/Conversion.purs` (937 lines)
- [ ] `Reactive/Feedback.purs` (930 lines)
- [ ] `Geometry/Symmetry.purs` (921 lines)
- [ ] `Motion/KeyframeAnimation.purs` (901 lines)
- [ ] `Geometry/Bezier.purs` (882 lines)
- [ ] `Graph/Viewport.purs` (847 lines)
- [ ] `Motion/TimeRemap.purs` (838 lines)

### Split Pattern

1. Identify logical sections (usually marked by section headers)
2. Create subdirectory: `<Module>/`
3. Move each section to its own file
4. Create leader module that re-exports all submodules
5. Update all imports in dependent files
6. Verify build passes

---

## 3. IMPORT HYGIENE - Implicit Prelude Imports

**Priority**: Medium
**Effort**: 3-4 days (can be automated)
**Count**: 485 files

### Automation Script Needed

```bash
# Pseudocode for conversion script
for file in src/Hydrogen/Schema/**/*.purs; do
  if grep -q "^import Prelude$" "$file"; then
    # Analyze which Prelude symbols are used
    # Generate explicit import list
    # Replace implicit import with explicit
  fi
done
```

### Files to Fix (Sample - Full list is 485 files)

Run this command to get full list:
```bash
grep -r "^import Prelude$" src/Hydrogen/Schema/ --files-with-matches
```

### Target Pattern

```purescript
-- BEFORE (violation):
import Prelude

-- AFTER (compliant):
import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , bind
  , pure
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  )
```

---

## 4. JSON SERIALIZATION - Missing Codecs

**Priority**: CRITICAL
**Effort**: 2-3 weeks
**Blocker**: Yes - cannot ship without this

### Module Structure to Create

```
src/Hydrogen/Codec/
  Json.purs                 -- Core typeclass and utilities
  Json/
    Color.purs              -- Hue, Channel, Saturation, RGB, HSL, OKLCH, etc.
    Dimension.purs          -- Pixel, Size2D, Rect, AspectRatio
    Typography.purs         -- FontSize, FontWeight, LineHeight
    Geometry.purs           -- Point2D, Vector3D, Angle, Transform
    Temporal.purs           -- Duration, Progress, Date, DateTime
    Material.purs           -- BlurRadius, NoiseConfig
    Elevation.purs          -- Shadow, ZIndex
    Audio.purs              -- Hertz, Decibel, MidiNote
    Spatial.purs            -- Metallic, Roughness, IOR
```

### Implementation Pattern

```purescript
module Hydrogen.Codec.Json.Color where

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson)
import Data.Argonaut.Core (Json, fromNumber, fromObject)
import Data.Argonaut.Decode (JsonDecodeError, (.:))
import Data.Argonaut.Encode ((~>), (:=))

-- For newtype atoms:
instance encodeJsonHue :: EncodeJson Hue where
  encodeJson (Hue h) = encodeJson h

instance decodeJsonHue :: DecodeJson Hue where
  decodeJson json = hue <$> decodeJson json

-- For record molecules:
instance encodeJsonHSL :: EncodeJson HSL where
  encodeJson (HSL { hue, saturation, lightness }) =
    "hue" := hue
    ~> "saturation" := saturation
    ~> "lightness" := lightness
    ~> jsonEmptyObject

instance decodeJsonHSL :: DecodeJson HSL where
  decodeJson json = do
    obj <- decodeJson json
    hue <- obj .: "hue"
    saturation <- obj .: "saturation"
    lightness <- obj .: "lightness"
    pure $ hsl hue saturation lightness  -- Uses smart constructor!
```

### Priority Order

1. **Week 1**: Color atoms (most common)
   - [ ] Hue, Channel, Saturation, Lightness, Opacity
   - [ ] RGB, RGBA, HSL, HSLA
   - [ ] OKLCH, OKLAB, P3A

2. **Week 2**: Dimension + Typography + Geometry
   - [ ] Pixel, Size2D, Point2D, Rect, AspectRatio
   - [ ] FontSize, FontWeight, LineHeight, LetterSpacing
   - [ ] Degrees, Radians, Vector2D, Vector3D

3. **Week 3**: Remaining pillars
   - [ ] Duration, Progress, Date, DateTime
   - [ ] BlurRadius, Shadow
   - [ ] Metallic, Roughness, IOR
   - [ ] Hertz, Decibel

### Property Tests Required

```purescript
-- For every codec:
prop_roundtrip :: forall a. Eq a => EncodeJson a => DecodeJson a => a -> Result
prop_roundtrip x = decodeJson (encodeJson x) === Right x
```

---

## 5. LEAN4 PROOFS - Missing Pillars

**Priority**: High
**Effort**: 8-10 weeks total

### Proofs to Create

- [ ] **Dimension Pillar** (Week 5)
  - `proofs/Hydrogen/Schema/Dimension/Pixel.lean`
  - `proofs/Hydrogen/Schema/Dimension/Viewport.lean`
  - `proofs/Hydrogen/Schema/Dimension/Physical.lean`
  - Theorems: bounds validity, unit conversion correctness

- [ ] **Temporal Pillar** (Week 6)
  - `proofs/Hydrogen/Schema/Temporal/Duration.lean`
  - `proofs/Hydrogen/Schema/Temporal/Easing.lean`
  - `proofs/Hydrogen/Schema/Temporal/Progress.lean`
  - Theorems: non-negativity, monotonicity of easing

- [ ] **Accessibility Pillar** (Week 6)
  - `proofs/Hydrogen/Schema/Accessibility/Contrast.lean`
  - `proofs/Hydrogen/Schema/Accessibility/WCAG.lean`
  - Theorems: contrast ratio thresholds, luminance bounds

- [ ] **Elevation Pillar** (Week 7)
  - `proofs/Hydrogen/Schema/Elevation/Shadow.lean`
  - `proofs/Hydrogen/Schema/Elevation/ZIndex.lean`
  - Theorems: non-negative blur, stacking order

- [ ] **Reactive Pillar** (Week 7)
  - `proofs/Hydrogen/Schema/Reactive/State.lean`
  - Theorems: state machine validity

- [ ] **Motion Pillar** (Week 8)
  - `proofs/Hydrogen/Schema/Motion/Spring.lean`
  - `proofs/Hydrogen/Schema/Motion/Bezier.lean`
  - Theorems: damping bounds, curve evaluation in [0,1]

- [ ] **Gestural Pillar** (Week 9)
  - `proofs/Hydrogen/Schema/Gestural/Gesture.lean`
  - Theorems: gesture phase transitions valid

- [ ] **Haptic Pillar** (Week 9)
  - `proofs/Hydrogen/Schema/Haptic/Pattern.lean`
  - Theorems: intensity bounds, duration non-negative

### Template

```lean
-- proofs/Hydrogen/Schema/<Pillar>/<Atom>.lean

import Hydrogen.Math.Bounded

namespace Hydrogen.Schema.<Pillar>.<Atom>

-- Define the type with bounds
structure <Atom> where
  val : Fin <upperBound>
  deriving Repr, DecidableEq

-- Constructor
def <atom> (n : Nat) : <Atom> :=
  ⟨Fin.ofNat n, by omega⟩

-- Core theorems
theorem bounds_valid (x : <Atom>) : x.val < <upperBound> := x.val.isLt

theorem clamp_idempotent (n : Nat) : <atom> (<atom> n).val = <atom> n := by
  simp [<atom>]
  
-- PureScript generation
def generatePureScript : String := "..."

end Hydrogen.Schema.<Pillar>.<Atom>
```

---

## 6. TESTING INFRASTRUCTURE

**Priority**: CRITICAL
**Effort**: 8-12 weeks for solid foundation

### Test Structure to Create

```
test/
  Schema/
    Color/
      Roundtrip.purs        -- JSON encode/decode roundtrips
      Predicates.purs       -- isWarm, isCool, etc.
      Conversion.purs       -- Color space conversions
    Dimension/
      Bounded.purs          -- All bounded types
    Typography/
      Properties.purs       -- Font metrics, scale
    Geometry/
      Vector.purs           -- Vec2, Vec3, Vec4 operations
      Matrix.purs           -- Matrix operations
      Quaternion.purs       -- Rotation composition
  Property/
    BoundedTypes.purs       -- Generic bounded type tests
    Serialization.purs      -- All roundtrip tests
  Browser/
    Render.spec.js          -- Puppeteer/Playwright
    Visual.spec.js          -- Screenshot comparison
  Benchmark/
    Render.purs             -- Timing tests
    Memory.purs             -- Allocation tests
```

### Property Test Templates

```purescript
-- test/Property/BoundedTypes.purs

module Test.Property.BoundedTypes where

import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (Result, (===), (<?>))

-- All bounded types should satisfy:
prop_clamp_idempotent :: forall a. BoundedAtom a => a -> Result
prop_clamp_idempotent x = construct (unwrap x) === x
  <?> "Clamping should be idempotent"

prop_within_bounds :: forall a. BoundedAtom a => a -> Result
prop_within_bounds x =
  let v = toNumber x
      b = bounds :: Bounds a
  in (v >= b.min && v <= b.max) <?> "Value should be within bounds"

prop_lerp_bounded :: forall a. BoundedAtom a => a -> a -> Number -> Result
prop_lerp_bounded from to t =
  let result = lerp from to (clamp 0.0 1.0 t)
      v = toNumber result
      b = bounds :: Bounds a
  in (v >= b.min && v <= b.max) <?> "Lerp result should be in bounds"
```

### Browser Testing Setup

```javascript
// test/Browser/Render.spec.js
const puppeteer = require('puppeteer');

describe('Element Rendering', () => {
  let browser, page;
  
  beforeAll(async () => {
    browser = await puppeteer.launch();
    page = await browser.newPage();
  });
  
  afterAll(async () => {
    await browser.close();
  });
  
  test('Rectangle renders with correct dimensions', async () => {
    await page.goto('http://localhost:8080/test/rectangle');
    const rect = await page.$eval('canvas', canvas => {
      // Get pixel data and verify
    });
    expect(rect.width).toBe(200);
    expect(rect.height).toBe(100);
  });
});
```

---

## 7. WEBGL RUNTIME

**Priority**: CRITICAL
**Effort**: 4-6 weeks

### Architecture

```
src/Hydrogen/Runtime/
  WebGL.purs              -- Main runtime
  WebGL/
    Context.purs          -- WebGL context management
    Shaders.purs          -- Shader compilation and linking
    Programs.purs         -- Shader program registry
    Buffers.purs          -- VBO/VAO management
    Textures.purs         -- Texture loading
    Renderer.purs         -- Main render loop
    Diff.purs             -- Element diffing
    Patch.purs            -- DOM/GPU patching
```

### Core Interface

```purescript
-- src/Hydrogen/Runtime/WebGL.purs

module Hydrogen.Runtime.WebGL where

import Hydrogen.Element.Pure (Element)
import Effect (Effect)

-- Initialize runtime with canvas element
foreign import initRuntime :: String -> Effect Runtime

-- Render an Element tree
foreign import render :: Runtime -> Element Msg -> Effect Unit

-- Subscribe to messages
foreign import subscribe :: Runtime -> (Msg -> Effect Unit) -> Effect (Effect Unit)

-- Main loop
run :: forall state msg. App state msg -> Effect Unit
run app = do
  runtime <- initRuntime "canvas"
  ref <- Ref.new app.init
  let
    update msg = do
      state <- Ref.read ref
      let newState = app.update msg state
      Ref.write newState ref
      render runtime (app.view newState)
  subscribe runtime update
  render runtime (app.view app.init)
```

### Implementation Phases

1. **Week 1**: Context + basic shapes
   - WebGL context initialization
   - Rectangle rendering (SDF shader exists)
   - Circle rendering

2. **Week 2**: Text + Images
   - Font atlas loading
   - Text rendering with SDF
   - Image/texture support

3. **Week 3**: Composition + Events
   - Element tree flattening
   - Z-ordering
   - Mouse/keyboard event capture

4. **Week 4**: Diffing + Animation
   - Element diff algorithm
   - Minimal GPU updates
   - Animation frame scheduling

5. **Week 5-6**: Polish
   - Clipping/masking
   - Gradients
   - Shadows/blur
   - Performance optimization

---

## 8. IDENTIFIABLE TYPECLASS

**Priority**: High
**Effort**: 1 week

### Typeclass Definition

```purescript
-- src/Hydrogen/Schema/Identity/Identifiable.purs

module Hydrogen.Schema.Identity.Identifiable where

import Hydrogen.Schema.Attestation.UUID5 (UUID5, Namespace, uuid5)

-- | Typeclass for types that have deterministic identity.
-- |
-- | At billion-agent scale, two agents creating the same value
-- | must produce the same UUID. This enables:
-- | - Content addressing
-- | - Deduplication
-- | - Distributed caching
class Identifiable a where
  -- | The namespace for this type's UUIDs
  identityNamespace :: Proxy a -> Namespace
  
  -- | Canonical string representation for hashing
  toCanonical :: a -> String
  
  -- | Generate deterministic UUID5
  identity :: a -> UUID5
  identity x = uuid5 (identityNamespace (Proxy :: Proxy a)) (toCanonical x)
```

### Instance Pattern

```purescript
instance identifiableHue :: Identifiable Hue where
  identityNamespace _ = nsColor
  toCanonical (Hue h) = "hue:" <> show h

instance identifiableRGB :: Identifiable RGB where
  identityNamespace _ = nsColor
  toCanonical (RGB { red, green, blue }) =
    "rgb:" <> show (Channel.unwrap red) 
    <> ":" <> show (Channel.unwrap green)
    <> ":" <> show (Channel.unwrap blue)
```

### Namespaces to Define

```purescript
nsColor :: Namespace
nsColor = namespace "hydrogen.schema.color"

nsDimension :: Namespace
nsDimension = namespace "hydrogen.schema.dimension"

nsTypography :: Namespace
nsTypography = namespace "hydrogen.schema.typography"

nsGeometry :: Namespace
nsGeometry = namespace "hydrogen.schema.geometry"

nsTemporal :: Namespace
nsTemporal = namespace "hydrogen.schema.temporal"

-- etc. for each pillar
```

---

## 9. BENCHMARKS

**Priority**: Low
**Effort**: 2 weeks

### Benchmark Structure

```
bench/
  Render/
    Rectangles.purs       -- N rectangles render time
    Text.purs             -- N glyphs render time
    Complex.purs          -- Mixed element tree
  Diff/
    Shallow.purs          -- Top-level changes
    Deep.purs             -- Nested changes
    Large.purs            -- Large tree diffs
  Serialization/
    Json.purs             -- Encode/decode throughput
  Memory/
    Allocation.purs       -- Per-element allocation
    Retention.purs        -- Memory over time
```

### Benchmark Framework

```purescript
-- bench/Benchmark.purs

module Benchmark where

import Effect.Console (log)
import Performance.Now (now)

benchmark :: String -> Effect a -> Effect Unit
benchmark name action = do
  start <- now
  _ <- action
  end <- now
  log $ name <> ": " <> show (end - start) <> "ms"

-- Usage:
main = do
  benchmark "Render 1000 rectangles" $ renderN 1000
  benchmark "Diff 10000 elements" $ diffN 10000
```

---

## 10. PROGRESS TRACKING

### Weekly Status Updates

| Week | Focus | Status | Notes |
|------|-------|--------|-------|
| 1 | JSON codecs (Color) | Not started | |
| 2 | JSON codecs (remaining) | Not started | |
| 3 | Roundtrip tests | Not started | |
| 4 | WebGL MVP | Not started | |
| 5 | Lean: Dimension | Not started | |
| 6 | Lean: Temporal + A11y | Not started | |
| 7 | Browser tests | Not started | |
| 8 | Property tests | Not started | |
| 9 | Split oversized files | Not started | |
| 10 | Explicit imports | Not started | |
| 11 | Benchmarks | Not started | |
| 12 | A11y testing | Not started | |

### Completion Metrics

| Metric | Current | Target | Progress |
|--------|---------|--------|----------|
| Test coverage | 2.4% | 80% | ░░░░░░░░░░ |
| Files < 500 lines | 83% | 100% | ████████░░ |
| Explicit Prelude | 0% | 100% | ░░░░░░░░░░ |
| JSON codecs | 0% | 100% | ░░░░░░░░░░ |
| Lean proofs | 65% | 100% | ██████░░░░ |
| `all*` arrays | 90% | 100% | █████████░ |

---

## APPENDIX: QUICK COMMANDS

### Find Files Over 500 Lines
```bash
find src/Hydrogen/Schema -name "*.purs" -exec wc -l {} \; | awk '$1 > 500 { print }' | sort -rn
```

### Find Implicit Prelude Imports
```bash
grep -r "^import Prelude$" src/Hydrogen/Schema/ --files-with-matches | wc -l
```

### Find Missing `all*` Exports
```bash
grep -r "^data " src/Hydrogen/Schema/ -A5 | grep -v "all"
```

### Build and Count Warnings
```bash
nix develop --command spago build 2>&1 | grep -c "WARNING"
```

### Run Tests
```bash
nix develop --command spago test
```

---

*Last updated: 2026-02-26*
