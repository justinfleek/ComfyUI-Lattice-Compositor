# Hydrogen Motion Graphics Roadmap

> After Effects Gap Analysis for Professional Motion Graphics
> 
> **For 25-Year MoGraph Experts**

---

## Executive Summary

The Hydrogen motion graphics system has **solid infrastructure** but is missing
**effect molecules and complete property records**. The architecture is correct:

- Pure data (no CSS, no JavaScript at runtime)
- Bounded atoms with explicit min/max
- Schema-first design
- WebGPU rendering target

**What exists:**
- Layer types (26 variants)
- Effect categories (12 categories)
- Shape content types (24 variants)
- Text animator infrastructure
- Camera3D (excellent coverage)
- Time remapping (excellent coverage)
- Track mattes and blend modes

**What's missing:**
- Effect **definitions** (atoms have enums, but no parameter records)
- Shape **property values** (types exist, but no actual property atoms)
- Color correction effects (zero exist)
- Light3D layer integration (exists in Spatial, not in Motion)
- Full mask type (MaskRef exists, actual Mask data incomplete)
- Simulation effects (particles, shatter, caustics)

---

## Architecture Context

### The Hydrogen Pattern

Every motion graphics primitive follows the Schema pattern:

```
Atom (bounded value) → Molecule (composed atoms) → Compound (complete feature)
```

**Example: Gaussian Blur**

```purescript
-- Atom: BlurRadius (in Schema/Material/BlurRadius.purs)
newtype BlurRadius = BlurRadius Number  -- 0.0 to none, finite, clamps

-- Molecule: GaussianBlurParams (in Schema/Motion/Effects/Blur.purs)
type GaussianBlurParams =
  { radius :: BlurRadius
  , dimensions :: BlurDimension  -- H/V/Both (already exists)
  , repeatEdge :: Boolean
  }

-- Compound: GaussianBlurEffect (complete effect definition)
type GaussianBlurEffect =
  { params :: GaussianBlurParams
  , enabled :: Boolean
  , expanded :: Boolean  -- UI state
  }
```

### File Organization

```
src/Hydrogen/Schema/Motion/
├── Effects/
│   ├── Core.purs         -- Effect infrastructure (EXISTS)
│   ├── Blur.purs         -- Blur enums (EXISTS, incomplete)
│   ├── Blur/
│   │   ├── Gaussian.purs -- GaussianBlurEffect (MISSING)
│   │   ├── Directional.purs
│   │   ├── Radial.purs
│   │   └── CameraLens.purs
│   ├── ColorCorrection/  -- (MISSING - entire directory)
│   │   ├── Levels.purs
│   │   ├── Curves.purs
│   │   ├── HueSaturation.purs
│   │   └── ...
│   ├── Distortion.purs   -- Distortion enums (EXISTS, incomplete)
│   ├── Distortion/
│   │   ├── BezierWarp.purs
│   │   ├── Bulge.purs
│   │   └── ...
│   └── ...
├── Shapes/               -- (MISSING - need property records)
│   ├── Rectangle.purs
│   ├── Ellipse.purs
│   ├── TrimPaths.purs
│   ├── Repeater.purs
│   └── ...
├── Light3D.purs          -- (MISSING - integrate from Spatial)
└── Mask.purs             -- (MISSING - full mask type)
```

---

## Priority 0: Blocking (Must Have)

### P0.1: Color Correction Effects

**Location:** `src/Hydrogen/Schema/Motion/Effects/ColorCorrection/`

**Why blocking:** Every professional project uses color correction. Zero effects
currently exist in this category despite `ECColorCorrection` being defined.

#### Levels.purs

| Parameter | Type | Min | Max | Behavior | Notes |
|-----------|------|-----|-----|----------|-------|
| InputBlack | Number | 0.0 | 1.0 | clamps | Black point (per-channel + master) |
| InputWhite | Number | 0.0 | 1.0 | clamps | White point (per-channel + master) |
| Gamma | Number | 0.1 | 10.0 | clamps | Midtone adjustment |
| OutputBlack | Number | 0.0 | 1.0 | clamps | Output black level |
| OutputWhite | Number | 0.0 | 1.0 | clamps | Output white level |

```purescript
type ChannelLevels =
  { inputBlack :: Number   -- 0.0-1.0
  , inputWhite :: Number   -- 0.0-1.0
  , gamma :: Number        -- 0.1-10.0
  , outputBlack :: Number  -- 0.0-1.0
  , outputWhite :: Number  -- 0.0-1.0
  }

type LevelsEffect =
  { master :: ChannelLevels
  , red :: ChannelLevels
  , green :: ChannelLevels
  , blue :: ChannelLevels
  , alpha :: ChannelLevels
  }
```

#### Curves.purs

| Parameter | Type | Min | Max | Behavior | Notes |
|-----------|------|-----|-----|----------|-------|
| CurvePoint.x | Number | 0.0 | 1.0 | clamps | Input value |
| CurvePoint.y | Number | 0.0 | 1.0 | clamps | Output value |
| CurvePoint.handleIn | Point2D | - | - | - | Bezier handle in |
| CurvePoint.handleOut | Point2D | - | - | - | Bezier handle out |

```purescript
type CurvesControlPoint =
  { x :: Number           -- 0.0-1.0 input
  , y :: Number           -- 0.0-1.0 output
  , handleIn :: Maybe { x :: Number, y :: Number }
  , handleOut :: Maybe { x :: Number, y :: Number }
  }

type CurveChannel = Array CurvesControlPoint  -- Min 2 points

type CurvesEffect =
  { master :: CurveChannel
  , red :: CurveChannel
  , green :: CurveChannel
  , blue :: CurveChannel
  , alpha :: CurveChannel
  }
```

#### HueSaturation.purs

| Parameter | Type | Min | Max | Behavior | Notes |
|-----------|------|-----|-----|----------|-------|
| MasterHue | Number | -180 | 180 | wraps | Global hue shift |
| MasterSaturation | Number | -100 | 100 | clamps | Global saturation |
| MasterLightness | Number | -100 | 100 | clamps | Global lightness |
| Colorize | Boolean | - | - | - | Colorize mode |
| ColorizeHue | Number | 0 | 359 | wraps | Colorize hue |
| ColorizeSaturation | Number | 0 | 100 | clamps | Colorize saturation |

```purescript
data ColorChannel
  = CCMaster
  | CCReds
  | CCYellows
  | CCGreens
  | CCCyans
  | CCBlues
  | CCMagentas

type ChannelAdjustment =
  { hue :: Number        -- -180 to 180 (wraps)
  , saturation :: Number -- -100 to 100 (clamps)
  , lightness :: Number  -- -100 to 100 (clamps)
  }

type HueSaturationEffect =
  { master :: ChannelAdjustment
  , reds :: ChannelAdjustment
  , yellows :: ChannelAdjustment
  , greens :: ChannelAdjustment
  , cyans :: ChannelAdjustment
  , blues :: ChannelAdjustment
  , magentas :: ChannelAdjustment
  , colorize :: Boolean
  , colorizeHue :: Number      -- 0-359 (wraps)
  , colorizeSaturation :: Number -- 0-100 (clamps)
  , colorizeLightness :: Number  -- -100 to 100 (clamps)
  }
```

#### Additional Color Correction Effects

| Effect | Key Parameters | Complexity |
|--------|----------------|------------|
| ColorBalance | Shadow/Mid/Highlight RGB shifts | Medium |
| Exposure | Exposure (-20 to 20), Offset, Gamma | Simple |
| Tint | Map Black To, Map White To colors | Simple |
| Tritone | Shadows, Midtones, Highlights colors | Simple |
| BlackAndWhite | 6 color filter strengths | Simple |
| SelectiveColor | Per-color CMYK adjustments | Complex |
| PhotoFilter | Warming/cooling presets | Simple |
| Vibrance | Vibrance, Saturation | Simple |
| LumetriColor | Full grading suite | Complex |

---

### P0.2: Light3D Layer Integration

**Location:** `src/Hydrogen/Schema/Motion/Light3D.purs`

**Why blocking:** Camera3D exists and is excellent. Light3D exists in `Schema/Spatial/Light.purs`
but is not integrated into the Motion layer system. A senior artist expects lights
as first-class layers like cameras.

**Current state:**
- `Schema/Spatial/Light.purs` has `Light` ADT with DirectionalLight, PointLight, SpotLight, etc.
- `Schema/Motion/Layer.purs` has `LTLight` layer type
- **Missing:** Light3D layer with animatable properties matching After Effects

```purescript
-- Bridge type connecting Spatial Light to Motion Layer system
type Light3DLayer =
  { base :: LayerBase
  , lightType :: LightType
  , color :: SRGB              -- Animatable
  , intensity :: Number        -- 0-400%, animatable
  , coneAngle :: Maybe Number  -- Spot only, 0-180 degrees
  , coneFeather :: Maybe Number -- Spot only, 0-100%
  , falloff :: LightFalloff    -- None | Smooth | InverseSquareClamped
  , falloffDistance :: Maybe Number -- For falloff
  , castsShadows :: ShadowMode -- Off | On | Only
  , shadowDarkness :: Number   -- 0-100%
  , shadowDiffusion :: Number  -- Soft shadow spread
  }

data LightType
  = LTParallel    -- Directional (sun)
  | LTSpot        -- Spot light
  | LTPoint       -- Omni light
  | LTAmbient     -- Ambient fill

data LightFalloff
  = LFNone
  | LFSmooth
  | LFInverseSquareClamped

data ShadowMode
  = SMOff
  | SMOn
  | SMOnly  -- Only cast shadows, no illumination
```

---

### P0.3: Complete Mask Type

**Location:** `src/Hydrogen/Schema/Motion/Mask.purs`

**Why blocking:** `MaskRef` exists in LayerReference.purs but the actual Mask
with path, feather, expansion, etc. is incomplete. The geometry Mask.purs has
a different purpose (compositing masks, not layer masks).

**Current state:**
- `Schema/Motion/LayerReference.purs` has `MaskRef` (uuid, layer, maskName, maskIndex)
- `Schema/Motion/LayerReference.purs` has `MaskMode` (None, Add, Subtract, etc.)
- `Schema/Geometry/Mask.purs` is for compositing (different purpose)
- **Missing:** Full layer mask with path data

```purescript
-- Full After Effects-style layer mask
type LayerMask =
  { id :: MaskRef
  , name :: String
  , path :: Path                -- From Schema/Geometry/Path (animatable)
  , mode :: MaskMode            -- Add, Subtract, Intersect, etc.
  , opacity :: Number           -- 0-100%, animatable
  , feather :: MaskFeather      -- X/Y feather amounts, animatable
  , expansion :: Number         -- Pixels, can be negative, animatable
  , inverted :: Boolean
  , locked :: Boolean
  , rotoBezier :: Boolean       -- Auto-smooth bezier mode
  }

type MaskFeather =
  { x :: Number  -- Horizontal feather in pixels, >= 0
  , y :: Number  -- Vertical feather in pixels, >= 0
  }
```

---

### P0.4: Shape Property Records

**Location:** `src/Hydrogen/Schema/Motion/Shapes/`

**Why blocking:** `ShapeContentType` exists with 24 variants, but the actual
property records are missing. An agent cannot construct a TrimPaths operation
without the Start, End, Offset properties.

#### TrimPaths.purs

```purescript
type TrimPathsProps =
  { start :: Number      -- 0-100%, animatable
  , end :: Number        -- 0-100%, animatable
  , offset :: Number     -- -360 to 360 degrees, animatable (wraps)
  , trimMode :: TrimMode -- Simultaneously | Individually
  }
```

#### Repeater.purs

```purescript
type RepeaterProps =
  { copies :: Int        -- 1+, animatable
  , offset :: Number     -- Fractional copy offset, animatable
  , composite :: RepeaterComposite  -- Above | Below
  , transform :: RepeaterTransform  -- Per-copy transform
  }

type RepeaterTransform =
  { anchorPoint :: Point2D   -- Animatable
  , position :: Point2D      -- Animatable
  , scale :: Size2D          -- Percentage, animatable
  , rotation :: Number       -- Degrees, animatable
  , startOpacity :: Number   -- 0-100%, animatable
  , endOpacity :: Number     -- 0-100%, animatable
  }
```

#### PuckerBloat.purs

```purescript
type PuckerBloatProps =
  { amount :: Number  -- -100 to 100%, animatable (negative = pucker, positive = bloat)
  }
```

#### ZigZag.purs

```purescript
type ZigZagProps =
  { size :: Number           -- 0+, pixels, animatable
  , ridgesPerSegment :: Number -- 0+, animatable
  , points :: ZigZagPointType  -- Corner | Smooth
  }
```

#### WigglePaths.purs

```purescript
type WigglePathsProps =
  { size :: Number            -- 0+, pixels, animatable
  , detail :: Number          -- 0+, animatable
  , points :: WigglePointType -- Corner | Smooth
  , correlation :: Number     -- 0-100%, animatable
  , temporalPhase :: Number   -- Degrees, animatable
  , spatialPhase :: Number    -- Degrees, animatable
  , randomSeed :: Int         -- Seed for randomness
  }
```

#### RoundedCorners.purs

```purescript
type RoundedCornersProps =
  { radius :: Number  -- 0+, pixels, animatable
  }
```

#### OffsetPaths.purs

```purescript
type OffsetPathsProps =
  { amount :: Number       -- Pixels, can be negative, animatable
  , lineJoin :: OffsetJoin -- Miter | Round | Bevel
  , miterLimit :: Number   -- For miter joins, >= 1
  }
```

#### Twist.purs

```purescript
type TwistProps =
  { angle :: Number    -- Degrees, animatable
  , center :: Point2D  -- Twist center, animatable
  }
```

#### Stroke Dashes

**Location:** `src/Hydrogen/Schema/Motion/Shapes/Stroke.purs`

```purescript
type StrokeProps =
  { color :: SRGB           -- Animatable
  , opacity :: Number       -- 0-100%, animatable
  , width :: Number         -- 0+, pixels, animatable
  , lineCap :: LineCap      -- Butt | Round | Square
  , lineJoin :: LineJoin    -- Miter | Round | Bevel
  , miterLimit :: Number    -- For miter joins, >= 1
  , dashes :: Maybe DashPattern
  , taper :: Maybe StrokeTaper
  }

type DashPattern =
  { dash :: Array Number    -- Dash segment lengths
  , gap :: Array Number     -- Gap lengths (alternating)
  , offset :: Number        -- Offset into pattern, animatable
  }

type StrokeTaper =
  { startLength :: Number   -- 0-100%, animatable
  , endLength :: Number     -- 0-100%, animatable
  , startWidth :: Number    -- 0-100%, animatable
  , endWidth :: Number      -- 0-100%, animatable
  , startEase :: Number     -- 0-100%, animatable
  , endEase :: Number       -- 0-100%, animatable
  }
```

---

## Priority 1: Critical (Expected by Senior Artists)

### P1.1: Blur Effect Definitions

**Location:** `src/Hydrogen/Schema/Motion/Effects/Blur/`

| Effect | Parameters | Status |
|--------|------------|--------|
| GaussianBlur | Blurriness, Repeat Edge, Dimensions | Missing |
| DirectionalBlur | Direction (0-360), Blur Length | Missing |
| RadialBlur | Amount, Center, Type (Spin/Zoom), AA | Missing (has enum) |
| CameraLensBlur | Blur Radius, Iris Shape/Rotation/Roundness, Specular | Missing |
| CompoundBlur | Blur Layer, Max Blur, Stretch Map, Invert | Missing |
| Sharpen | Sharpen Amount (0-500) | Missing |
| UnsharpMask | Amount, Radius, Threshold | Missing |
| FastBoxBlur | Blur Radius, Iterations, Dimensions | Missing |

### P1.2: Distortion Effect Definitions

**Location:** `src/Hydrogen/Schema/Motion/Effects/Distortion/`

| Effect | Parameters | Status |
|--------|------------|--------|
| BezierWarp | 12-point bezier grid | Missing |
| Bulge | H/V Radius, Bulge Height, Taper Radius, Center | Missing |
| CornerPin | Four corners (8 numbers) | Missing |
| Mirror | Reflection Center, Reflection Angle | Missing |
| Offset | Shift Center To, Blend With Original | Missing |
| OpticsCompensation | FOV, Reverse Lens Distortion | Missing |
| PolarCoordinates | Interpolation, Type (Rect↔Polar) | Missing |
| Ripple | Radius, Center, Wave Speed/Width/Height, Phase | Missing |
| Spherize | Radius, Center | Missing |
| TurbulentDisplace | Amount, Size, Offset, Complexity, Evolution, Seed | Missing |
| Twirl | Angle, Twirl Radius, Center | Missing |
| WaveWarp | Wave Type, Height/Width, Direction, Phase, AA | Missing |

### P1.3: Keying Effects

**Location:** `src/Hydrogen/Schema/Motion/Effects/Keying/`

| Effect | Parameters | Notes |
|--------|------------|-------|
| Keylight | Screen Color, Screen Gain/Balance, Despill, Edge | Industry standard |
| LinearColorKey | Key Color, Tolerance, Softness | Simple key |
| LumaKey | Key Type, Threshold, Tolerance, Edge | Luminance-based |
| ColorRange | Selection, Lab values | Selection-based |
| Extract | White/Black Point, Softness, Invert | Luminance extract |

### P1.4: Text Per-Character 3D

**Location:** `src/Hydrogen/Schema/Motion/TextAnimator.purs` (extend)

**Missing properties for TextAnimatorProperties:**

```purescript
-- Extend existing TextAnimatorProperties
type TextAnimator3DProperties =
  { xRotation :: Number      -- Per-character X rotation, animatable
  , yRotation :: Number      -- Per-character Y rotation, animatable
  , zRotation :: Number      -- Per-character Z rotation (existing as rotation)
  , zAnchor :: Number        -- Z anchor point, animatable
  , zPosition :: Number      -- Z position offset, animatable
  }
```

### P1.5: Gradient Types for Shapes

**Location:** `src/Hydrogen/Schema/Motion/Shapes/Gradient.purs`

**Missing gradient types:**

```purescript
data GradientType
  = GTLinear    -- Exists
  | GTRadial    -- Exists
  | GTAngular   -- MISSING: Conic/angular gradient
  | GTReflected -- MISSING: Reflected (mirrored linear)
  | GTDiamond   -- MISSING: Diamond/square gradient
```

---

## Priority 2: Important (Quality of Life)

### P2.1: Layer Properties

| Property | Type | Location | Notes |
|----------|------|----------|-------|
| autoOrient | AutoOrientMode | Layer.purs | None/AlongPath/TowardsCamera |
| collapseTransformations | Boolean | Layer.purs | For precomps and vectors |
| separatePositionXYZ | Boolean | Layer.purs | Position as 3 separate properties |
| audioEnabled | Boolean | Layer.purs | Enable/disable layer audio |
| audioLevels | AudioLevels | Layer.purs | L/R audio levels |
| sourceText | TextSource | Layer.purs | For text layers |

```purescript
data AutoOrientMode
  = AOOff
  | AOAlongPath
  | AOTowardsCamera
  | AOTowardsPOI  -- For two-node cameras
```

### P2.2: Frame Blending

| Property | Type | Location | Notes |
|----------|------|----------|-------|
| frameBlendMode | FrameBlendMode | Layer.purs | Frame Mix / Pixel Motion / Optical Flow |

```purescript
data FrameBlendMode
  = FBMFrameMix        -- Simple blending
  | FBMPixelMotion     -- Motion vector interpolation
  | FBMOpticalFlow     -- Optical flow interpolation
```

### P2.3: More Expression Functions

The expression system has foundation (`ExpressionType` with 24 types) but needs
more evaluation atoms for the Haskell backend to interpret:

| Function | Description | Category |
|----------|-------------|----------|
| toComp/toWorld | Coordinate space conversions | Space |
| fromComp/fromWorld | Coordinate space conversions | Space |
| sampleImage | Sample pixel colors from layers | Sample |
| createPath | Create paths programmatically | Path |
| pointOnPath | Get point at path position | Path |
| tangentOnPath | Get tangent at path position | Path |
| normalOnPath | Get normal at path position | Path |
| sourceRectAtTime | Get layer bounds at time | Bounds |
| valueAtTime | Sample property at time | Time |
| velocityAtTime | Motion derivative at time | Time |
| speedAtTime | Speed at time | Time |
| nearestKey | Find nearest keyframe | Keyframe |
| key | Access keyframe by index | Keyframe |
| loopIn/loopOut | Loop modes | Loop |

---

## Priority 3: Simulation Effects

**Location:** `src/Hydrogen/Schema/Motion/Effects/Simulation/`

**Note:** These are complex and may require GPU compute kernels.

| Effect | Complexity | Notes |
|--------|------------|-------|
| CCParticleWorld | High | 3D particle system |
| CCParticleSystems | Medium | 2D particle system |
| Shatter | High | Glass shatter simulation |
| CardDance | Medium | Grid-based card animation |
| Caustics | High | Water caustics |
| Foam | Medium | Bubbles/foam |
| WaveWorld | High | 3D water simulation |

---

## Implementation Order

### Phase 1: Core Gaps (Unblocks Professional Work)

1. **ColorCorrection/Levels.purs** — Most used color effect
2. **ColorCorrection/Curves.purs** — Second most used
3. **ColorCorrection/HueSaturation.purs** — Third most used
4. **Light3D.purs** — Integrate existing Spatial Light
5. **Mask.purs** — Full layer mask type
6. **Shapes/TrimPaths.purs** — Most used shape operator
7. **Shapes/Repeater.purs** — Second most used
8. **Shapes/Stroke.purs** — Dashes and taper

### Phase 2: Complete Effects

9. **Blur/Gaussian.purs**
10. **Blur/Directional.purs**
11. **Blur/Radial.purs**
12. **Blur/CameraLens.purs**
13. **Distortion/BezierWarp.purs**
14. **Distortion/CornerPin.purs**
15. **Distortion/TurbulentDisplace.purs**
16. **Keying/Keylight.purs**

### Phase 3: Shape Operators

17. **Shapes/PuckerBloat.purs**
18. **Shapes/ZigZag.purs**
19. **Shapes/WigglePaths.purs**
20. **Shapes/RoundedCorners.purs**
21. **Shapes/OffsetPaths.purs**
22. **Shapes/Twist.purs**
23. **Shapes/Gradient.purs** — Angular, Reflected, Diamond

### Phase 4: Layer Enhancements

24. **Layer.purs** — autoOrient, collapseTransformations
25. **TextAnimator.purs** — 3D properties
26. **FrameBlending.purs**

### Phase 5: Simulation (GPU Compute)

27. Particle systems
28. Shatter
29. Caustics

---

## Atom Patterns to Follow

### Bounded Number Pattern

```purescript
-- From Schema/Material/BlurRadius.purs
newtype BlurRadius = BlurRadius Number

blurRadius :: Number -> BlurRadius
blurRadius n = BlurRadius (max 0.0 n)  -- Clamps at 0
```

### Wrapping Pattern (Hue, Angle)

```purescript
-- From Schema/Color/Hue.purs
newtype Hue = Hue Int

mkHue :: Int -> Hue
mkHue h = Hue (h `mod` 360)  -- Wraps at 360
```

### Clamped Percentage Pattern

```purescript
-- From Schema/Dimension/Percentage.purs
newtype Percent = Percent Number

mkPercent :: Number -> Percent
mkPercent p = Percent (max 0.0 (min 100.0 p))  -- Clamps 0-100
```

### Signed Clamped Pattern

```purescript
-- For parameters like Saturation adjustment (-100 to 100)
newtype SignedPercent = SignedPercent Number

mkSignedPercent :: Number -> SignedPercent
mkSignedPercent p = SignedPercent (max (-100.0) (min 100.0 p))
```

---

## Testing Strategy

Each effect definition needs:

1. **Property tests** — Verify all bounds are respected
2. **Determinism tests** — Same input = same output
3. **Composition tests** — Effects compose correctly
4. **Serialization tests** — Round-trip to JSON/binary

Example from existing codebase (`Test.Sensation.Property`):

```purescript
propBoundedness :: Gen Number -> Property
propBoundedness gen = property do
  n <- forAll gen
  let result = mkPercent n
  assert $ result >= 0.0 && result <= 100.0
```

---

## Dependencies

### Existing Atoms to Reuse

| Need | Existing Location | Type |
|------|-------------------|------|
| Colors | Schema/Color/SRGB.purs | SRGB |
| Points | Schema/Dimension/Point2D.purs | Point2D |
| Blur radius | Schema/Material/BlurRadius.purs | BlurRadius |
| Opacity | Schema/Color/Opacity.purs | Opacity |
| Angles | Schema/Geometry/Angle.purs | Degrees, Radians |
| Paths | Schema/Geometry/Path.purs | Path |
| Light | Schema/Spatial/Light.purs | Light ADT |

### New Atoms Needed

| Atom | Min | Max | Behavior | Used By |
|------|-----|-----|----------|---------|
| Gamma | 0.1 | 10.0 | clamps | Levels, Exposure |
| FeatherAmount | 0.0 | none | finite | Masks, Blur |
| Expansion | none | none | finite | Masks |
| TaperPercent | 0.0 | 100.0 | clamps | Stroke taper |
| ConeAngle | 0.0 | 180.0 | clamps | Spot lights |
| ShadowDarkness | 0.0 | 100.0 | clamps | Lights |
| SignedPercent | -100.0 | 100.0 | clamps | Hue/Sat adjustments |

---

## Summary Table

| Category | Coverage | Critical Gaps | Est. Files |
|----------|----------|---------------|------------|
| Color Correction | 0% | Levels, Curves, HSL | 10 |
| Blur/Sharpen | 30% | Full definitions | 8 |
| Distortion | 30% | Full definitions | 12 |
| Keying | 0% | Keylight, Luma Key | 5 |
| Matte | 50% | Full mask type | 2 |
| Simulation | 0% | All | 7 |
| Shape Properties | 20% | TrimPaths, Repeater, etc. | 10 |
| Light3D | 60% | Layer integration | 1 |
| Text 3D | 85% | Per-character 3D | 1 |
| Layer Props | 80% | autoOrient, collapse | 1 |

**Total estimated new files:** ~57
**Total estimated new types:** ~150

---

## Notes for Implementers

1. **Never use strings where enums exist** — If AE has a dropdown, we have an ADT
2. **All animatable properties are atoms** — They get their own bounded type
3. **Effects are molecules** — Composed from parameter atoms
4. **EffectInstance references EffectDefinition** — Separation of template and instance
5. **500 line max per file** — Split into submodules if needed
6. **Explicit imports only** — No `(..)` patterns
7. **No TODOs** — Complete implementations only

---

                                                         — Hydrogen Motion Graphics Roadmap
                                                                          v1.0 // 2026-02-27
