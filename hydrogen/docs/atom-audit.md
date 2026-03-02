-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // docs // atom audit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# HYDROGEN SCHEMA ATOM AUDIT

**Date**: 2026-02-26
**Purpose**: Detailed per-atom completeness assessment
**Scope**: All bounded numeric atoms and ADT enums

---

## COMPLETENESS CRITERIA

For an atom to be **COMPLETE**, it must have:

| Category | Requirements |
|----------|--------------|
| **BOUNDS** | Min/max defined, smart constructor clamps, `bounds` export |
| **CALCULATIONS** | `blend`, `lerp`, `scale`, `add`/`subtract` where applicable |
| **CONVERSIONS** | `toNumber`, `unwrap`, unit conversions where applicable |
| **PREDICATES** | Named range checks (e.g., `isWarm`, `isMetal`, `isReadable`) |
| **CONSTANTS** | Named values for common cases (e.g., `metal`, `dielectric`) |

---

## AUDIT RESULTS BY PILLAR

### COLOR PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Hue** | ✅ 0-359 wraps | ✅ blend, blendShortestPath, lerp, rotate | ✅ toNumber, toRadians, toDegrees | ✅ isWarm, isCool, isRed, isOrange, isYellow, isGreen, isCyan, isBlue, isMagenta, colorCategory | ✅ COMPLETE |
| **Channel** | ✅ 0-255 | ✅ blend, lerp, scale, add, subtract, invert, multiply | ✅ toNumber, toUnitInterval, fromUnitInterval | ✅ isBlack, isWhite, isMidtone | ✅ COMPLETE |
| **Saturation** | ✅ 0-100 | ✅ blend, lerp, scale, increase, decrease, invert | ✅ toNumber, toUnitInterval, fromUnitInterval | ✅ isGrayscale, isVivid, isMuted | ✅ COMPLETE |
| **Lightness** | ✅ 0-100 | ✅ scale, increase, decrease | ✅ toNumber, toUnitInterval | ✅ isDark, isLight | ✅ COMPLETE |
| **Opacity** | ✅ 0-100 | ✅ blend, scale, increase, decrease, invert, multiply | ✅ toNumber, toUnitInterval, toChannel | ✅ isTransparent, isOpaque, isSemiTransparent | ✅ COMPLETE |

#### Color Molecules (Composed from Atoms)

| Molecule | Composition | Status |
|----------|-------------|--------|
| HSL | Hue + Saturation + Lightness | ✅ COMPLETE |
| HSLA | HSL + Opacity | ✅ COMPLETE |
| RGB | Channel × 3 | ✅ COMPLETE |
| RGBA | RGB + Opacity | ✅ COMPLETE |
| OKLCH | OkL + OkChroma + Hue | ✅ COMPLETE |
| HWB | Hue + Whiteness + Blackness | ✅ COMPLETE |

---

### SPATIAL PILLAR (PBR Materials)

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Metallic** | ✅ 0.0-1.0 | ✅ blend, lerp, scale, add, subtract | ✅ toNumber, unwrap | ✅ isDielectric, isMetal, isHybrid | ✅ COMPLETE |
| **Roughness** | ✅ 0.0-1.0 | ✅ blend, lerp, scale, add, subtract, invert, toSmoothness, fromSmoothness | ✅ toNumber, unwrap | ✅ isMirror, isGlossy, isSemiRough, isMatte | ✅ COMPLETE |
| **IOR** | ✅ 1.0-3.0 | ✅ blend, lerp, fresnelF0, reflectivity, criticalAngle | ✅ toNumber, unwrap | ✅ isAir, isWater, isGlass, isDiamond, isLowIOR, isHighIOR | ✅ COMPLETE |
| **FOV** | ✅ 1-179 | ⚠️ scale only | ✅ toNumber, toRadians | ⚠️ isNarrow, isWide, isUltraWide needed | ⚠️ PARTIAL |

---

### TYPOGRAPHY PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **FontSize** | ✅ 1-1000px | ✅ blend, lerp, scale, add, subtract, minor, major | ✅ toNumber, toRem, toLegacyCss | ✅ isReadable, isCompact, isDisplay, isHero | ✅ COMPLETE |
| **FontWeight** | ✅ 1-1000 | ✅ scale, increase, decrease | ✅ toNumber, toCssKeyword | ✅ isThin, isLight, isNormal, isMedium, isBold, isBlack | ✅ COMPLETE |
| **LineHeight** | ✅ 0.5-5.0 | ✅ blend, lerp, scale, add, subtract, toPixels | ✅ toNumber, toLegacyCss | ✅ isSolid, isTight, isNormal, isRelaxed, isLoose, atLeast, lessThan | ✅ COMPLETE |
| **LetterSpacing** | ✅ -500 to 1000 | ✅ blend, lerp, scale, add, subtract, invert | ✅ toNumber, toEm, toLegacyCss | ✅ isTight, isNone, isLoose, isNegative, isPositive | ✅ COMPLETE |

---

### GEOMETRY PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Degrees** | ✅ 0-360 cyclic | ✅ rotate, complement, lerp | ✅ toNumber, toRadians, toTurns | ✅ isAcute, isObtuse, isRight, isReflex | ✅ COMPLETE |
| **Radians** | ✅ 0-2π cyclic | ✅ rotate, complement, lerp | ✅ toNumber, toDegrees, toTurns | ✅ predicates via Degrees | ✅ COMPLETE |
| **Turns** | ✅ 0-1 cyclic | ✅ rotate, complement, lerp | ✅ toNumber, toDegrees, toRadians | ✅ predicates via Degrees | ✅ COMPLETE |
| **MiterLimit** | ✅ 1-100 | ⚠️ basic only | ✅ toNumber, unwrap | N/A (semantic) | ✅ COMPLETE |

---

### MATERIAL PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **BlurRadius** | ✅ 0-1000 | ✅ blend, lerp, scale, add, subtract | ✅ toNumber, toLegacyCss | ✅ isSharp, isSubtle, isModerate, isHeavy, isExtreme, atLeast, lessThan | ✅ COMPLETE |
| **NoiseOctaves** | ✅ 1-8 | N/A (discrete) | ✅ toNumber, unwrap | N/A (discrete) | ✅ COMPLETE |

---

### TEMPORAL PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Duration** | ✅ 0+ | ✅ add, scale, divide | ✅ toMilliseconds, toSeconds, toMinutes | ✅ isInstant, isShort, isMedium, isLong | ✅ COMPLETE |
| **Progress** | ✅ 0-1 | ✅ lerp, scale | ✅ toNumber, unwrapProgress | ⚠️ isStart, isEnd, isHalfway needed | ⚠️ PARTIAL |

---

### AUDIO PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Hertz** | ✅ 0-20000 | ✅ octaveUp, octaveDown, cents, semitones | ✅ toNumber, toKilohertz | ✅ isSubBass, isBass, isMid, isTreble, isUltrasonic | ✅ COMPLETE |
| **Decibel** | ✅ -120 to 0 | ✅ add, scale | ✅ toNumber, toLinearGain | ✅ isSilent, isQuiet, isNormal, isLoud | ✅ COMPLETE |
| **LinearGain** | ✅ 0-1 | ✅ scale, multiply | ✅ toNumber, toDecibel | ✅ isSilent, isFull, isHalfPower | ✅ COMPLETE |
| **MidiNote** | ✅ 0-127 | ✅ transpose | ✅ toNumber, toHertz, toNoteName | ✅ byOctave, inRange | ✅ COMPLETE |

---

### DIMENSION PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Pixel** | N/A (unbounded) | ✅ add, subtract, scale | ✅ toNumber, toRem | ⚠️ isZero only | ⚠️ PARTIAL |
| **AspectRatio** | ✅ 0+ | ✅ invert, scale | ✅ toNumber, toFraction | ✅ isSquare, isPortrait, isLandscape, isUltrawide | ✅ COMPLETE |
| **ObjectFit** | ADT (5 values) | N/A | ✅ objectFitToCss | ✅ maintainsAspectRatio, canClip, canDistort | ✅ COMPLETE |

---

### REACTIVE PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **Progress** | ✅ 0-1 | ⚠️ basic lerp | ✅ toNumber | ⚠️ predicates needed | ⚠️ PARTIAL |

---

### GESTURAL PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **SwipeVelocityThreshold** | ✅ 0.1-5.0 | ⚠️ basic only | ✅ toNumber | ⚠️ isSlow, isFast needed | ⚠️ PARTIAL |
| **SwipeDirection** (ADT) | 4 values | N/A | N/A | N/A | ⚠️ Missing `allSwipeDirections` |
| **GesturePhase** (ADT) | 6 values | N/A | N/A | N/A | ⚠️ Missing `allGesturePhases` |

---

### MOTION PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **AnimationDirection** (ADT) | 4 values | N/A | ✅ toCss | N/A | ⚠️ Missing `allAnimationDirections` |
| **AnimationFillMode** (ADT) | 4 values | N/A | ✅ toCss | N/A | ⚠️ Missing `allAnimationFillModes` |
| **AnimationPlayState** (ADT) | 2 values | N/A | ✅ toCss | N/A | ⚠️ Missing `allAnimationPlayStates` |
| **FullInterpolationType** (ADT) | 33 values | N/A | N/A | N/A | ⚠️ Missing `allInterpolationTypes` |
| **ControlMode** (ADT) | 3 values | N/A | N/A | N/A | ⚠️ Missing `allControlModes` |

---

### ELEVATION PILLAR

| Atom | Bounds | Calculations | Conversions | Predicates | Status |
|------|--------|--------------|-------------|------------|--------|
| **ZIndex** | ✅ -999 to 9999 | ✅ raise, lower | ✅ toNumber, toCss | ✅ isNegative, isPositive, isStacking | ✅ COMPLETE |

---

## SUMMARY STATISTICS

### By Completion Status

| Status | Count | Percentage |
|--------|-------|------------|
| ✅ COMPLETE | 25 | 76% |
| ⚠️ PARTIAL | 8 | 24% |
| ❌ BROKEN | 0 | 0% |

### By Category Gap

| Missing Category | Atoms Affected |
|------------------|----------------|
| Missing `all*` array | SwipeDirection, AnimationDirection, AnimationFillMode, AnimationPlayState, FullInterpolationType, ControlMode, NoteName, GesturePhase, Easing |
| Missing predicates | Progress (Temporal), Progress (Reactive), SwipeVelocityThreshold, FOV, Pixel |
| Missing calculations | FOV (needs blend/lerp) |

---

## ATOMS COMPLETED THIS SESSION (2026-02-26)

The following atoms were upgraded from PARTIAL to COMPLETE:

### Spatial Pillar

| Atom | Added Functions | Added Predicates |
|------|-----------------|------------------|
| **Metallic** | `blend`, `lerp`, `scale`, `add`, `subtract` | `isDielectric`, `isMetal`, `isHybrid` |
| **Roughness** | `blend`, `lerp`, `scale`, `add`, `subtract`, `invert`, `toSmoothness`, `fromSmoothness` | `isMirror`, `isGlossy`, `isSemiRough`, `isMatte` |
| **IOR** | `blend`, `lerp`, `fresnelF0`, `reflectivity`, `criticalAngle` | `isAir`, `isWater`, `isGlass`, `isDiamond`, `isLowIOR`, `isHighIOR` |

### Color Pillar

| Atom | Added Functions | Added Predicates |
|------|-----------------|------------------|
| **Hue** | `blend`, `blendShortestPath`, `lerp`, `toRadians`, `toDegrees`, `distance`, `shortestDistance` | `isWarm`, `isCool`, `isRed`, `isOrange`, `isYellow`, `isGreen`, `isCyan`, `isBlue`, `isMagenta`, `colorCategory` |
| **Saturation** | `blend`, `lerp`, `invert`, `fromUnitInterval` | `isMuted` |

### Typography Pillar

| Atom | Added Functions | Added Predicates |
|------|-----------------|------------------|
| **FontSize** | `blend`, `lerp`, `add`, `subtract`, `toNumber`, `toRem`, `minor`, `major` | `isReadable`, `isCompact`, `isDisplay`, `isHero` |
| **LineHeight** | `blend`, `lerp`, `scale`, `add`, `subtract`, `toNumber` | `isSolid`, `isTight`, `isNormal`, `isRelaxed`, `isLoose`, `atLeast`, `lessThan` |
| **LetterSpacing** | `blend`, `lerp`, `scale`, `add`, `subtract`, `invert`, `toNumber` | `isTight`, `isNone`, `isLoose`, `isNegative`, `isPositive` |

### Material Pillar

| Atom | Added Functions | Added Predicates |
|------|-----------------|------------------|
| **BlurRadius** | `blend`, `lerp`, `scale`, `add`, `subtract`, `toLegacyCss` | `isSharp`, `isSubtle`, `isModerate`, `isHeavy`, `isExtreme`, `atLeast`, `lessThan` |

---

## NEXT ATOMS TO COMPLETE

### Priority 1: Add Missing `all*` Arrays

Quick win - just enumerate constructors:

1. `SwipeDirection` → `allSwipeDirections`
2. `AnimationDirection` → `allAnimationDirections`
3. `AnimationFillMode` → `allAnimationFillModes`
4. `AnimationPlayState` → `allAnimationPlayStates`
5. `ControlMode` → `allControlModes`
6. `NoteName` → `allNoteNames`
7. `GesturePhase` → `allGesturePhases`
8. `Easing` → `allEasings`
9. `FullInterpolationType` → `allInterpolationTypes`

### Priority 2: Add Missing Predicates

| Atom | Predicates Needed |
|------|-------------------|
| `Progress` (Temporal) | `isStart`, `isEnd`, `isHalfway`, `isPastHalf` |
| `Progress` (Reactive) | Same as above |
| `FOV` | `isNarrow`, `isNormal`, `isWide`, `isUltraWide` |
| `SwipeVelocityThreshold` | `isSlow`, `isNormal`, `isFast` |
| `Pixel` | `isSmall`, `isMedium`, `isLarge` |

### Priority 3: Add Missing Calculations

| Atom | Calculations Needed |
|------|---------------------|
| `FOV` | `blend`, `lerp` |
| `Progress` (both) | `blend` |

---

## VERIFICATION COMMANDS

### Check All Atoms Build

```bash
nix develop --command spago build
```

### Count Exports Per Atom

```bash
grep -E "^  , " src/Hydrogen/Schema/Color/Hue.purs | wc -l
```

### Find Atoms Missing `bounds` Export

```bash
for f in src/Hydrogen/Schema/**/*.purs; do
  if grep -q "newtype.*Number\|newtype.*Int" "$f"; then
    if ! grep -q "bounds ::" "$f"; then
      echo "Missing bounds: $f"
    fi
  fi
done
```

### Find Atoms Missing `lerp`

```bash
grep -rL "lerp ::" src/Hydrogen/Schema/*/*.purs | grep -v "ADT\|Types"
```

---

## ATOM TEMPLATE

When creating new atoms, follow this template:

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // <pillar> // <atom>
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | <Atom> - <one line description>
-- |
-- | Range: <min> to <max> (<clamps|wraps>)
-- | - **<min>**: <meaning>
-- | - **<mid>**: <meaning>
-- | - **<max>**: <meaning>
-- |
-- | <Additional context about the atom's purpose and usage>

module Hydrogen.Schema.<Pillar>.<Atom>
  ( <Atom>
  , <atom>                -- Smart constructor
  , unwrap
  , toNumber
  , bounds
  -- Constants
  , <constant1>
  , <constant2>
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  -- Predicates
  , is<Category1>
  , is<Category2>
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // <atom>
-- ═══════════════════════════════════════════════════════════════════════════════

newtype <Atom> = <Atom> Number

derive instance eq<Atom> :: Eq <Atom>
derive instance ord<Atom> :: Ord <Atom>

instance show<Atom> :: Show <Atom> where
  show (<Atom> x) = show x <> "<unit>"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

<atom> :: Number -> <Atom>
<atom> n = <Atom> (Bounded.clampNumber <min> <max> n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // constants
-- ═══════════════════════════════════════════════════════════════════════════════

<constant1> :: <Atom>
<constant1> = <Atom> <value>

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

blend :: Number -> <Atom> -> <Atom> -> <Atom>
blend weight (<Atom> a) (<Atom> b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in <atom> (a * (1.0 - w) + b * w)

lerp :: <Atom> -> <Atom> -> Number -> <Atom>
lerp from to t = blend t from to

scale :: Number -> <Atom> -> <Atom>
scale factor (<Atom> x) = <atom> (x * factor)

add :: Number -> <Atom> -> <Atom>
add amount (<Atom> x) = <atom> (x + amount)

subtract :: Number -> <Atom> -> <Atom>
subtract amount (<Atom> x) = <atom> (x - amount)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // predicates
-- ═══════════════════════════════════════════════════════════════════════════════

is<Category1> :: <Atom> -> Boolean
is<Category1> (<Atom> x) = x <= <threshold>

is<Category2> :: <Atom> -> Boolean
is<Category2> (<Atom> x) = x > <threshold>

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

unwrap :: <Atom> -> Number
unwrap (<Atom> x) = x

toNumber :: <Atom> -> Number
toNumber (<Atom> x) = x

bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds <min> <max> "<atom>" "<description>"
```

---

*Last updated: 2026-02-26*
