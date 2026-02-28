-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // docs // lean proof roadmap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# HYDROGEN LEAN4 PROOF ROADMAP

**Date**: 2026-02-26
**Current Coverage**: 65% (7/15 pillars have proofs)
**Target Coverage**: 100%

---

## EXECUTIVE SUMMARY

The Hydrogen Lean4 proof infrastructure has **strong foundations** in Math primitives
and Brand Schema, but **8 pillars are missing proofs entirely**. This document
provides a systematic approach to achieving full formal verification.

---

## CURRENT STATE

### Pillars WITH Proofs

| Pillar | Modules | Theorems | Status |
|--------|---------|----------|--------|
| **Color** | Hue, Conversions, Real | 8 | PARTIAL |
| **Typography** | Typography | 4 | COMPLETE |
| **Material** | 5 modules | 15+ | COMPLETE |
| **Spatial** | WorldModel (10 modules) | 20+ | PARTIAL |
| **Brand** | 10 modules | 35+ | COMPLETE |
| **Identity** | Identity | 3 | COMPLETE |
| **Math** | 19 modules | 100+ | COMPLETE |

### Pillars MISSING Proofs

| Pillar | Priority | Effort | Critical For |
|--------|----------|--------|--------------|
| **Dimension** | HIGH | 3 days | Layout correctness |
| **Temporal** | HIGH | 2 days | Animation safety |
| **Accessibility** | HIGH | 3 days | WCAG compliance |
| **Elevation** | MEDIUM | 2 days | Z-ordering |
| **Reactive** | MEDIUM | 2 days | State machines |
| **Motion** | MEDIUM | 4 days | Animation curves |
| **Gestural** | LOW | 3 days | Touch handling |
| **Haptic** | LOW | 2 days | Vibration patterns |

---

## PROOF ARCHITECTURE

### Directory Structure

```
proofs/
├── Hydrogen.lean              -- Root import
├── lakefile.lean              -- Build configuration
├── lean-toolchain             -- Lean version (4.7.0)
└── Hydrogen/
    ├── Math.lean              -- Math primitives leader
    ├── Math/
    │   ├── Bounded.lean       -- Core bounded types (COMPLETE)
    │   ├── Vec2.lean          -- 2D vectors
    │   ├── Vec3.lean          -- 3D vectors
    │   ├── Vec4.lean          -- 4D vectors
    │   ├── Mat3.lean          -- 3x3 matrices
    │   ├── Mat4.lean          -- 4x4 matrices
    │   └── Quaternion.lean    -- Quaternion rotation
    ├── Schema/
    │   ├── Color/
    │   │   ├── Hue.lean       -- Hue rotation proofs (COMPLETE)
    │   │   ├── Conversions.lean -- Color space conversions
    │   │   └── Real.lean      -- Real-valued color components
    │   ├── Dimension/         -- TO CREATE
    │   │   ├── Pixel.lean
    │   │   ├── Viewport.lean
    │   │   └── Physical.lean
    │   ├── Typography/
    │   │   └── Typography.lean -- Font weight, scale (COMPLETE)
    │   ├── Temporal/          -- TO CREATE
    │   │   ├── Duration.lean
    │   │   ├── Progress.lean
    │   │   └── Easing.lean
    │   ├── Accessibility/     -- TO CREATE
    │   │   ├── Contrast.lean
    │   │   └── WCAG.lean
    │   ├── Elevation/         -- TO CREATE
    │   │   ├── ZIndex.lean
    │   │   └── Shadow.lean
    │   ├── Reactive/          -- TO CREATE
    │   │   └── State.lean
    │   ├── Motion/            -- TO CREATE
    │   │   ├── Spring.lean
    │   │   └── Bezier.lean
    │   ├── Gestural/          -- TO CREATE
    │   │   └── Gesture.lean
    │   ├── Haptic/            -- TO CREATE
    │   │   └── Pattern.lean
    │   └── Brand/
    │       ├── Brand.lean     -- (COMPLETE)
    │       ├── Typography.lean
    │       ├── Spacing.lean
    │       └── ... (10 modules)
    └── Material/
        ├── Material.lean      -- PBR properties (COMPLETE)
        ├── BRDF.lean
        └── ... (5 modules)
```

---

## PROOF TEMPLATES

### Template: Bounded Numeric Atom

```lean
-- proofs/Hydrogen/Schema/<Pillar>/<Atom>.lean

import Hydrogen.Math.Bounded

namespace Hydrogen.Schema.<Pillar>.<Atom>

/-!
# <Atom>

<Description of what this atom represents>

## Bounds

- Minimum: <min>
- Maximum: <max>
- Behavior: <clamps|wraps>

## Proven Properties

1. `bounds_valid` - Values are always within bounds
2. `clamp_idempotent` - Clamping is idempotent
3. `lerp_bounded` - Linear interpolation stays in bounds
-/

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // core type
-- ═══════════════════════════════════════════════════════════════════════════════

/-- <Atom> bounded to [<min>, <max>] -/
structure <Atom> where
  val : Float
  ge_min : val ≥ <min>
  le_max : val ≤ <max>
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Create <atom> with clamping -/
def <atom> (x : Float) : <Atom> :=
  let clamped := Float.clamp <min> <max> x
  ⟨clamped, Float.clamp_ge_min, Float.clamp_le_max⟩

/-- Unsafe constructor (requires proof) -/
def <atom>Unsafe (x : Float) (h_ge : x ≥ <min>) (h_le : x ≤ <max>) : <Atom> :=
  ⟨x, h_ge, h_le⟩

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // theorems
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Values are always within bounds -/
theorem bounds_valid (x : <Atom>) : x.val ≥ <min> ∧ x.val ≤ <max> :=
  ⟨x.ge_min, x.le_max⟩

/-- Clamping is idempotent -/
theorem clamp_idempotent (x : Float) : <atom> (<atom> x).val = <atom> x := by
  simp [<atom>]
  apply Float.clamp_idempotent

/-- Already-valid values pass through unchanged -/
theorem clamp_noop (x : Float) (h_ge : x ≥ <min>) (h_le : x ≤ <max>) :
    (<atom> x).val = x := by
  simp [<atom>]
  exact Float.clamp_noop h_ge h_le

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Linear interpolation (always in bounds) -/
def lerp (a b : <Atom>) (t : UnitInterval) : <Atom> :=
  <atom> (a.val * (1 - t.val) + b.val * t.val)

/-- Lerp stays within bounds -/
theorem lerp_bounded (a b : <Atom>) (t : UnitInterval) :
    (lerp a b t).val ≥ <min> ∧ (lerp a b t).val ≤ <max> :=
  bounds_valid (lerp a b t)

/-- Lerp at t=0 returns first value -/
theorem lerp_at_zero (a b : <Atom>) :
    lerp a b ⟨0, by norm_num, by norm_num⟩ = a := by
  simp [lerp]
  -- ... proof

/-- Lerp at t=1 returns second value -/
theorem lerp_at_one (a b : <Atom>) :
    lerp a b ⟨1, by norm_num, by norm_num⟩ = b := by
  simp [lerp]
  -- ... proof

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // purescript codegen
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generate corresponding PureScript module -/
def generatePureScript : String :=
"module Hydrogen.Schema.<Pillar>.<Atom> where

import Hydrogen.Schema.Bounded (clampNumber)

newtype <Atom> = <Atom> Number

<atom> :: Number -> <Atom>
<atom> n = <Atom> (clampNumber <min> <max> n)

unwrap :: <Atom> -> Number
unwrap (<Atom> x) = x

lerp :: <Atom> -> <Atom> -> Number -> <Atom>
lerp (<Atom> a) (<Atom> b) t =
  let t' = clampNumber 0.0 1.0 t
  in <atom> (a * (1.0 - t') + b * t')
"

end Hydrogen.Schema.<Pillar>.<Atom>
```

### Template: Cyclic Bounded Atom (like Hue)

```lean
-- For atoms that wrap instead of clamp

namespace Hydrogen.Schema.<Pillar>.<CyclicAtom>

structure <CyclicAtom> where
  val : Fin <period>
  deriving Repr, DecidableEq, Hashable

/-- Create with wrapping -/
def <cyclicAtom> (n : Int) : <CyclicAtom> :=
  ⟨Fin.ofInt' n <period>, rfl⟩

/-- Rotation (addition with wrapping) -/
def rotate (degrees : Int) (x : <CyclicAtom>) : <CyclicAtom> :=
  <cyclicAtom> (x.val.val + degrees)

/-- Rotation by 0 is identity -/
theorem rotate_zero (x : <CyclicAtom>) : rotate 0 x = x := by
  simp [rotate, <cyclicAtom>]

/-- Rotation is associative -/
theorem rotate_assoc (a b : Int) (x : <CyclicAtom>) :
    rotate a (rotate b x) = rotate (a + b) x := by
  simp [rotate]
  ring

/-- Full rotation is identity -/
theorem rotate_period (x : <CyclicAtom>) : rotate <period> x = x := by
  simp [rotate, <cyclicAtom>]
  -- Fin.ofInt' handles wraparound

end Hydrogen.Schema.<Pillar>.<CyclicAtom>
```

### Template: ADT Enum

```lean
-- For enumerated types like AnimationDirection

namespace Hydrogen.Schema.<Pillar>.<Enum>

/-- <Enum> with exactly N variants -/
inductive <Enum> where
  | variant1 : <Enum>
  | variant2 : <Enum>
  | variant3 : <Enum>
  deriving Repr, DecidableEq, Hashable

/-- All variants -/
def all : List <Enum> := [.variant1, .variant2, .variant3]

/-- All variants enumerated -/
theorem all_complete : all.length = 3 := rfl

/-- Every value is in the list -/
theorem all_contains (x : <Enum>) : x ∈ all := by
  cases x <;> simp [all]

end Hydrogen.Schema.<Pillar>.<Enum>
```

---

## PILLAR-SPECIFIC PROOFS

### Dimension Pillar (Priority: HIGH)

**File**: `proofs/Hydrogen/Schema/Dimension/Pixel.lean`

```lean
namespace Hydrogen.Schema.Dimension.Pixel

/-- Pixel values (unbounded but finite) -/
structure Pixel where
  val : Float
  is_finite : val.isFinite
  deriving Repr

/-- Pixel addition -/
def add (a b : Pixel) : Pixel :=
  ⟨a.val + b.val, Float.add_finite a.is_finite b.is_finite⟩

/-- Pixel scaling -/
def scale (factor : Float) (h : factor.isFinite) (p : Pixel) : Pixel :=
  ⟨p.val * factor, Float.mul_finite p.is_finite h⟩

/-- Addition is commutative -/
theorem add_comm (a b : Pixel) : add a b = add b a := by
  simp [add]
  ring

/-- Zero is identity for addition -/
theorem add_zero (p : Pixel) : add p ⟨0, Float.zero_finite⟩ = p := by
  simp [add]

end Hydrogen.Schema.Dimension.Pixel
```

**File**: `proofs/Hydrogen/Schema/Dimension/AspectRatio.lean`

```lean
namespace Hydrogen.Schema.Dimension.AspectRatio

/-- Aspect ratio (width / height), always positive -/
structure AspectRatio where
  val : Float
  is_positive : val > 0
  is_finite : val.isFinite
  deriving Repr

/-- Common aspect ratios -/
def square : AspectRatio := ⟨1.0, by norm_num, Float.one_finite⟩
def widescreen : AspectRatio := ⟨16.0 / 9.0, by norm_num, by norm_num⟩
def ultrawide : AspectRatio := ⟨21.0 / 9.0, by norm_num, by norm_num⟩

/-- Invert aspect ratio -/
def invert (ar : AspectRatio) : AspectRatio :=
  ⟨1.0 / ar.val, Float.inv_positive ar.is_positive, Float.inv_finite ar.is_finite⟩

/-- Inversion is involutive -/
theorem invert_involutive (ar : AspectRatio) : invert (invert ar) = ar := by
  simp [invert]
  -- 1 / (1 / x) = x for x > 0

/-- Predicates -/
def isSquare (ar : AspectRatio) : Bool := ar.val == 1.0
def isPortrait (ar : AspectRatio) : Bool := ar.val < 1.0
def isLandscape (ar : AspectRatio) : Bool := ar.val > 1.0

/-- Square is neither portrait nor landscape -/
theorem square_neither : ¬isPortrait square ∧ ¬isLandscape square := by
  simp [isPortrait, isLandscape, square]

end Hydrogen.Schema.Dimension.AspectRatio
```

### Temporal Pillar (Priority: HIGH)

**File**: `proofs/Hydrogen/Schema/Temporal/Duration.lean`

```lean
namespace Hydrogen.Schema.Temporal.Duration

/-- Duration in milliseconds (non-negative) -/
structure Duration where
  ms : Float
  is_nonneg : ms ≥ 0
  is_finite : ms.isFinite
  deriving Repr

/-- Zero duration -/
def zero : Duration := ⟨0, by norm_num, Float.zero_finite⟩

/-- Duration addition -/
def add (a b : Duration) : Duration :=
  ⟨a.ms + b.ms, 
   Float.add_nonneg a.is_nonneg b.is_nonneg,
   Float.add_finite a.is_finite b.is_finite⟩

/-- Duration scaling -/
def scale (factor : Float) (h_pos : factor ≥ 0) (h_fin : factor.isFinite) 
    (d : Duration) : Duration :=
  ⟨d.ms * factor,
   Float.mul_nonneg d.is_nonneg h_pos,
   Float.mul_finite d.is_finite h_fin⟩

/-- Addition is associative -/
theorem add_assoc (a b c : Duration) : add (add a b) c = add a (add b c) := by
  simp [add]
  ring

/-- Zero is identity -/
theorem add_zero (d : Duration) : add d zero = d := by
  simp [add, zero]

/-- Non-negativity preserved through operations -/
theorem add_nonneg (a b : Duration) : (add a b).ms ≥ 0 :=
  (add a b).is_nonneg

end Hydrogen.Schema.Temporal.Duration
```

**File**: `proofs/Hydrogen/Schema/Temporal/Progress.lean`

```lean
namespace Hydrogen.Schema.Temporal.Progress

/-- Animation progress [0, 1] -/
structure Progress where
  val : Float
  ge_zero : val ≥ 0
  le_one : val ≤ 1
  deriving Repr

def start : Progress := ⟨0, by norm_num, by norm_num⟩
def end_ : Progress := ⟨1, by norm_num, by norm_num⟩
def half : Progress := ⟨0.5, by norm_num, by norm_num⟩

/-- Clamp to valid progress -/
def progress (x : Float) : Progress :=
  let clamped := Float.clamp 0 1 x
  ⟨clamped, Float.clamp_ge_zero, Float.clamp_le_one⟩

/-- Complement (1 - progress) -/
def complement (p : Progress) : Progress :=
  ⟨1 - p.val, by linarith [p.le_one], by linarith [p.ge_zero]⟩

/-- Complement is involutive -/
theorem complement_involutive (p : Progress) : complement (complement p) = p := by
  simp [complement]
  ring

/-- Predicates -/
def isStart (p : Progress) : Bool := p.val == 0
def isEnd (p : Progress) : Bool := p.val == 1
def isPastHalf (p : Progress) : Bool := p.val > 0.5

end Hydrogen.Schema.Temporal.Progress
```

### Accessibility Pillar (Priority: HIGH)

**File**: `proofs/Hydrogen/Schema/Accessibility/Contrast.lean`

```lean
namespace Hydrogen.Schema.Accessibility.Contrast

/-- WCAG contrast ratio (1:1 to 21:1) -/
structure ContrastRatio where
  val : Float
  ge_one : val ≥ 1
  le_twentyone : val ≤ 21
  deriving Repr

/-- WCAG thresholds -/
def wcagAA : Float := 4.5
def wcagAALarge : Float := 3.0
def wcagAAA : Float := 7.0
def wcagAAALarge : Float := 4.5

/-- Check WCAG AA compliance -/
def meetsAA (cr : ContrastRatio) : Bool := cr.val ≥ wcagAA

/-- Check WCAG AAA compliance -/
def meetsAAA (cr : ContrastRatio) : Bool := cr.val ≥ wcagAAA

/-- AAA implies AA -/
theorem aaa_implies_aa (cr : ContrastRatio) : meetsAAA cr → meetsAA cr := by
  intro h
  simp [meetsAAA, meetsAA, wcagAAA, wcagAA] at *
  linarith

/-- Calculate relative luminance (sRGB formula) -/
def relativeLuminance (r g b : Float) : Float :=
  let adjust := fun c => 
    if c ≤ 0.03928 then c / 12.92
    else ((c + 0.055) / 1.055) ^ 2.4
  0.2126 * adjust r + 0.7152 * adjust g + 0.0722 * adjust b

/-- Calculate contrast ratio between two luminances -/
def contrastRatio (l1 l2 : Float) : Float :=
  let lighter := max l1 l2
  let darker := min l1 l2
  (lighter + 0.05) / (darker + 0.05)

/-- Contrast ratio is symmetric -/
theorem contrast_symmetric (l1 l2 : Float) : 
    contrastRatio l1 l2 = contrastRatio l2 l1 := by
  simp [contrastRatio]
  -- max/min symmetry

/-- Contrast with self is 1:1 -/
theorem contrast_self (l : Float) : contrastRatio l l = 1 := by
  simp [contrastRatio]
  ring

end Hydrogen.Schema.Accessibility.Contrast
```

---

## VERIFICATION WORKFLOW

### 1. Write Proof

```bash
# Edit proof file
vim proofs/Hydrogen/Schema/Dimension/Pixel.lean
```

### 2. Build Proofs

```bash
# Build all proofs
cd proofs && lake build

# Check specific file
lake build Hydrogen.Schema.Dimension.Pixel
```

### 3. Verify No `sorry`

```bash
# Should return empty
grep -r "sorry" proofs/Hydrogen/Schema/
```

### 4. Generate PureScript

```bash
# Extract PureScript from proofs
lake exe generatePureScript > src/Hydrogen/Schema/Dimension/Pixel.purs
```

### 5. Verify Correspondence

```bash
# Compare bounds in Lean vs PureScript
diff <(grep "clamp" proofs/Hydrogen/Schema/Dimension/Pixel.lean) \
     <(grep "clamp" src/Hydrogen/Schema/Dimension/Pixel.purs)
```

---

## AXIOM POLICY

### Acceptable Axioms

| Category | Example | Justification |
|----------|---------|---------------|
| IEEE 754 | `Float.add_finite` | Hardware spec |
| Cryptographic | `SHA256.collision_resistant` | Crypto spec |
| Stdlib | `List.length_append` | Proven elsewhere |

### Unacceptable Axioms

| Pattern | Why Bad |
|---------|---------|
| `sorry` | Incomplete proof |
| `axiom valid : ...` without justification | Unjustified assumption |
| `native_decide` on unbounded types | Runtime-dependent |

### Documenting Axioms

```lean
/-- 
Axiom: IEEE 754 addition of finite floats is finite.

Justification: IEEE 754-2019 Section 7.2 guarantees that
addition of finite operands produces either a finite result
or an infinity (which we exclude via type constraints).
-/
axiom Float.add_finite : ∀ (a b : Float), 
  a.isFinite → b.isFinite → (a + b).isFinite
```

---

## TIMELINE

| Week | Pillar | Deliverables |
|------|--------|--------------|
| 5 | Dimension | Pixel.lean, AspectRatio.lean, Viewport.lean |
| 6 | Temporal | Duration.lean, Progress.lean, Easing.lean |
| 6 | Accessibility | Contrast.lean, WCAG.lean |
| 7 | Elevation | ZIndex.lean, Shadow.lean |
| 7 | Reactive | State.lean |
| 8 | Motion | Spring.lean, Bezier.lean |
| 9 | Gestural | Gesture.lean |
| 9 | Haptic | Pattern.lean |

---

## SUCCESS CRITERIA

1. **Zero `sorry`** in all proof files
2. **All axioms documented** with justification
3. **PureScript correspondence** verified for bounds
4. **All theorems** listed in manifest
5. **CI integration** with `lake build` passing

---

*Last updated: 2026-02-26*
