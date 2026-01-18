# Hybrid Architecture: Lean4 Verified Math Core + TypeScript/Vue Frontend

> **Goal:** Extract mathematically critical code to Lean4 with formal proofs, compile to JavaScript, integrate with existing TypeScript codebase.
>
> **Timeline:** 6-12 months (parallel with ongoing development)
>
> **Risk Level:** MEDIUM - Incremental, can abort without losing work

---

## Executive Summary

### The Hybrid Approach

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        EXISTING FRONTEND (KEEP)                             │
│  Vue 3 + TypeScript + Three.js + Pinia                                      │
│  175,000 lines of working code                                              │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                      TYPE-SAFE FFI BOUNDARY                                 │
│  Generated TypeScript types from Lean4 definitions                          │
│  Runtime validation at boundary                                             │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        LEAN4 VERIFIED CORE (NEW)                            │
│  Mathlib4 for proofs | Compiled to JavaScript                               │
│  ~8,000 lines of verified math code                                         │
└─────────────────────────────────────────────────────────────────────────────┘
```

### What Gets Verified

| Domain | Lines | Why Verify | Proof Goals |
|--------|-------|------------|-------------|
| **Interpolation** | ~900 | Core animation math | Continuity, bounds, determinism |
| **Easing** | ~215 | 35 easing functions | Range [0,1] → [0,1], monotonicity |
| **Bezier** | ~400 | Curve evaluation | Derivative continuity, bounds |
| **Vector/Matrix** | ~1,050 | 3D transforms | Invertibility, associativity |
| **Physics** | ~1,600 | Particle simulation | Energy conservation, stability |
| **Color** | ~300 | Color space conversion | Gamut mapping, round-trip |
| **Random** | ~100 | Deterministic RNG | Uniformity, period length |
| **TOTAL** | ~4,565 | | |

---

## Phase 0: Foundation & Tooling (Weeks 1-4)

### 0.1 Lean4 Development Environment

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Create Lean4 project
mkdir lattice-math-core
cd lattice-math-core
lake init LatticeCore math
```

**Project structure:**
```
lattice-math-core/
├── LatticeCore/
│   ├── Interpolation/
│   │   ├── Linear.lean
│   │   ├── Bezier.lean
│   │   ├── Easing.lean
│   │   └── Properties.lean      # Proofs
│   ├── Geometry/
│   │   ├── Vec2.lean
│   │   ├── Vec3.lean
│   │   ├── Mat4.lean
│   │   └── Properties.lean      # Proofs
│   ├── Physics/
│   │   ├── Forces.lean
│   │   ├── Integration.lean
│   │   └── Properties.lean      # Proofs
│   └── Random/
│       ├── Mulberry32.lean
│       └── Properties.lean      # Proofs
├── Tests/
├── lakefile.lean
└── lean-toolchain
```

### 0.2 Lean4 → JavaScript Compilation Setup

Lean4 compiles to C by default. For JavaScript:

**Option A: lean4-js (experimental)**
```lean
-- In lakefile.lean
require lean4js from git "https://github.com/AdrienChampion/lean4-js"
```

**Option B: Export to JSON + codegen**
```lean
-- Generate JSON spec, use custom TS codegen
@[export] def interpolate_linear (t a b : Float) : Float := ...
```

**Option C: Foreign Function Interface (most practical)**
```typescript
// Generated TypeScript wrapper calls Lean4-compiled WASM
import { LatticeCore } from './lattice-core.wasm';

export function interpolateLinear(t: number, a: number, b: number): number {
  return LatticeCore.interpolate_linear(t, a, b);
}
```

### 0.3 Continuous Integration

```yaml
# .github/workflows/lean4-proofs.yml
name: Lean4 Proofs
on: [push, pull_request]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          build: true
          test: true
      - name: Verify proofs
        run: lake build
      - name: Generate JavaScript
        run: lake exe codegen
```

---

## Phase 1: Easing Functions (Weeks 5-8)

### 1.1 Why Start Here

- **Self-contained:** No dependencies on other modules
- **Well-specified:** Mathematical definitions are clear
- **Testable:** Easy to compare Lean4 output vs TypeScript
- **Low risk:** If it fails, we lose nothing

### 1.2 Lean4 Implementation

```lean
-- LatticeCore/Interpolation/Easing.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace LatticeCore.Easing

/-- Easing function type: maps [0,1] → ℝ -/
def EasingFn := { f : Float → Float // f 0 = 0 ∧ f 1 = 1 }

/-- Linear easing (identity) -/
def linear : EasingFn := ⟨id, by simp, by simp⟩

/-- Quadratic ease-in: t² -/
def easeInQuad : EasingFn := ⟨fun t => t * t, by ring, by ring⟩

/-- Quadratic ease-out: 1 - (1-t)² -/
def easeOutQuad : EasingFn := ⟨fun t => 1 - (1 - t) * (1 - t), by ring, by ring⟩

/-- Cubic ease-in: t³ -/
def easeInCubic : EasingFn := ⟨fun t => t * t * t, by ring, by ring⟩

-- ... 35 easing functions total

end LatticeCore.Easing
```

### 1.3 Proofs to Verify

```lean
-- LatticeCore/Interpolation/Properties.lean

/-- All easing functions map [0,1] to bounded range -/
theorem easing_bounded (f : EasingFn) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ (lo hi : Float), lo ≤ f.val t ∧ f.val t ≤ hi := by
  -- Proof depends on specific easing function
  sorry

/-- Ease-in functions are monotonically increasing -/
theorem ease_in_monotone (f : EasingFn) (hf : IsEaseIn f) :
    ∀ t₁ t₂, t₁ ≤ t₂ → f.val t₁ ≤ f.val t₂ := by
  sorry

/-- Determinism: same input always produces same output -/
theorem easing_deterministic (f : EasingFn) (t : Float) :
    f.val t = f.val t := rfl
```

### 1.4 Generated TypeScript Interface

```typescript
// Generated: lattice-core/easing.ts

/**
 * @verified Lean4 proof: easing_bounded
 * @verified Lean4 proof: ease_in_monotone
 */
export type EasingName =
  | 'linear'
  | 'easeInQuad' | 'easeOutQuad' | 'easeInOutQuad'
  | 'easeInCubic' | 'easeOutCubic' | 'easeInOutCubic'
  // ... all 35

/**
 * Apply easing function to normalized time value
 * @param name - Easing function name
 * @param t - Time value in range [0, 1]
 * @returns Eased value (may exceed [0,1] for overshoot easings)
 * 
 * @verified Contracts:
 * - If t ∈ [0,1] and name is non-overshoot, result ∈ [0,1]
 * - f(0) = 0, f(1) = 1 for all functions
 * - Deterministic: f(t) always equals f(t)
 */
export function applyEasing(name: EasingName, t: number): number {
  // Calls into Lean4-compiled code
  return LatticeCore.applyEasing(name, t);
}
```

### 1.5 Integration Test

```typescript
// ui/src/__tests__/lean4/easing.integration.test.ts

import { applyEasing } from '@/lean4/easing';
import { easings } from '@/services/easing'; // Original TypeScript

describe('Lean4 Easing Integration', () => {
  const testCases = [0, 0.25, 0.5, 0.75, 1];
  
  for (const [name, fn] of Object.entries(easings)) {
    it(`${name} matches original implementation`, () => {
      for (const t of testCases) {
        const lean4Result = applyEasing(name as EasingName, t);
        const tsResult = fn(t);
        expect(lean4Result).toBeCloseTo(tsResult, 10);
      }
    });
  }
});
```

---

## Phase 2: Linear Interpolation (Weeks 9-12)

### 2.1 Core Interpolation Types

```lean
-- LatticeCore/Interpolation/Linear.lean

namespace LatticeCore.Interpolation

/-- Linear interpolation: lerp(t, a, b) = a + t * (b - a) -/
def lerp (t a b : Float) : Float := a + t * (b - a)

/-- Alternative formulation: lerp(t, a, b) = (1-t)*a + t*b -/
def lerp' (t a b : Float) : Float := (1 - t) * a + t * b

/-- The two formulations are equivalent -/
theorem lerp_equiv (t a b : Float) : lerp t a b = lerp' t a b := by ring

/-- Lerp at t=0 returns a -/
theorem lerp_zero (a b : Float) : lerp 0 a b = a := by simp [lerp]

/-- Lerp at t=1 returns b -/
theorem lerp_one (a b : Float) : lerp 1 a b = b := by simp [lerp]

/-- Lerp is continuous in t -/
theorem lerp_continuous (a b : Float) : Continuous (fun t => lerp t a b) := by
  simp [lerp]
  continuity

end LatticeCore.Interpolation
```

### 2.2 Vector Interpolation

```lean
-- LatticeCore/Geometry/Vec2.lean

structure Vec2 where
  x : Float
  y : Float
  deriving Repr, DecidableEq

namespace Vec2

def lerp (t : Float) (a b : Vec2) : Vec2 :=
  { x := LatticeCore.Interpolation.lerp t a.x b.x
  , y := LatticeCore.Interpolation.lerp t a.y b.y }

theorem lerp_zero (a b : Vec2) : lerp 0 a b = a := by
  simp [lerp, LatticeCore.Interpolation.lerp_zero]

theorem lerp_one (a b : Vec2) : lerp 1 a b = b := by
  simp [lerp, LatticeCore.Interpolation.lerp_one]

end Vec2
```

### 2.3 Color Interpolation (with Gamut Proofs)

```lean
-- LatticeCore/Color/Rgb.lean

structure Rgb where
  r : Float
  g : Float
  b : Float
  h_r : 0 ≤ r ∧ r ≤ 1
  h_g : 0 ≤ g ∧ g ≤ 1
  h_b : 0 ≤ b ∧ b ≤ 1

/-- Linear RGB interpolation preserves gamut -/
theorem rgb_lerp_in_gamut (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) (a b : Rgb) :
    let result := Rgb.lerp t a b
    0 ≤ result.r ∧ result.r ≤ 1 ∧
    0 ≤ result.g ∧ result.g ≤ 1 ∧
    0 ≤ result.b ∧ result.b ≤ 1 := by
  -- Convex combination of values in [0,1] stays in [0,1]
  sorry
```

---

## Phase 3: Bezier Curves (Weeks 13-18)

### 3.1 Cubic Bezier Definition

```lean
-- LatticeCore/Interpolation/Bezier.lean

namespace LatticeCore.Bezier

/-- Control points for cubic Bezier curve -/
structure CubicBezier where
  p0 : Vec2  -- Start point
  p1 : Vec2  -- Control point 1
  p2 : Vec2  -- Control point 2
  p3 : Vec2  -- End point

/-- Evaluate cubic Bezier at parameter t ∈ [0,1] -/
def eval (curve : CubicBezier) (t : Float) : Vec2 :=
  let t2 := t * t
  let t3 := t2 * t
  let mt := 1 - t
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  { x := mt3 * curve.p0.x + 3 * mt2 * t * curve.p1.x + 
         3 * mt * t2 * curve.p2.x + t3 * curve.p3.x
  , y := mt3 * curve.p0.y + 3 * mt2 * t * curve.p1.y + 
         3 * mt * t2 * curve.p2.y + t3 * curve.p3.y }

/-- Bezier curve passes through endpoints -/
theorem eval_endpoints (curve : CubicBezier) :
    eval curve 0 = curve.p0 ∧ eval curve 1 = curve.p3 := by
  constructor <;> simp [eval]

/-- Bezier curve is C∞ continuous -/
theorem eval_smooth (curve : CubicBezier) :
    ContDiff ℝ ⊤ (fun t => eval curve t) := by
  -- Polynomial, hence smooth
  sorry

end LatticeCore.Bezier
```

### 3.2 Newton-Raphson Solver (for timing curves)

```lean
-- LatticeCore/Interpolation/Bezier.lean (continued)

/-- Find t such that bezier(t).x = targetX using Newton-Raphson -/
def solveForX (curve : CubicBezier) (targetX : Float) 
    (maxIter : Nat := 10) (epsilon : Float := 1e-6) : Float :=
  let rec iterate (t : Float) (iter : Nat) : Float :=
    if iter = 0 then t
    else
      let x := (eval curve t).x
      let dx := deriv (fun s => (eval curve s).x) t
      if Float.abs (x - targetX) < epsilon then t
      else if Float.abs dx < 1e-10 then t  -- Avoid division by zero
      else iterate (t - (x - targetX) / dx) (iter - 1)
  iterate 0.5 maxIter

/-- Newton-Raphson converges for well-behaved curves -/
theorem newton_converges (curve : CubicBezier) (targetX : Float)
    (hMonotone : ∀ t₁ t₂, t₁ < t₂ → (eval curve t₁).x < (eval curve t₂).x)
    (hRange : curve.p0.x ≤ targetX ∧ targetX ≤ curve.p3.x) :
    ∃ t, (eval curve t).x = targetX := by
  -- Intermediate value theorem + monotonicity
  sorry
```

---

## Phase 4: 3D Math (Weeks 19-24)

### 4.1 Matrix Operations

```lean
-- LatticeCore/Geometry/Mat4.lean

/-- 4x4 matrix in column-major order -/
structure Mat4 where
  elements : Array Float
  h_size : elements.size = 16

namespace Mat4

/-- Identity matrix -/
def identity : Mat4 := ⟨#[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1], rfl⟩

/-- Matrix multiplication -/
def mul (a b : Mat4) : Mat4 := sorry

/-- Matrix inverse (partial function - may not exist) -/
def inverse (m : Mat4) : Option Mat4 := sorry

/-- Determinant -/
def det (m : Mat4) : Float := sorry

/-- Matrix is invertible iff determinant is non-zero -/
theorem invertible_iff_det_nonzero (m : Mat4) :
    (inverse m).isSome ↔ det m ≠ 0 := by
  sorry

/-- Matrix multiplication is associative -/
theorem mul_assoc (a b c : Mat4) : mul (mul a b) c = mul a (mul b c) := by
  sorry

/-- Identity is neutral element -/
theorem mul_identity (m : Mat4) : mul m identity = m ∧ mul identity m = m := by
  sorry

/-- Inverse is actual inverse -/
theorem inverse_correct (m : Mat4) (hInv : (inverse m).isSome) :
    mul m (inverse m).get! = identity ∧ mul (inverse m).get! m = identity := by
  sorry

end Mat4
```

### 4.2 Quaternion Operations

```lean
-- LatticeCore/Geometry/Quaternion.lean

/-- Unit quaternion for rotation representation -/
structure Quat where
  w : Float
  x : Float
  y : Float
  z : Float
  h_unit : w*w + x*x + y*y + z*z = 1

namespace Quat

/-- Quaternion multiplication (Hamilton product) -/
def mul (q1 q2 : Quat) : Quat := sorry

/-- Quaternion conjugate -/
def conj (q : Quat) : Quat := ⟨q.w, -q.x, -q.y, -q.z, by simp [q.h_unit]⟩

/-- SLERP: Spherical linear interpolation -/
def slerp (t : Float) (q1 q2 : Quat) : Quat := sorry

/-- SLERP at endpoints -/
theorem slerp_endpoints (q1 q2 : Quat) :
    slerp 0 q1 q2 = q1 ∧ slerp 1 q1 q2 = q2 := by
  sorry

/-- SLERP produces unit quaternions -/
theorem slerp_unit (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) (q1 q2 : Quat) :
    (slerp t q1 q2).w^2 + (slerp t q1 q2).x^2 + 
    (slerp t q1 q2).y^2 + (slerp t q1 q2).z^2 = 1 := by
  sorry

end Quat
```

---

## Phase 5: Particle Physics (Weeks 25-32)

### 5.1 Force Calculations

```lean
-- LatticeCore/Physics/Forces.lean

/-- 3D vector for physics -/
structure Vec3 where
  x : Float
  y : Float
  z : Float

/-- Force field configuration -/
inductive ForceFieldType
  | gravity
  | attractor
  | vortex
  | turbulence
  | drag

structure ForceField where
  fieldType : ForceFieldType
  position : Vec3
  strength : Float
  falloffStart : Float
  falloffEnd : Float

/-- Calculate force on particle from force field -/
def calculateForce (field : ForceField) (pos vel : Vec3) (mass : Float) : Vec3 :=
  match field.fieldType with
  | .gravity => { x := 0, y := -field.strength * mass, z := 0 }
  | .attractor =>
    let dir := Vec3.sub field.position pos
    let dist := Vec3.length dir
    let falloff := computeFalloff field dist
    Vec3.scale (Vec3.normalize dir) (field.strength * mass * falloff)
  | _ => sorry

/-- Gravity force is proportional to mass (F = mg) -/
theorem gravity_proportional (field : ForceField) (hGrav : field.fieldType = .gravity)
    (pos vel : Vec3) (m1 m2 : Float) (hPos : m1 > 0) :
    let f1 := calculateForce field pos vel m1
    let f2 := calculateForce field pos vel m2
    f1.y / m1 = f2.y / m2 := by
  sorry
```

### 5.2 Integration Methods

```lean
-- LatticeCore/Physics/Integration.lean

/-- Euler integration step -/
def eulerStep (pos vel acc : Vec3) (dt : Float) : Vec3 × Vec3 :=
  let newVel := Vec3.add vel (Vec3.scale acc dt)
  let newPos := Vec3.add pos (Vec3.scale vel dt)
  (newPos, newVel)

/-- Verlet integration step (more stable) -/
def verletStep (pos prevPos acc : Vec3) (dt : Float) : Vec3 :=
  Vec3.add (Vec3.sub (Vec3.scale pos 2) prevPos) (Vec3.scale acc (dt * dt))

/-- RK4 integration step (most accurate) -/
def rk4Step (pos vel : Vec3) (accelFn : Vec3 → Vec3 → Vec3) (dt : Float) : Vec3 × Vec3 :=
  sorry

/-- Energy is approximately conserved in symplectic integrators -/
theorem verlet_energy_bounded (pos₀ prevPos₀ : Vec3) (acc : Vec3 → Vec3)
    (dt : Float) (hSmall : dt < 0.1) (n : Nat) :
    let trajectory := verletTrajectory pos₀ prevPos₀ acc dt n
    let E₀ := kineticEnergy pos₀ prevPos₀ dt + potentialEnergy pos₀
    let Eₙ := kineticEnergy trajectory.last trajectory.secondLast dt + potentialEnergy trajectory.last
    |Eₙ - E₀| ≤ C * dt^2 * n := by
  -- Verlet is symplectic, preserves phase space volume
  sorry
```

### 5.3 Deterministic Random Number Generator

```lean
-- LatticeCore/Random/Mulberry32.lean

/-- Mulberry32 PRNG state -/
structure Mulberry32 where
  state : UInt32

/-- Advance PRNG state and get next value -/
def next (rng : Mulberry32) : Float × Mulberry32 :=
  let t := rng.state + 0x6D2B79F5
  let t := t ^^^ (t >>> 15)
  let t := t * (t ||| 1)
  let t := t ^^^ (t + (t ^^^ (t >>> 7)) * (t ||| 61))
  let t := t ^^^ (t >>> 14)
  let f := (t.toFloat / 4294967296.0)
  (f, ⟨t⟩)

/-- Same seed produces same sequence -/
theorem next_deterministic (seed : UInt32) :
    let rng := Mulberry32.mk seed
    (next rng).1 = (next (Mulberry32.mk seed)).1 := rfl

/-- Period is 2^32 (no proof - verified empirically) -/
axiom mulberry32_period : ∀ seed : UInt32, 
    let rng := Mulberry32.mk seed
    (iterate next (2^32) rng).2 = rng
```

---

## Phase 6: Integration & Migration (Weeks 33-40)

### 6.1 TypeScript FFI Layer

```typescript
// ui/src/lean4/index.ts

import initWasm, { LatticeCore } from './lattice-core.wasm';

let initialized = false;
let core: typeof LatticeCore;

/**
 * Initialize Lean4 verified math core
 * Must be called before using any verified functions
 */
export async function initLatticeCore(): Promise<void> {
  if (initialized) return;
  const module = await initWasm();
  core = module.LatticeCore;
  initialized = true;
}

/**
 * Verified easing function
 * @verified Lean4 proofs: easing_bounded, ease_in_monotone
 */
export function applyEasing(name: string, t: number): number {
  if (!initialized) throw new Error('LatticeCore not initialized');
  return core.applyEasing(name, t);
}

/**
 * Verified linear interpolation
 * @verified Lean4 proofs: lerp_zero, lerp_one, lerp_continuous
 */
export function lerp(t: number, a: number, b: number): number {
  if (!initialized) throw new Error('LatticeCore not initialized');
  return core.lerp(t, a, b);
}

/**
 * Verified cubic Bezier evaluation
 * @verified Lean4 proofs: eval_endpoints, eval_smooth
 */
export function evalCubicBezier(
  p0x: number, p0y: number,
  p1x: number, p1y: number,
  p2x: number, p2y: number,
  p3x: number, p3y: number,
  t: number
): { x: number; y: number } {
  if (!initialized) throw new Error('LatticeCore not initialized');
  return core.evalCubicBezier(p0x, p0y, p1x, p1y, p2x, p2y, p3x, p3y, t);
}

// ... more verified functions
```

### 6.2 Gradual Migration Strategy

```typescript
// ui/src/services/interpolation.ts (MODIFIED)

import { lerp as leanLerp, initLatticeCore } from '@/lean4';

// Feature flag for gradual rollout
const USE_LEAN4_MATH = import.meta.env.VITE_USE_LEAN4_MATH === 'true';

/**
 * Linear interpolation
 * 
 * Uses Lean4 verified implementation when available,
 * falls back to TypeScript for compatibility.
 */
export function lerp(t: number, a: number, b: number): number {
  if (USE_LEAN4_MATH) {
    return leanLerp(t, a, b);
  }
  // Original TypeScript fallback
  return a + t * (b - a);
}
```

### 6.3 Verification Tests

```typescript
// ui/src/__tests__/lean4/verification.test.ts

import { describe, it, expect, beforeAll } from 'vitest';
import * as fc from 'fast-check';
import { initLatticeCore, lerp, applyEasing, evalCubicBezier } from '@/lean4';

beforeAll(async () => {
  await initLatticeCore();
});

describe('Lean4 Verified Math', () => {
  describe('lerp', () => {
    it('satisfies boundary conditions', () => {
      fc.assert(fc.property(
        fc.float(), fc.float(),
        (a, b) => {
          expect(lerp(0, a, b)).toBeCloseTo(a, 10);
          expect(lerp(1, a, b)).toBeCloseTo(b, 10);
        }
      ));
    });

    it('is monotonic when a < b', () => {
      fc.assert(fc.property(
        fc.float({ min: 0, max: 1 }),
        fc.float({ min: 0, max: 1 }),
        fc.float(),
        fc.float(),
        (t1, t2, a, b) => {
          if (a < b && t1 < t2) {
            expect(lerp(t1, a, b)).toBeLessThanOrEqual(lerp(t2, a, b));
          }
        }
      ));
    });
  });

  describe('easing', () => {
    it('all easings satisfy boundary conditions', () => {
      const easings = [
        'linear', 'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
        'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
        // ... all 35
      ];
      
      for (const name of easings) {
        expect(applyEasing(name, 0)).toBeCloseTo(0, 10);
        expect(applyEasing(name, 1)).toBeCloseTo(1, 10);
      }
    });
  });

  describe('bezier', () => {
    it('passes through endpoints', () => {
      fc.assert(fc.property(
        fc.float(), fc.float(), // p0
        fc.float(), fc.float(), // p1
        fc.float(), fc.float(), // p2
        fc.float(), fc.float(), // p3
        (p0x, p0y, p1x, p1y, p2x, p2y, p3x, p3y) => {
          const at0 = evalCubicBezier(p0x, p0y, p1x, p1y, p2x, p2y, p3x, p3y, 0);
          const at1 = evalCubicBezier(p0x, p0y, p1x, p1y, p2x, p2y, p3x, p3y, 1);
          
          expect(at0.x).toBeCloseTo(p0x, 10);
          expect(at0.y).toBeCloseTo(p0y, 10);
          expect(at1.x).toBeCloseTo(p3x, 10);
          expect(at1.y).toBeCloseTo(p3y, 10);
        }
      ));
    });
  });
});
```

---

## Phase 7: Documentation & Maintenance (Ongoing)

### 7.1 Proof Documentation

```lean
/-!
# LatticeCore Mathematical Proofs

## Interpolation

### Linear Interpolation (`lerp`)

**Definition:** `lerp(t, a, b) = a + t * (b - a)`

**Proven Properties:**
1. `lerp(0, a, b) = a` (lerp_zero)
2. `lerp(1, a, b) = b` (lerp_one)
3. `lerp` is continuous in all arguments (lerp_continuous)
4. For `a ≤ b`, `lerp` is monotonically increasing in `t` (lerp_monotone)

### Bezier Curves

**Definition:** Cubic Bezier with control points P₀, P₁, P₂, P₃

**Proven Properties:**
1. `B(0) = P₀`, `B(1) = P₃` (eval_endpoints)
2. `B` is C∞ smooth (eval_smooth)
3. `B(t)` lies within convex hull of control points (convex_hull)

## Geometry

### Matrices

**Proven Properties:**
1. Matrix multiplication is associative (mul_assoc)
2. Identity is neutral element (mul_identity)
3. Inverse is correct when it exists (inverse_correct)
4. Invertibility ↔ non-zero determinant (invertible_iff_det_nonzero)

### Quaternions

**Proven Properties:**
1. SLERP produces unit quaternions (slerp_unit)
2. SLERP interpolates endpoints correctly (slerp_endpoints)

## Physics

### Integration

**Proven Properties:**
1. Verlet integration preserves energy to O(dt²) (verlet_energy_bounded)

### Random Number Generation

**Proven Properties:**
1. Mulberry32 is deterministic (next_deterministic)
2. Period is 2³² (axiom - verified empirically)
-/
```

### 7.2 CI/CD Integration

```yaml
# .github/workflows/ci.yml (updated)

name: CI
on: [push, pull_request]

jobs:
  # Existing TypeScript/Vue tests
  frontend:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
      - run: npm ci
      - run: npm test

  # NEW: Lean4 proof verification
  lean4-proofs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - run: cd lattice-math-core && lake build
      - run: cd lattice-math-core && lake exe verify_all

  # NEW: Integration tests (Lean4 + TypeScript)
  integration:
    needs: [frontend, lean4-proofs]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - uses: actions/setup-node@v4
      - run: cd lattice-math-core && lake exe codegen
      - run: npm ci
      - run: VITE_USE_LEAN4_MATH=true npm test
```

---

## Risk Mitigation

### Technical Risks

| Risk | Mitigation |
|------|------------|
| Lean4 → JS compilation issues | Use WASM as fallback; maintain TS fallback |
| Performance regression | Benchmark before each migration; keep TS fallback |
| Proof complexity | Start with simple proofs; get help from mathlib community |
| WASM bundle size | Tree-shake; lazy-load math core |

### Schedule Risks

| Risk | Mitigation |
|------|------------|
| Proofs take longer than expected | Phases are independent; can ship partial |
| Team unfamiliar with Lean4 | Training time built in; start with simple functions |
| Integration issues | Gradual migration with feature flags |

### Fallback Plan

If Lean4 integration fails:
1. Keep all existing TypeScript code (it works!)
2. Use property-based tests (fast-check) for confidence
3. Document edge cases thoroughly
4. Add runtime assertions at boundaries

---

## Timeline Summary

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 0: Foundation | Weeks 1-4 | Lean4 project setup, CI/CD |
| 1: Easing | Weeks 5-8 | 35 verified easing functions |
| 2: Linear Interp | Weeks 9-12 | Verified lerp, vec2/vec3 lerp, color interp |
| 3: Bezier | Weeks 13-18 | Verified cubic Bezier, Newton-Raphson solver |
| 4: 3D Math | Weeks 19-24 | Verified Mat4, Quat, SLERP |
| 5: Physics | Weeks 25-32 | Verified forces, integration, RNG |
| 6: Integration | Weeks 33-40 | Full migration with feature flags |
| 7: Ongoing | Continuous | Documentation, maintenance |

**Total: 40 weeks (~10 months)**

---

## Success Criteria

### Phase Gates

Each phase must pass before proceeding:

1. **All proofs compile** - `lake build` succeeds
2. **Generated JS matches TS** - Integration tests pass at 10⁻¹⁰ precision
3. **No performance regression** - Benchmarks within 10% of TS
4. **Feature flag works** - Can enable/disable Lean4 at runtime

### Final Success Metrics

- [ ] 100% of identified math functions have Lean4 proofs
- [ ] All proofs verify without `sorry`
- [ ] Generated JS passes all existing tests
- [ ] Bundle size increase < 500KB
- [ ] No performance regression in animation playback
- [ ] Documentation complete for all proven properties

---

## Appendix A: Files to Extract

### Current TypeScript → Lean4 Mapping

| TypeScript File | Lines | Lean4 Module | Priority |
|-----------------|-------|--------------|----------|
| `services/easing.ts` | 215 | `Interpolation/Easing.lean` | P0 |
| `services/interpolation.ts` | 900 | `Interpolation/Linear.lean`, `Bezier.lean` | P0 |
| `services/math3d.ts` | 1,050 | `Geometry/Vec3.lean`, `Mat4.lean`, `Quat.lean` | P1 |
| `utils/numericSafety.ts` | 150 | `Numeric/Safety.lean` | P1 |
| `utils/colorUtils.ts` | 300 | `Color/Rgb.lean`, `Hsl.lean` | P2 |
| `services/physics/PhysicsEngine.ts` (math parts) | 400 | `Physics/Forces.lean` | P2 |
| `engine/particles/ParticleForceCalculator.ts` | 320 | `Physics/Forces.lean` | P2 |
| `services/particles/SeededRandom.ts` | 100 | `Random/Mulberry32.lean` | P1 |

### What Stays in TypeScript

- All Vue components
- All Pinia stores
- All Three.js rendering code
- All DOM manipulation
- All async/networking code
- All UI state management

---

## Appendix B: Learning Resources

### Lean4
- [Lean4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)

### Formal Verification of Floating Point
- [Flocq Library](https://flocq.gitlabpages.inria.fr/flocq/)
- [IEEE 754 in Coq/Lean](https://github.com/coq-community/coq-flocq)

### Property-Based Testing (for validation)
- [fast-check](https://github.com/dubzzz/fast-check)
- [Hypothesis](https://hypothesis.works/) (Python, for reference)

---

## Appendix C: Cost Estimate

### Development Time

| Phase | Person-Weeks | Notes |
|-------|--------------|-------|
| 0: Foundation | 4 | Setup, learning |
| 1: Easing | 4 | Simple proofs |
| 2: Linear Interp | 4 | Vector/color |
| 3: Bezier | 6 | Complex proofs |
| 4: 3D Math | 6 | Matrix algebra |
| 5: Physics | 8 | Most complex |
| 6: Integration | 8 | Testing, migration |
| **TOTAL** | **40 weeks** | 1 person |

### Parallel Work

This can be done in parallel with ongoing TypeScript development:
- **Week 1-20:** One person on Lean4, others on features
- **Week 21-40:** Integration, with full team awareness

### Alternative: Consultant

Hire a Lean4/formal verification consultant:
- ~$150-250/hr for experienced Lean4 developer
- ~200 hours for core proofs = $30,000-50,000
- Faster timeline (3-4 months vs 10 months)

---

*This plan allows you to gain the benefits of formal verification for critical math while keeping your working 175,000-line codebase intact. The key insight is that you don't need to verify everything—just the mathematical core that, if wrong, would cause subtle animation bugs.*
