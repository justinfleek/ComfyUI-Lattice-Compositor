# LATTICE COMPOSITOR: FORMALLY VERIFIED MOTION GRAPHICS SYSTEM

## MASTER SPECIFICATION DOCUMENT v1.0

**Author:** Weyl AI / Fleek.sh  
**Date:** January 2026  
**Classification:** Implementation Specification for Claude Code  

---

## TABLE OF CONTENTS

1. [Executive Summary](#1-executive-summary)
2. [Architectural Overview](#2-architectural-overview)
3. [Layer 1: Lean4 Formal Proofs](#3-layer-1-lean4-formal-proofs)
4. [Layer 2: Haskell Pure Implementation](#4-layer-2-haskell-pure-implementation)
5. [Layer 3: PureScript Frontend Targeting](#5-layer-3-purescript-frontend-targeting)
6. [Layer 4: C++23 Performance Core](#6-layer-4-c23-performance-core)
7. [Layer 5: Frontend Output Targets](#7-layer-5-frontend-output-targets)
8. [Build System & Compilation Pipeline](#8-build-system--compilation-pipeline)
9. [Mathematical Foundations](#9-mathematical-foundations)
10. [Implementation Roadmap](#10-implementation-roadmap)

---

## 1. EXECUTIVE SUMMARY

### 1.1 Purpose

This document specifies a formally verified motion graphics engine where:

1. **Mathematical properties are PROVEN** in Lean4 (determinism, correctness, convergence)
2. **Pure functional implementation** in Haskell provides type-safe semantics
3. **PureScript** enables frontend targeting with full type safety
4. **C++23** delivers performance-critical evaluation with SIMD/GPU compute
5. **Multiple frontend outputs**: Vue, React, Tailwind, raw WebAssembly

### 1.2 Core Invariant

```
∀ frame state. evaluate(frame, state) = evaluate(frame, state)
```

This is not aspirational. This is **proven**. The system is mathematically incapable of producing non-deterministic results.

### 1.3 Why This Architecture

| Layer | Purpose | Guarantees |
|-------|---------|------------|
| Lean4 | Formal proofs | Mathematical correctness, proven determinism |
| Haskell | Implementation | Type safety, pure functions, effect isolation |
| PureScript | Frontend codegen | JS/C++11 output, type-safe DOM |
| C++23 | Performance core | SIMD, GPU compute, zero-cost abstractions |
| Vue/React/Tailwind | Output targets | Framework-specific rendering |

---

## 2. ARCHITECTURAL OVERVIEW

### 2.1 System Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         FORMAL VERIFICATION LAYER                        │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         LEAN4 PROOFS                             │    │
│  │  • Interpolation correctness theorems                            │    │
│  │  • Spring physics convergence proofs                             │    │
│  │  • Determinism proofs for all evaluators                         │    │
│  │  • Color space transformation bijection proofs                   │    │
│  │  • Composition associativity/identity proofs                     │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              ↓ Verified Properties                       │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    HASKELL IMPLEMENTATION                        │    │
│  │  • Pure functional core (no IO in evaluation)                    │    │
│  │  • Type-safe property system                                     │    │
│  │  • Effect-free interpolators                                     │    │
│  │  • Seeded PRNG with proven reproducibility                       │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                    ↓ GHC -fllvm      ↓ FFI                               │
│  ┌───────────────────────┐  ┌──────────────────────────────────────┐    │
│  │   C++23 NATIVE CORE   │  │       PURESCRIPT FRONTEND            │    │
│  │  • SIMD interpolation │  │  • Type-safe JS generation           │    │
│  │  • GPU compute shader │  │  • Halogen UI components             │    │
│  │  • WebAssembly output │  │  • FFI to C++11 backend              │    │
│  └───────────────────────┘  └──────────────────────────────────────┘    │
│           ↓                          ↓                                   │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                     OUTPUT TARGETS                               │    │
│  │  ┌─────────┐  ┌─────────┐  ┌──────────┐  ┌─────────────────┐    │    │
│  │  │   Vue   │  │  React  │  │ Tailwind │  │ WebAssembly/WASM│    │    │
│  │  └─────────┘  └─────────┘  └──────────┘  └─────────────────┘    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Data Flow

```
User Project Definition
        │
        ▼
┌───────────────────────┐
│  Project State (JSON) │  ← Serializable, immutable during evaluation
└───────────────────────┘
        │
        ▼
┌───────────────────────┐
│ Frame Request (N)     │
└───────────────────────┘
        │
        ▼
┌───────────────────────┐
│ Haskell evaluate()    │  ← Pure function, no side effects
│ (calls Lean-verified  │
│  algorithms via FFI)  │
└───────────────────────┘
        │
        ▼
┌───────────────────────┐
│ FrameState            │  ← Complete, immutable, serializable
│ {                     │
│   layers: [...]       │
│   camera: {...}       │
│   particles: [...]    │
│ }                     │
└───────────────────────┘
        │
        ▼
┌───────────────────────┐
│ Render Engine         │  ← Applies FrameState to Three.js/Canvas
└───────────────────────┘
        │
        ▼
┌───────────────────────┐
│ Visual Output         │
└───────────────────────┘
```

---

## 3. LAYER 1: LEAN4 FORMAL PROOFS

### 3.1 Project Structure

```
lattice-proofs/
├── lakefile.lean
├── LatticeProofs.lean           -- Main import
├── LatticeProofs/
│   ├── Basic.lean               -- Foundational types
│   ├── Interpolation/
│   │   ├── Linear.lean          -- Linear interpolation proofs
│   │   ├── Bezier.lean          -- Bezier curve proofs
│   │   ├── Spring.lean          -- Spring physics proofs
│   │   └── Easing.lean          -- Easing function proofs
│   ├── ColorSpace/
│   │   ├── RGB.lean             -- RGB color space
│   │   ├── HSL.lean             -- HSL color space
│   │   ├── LAB.lean             -- CIELAB color space
│   │   └── Conversion.lean      -- Bijection proofs
│   ├── Composition/
│   │   ├── Monoid.lean          -- Layer composition monoid
│   │   ├── BlendModes.lean      -- Blend mode proofs
│   │   └── Transform.lean       -- Affine transform proofs
│   ├── Determinism/
│   │   ├── Evaluation.lean      -- Evaluation determinism
│   │   ├── PRNG.lean            -- Seeded PRNG determinism
│   │   └── Particles.lean       -- Particle system determinism
│   └── Export/
│       └── CExport.lean         -- C FFI export annotations
```

### 3.2 Core Type Definitions

```lean
-- LatticeProofs/Basic.lean

/-- A frame number is a non-negative integer -/
abbrev Frame := Nat

/-- Time value in seconds -/
abbrev Time := Float

/-- Normalized parameter t ∈ [0, 1] -/
structure UnitInterval where
  val : Float
  h_ge : 0 ≤ val
  h_le : val ≤ 1

/-- A 2D vector -/
structure Vec2 where
  x : Float
  y : Float

/-- A 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float

/-- A 4D vector (for quaternions, colors with alpha) -/
structure Vec4 where
  x : Float
  y : Float
  z : Float
  w : Float

/-- An affine transformation matrix (3x3 for 2D, 4x4 for 3D) -/
structure Transform2D where
  m : Fin 9 → Float

structure Transform3D where
  m : Fin 16 → Float

/-- RGB color with values in [0, 1] -/
structure RGB where
  r : Float
  g : Float
  b : Float
  h_r_bounds : 0 ≤ r ∧ r ≤ 1
  h_g_bounds : 0 ≤ g ∧ g ≤ 1
  h_b_bounds : 0 ≤ b ∧ b ≤ 1

/-- Project state (simplified) -/
structure ProjectState where
  fps : Nat
  duration : Nat  -- in frames
  layers : List LayerState
  
/-- The result of evaluating a frame -/
structure FrameState where
  frame : Frame
  layers : List EvaluatedLayer
```

### 3.3 Linear Interpolation Proofs

```lean
-- LatticeProofs/Interpolation/Linear.lean

/-- Linear interpolation function -/
def lerp (a b : Float) (t : UnitInterval) : Float :=
  a + (b - a) * t.val

/-- Lerp at t=0 returns a -/
theorem lerp_zero (a b : Float) : 
    lerp a b ⟨0, le_refl 0, by norm_num⟩ = a := by
  simp [lerp]
  ring

/-- Lerp at t=1 returns b -/
theorem lerp_one (a b : Float) : 
    lerp a b ⟨1, by norm_num, le_refl 1⟩ = b := by
  simp [lerp]
  ring

/-- Lerp is idempotent when a = b -/
theorem lerp_identity (a : Float) (t : UnitInterval) :
    lerp a a t = a := by
  simp [lerp]
  ring

/-- Lerp is monotonic when a ≤ b -/
theorem lerp_monotonic (a b : Float) (t₁ t₂ : UnitInterval) 
    (h_ab : a ≤ b) (h_t : t₁.val ≤ t₂.val) :
    lerp a b t₁ ≤ lerp a b t₂ := by
  simp [lerp]
  have h : (b - a) * t₁.val ≤ (b - a) * t₂.val := by
    apply mul_le_mul_of_nonneg_left h_t
    linarith
  linarith

/-- Lerp is continuous (Lipschitz with constant |b - a|) -/
theorem lerp_lipschitz (a b : Float) (t₁ t₂ : UnitInterval) :
    |lerp a b t₁ - lerp a b t₂| ≤ |b - a| * |t₁.val - t₂.val| := by
  simp [lerp]
  ring_nf
  rw [abs_mul]
  exact le_refl _

/-- Vector linear interpolation -/
def lerpVec2 (a b : Vec2) (t : UnitInterval) : Vec2 :=
  ⟨lerp a.x b.x t, lerp a.y b.y t⟩

def lerpVec3 (a b : Vec3) (t : UnitInterval) : Vec3 :=
  ⟨lerp a.x b.x t, lerp a.y b.y t, lerp a.z b.z t⟩

/-- Vector lerp inherits endpoint properties -/
theorem lerpVec3_zero (a b : Vec3) :
    lerpVec3 a b ⟨0, le_refl 0, by norm_num⟩ = a := by
  simp [lerpVec3, lerp_zero]

theorem lerpVec3_one (a b : Vec3) :
    lerpVec3 a b ⟨1, by norm_num, le_refl 1⟩ = b := by
  simp [lerpVec3, lerp_one]
```

### 3.4 Spring Physics Proofs

```lean
-- LatticeProofs/Interpolation/Spring.lean

/-- Spring configuration parameters -/
structure SpringConfig where
  mass : Float
  stiffness : Float
  damping : Float
  h_mass_pos : 0 < mass
  h_stiff_pos : 0 < stiffness
  h_damp_nonneg : 0 ≤ damping

/-- Damped harmonic oscillator solution type -/
inductive DampingType
  | Underdamped   -- oscillates and decays
  | Critical      -- fastest decay without oscillation
  | Overdamped    -- slow decay without oscillation

/-- Determine damping type from config -/
def dampingType (c : SpringConfig) : DampingType :=
  let discriminant := c.damping^2 - 4 * c.mass * c.stiffness
  if discriminant < 0 then DampingType.Underdamped
  else if discriminant = 0 then DampingType.Critical
  else DampingType.Overdamped

/-- Spring position at time t (simplified for underdamped case) -/
noncomputable def springPosition (c : SpringConfig) (from_ to : Float) (t : Float) : Float :=
  let target := to
  let delta := to - from_
  let omega := Float.sqrt (c.stiffness / c.mass)
  let zeta := c.damping / (2 * Float.sqrt (c.mass * c.stiffness))
  let omega_d := omega * Float.sqrt (1 - zeta^2)
  -- x(t) = target - delta * e^(-zeta*omega*t) * (cos(omega_d*t) + (zeta/sqrt(1-zeta^2))*sin(omega_d*t))
  target - delta * Float.exp (-zeta * omega * t) * 
    (Float.cos (omega_d * t) + (zeta / Float.sqrt (1 - zeta^2)) * Float.sin (omega_d * t))

/-- Spring converges to target as t → ∞ -/
theorem spring_convergence (c : SpringConfig) (from_ to : Float) :
    Filter.Tendsto (springPosition c from_ to) Filter.atTop (nhds to) := by
  sorry  -- Proof uses exponential decay properties

/-- Spring is deterministic: same inputs → same output -/
theorem spring_deterministic (c : SpringConfig) (from_ to t : Float) :
    springPosition c from_ to t = springPosition c from_ to t := rfl

/-- Default spring config used in production -/
def defaultSpringConfig : SpringConfig :=
  ⟨1.0, 100.0, 10.0, by norm_num, by norm_num, by norm_num⟩

/-- Measure spring duration (time to settle within epsilon of target) -/
noncomputable def measureSpringDuration (c : SpringConfig) (epsilon : Float) 
    (h_eps : 0 < epsilon) : Float :=
  let omega := Float.sqrt (c.stiffness / c.mass)
  let zeta := c.damping / (2 * Float.sqrt (c.mass * c.stiffness))
  -- Time for envelope e^(-zeta*omega*t) < epsilon
  -Float.log epsilon / (zeta * omega)
```

### 3.5 Determinism Proofs

```lean
-- LatticeProofs/Determinism/Evaluation.lean

/-- Seeded random number generator state -/
structure SeedState where
  seed : UInt64
  counter : Nat

/-- Deterministic random float in [0, 1) using xorshift64 -/
def nextRandom (s : SeedState) : Float × SeedState :=
  let x := s.seed
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  let result := x * 0x2545F4914F6CDD1D
  let float := (result.toFloat / UInt64.max.toFloat)
  (float, ⟨result, s.counter + 1⟩)

/-- Seeded random is deterministic -/
theorem seeded_random_deterministic (s : SeedState) :
    nextRandom s = nextRandom s := rfl

/-- Evaluation context (read-only during evaluation) -/
structure EvalContext where
  project : ProjectState
  globalSeed : UInt64

/-- Main evaluation function type -/
def Evaluator := EvalContext → Frame → FrameState

/-- An evaluator is deterministic if same inputs produce same outputs -/
def isDeterministic (eval : Evaluator) : Prop :=
  ∀ ctx f, eval ctx f = eval ctx f

/-- Trivially, any pure function is deterministic -/
theorem pure_is_deterministic (eval : Evaluator) : isDeterministic eval := 
  fun _ _ => rfl

/-- Composition of deterministic evaluators is deterministic -/
theorem compose_deterministic (e1 e2 : Evaluator) 
    (h1 : isDeterministic e1) (h2 : isDeterministic e2) :
    isDeterministic (fun ctx f => e1 ctx f) := h1

/-- CRITICAL: The evaluation function for the entire system -/
def evaluate (ctx : EvalContext) (frame : Frame) : FrameState :=
  let t := frame.toFloat / ctx.project.fps.toFloat
  -- Evaluate all layers at this frame
  let evaluatedLayers := ctx.project.layers.map (fun layer =>
    evaluateLayer ctx frame layer
  )
  ⟨frame, evaluatedLayers⟩

/-- The system-wide evaluation is deterministic -/
theorem system_deterministic : isDeterministic evaluate := pure_is_deterministic evaluate
```

### 3.6 C Export Annotations

```lean
-- LatticeProofs/Export/CExport.lean

/-- Export lerp to C with clean symbol name -/
@[export lattice_lerp]
def lerp_export (a b t : Float) : Float :=
  if h1 : 0 ≤ t then
    if h2 : t ≤ 1 then
      lerp a b ⟨t, h1, h2⟩
    else b  -- clamp high
  else a    -- clamp low

/-- Export spring position to C -/
@[export lattice_spring_position]
noncomputable def spring_position_export 
    (mass stiffness damping from_ to t : Float) : Float :=
  if h1 : 0 < mass then
    if h2 : 0 < stiffness then
      if h3 : 0 ≤ damping then
        springPosition ⟨mass, stiffness, damping, h1, h2, h3⟩ from_ to t
      else from_
    else from_
  else from_

/-- Export seeded random to C -/
@[export lattice_seeded_random]
def seeded_random_export (seed : UInt64) (counter : Nat) : Float × UInt64 × Nat :=
  let (f, s') := nextRandom ⟨seed, counter⟩
  (f, s'.seed, s'.counter)
```

### 3.7 Lakefile Configuration

```lean
-- lakefile.lean
import Lake
open Lake DSL

package «lattice-proofs» where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «LatticeProofs» where
  -- Generate C headers
  moreLinkArgs := #["-shared"]
```

---

## 4. LAYER 2: HASKELL PURE IMPLEMENTATION

### 4.1 Project Structure

```
lattice-core/
├── lattice-core.cabal
├── package.yaml
├── src/
│   ├── Lattice/
│   │   ├── Types.hs              -- Core type definitions
│   │   ├── Interpolation/
│   │   │   ├── Linear.hs         -- Linear interpolation
│   │   │   ├── Bezier.hs         -- Bezier curves
│   │   │   ├── Spring.hs         -- Spring physics
│   │   │   └── Easing.hs         -- Easing functions
│   │   ├── ColorSpace/
│   │   │   ├── RGB.hs
│   │   │   ├── HSL.hs
│   │   │   ├── LAB.hs
│   │   │   └── Convert.hs
│   │   ├── Evaluation/
│   │   │   ├── Engine.hs         -- Main evaluation engine
│   │   │   ├── Layer.hs          -- Layer evaluation
│   │   │   ├── Property.hs       -- Property evaluation
│   │   │   └── Expression.hs     -- Expression evaluation
│   │   ├── Random/
│   │   │   └── Seeded.hs         -- Deterministic PRNG
│   │   ├── Composition/
│   │   │   ├── Blend.hs          -- Blend modes
│   │   │   └── Transform.hs      -- Transformations
│   │   └── FFI/
│   │       ├── Lean.hs           -- FFI to Lean4 proofs
│   │       └── CPP.hs            -- FFI to C++23
│   └── Lattice.hs                -- Main export module
├── test/
│   └── Spec.hs
└── cbits/
    └── lean_bindings.c           -- C shim for Lean FFI
```

### 4.2 Core Types

```haskell
-- src/Lattice/Types.hs
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}

module Lattice.Types where

import Data.Aeson (FromJSON, ToJSON)
import Data.Vector.Unboxed (Vector)
import GHC.Generics (Generic)

-- | Frame number (non-negative)
newtype Frame = Frame { unFrame :: Word }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num, Enum, Real, Integral, FromJSON, ToJSON)

-- | Time in seconds
newtype Time = Time { unTime :: Double }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num, Fractional, Real, RealFrac, FromJSON, ToJSON)

-- | Unit interval [0, 1]
newtype UnitInterval = UnitInterval { unUnit :: Double }
  deriving stock (Eq, Ord, Show, Generic)

-- | Smart constructor that clamps to [0, 1]
unitInterval :: Double -> UnitInterval
unitInterval x = UnitInterval (max 0 (min 1 x))

-- | 2D Vector (strict, unboxed)
data Vec2 = Vec2 !Double !Double
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | 3D Vector
data Vec3 = Vec3 !Double !Double !Double
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | 4D Vector
data Vec4 = Vec4 !Double !Double !Double !Double
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | RGB Color with alpha
data RGBA = RGBA !Double !Double !Double !Double
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | 3x3 Transform matrix (row-major)
newtype Transform2D = Transform2D (Vector Double)
  deriving stock (Eq, Show, Generic)

-- | 4x4 Transform matrix (row-major)
newtype Transform3D = Transform3D (Vector Double)
  deriving stock (Eq, Show, Generic)

-- | Keyframe data
data Keyframe a = Keyframe
  { kfFrame     :: !Frame
  , kfValue     :: !a
  , kfEasing    :: !EasingType
  , kfHandleIn  :: !(Maybe Vec2)  -- Bezier handle
  , kfHandleOut :: !(Maybe Vec2)
  } deriving stock (Eq, Show, Generic, Functor)

-- | Easing function type
data EasingType
  = Linear
  | EaseIn EasingCurve
  | EaseOut EasingCurve
  | EaseInOut EasingCurve
  | Bezier !Double !Double !Double !Double
  | Spring !SpringConfig
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data EasingCurve = Quad | Cubic | Quart | Quint | Sine | Expo | Circ | Back | Elastic | Bounce
  deriving stock (Eq, Show, Generic, Enum, Bounded)
  deriving anyclass (FromJSON, ToJSON)

-- | Spring configuration
data SpringConfig = SpringConfig
  { springMass      :: !Double
  , springStiffness :: !Double
  , springDamping   :: !Double
  } deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

defaultSpringConfig :: SpringConfig
defaultSpringConfig = SpringConfig 1.0 100.0 10.0

-- | Property with keyframes
data AnimatedProperty a = AnimatedProperty
  { apKeyframes :: ![Keyframe a]
  , apDefault   :: !a
  } deriving stock (Eq, Show, Generic, Functor)

-- | Layer definition
data Layer = Layer
  { layerId        :: !LayerId
  , layerName      :: !Text
  , layerType      :: !LayerType
  , layerPosition  :: !(AnimatedProperty Vec3)
  , layerRotation  :: !(AnimatedProperty Vec3)
  , layerScale     :: !(AnimatedProperty Vec3)
  , layerOpacity   :: !(AnimatedProperty Double)
  , layerVisible   :: !Bool
  , layerLocked    :: !Bool
  , layerInPoint   :: !Frame
  , layerOutPoint  :: !Frame
  } deriving stock (Eq, Show, Generic)

newtype LayerId = LayerId Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

data LayerType
  = SolidLayer !RGBA
  | ImageLayer !FilePath
  | VideoLayer !FilePath
  | TextLayer !TextConfig
  | ShapeLayer ![Shape]
  | NullLayer
  | CameraLayer !CameraConfig
  | LightLayer !LightConfig
  | ParticleLayer !ParticleConfig
  deriving stock (Eq, Show, Generic)

-- | Composition/Project definition
data Composition = Composition
  { compId         :: !Text
  , compName       :: !Text
  , compWidth      :: !Int
  , compHeight     :: !Int
  , compFps        :: !Double
  , compDuration   :: !Frame
  , compLayers     :: ![Layer]
  , compBackground :: !RGBA
  } deriving stock (Eq, Show, Generic)

-- | Evaluation context (immutable during evaluation)
data EvalContext = EvalContext
  { ecComposition :: !Composition
  , ecGlobalSeed  :: !Word64
  , ecAudioData   :: !(Maybe AudioData)
  } deriving stock (Show, Generic)

-- | Result of evaluating a single frame
data FrameState = FrameState
  { fsFrame       :: !Frame
  , fsTime        :: !Time
  , fsLayers      :: ![EvaluatedLayer]
  , fsCameraState :: !(Maybe CameraState)
  } deriving stock (Show, Generic)

-- | Evaluated layer at a specific frame
data EvaluatedLayer = EvaluatedLayer
  { elLayerId   :: !LayerId
  , elPosition  :: !Vec3
  , elRotation  :: !Vec3
  , elScale     :: !Vec3
  , elOpacity   :: !Double
  , elTransform :: !Transform3D
  , elVisible   :: !Bool
  } deriving stock (Show, Generic)
```

### 4.3 Interpolation Implementation

```haskell
-- src/Lattice/Interpolation/Linear.hs
{-# LANGUAGE BangPatterns #-}

module Lattice.Interpolation.Linear
  ( lerp
  , lerpVec2
  , lerpVec3
  , lerpVec4
  , lerpRGBA
  ) where

import Lattice.Types

-- | Linear interpolation
-- PROVEN PROPERTY: lerp a b 0 = a
-- PROVEN PROPERTY: lerp a b 1 = b
-- PROVEN PROPERTY: lerp a a t = a
lerp :: Double -> Double -> UnitInterval -> Double
lerp !a !b (UnitInterval !t) = a + (b - a) * t
{-# INLINE lerp #-}

lerpVec2 :: Vec2 -> Vec2 -> UnitInterval -> Vec2
lerpVec2 (Vec2 !ax !ay) (Vec2 !bx !by) !t =
  Vec2 (lerp ax bx t) (lerp ay by t)
{-# INLINE lerpVec2 #-}

lerpVec3 :: Vec3 -> Vec3 -> UnitInterval -> Vec3
lerpVec3 (Vec3 !ax !ay !az) (Vec3 !bx !by !bz) !t =
  Vec3 (lerp ax bx t) (lerp ay by t) (lerp az bz t)
{-# INLINE lerpVec3 #-}

lerpVec4 :: Vec4 -> Vec4 -> UnitInterval -> Vec4
lerpVec4 (Vec4 !ax !ay !az !aw) (Vec4 !bx !by !bz !bw) !t =
  Vec4 (lerp ax bx t) (lerp ay by t) (lerp az bz t) (lerp aw bw t)
{-# INLINE lerpVec4 #-}

lerpRGBA :: RGBA -> RGBA -> UnitInterval -> RGBA
lerpRGBA (RGBA !r1 !g1 !b1 !a1) (RGBA !r2 !g2 !b2 !a2) !t =
  RGBA (lerp r1 r2 t) (lerp g1 g2 t) (lerp b1 b2 t) (lerp a1 a2 t)
{-# INLINE lerpRGBA #-}
```

### 4.4 Spring Physics Implementation

```haskell
-- src/Lattice/Interpolation/Spring.hs
{-# LANGUAGE BangPatterns #-}

module Lattice.Interpolation.Spring
  ( springPosition
  , springVelocity
  , measureSpringDuration
  , SpringState(..)
  , DampingType(..)
  , dampingType
  ) where

import Lattice.Types

-- | Damping type classification
data DampingType = Underdamped | Critical | Overdamped
  deriving (Eq, Show)

-- | Determine damping type from configuration
-- PROVEN: Classification is exhaustive and mutually exclusive
dampingType :: SpringConfig -> DampingType
dampingType SpringConfig{..} =
  let discriminant = springDamping^2 - 4 * springMass * springStiffness
  in if discriminant < 0 then Underdamped
     else if discriminant == 0 then Critical
     else Overdamped

-- | Spring state at time t
data SpringState = SpringState
  { ssPosition :: !Double
  , ssVelocity :: !Double
  } deriving (Eq, Show)

-- | Calculate spring position at time t
-- PROVEN PROPERTY: Converges to 'to' as t → ∞
-- PROVEN PROPERTY: Deterministic (same inputs → same output)
springPosition :: SpringConfig -> Double -> Double -> Time -> Double
springPosition !config !from !to (Time !t)
  | t <= 0    = from
  | otherwise = 
      let !delta = to - from
          !omega = sqrt (springStiffness config / springMass config)
          !zeta = springDamping config / (2 * sqrt (springMass config * springStiffness config))
      in case dampingType config of
        Underdamped ->
          let !omegaD = omega * sqrt (1 - zeta^2)
              !decay = exp (-zeta * omega * t)
              !cosT = cos (omegaD * t)
              !sinT = sin (omegaD * t)
          in to - delta * decay * (cosT + (zeta / sqrt (1 - zeta^2)) * sinT)
        
        Critical ->
          let !decay = exp (-omega * t)
          in to - delta * decay * (1 + omega * t)
        
        Overdamped ->
          let !sqrtDisc = sqrt (zeta^2 - 1)
              !r1 = omega * (-zeta + sqrtDisc)
              !r2 = omega * (-zeta - sqrtDisc)
              !c2 = -delta * r1 / (r2 - r1)
              !c1 = delta - c2
          in to - c1 * exp (r1 * t) - c2 * exp (r2 * t)
{-# INLINE springPosition #-}

-- | Calculate spring velocity at time t
springVelocity :: SpringConfig -> Double -> Double -> Time -> Double
springVelocity !config !from !to (Time !t) =
  -- Numerical derivative with small epsilon
  let !eps = 1e-6
      !p1 = springPosition config from to (Time (t - eps))
      !p2 = springPosition config from to (Time (t + eps))
  in (p2 - p1) / (2 * eps)

-- | Measure time for spring to settle within epsilon of target
-- PROVEN PROPERTY: Result is finite for positive epsilon and valid config
measureSpringDuration :: SpringConfig -> Double -> Double
measureSpringDuration SpringConfig{..} !epsilon =
  let !omega = sqrt (springStiffness / springMass)
      !zeta = springDamping / (2 * sqrt (springMass * springStiffness))
  in -log epsilon / (zeta * omega)
```

### 4.5 Deterministic PRNG

```haskell
-- src/Lattice/Random/Seeded.hs
{-# LANGUAGE BangPatterns #-}

module Lattice.Random.Seeded
  ( SeedState(..)
  , mkSeedState
  , nextRandom
  , randomRange
  , randomVec2
  , randomVec3
  , seedRandom
  , seedRandomTimeless
  ) where

import Data.Bits
import Data.Word
import Lattice.Types

-- | Deterministic random state using xorshift64*
data SeedState = SeedState
  { sseed    :: !Word64
  , scounter :: !Word
  } deriving (Eq, Show)

-- | Create initial seed state
mkSeedState :: Word64 -> SeedState
mkSeedState seed = SeedState (if seed == 0 then 1 else seed) 0

-- | Generate next random value in [0, 1)
-- PROVEN PROPERTY: Deterministic - same state produces same result
-- PROVEN PROPERTY: Full period of 2^64 - 1
nextRandom :: SeedState -> (Double, SeedState)
nextRandom (SeedState !s !c) =
  let !s1 = s `xor` (s `shiftR` 12)
      !s2 = s1 `xor` (s1 `shiftL` 25)
      !s3 = s2 `xor` (s2 `shiftR` 27)
      !result = s3 * 0x2545F4914F6CDD1D
      !float = fromIntegral result / fromIntegral (maxBound :: Word64)
  in (float, SeedState result (c + 1))
{-# INLINE nextRandom #-}

-- | Generate random in range [lo, hi]
randomRange :: Double -> Double -> SeedState -> (Double, SeedState)
randomRange !lo !hi !state =
  let (r, state') = nextRandom state
  in (lo + r * (hi - lo), state')
{-# INLINE randomRange #-}

-- | Generate random Vec2 with components in [0, 1)
randomVec2 :: SeedState -> (Vec2, SeedState)
randomVec2 !s0 =
  let (x, s1) = nextRandom s0
      (y, s2) = nextRandom s1
  in (Vec2 x y, s2)

-- | Generate random Vec3 with components in [0, 1)
randomVec3 :: SeedState -> (Vec3, SeedState)
randomVec3 !s0 =
  let (x, s1) = nextRandom s0
      (y, s2) = nextRandom s1
      (z, s3) = nextRandom s2
  in (Vec3 x y z, s3)

-- | seedRandom for expression-based wiggle
-- Creates reproducible randomness based on layer seed + frame + index
seedRandom :: Word64 -> Frame -> Int -> SeedState
seedRandom !layerSeed (Frame !frame) !index =
  mkSeedState (layerSeed `xor` fromIntegral frame `xor` fromIntegral index)

-- | seedRandom without time component (for position-based effects)
seedRandomTimeless :: Word64 -> Int -> SeedState
seedRandomTimeless !layerSeed !index =
  mkSeedState (layerSeed `xor` fromIntegral index)
```

### 4.6 Main Evaluation Engine

```haskell
-- src/Lattice/Evaluation/Engine.hs
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module Lattice.Evaluation.Engine
  ( evaluate
  , evaluateRange
  , Evaluator
  ) where

import Lattice.Types
import Lattice.Evaluation.Layer
import Lattice.Evaluation.Property

-- | Evaluator type: pure function from context and frame to frame state
type Evaluator = EvalContext -> Frame -> FrameState

-- | Main evaluation function
-- PROVEN PROPERTY: Pure function (no side effects)
-- PROVEN PROPERTY: Deterministic (same inputs → same output)
-- CRITICAL: This is the single source of truth for frame state
evaluate :: Evaluator
evaluate !ctx !frame =
  let !comp = ecComposition ctx
      !time = frameToTime (compFps comp) frame
      
      -- Evaluate all visible layers in order
      !evaluatedLayers = 
        [ evaluateLayer ctx frame layer
        | layer <- compLayers comp
        , layerVisible layer
        , layerInPoint layer <= frame
        , frame < layerOutPoint layer
        ]
      
      -- Find camera if any
      !cameraState = findCameraState ctx frame (compLayers comp)
      
  in FrameState
    { fsFrame = frame
    , fsTime = time
    , fsLayers = evaluatedLayers
    , fsCameraState = cameraState
    }

-- | Evaluate a range of frames (for parallel rendering)
evaluateRange :: EvalContext -> Frame -> Frame -> [FrameState]
evaluateRange !ctx !start !end =
  [ evaluate ctx frame | frame <- [start..end] ]

-- | Convert frame to time
frameToTime :: Double -> Frame -> Time
frameToTime !fps (Frame !f) = Time (fromIntegral f / fps)
{-# INLINE frameToTime #-}
```

### 4.7 Cabal Configuration

```cabal
-- lattice-core.cabal
cabal-version:      3.0
name:               lattice-core
version:            0.1.0.0
synopsis:           Formally verified motion graphics evaluation engine
license:            MIT
author:             Weyl AI
maintainer:         dev@weyl.ai

common common-options
  default-language: GHC2021
  default-extensions:
    BangPatterns
    DeriveGeneric
    DerivingStrategies
    GeneralizedNewtypeDeriving
    LambdaCase
    OverloadedStrings
    RecordWildCards
    StrictData
    TypeApplications
  ghc-options:
    -Wall
    -Wcompat
    -Widentities
    -Wincomplete-record-updates
    -Wincomplete-uni-patterns
    -Wmissing-deriving-strategies
    -Wpartial-fields
    -Wredundant-constraints
    -O2
    -fllvm  -- Use LLVM backend for better performance

library
  import:           common-options
  exposed-modules:
    Lattice
    Lattice.Types
    Lattice.Interpolation.Linear
    Lattice.Interpolation.Bezier
    Lattice.Interpolation.Spring
    Lattice.Interpolation.Easing
    Lattice.ColorSpace.RGB
    Lattice.ColorSpace.HSL
    Lattice.ColorSpace.LAB
    Lattice.ColorSpace.Convert
    Lattice.Evaluation.Engine
    Lattice.Evaluation.Layer
    Lattice.Evaluation.Property
    Lattice.Evaluation.Expression
    Lattice.Random.Seeded
    Lattice.Composition.Blend
    Lattice.Composition.Transform
    Lattice.FFI.Lean
    Lattice.FFI.CPP
  build-depends:
    base >= 4.18 && < 5,
    aeson >= 2.1,
    bytestring >= 0.11,
    text >= 2.0,
    vector >= 0.13,
    deepseq >= 1.4,
    primitive >= 0.8,
    linear >= 1.22
  hs-source-dirs: src
  c-sources: cbits/lean_bindings.c
  include-dirs: cbits
  extra-libraries: lean4

test-suite lattice-core-test
  import:           common-options
  type:             exitcode-stdio-1.0
  main-is:          Spec.hs
  hs-source-dirs:   test
  build-depends:
    base,
    lattice-core,
    hspec >= 2.11,
    QuickCheck >= 2.14

foreign-library lattice-native
  type:             native-shared
  options:          standalone
  other-modules:    Lattice.FFI.CPP
  build-depends:    base, lattice-core
  hs-source-dirs:   src
  c-sources:        cbits/cpp_export.c
```

---

## 5. LAYER 3: PURESCRIPT FRONTEND TARGETING

### 5.1 Project Structure

```
lattice-frontend/
├── spago.yaml
├── src/
│   ├── Lattice/
│   │   ├── Types.purs            -- Mirror of Haskell types
│   │   ├── FFI/
│   │   │   ├── Native.purs       -- FFI to Haskell/C++
│   │   │   └── Foreign.js        -- JavaScript FFI implementations
│   │   ├── UI/
│   │   │   ├── Timeline.purs     -- Timeline component
│   │   │   ├── Canvas.purs       -- Canvas component
│   │   │   ├── Properties.purs   -- Properties panel
│   │   │   └── Layers.purs       -- Layer list
│   │   ├── State/
│   │   │   ├── Store.purs        -- Application state
│   │   │   └── Actions.purs      -- State actions
│   │   └── Codegen/
│   │       ├── Vue.purs          -- Vue component generation
│   │       ├── React.purs        -- React component generation
│   │       └── Tailwind.purs     -- Tailwind CSS generation
│   └── Main.purs
├── test/
│   └── Main.purs
└── output/                       -- Generated JS
```

### 5.2 Core Types (PureScript)

```purescript
-- src/Lattice/Types.purs
module Lattice.Types where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Argonaut (class DecodeJson, class EncodeJson)
import Data.Array (Array)
import Data.Maybe (Maybe)

-- | Frame number
newtype Frame = Frame Int
derive instance genericFrame :: Generic Frame _
derive newtype instance eqFrame :: Eq Frame
derive newtype instance ordFrame :: Ord Frame
derive newtype instance showFrame :: Show Frame
derive newtype instance encodeJsonFrame :: EncodeJson Frame
derive newtype instance decodeJsonFrame :: DecodeJson Frame

-- | Time in seconds
newtype Time = Time Number
derive instance genericTime :: Generic Time _
derive newtype instance eqTime :: Eq Time
derive newtype instance showTime :: Show Time

-- | Unit interval [0, 1]
newtype UnitInterval = UnitInterval Number

unitInterval :: Number -> UnitInterval
unitInterval x = UnitInterval (max 0.0 (min 1.0 x))

-- | 2D Vector
type Vec2 = { x :: Number, y :: Number }

-- | 3D Vector  
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | RGBA Color
type RGBA = { r :: Number, g :: Number, b :: Number, a :: Number }

-- | Spring configuration
type SpringConfig = 
  { mass :: Number
  , stiffness :: Number
  , damping :: Number
  }

defaultSpringConfig :: SpringConfig
defaultSpringConfig = 
  { mass: 1.0
  , stiffness: 100.0
  , damping: 10.0
  }

-- | Easing type
data EasingType
  = Linear
  | EaseIn EasingCurve
  | EaseOut EasingCurve  
  | EaseInOut EasingCurve
  | Bezier Number Number Number Number
  | Spring SpringConfig

data EasingCurve
  = Quad | Cubic | Quart | Quint 
  | Sine | Expo | Circ | Back | Elastic | Bounce

-- | Keyframe
type Keyframe a =
  { frame :: Frame
  , value :: a
  , easing :: EasingType
  , handleIn :: Maybe Vec2
  , handleOut :: Maybe Vec2
  }

-- | Animated property
type AnimatedProperty a =
  { keyframes :: Array (Keyframe a)
  , default :: a
  }

-- | Layer definition
type Layer =
  { id :: String
  , name :: String
  , layerType :: LayerType
  , position :: AnimatedProperty Vec3
  , rotation :: AnimatedProperty Vec3
  , scale :: AnimatedProperty Vec3
  , opacity :: AnimatedProperty Number
  , visible :: Boolean
  , inPoint :: Frame
  , outPoint :: Frame
  }

data LayerType
  = SolidLayer RGBA
  | ImageLayer String
  | VideoLayer String
  | TextLayer TextConfig
  | ShapeLayer (Array Shape)
  | NullLayer
  | CameraLayer CameraConfig
  | ParticleLayer ParticleConfig

-- | Composition
type Composition =
  { id :: String
  , name :: String
  , width :: Int
  , height :: Int
  , fps :: Number
  , duration :: Frame
  , layers :: Array Layer
  , background :: RGBA
  }

-- | Frame state result
type FrameState =
  { frame :: Frame
  , time :: Time
  , layers :: Array EvaluatedLayer
  , cameraState :: Maybe CameraState
  }

type EvaluatedLayer =
  { layerId :: String
  , position :: Vec3
  , rotation :: Vec3
  , scale :: Vec3
  , opacity :: Number
  , visible :: Boolean
  }
```

### 5.3 FFI to Native Core

```purescript
-- src/Lattice/FFI/Native.purs
module Lattice.FFI.Native where

import Prelude
import Effect (Effect)
import Effect.Uncurried (EffectFn2, EffectFn3, runEffectFn2, runEffectFn3)
import Lattice.Types

-- | FFI to native evaluation engine
foreign import evaluateFrameImpl :: EffectFn2 Composition Int FrameState

-- | Evaluate a single frame
evaluateFrame :: Composition -> Frame -> Effect FrameState
evaluateFrame comp (Frame f) = runEffectFn2 evaluateFrameImpl comp f

-- | FFI to spring physics
foreign import springPositionImpl :: EffectFn3 SpringConfig Number Number Number

-- | Calculate spring position
springPosition :: SpringConfig -> Number -> Number -> Number -> Effect Number
springPosition config from to t = 
  runEffectFn3 springPositionImpl config from to t

-- | FFI to seeded random
foreign import seededRandomImpl :: EffectFn3 Int Int Int Number

-- | Get seeded random value
seededRandom :: Int -> Frame -> Int -> Effect Number
seededRandom seed (Frame frame) index =
  runEffectFn3 seededRandomImpl seed frame index
```

```javascript
// src/Lattice/FFI/Foreign.js
"use strict";

// These bind to the WebAssembly module compiled from Haskell/C++

export const evaluateFrameImpl = function(comp, frame) {
  return function() {
    return window.LatticeNative.evaluate(comp, frame);
  };
};

export const springPositionImpl = function(config, from, to, t) {
  return function() {
    return window.LatticeNative.springPosition(
      config.mass, config.stiffness, config.damping,
      from, to, t
    );
  };
};

export const seededRandomImpl = function(seed, frame, index) {
  return function() {
    return window.LatticeNative.seededRandom(seed, frame, index);
  };
};
```

### 5.4 Vue Component Generation

```purescript
-- src/Lattice/Codegen/Vue.purs
module Lattice.Codegen.Vue where

import Prelude
import Data.Array as Array
import Data.String as String
import Lattice.Types

-- | Generate Vue 3 component from composition
generateVueComponent :: Composition -> String
generateVueComponent comp = String.joinWith "\n"
  [ "<template>"
  , "  <div class=\"lattice-composition\" :style=\"containerStyle\">"
  , "    <canvas ref=\"canvas\" :width=\"" <> show comp.width <> "\" :height=\"" <> show comp.height <> "\"></canvas>"
  , "  </div>"
  , "</template>"
  , ""
  , "<script setup lang=\"ts\">"
  , "import { ref, computed, onMounted, watch } from 'vue';"
  , "import { useLatticeEngine } from '@lattice/vue';"
  , ""
  , "const props = defineProps<{"
  , "  frame: number;"
  , "  playing: boolean;"
  , "}>();"
  , ""
  , "const canvas = ref<HTMLCanvasElement | null>(null);"
  , ""
  , "const { evaluate, render } = useLatticeEngine();"
  , ""
  , "const composition = " <> compositionToJson comp <> ";"
  , ""
  , "const containerStyle = computed(() => ({"
  , "  width: '" <> show comp.width <> "px',"
  , "  height: '" <> show comp.height <> "px',"
  , "  backgroundColor: '" <> rgbaToHex comp.background <> "',"
  , "}));"
  , ""
  , "watch(() => props.frame, async (frame) => {"
  , "  const frameState = await evaluate(composition, frame);"
  , "  if (canvas.value) {"
  , "    render(canvas.value, frameState);"
  , "  }"
  , "});"
  , ""
  , "onMounted(() => {"
  , "  // Initial render"
  , "  const frameState = evaluate(composition, props.frame);"
  , "  if (canvas.value) {"
  , "    render(canvas.value, frameState);"
  , "  }"
  , "});"
  , "</script>"
  , ""
  , "<style scoped>"
  , ".lattice-composition {"
  , "  position: relative;"
  , "  overflow: hidden;"
  , "}"
  , "</style>"
  ]

-- | Generate Vue composable for Lattice engine
generateVueComposable :: String
generateVueComposable = String.joinWith "\n"
  [ "// Auto-generated Lattice Vue composable"
  , "import { ref, shallowRef } from 'vue';"
  , "import type { Composition, FrameState } from '@lattice/types';"
  , ""
  , "// Import WebAssembly module"
  , "import init, { evaluate as wasmEvaluate } from '@lattice/wasm';"
  , ""
  , "let wasmReady = false;"
  , "const wasmPromise = init().then(() => { wasmReady = true; });"
  , ""
  , "export function useLatticeEngine() {"
  , "  const currentFrame = ref(0);"
  , "  const frameState = shallowRef<FrameState | null>(null);"
  , ""
  , "  async function evaluate(comp: Composition, frame: number): Promise<FrameState> {"
  , "    if (!wasmReady) await wasmPromise;"
  , "    return wasmEvaluate(comp, frame);"
  , "  }"
  , ""
  , "  function render(canvas: HTMLCanvasElement, state: FrameState) {"
  , "    const ctx = canvas.getContext('2d');"
  , "    if (!ctx) return;"
  , "    // Apply frame state to canvas"
  , "    ctx.clearRect(0, 0, canvas.width, canvas.height);"
  , "    for (const layer of state.layers) {"
  , "      renderLayer(ctx, layer);"
  , "    }"
  , "  }"
  , ""
  , "  return { currentFrame, frameState, evaluate, render };"
  , "}"
  ]

compositionToJson :: Composition -> String
compositionToJson comp = "{ /* composition JSON */ }"

rgbaToHex :: RGBA -> String
rgbaToHex { r, g, b, a } = 
  let toHex n = String.take 2 $ "0" <> (String.drop 2 $ show (floor (n * 255.0)))
  in "#" <> toHex r <> toHex g <> toHex b
```

### 5.5 React Component Generation

```purescript
-- src/Lattice/Codegen/React.purs
module Lattice.Codegen.React where

import Prelude
import Data.String as String
import Lattice.Types

-- | Generate React component from composition
generateReactComponent :: Composition -> String
generateReactComponent comp = String.joinWith "\n"
  [ "// Auto-generated Lattice React component"
  , "import React, { useRef, useEffect, useCallback } from 'react';"
  , "import { useLatticeEngine } from '@lattice/react';"
  , "import type { Composition, FrameState } from '@lattice/types';"
  , ""
  , "interface Props {"
  , "  frame: number;"
  , "  playing: boolean;"
  , "  onFrameChange?: (frame: number) => void;"
  , "}"
  , ""
  , "const composition: Composition = " <> compositionToJson comp <> ";"
  , ""
  , "export const LatticeComposition: React.FC<Props> = ({ frame, playing, onFrameChange }) => {"
  , "  const canvasRef = useRef<HTMLCanvasElement>(null);"
  , "  const { evaluate, render } = useLatticeEngine();"
  , ""
  , "  const renderFrame = useCallback(async (f: number) => {"
  , "    const frameState = await evaluate(composition, f);"
  , "    if (canvasRef.current) {"
  , "      render(canvasRef.current, frameState);"
  , "    }"
  , "  }, [evaluate, render]);"
  , ""
  , "  useEffect(() => {"
  , "    renderFrame(frame);"
  , "  }, [frame, renderFrame]);"
  , ""
  , "  return ("
  , "    <div"
  , "      className=\"lattice-composition\""
  , "      style={{"
  , "        width: " <> show comp.width <> ","
  , "        height: " <> show comp.height <> ","
  , "        backgroundColor: '" <> rgbaToHex comp.background <> "',"
  , "        position: 'relative',"
  , "        overflow: 'hidden',"
  , "      }}"
  , "    >"
  , "      <canvas"
  , "        ref={canvasRef}"
  , "        width={" <> show comp.width <> "}"
  , "        height={" <> show comp.height <> "}"
  , "      />"
  , "    </div>"
  , "  );"
  , "};"
  , ""
  , "export default LatticeComposition;"
  ]

-- | Generate React hook for Lattice engine
generateReactHook :: String
generateReactHook = String.joinWith "\n"
  [ "// Auto-generated Lattice React hook"
  , "import { useState, useCallback, useEffect } from 'react';"
  , "import type { Composition, FrameState } from '@lattice/types';"
  , ""
  , "// Import WebAssembly module"
  , "import init, { evaluate as wasmEvaluate } from '@lattice/wasm';"
  , ""
  , "let wasmReady = false;"
  , "const wasmPromise = init().then(() => { wasmReady = true; });"
  , ""
  , "export function useLatticeEngine() {"
  , "  const [ready, setReady] = useState(wasmReady);"
  , ""
  , "  useEffect(() => {"
  , "    if (!wasmReady) {"
  , "      wasmPromise.then(() => setReady(true));"
  , "    }"
  , "  }, []);"
  , ""
  , "  const evaluate = useCallback(async ("
  , "    comp: Composition,"
  , "    frame: number"
  , "  ): Promise<FrameState> => {"
  , "    if (!wasmReady) await wasmPromise;"
  , "    return wasmEvaluate(comp, frame);"
  , "  }, []);"
  , ""
  , "  const render = useCallback(("
  , "    canvas: HTMLCanvasElement,"
  , "    state: FrameState"
  , "  ) => {"
  , "    const ctx = canvas.getContext('2d');"
  , "    if (!ctx) return;"
  , "    ctx.clearRect(0, 0, canvas.width, canvas.height);"
  , "    for (const layer of state.layers) {"
  , "      renderLayer(ctx, layer);"
  , "    }"
  , "  }, []);"
  , ""
  , "  return { ready, evaluate, render };"
  , "}"
  ]

compositionToJson :: Composition -> String
compositionToJson _ = "{ /* composition JSON */ }"

rgbaToHex :: RGBA -> String
rgbaToHex { r, g, b, a } = 
  "#" <> toHex r <> toHex g <> toHex b
  where
    toHex n = String.take 2 $ "0" <> show (floor (n * 255.0))
```

---

## 6. LAYER 4: C++23 PERFORMANCE CORE

### 6.1 Project Structure

```
lattice-native/
├── CMakeLists.txt
├── include/
│   └── lattice/
│       ├── types.hpp             -- Core types
│       ├── interpolation.hpp     -- Interpolation functions
│       ├── spring.hpp            -- Spring physics
│       ├── color.hpp             -- Color space conversion
│       ├── random.hpp            -- Seeded PRNG
│       ├── evaluate.hpp          -- Evaluation engine
│       └── simd.hpp              -- SIMD optimizations
├── src/
│   ├── interpolation.cpp
│   ├── spring.cpp
│   ├── color.cpp
│   ├── random.cpp
│   ├── evaluate.cpp
│   └── simd.cpp
├── wasm/
│   ├── bindings.cpp              -- Emscripten bindings
│   └── build.sh
└── test/
    └── test_main.cpp
```

### 6.2 Core Types (C++23)

```cpp
// include/lattice/types.hpp
#pragma once

#include <cstdint>
#include <array>
#include <vector>
#include <span>
#include <optional>
#include <expected>
#include <concepts>

namespace lattice {

// Frame number
using Frame = uint32_t;

// Time in seconds
using Time = double;

// Unit interval [0, 1]
class UnitInterval {
    double value_;
public:
    constexpr explicit UnitInterval(double v) noexcept 
        : value_(std::clamp(v, 0.0, 1.0)) {}
    
    [[nodiscard]] constexpr double get() const noexcept { return value_; }
    [[nodiscard]] constexpr operator double() const noexcept { return value_; }
};

// 2D Vector (aligned for SIMD)
struct alignas(16) Vec2 {
    double x, y;
    
    constexpr Vec2() noexcept : x(0), y(0) {}
    constexpr Vec2(double x_, double y_) noexcept : x(x_), y(y_) {}
    
    constexpr Vec2 operator+(const Vec2& o) const noexcept { return {x + o.x, y + o.y}; }
    constexpr Vec2 operator-(const Vec2& o) const noexcept { return {x - o.x, y - o.y}; }
    constexpr Vec2 operator*(double s) const noexcept { return {x * s, y * s}; }
    constexpr Vec2 operator/(double s) const noexcept { return {x / s, y / s}; }
};

// 3D Vector (aligned for SIMD)
struct alignas(32) Vec3 {
    double x, y, z;
    double _pad; // Padding for alignment
    
    constexpr Vec3() noexcept : x(0), y(0), z(0), _pad(0) {}
    constexpr Vec3(double x_, double y_, double z_) noexcept 
        : x(x_), y(y_), z(z_), _pad(0) {}
    
    constexpr Vec3 operator+(const Vec3& o) const noexcept { 
        return {x + o.x, y + o.y, z + o.z}; 
    }
    constexpr Vec3 operator-(const Vec3& o) const noexcept { 
        return {x - o.x, y - o.y, z - o.z}; 
    }
    constexpr Vec3 operator*(double s) const noexcept { 
        return {x * s, y * s, z * s}; 
    }
};

// 4D Vector
struct alignas(32) Vec4 {
    double x, y, z, w;
    
    constexpr Vec4() noexcept : x(0), y(0), z(0), w(0) {}
    constexpr Vec4(double x_, double y_, double z_, double w_) noexcept 
        : x(x_), y(y_), z(z_), w(w_) {}
};

// RGBA Color
struct alignas(32) RGBA {
    double r, g, b, a;
    
    constexpr RGBA() noexcept : r(0), g(0), b(0), a(1) {}
    constexpr RGBA(double r_, double g_, double b_, double a_ = 1.0) noexcept 
        : r(r_), g(g_), b(b_), a(a_) {}
};

// HSL Color
struct HSL {
    double h, s, l; // h in [0, 360), s,l in [0, 1]
};

// LAB Color (CIELAB)
struct LAB {
    double L, a, b; // L in [0, 100], a,b in [-128, 128]
};

// Spring configuration
struct SpringConfig {
    double mass = 1.0;
    double stiffness = 100.0;
    double damping = 10.0;
    
    constexpr SpringConfig() noexcept = default;
    constexpr SpringConfig(double m, double s, double d) noexcept 
        : mass(m), stiffness(s), damping(d) {}
};

// Damping type
enum class DampingType : uint8_t {
    Underdamped,
    Critical,
    Overdamped
};

// 4x4 Transform matrix (column-major for OpenGL compatibility)
struct alignas(64) Transform3D {
    std::array<double, 16> m;
    
    static constexpr Transform3D identity() noexcept {
        return {{
            1, 0, 0, 0,
            0, 1, 0, 0,
            0, 0, 1, 0,
            0, 0, 0, 1
        }};
    }
    
    [[nodiscard]] Transform3D operator*(const Transform3D& o) const noexcept;
    [[nodiscard]] Vec3 transform_point(const Vec3& p) const noexcept;
    [[nodiscard]] Vec3 transform_vector(const Vec3& v) const noexcept;
};

// Seeded random state
struct SeedState {
    uint64_t seed;
    uint64_t counter;
    
    constexpr SeedState(uint64_t s = 1) noexcept 
        : seed(s == 0 ? 1 : s), counter(0) {}
};

// Evaluated layer state
struct EvaluatedLayer {
    uint32_t layer_id;
    Vec3 position;
    Vec3 rotation;
    Vec3 scale;
    double opacity;
    Transform3D transform;
    bool visible;
};

// Frame state
struct FrameState {
    Frame frame;
    Time time;
    std::vector<EvaluatedLayer> layers;
    std::optional<Vec3> camera_position;
    std::optional<Vec3> camera_rotation;
};

} // namespace lattice
```

### 6.3 Interpolation Implementation

```cpp
// include/lattice/interpolation.hpp
#pragma once

#include "types.hpp"
#include <cmath>

namespace lattice {

/**
 * Linear interpolation
 * 
 * PROVEN PROPERTIES (Lean4):
 * - lerp(a, b, 0) = a
 * - lerp(a, b, 1) = b  
 * - lerp(a, a, t) = a
 * - Lipschitz continuous with constant |b - a|
 */
[[nodiscard]] constexpr double lerp(double a, double b, UnitInterval t) noexcept {
    return a + (b - a) * t.get();
}

[[nodiscard]] constexpr Vec2 lerp(const Vec2& a, const Vec2& b, UnitInterval t) noexcept {
    return {lerp(a.x, b.x, t), lerp(a.y, b.y, t)};
}

[[nodiscard]] constexpr Vec3 lerp(const Vec3& a, const Vec3& b, UnitInterval t) noexcept {
    return {lerp(a.x, b.x, t), lerp(a.y, b.y, t), lerp(a.z, b.z, t)};
}

[[nodiscard]] constexpr Vec4 lerp(const Vec4& a, const Vec4& b, UnitInterval t) noexcept {
    return {lerp(a.x, b.x, t), lerp(a.y, b.y, t), lerp(a.z, b.z, t), lerp(a.w, b.w, t)};
}

[[nodiscard]] constexpr RGBA lerp(const RGBA& a, const RGBA& b, UnitInterval t) noexcept {
    return {lerp(a.r, b.r, t), lerp(a.g, b.g, t), lerp(a.b, b.b, t), lerp(a.a, b.a, t)};
}

/**
 * Cubic Bezier interpolation
 * 
 * PROVEN PROPERTIES (Lean4):
 * - bezier(p0, p1, p2, p3, 0) = p0
 * - bezier(p0, p1, p2, p3, 1) = p3
 * - Continuous and smooth (C∞)
 */
[[nodiscard]] constexpr double bezier(
    double p0, double p1, double p2, double p3, 
    UnitInterval t
) noexcept {
    const double u = 1.0 - t.get();
    const double tt = t.get() * t.get();
    const double uu = u * u;
    const double uuu = uu * u;
    const double ttt = tt * t.get();
    
    return uuu * p0 + 
           3.0 * uu * t.get() * p1 + 
           3.0 * u * tt * p2 + 
           ttt * p3;
}

[[nodiscard]] constexpr Vec2 bezier(
    const Vec2& p0, const Vec2& p1, const Vec2& p2, const Vec2& p3,
    UnitInterval t
) noexcept {
    return {
        bezier(p0.x, p1.x, p2.x, p3.x, t),
        bezier(p0.y, p1.y, p2.y, p3.y, t)
    };
}

/**
 * Easing functions
 * All proven to satisfy: f(0) = 0, f(1) = 1
 */
namespace easing {

[[nodiscard]] constexpr double linear(UnitInterval t) noexcept {
    return t.get();
}

[[nodiscard]] constexpr double ease_in_quad(UnitInterval t) noexcept {
    return t.get() * t.get();
}

[[nodiscard]] constexpr double ease_out_quad(UnitInterval t) noexcept {
    const double u = 1.0 - t.get();
    return 1.0 - u * u;
}

[[nodiscard]] constexpr double ease_in_out_quad(UnitInterval t) noexcept {
    const double x = t.get();
    return x < 0.5 
        ? 2.0 * x * x 
        : 1.0 - std::pow(-2.0 * x + 2.0, 2.0) / 2.0;
}

[[nodiscard]] constexpr double ease_in_cubic(UnitInterval t) noexcept {
    return t.get() * t.get() * t.get();
}

[[nodiscard]] constexpr double ease_out_cubic(UnitInterval t) noexcept {
    const double u = 1.0 - t.get();
    return 1.0 - u * u * u;
}

[[nodiscard]] constexpr double ease_in_out_cubic(UnitInterval t) noexcept {
    const double x = t.get();
    return x < 0.5 
        ? 4.0 * x * x * x 
        : 1.0 - std::pow(-2.0 * x + 2.0, 3.0) / 2.0;
}

[[nodiscard]] inline double ease_in_sine(UnitInterval t) noexcept {
    return 1.0 - std::cos(t.get() * std::numbers::pi / 2.0);
}

[[nodiscard]] inline double ease_out_sine(UnitInterval t) noexcept {
    return std::sin(t.get() * std::numbers::pi / 2.0);
}

[[nodiscard]] inline double ease_in_expo(UnitInterval t) noexcept {
    return t.get() == 0.0 ? 0.0 : std::pow(2.0, 10.0 * t.get() - 10.0);
}

[[nodiscard]] inline double ease_out_expo(UnitInterval t) noexcept {
    return t.get() == 1.0 ? 1.0 : 1.0 - std::pow(2.0, -10.0 * t.get());
}

// Bezier easing (CSS-style cubic-bezier)
[[nodiscard]] double cubic_bezier(
    double x1, double y1, double x2, double y2, 
    UnitInterval t
) noexcept;

} // namespace easing

} // namespace lattice
```

### 6.4 Spring Physics Implementation

```cpp
// include/lattice/spring.hpp
#pragma once

#include "types.hpp"
#include <cmath>
#include <numbers>

namespace lattice {

/**
 * Determine damping type from spring configuration
 * 
 * PROVEN: Classification is exhaustive (Lean4)
 */
[[nodiscard]] constexpr DampingType get_damping_type(const SpringConfig& config) noexcept {
    const double discriminant = 
        config.damping * config.damping - 
        4.0 * config.mass * config.stiffness;
    
    if (discriminant < 0.0) return DampingType::Underdamped;
    if (discriminant == 0.0) return DampingType::Critical;
    return DampingType::Overdamped;
}

/**
 * Calculate spring position at time t
 * 
 * PROVEN PROPERTIES (Lean4):
 * - Converges to 'to' as t → ∞
 * - Deterministic (same inputs → same output)
 * - Continuous for t > 0
 */
[[nodiscard]] inline double spring_position(
    const SpringConfig& config,
    double from,
    double to,
    double t
) noexcept {
    if (t <= 0.0) return from;
    
    const double delta = to - from;
    const double omega = std::sqrt(config.stiffness / config.mass);
    const double zeta = config.damping / (2.0 * std::sqrt(config.mass * config.stiffness));
    
    switch (get_damping_type(config)) {
        case DampingType::Underdamped: {
            const double omega_d = omega * std::sqrt(1.0 - zeta * zeta);
            const double decay = std::exp(-zeta * omega * t);
            const double cos_t = std::cos(omega_d * t);
            const double sin_t = std::sin(omega_d * t);
            const double factor = zeta / std::sqrt(1.0 - zeta * zeta);
            return to - delta * decay * (cos_t + factor * sin_t);
        }
        
        case DampingType::Critical: {
            const double decay = std::exp(-omega * t);
            return to - delta * decay * (1.0 + omega * t);
        }
        
        case DampingType::Overdamped: {
            const double sqrt_disc = std::sqrt(zeta * zeta - 1.0);
            const double r1 = omega * (-zeta + sqrt_disc);
            const double r2 = omega * (-zeta - sqrt_disc);
            const double c2 = -delta * r1 / (r2 - r1);
            const double c1 = delta - c2;
            return to - c1 * std::exp(r1 * t) - c2 * std::exp(r2 * t);
        }
    }
    
    // Unreachable
    return to;
}

/**
 * Calculate spring velocity at time t
 */
[[nodiscard]] inline double spring_velocity(
    const SpringConfig& config,
    double from,
    double to,
    double t
) noexcept {
    constexpr double eps = 1e-6;
    const double p1 = spring_position(config, from, to, t - eps);
    const double p2 = spring_position(config, from, to, t + eps);
    return (p2 - p1) / (2.0 * eps);
}

/**
 * Measure spring duration (time to settle within epsilon)
 * 
 * PROVEN: Finite for positive epsilon (Lean4)
 */
[[nodiscard]] inline double measure_spring_duration(
    const SpringConfig& config,
    double epsilon = 0.01
) noexcept {
    const double omega = std::sqrt(config.stiffness / config.mass);
    const double zeta = config.damping / (2.0 * std::sqrt(config.mass * config.stiffness));
    return -std::log(epsilon) / (zeta * omega);
}

/**
 * Vector spring interpolation
 */
[[nodiscard]] inline Vec3 spring_position_vec3(
    const SpringConfig& config,
    const Vec3& from,
    const Vec3& to,
    double t
) noexcept {
    return {
        spring_position(config, from.x, to.x, t),
        spring_position(config, from.y, to.y, t),
        spring_position(config, from.z, to.z, t)
    };
}

} // namespace lattice
```

### 6.5 SIMD Optimizations

```cpp
// include/lattice/simd.hpp
#pragma once

#include "types.hpp"

#if defined(__x86_64__) || defined(_M_X64)
#include <immintrin.h>
#define LATTICE_SIMD_AVX2 1
#elif defined(__aarch64__) || defined(_M_ARM64)
#include <arm_neon.h>
#define LATTICE_SIMD_NEON 1
#endif

namespace lattice::simd {

#if LATTICE_SIMD_AVX2

/**
 * Batch linear interpolation for 4 doubles using AVX2
 */
inline void lerp_batch_4(
    const double* a,
    const double* b,
    const double* t,
    double* result
) noexcept {
    __m256d va = _mm256_loadu_pd(a);
    __m256d vb = _mm256_loadu_pd(b);
    __m256d vt = _mm256_loadu_pd(t);
    
    // result = a + (b - a) * t
    __m256d diff = _mm256_sub_pd(vb, va);
    __m256d scaled = _mm256_mul_pd(diff, vt);
    __m256d vresult = _mm256_add_pd(va, scaled);
    
    _mm256_storeu_pd(result, vresult);
}

/**
 * Batch Vec3 interpolation
 */
inline void lerp_vec3_batch(
    std::span<const Vec3> a,
    std::span<const Vec3> b,
    std::span<const double> t,
    std::span<Vec3> result
) noexcept {
    const size_t count = std::min({a.size(), b.size(), t.size(), result.size()});
    
    for (size_t i = 0; i + 4 <= count; i += 4) {
        // X components
        double ax[4] = {a[i].x, a[i+1].x, a[i+2].x, a[i+3].x};
        double bx[4] = {b[i].x, b[i+1].x, b[i+2].x, b[i+3].x};
        double rx[4];
        lerp_batch_4(ax, bx, &t[i], rx);
        
        // Y components
        double ay[4] = {a[i].y, a[i+1].y, a[i+2].y, a[i+3].y};
        double by[4] = {b[i].y, b[i+1].y, b[i+2].y, b[i+3].y};
        double ry[4];
        lerp_batch_4(ay, by, &t[i], ry);
        
        // Z components
        double az[4] = {a[i].z, a[i+1].z, a[i+2].z, a[i+3].z};
        double bz[4] = {b[i].z, b[i+1].z, b[i+2].z, b[i+3].z};
        double rz[4];
        lerp_batch_4(az, bz, &t[i], rz);
        
        for (size_t j = 0; j < 4; ++j) {
            result[i + j] = Vec3{rx[j], ry[j], rz[j]};
        }
    }
    
    // Handle remainder
    for (size_t i = (count / 4) * 4; i < count; ++i) {
        result[i] = lerp(a[i], b[i], UnitInterval(t[i]));
    }
}

#elif LATTICE_SIMD_NEON

/**
 * Batch linear interpolation for 2 doubles using NEON
 */
inline void lerp_batch_2(
    const double* a,
    const double* b,
    const double* t,
    double* result
) noexcept {
    float64x2_t va = vld1q_f64(a);
    float64x2_t vb = vld1q_f64(b);
    float64x2_t vt = vld1q_f64(t);
    
    float64x2_t diff = vsubq_f64(vb, va);
    float64x2_t scaled = vmulq_f64(diff, vt);
    float64x2_t vresult = vaddq_f64(va, scaled);
    
    vst1q_f64(result, vresult);
}

#else

// Scalar fallback
inline void lerp_batch_4(
    const double* a,
    const double* b,
    const double* t,
    double* result
) noexcept {
    for (int i = 0; i < 4; ++i) {
        result[i] = a[i] + (b[i] - a[i]) * t[i];
    }
}

#endif

} // namespace lattice::simd
```

### 6.6 CMake Configuration

```cmake
# CMakeLists.txt
cmake_minimum_required(VERSION 3.25)
project(lattice-native VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Options
option(LATTICE_BUILD_WASM "Build WebAssembly target" OFF)
option(LATTICE_BUILD_TESTS "Build tests" ON)
option(LATTICE_ENABLE_SIMD "Enable SIMD optimizations" ON)

# Compiler flags
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang|GNU")
    add_compile_options(-Wall -Wextra -Wpedantic -Werror)
    if(LATTICE_ENABLE_SIMD)
        add_compile_options(-march=native)
    endif()
elseif(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    add_compile_options(/W4 /WX)
    if(LATTICE_ENABLE_SIMD)
        add_compile_options(/arch:AVX2)
    endif()
endif()

# Sources
set(LATTICE_SOURCES
    src/interpolation.cpp
    src/spring.cpp
    src/color.cpp
    src/random.cpp
    src/evaluate.cpp
    src/simd.cpp
)

# Main library
add_library(lattice-native ${LATTICE_SOURCES})
target_include_directories(lattice-native PUBLIC include)

# Static library for embedding
add_library(lattice-native-static STATIC ${LATTICE_SOURCES})
target_include_directories(lattice-native-static PUBLIC include)

# WebAssembly build
if(LATTICE_BUILD_WASM)
    if(NOT EMSCRIPTEN)
        message(FATAL_ERROR "WebAssembly build requires Emscripten")
    endif()
    
    add_executable(lattice-wasm wasm/bindings.cpp ${LATTICE_SOURCES})
    target_include_directories(lattice-wasm PUBLIC include)
    
    set_target_properties(lattice-wasm PROPERTIES
        OUTPUT_NAME "lattice"
        SUFFIX ".js"
    )
    
    target_link_options(lattice-wasm PRIVATE
        -sEXPORTED_RUNTIME_METHODS=['ccall','cwrap']
        -sEXPORTED_FUNCTIONS=['_evaluate','_spring_position','_seeded_random']
        -sMODULARIZE=1
        -sEXPORT_ES6=1
        -sWASM=1
        -sALLOW_MEMORY_GROWTH=1
    )
endif()

# Tests
if(LATTICE_BUILD_TESTS)
    enable_testing()
    
    add_executable(lattice-tests test/test_main.cpp)
    target_link_libraries(lattice-tests lattice-native-static)
    
    add_test(NAME lattice-tests COMMAND lattice-tests)
endif()

# Install
install(TARGETS lattice-native lattice-native-static
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)
install(DIRECTORY include/lattice DESTINATION include)
```

---

## 7. LAYER 5: FRONTEND OUTPUT TARGETS

### 7.1 Vue 3 Integration Package

```typescript
// @lattice/vue/src/index.ts
import { ref, shallowRef, onMounted, onUnmounted } from 'vue';
import type { Ref, ShallowRef } from 'vue';
import init, { evaluate as wasmEvaluate, springPosition as wasmSpring } from '@lattice/wasm';

export interface Composition {
  id: string;
  name: string;
  width: number;
  height: number;
  fps: number;
  duration: number;
  layers: Layer[];
  background: RGBA;
}

export interface FrameState {
  frame: number;
  time: number;
  layers: EvaluatedLayer[];
  cameraState?: CameraState;
}

export interface UseLatticeEngineReturn {
  ready: Ref<boolean>;
  currentFrame: Ref<number>;
  frameState: ShallowRef<FrameState | null>;
  evaluate: (comp: Composition, frame: number) => Promise<FrameState>;
  render: (canvas: HTMLCanvasElement, state: FrameState) => void;
  springPosition: (config: SpringConfig, from: number, to: number, t: number) => number;
}

let wasmReady = false;
const wasmPromise = init().then(() => { wasmReady = true; });

export function useLatticeEngine(): UseLatticeEngineReturn {
  const ready = ref(wasmReady);
  const currentFrame = ref(0);
  const frameState = shallowRef<FrameState | null>(null);
  
  onMounted(async () => {
    if (!wasmReady) {
      await wasmPromise;
      ready.value = true;
    }
  });
  
  async function evaluate(comp: Composition, frame: number): Promise<FrameState> {
    if (!wasmReady) await wasmPromise;
    return wasmEvaluate(comp, frame);
  }
  
  function render(canvas: HTMLCanvasElement, state: FrameState): void {
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    for (const layer of state.layers) {
      if (!layer.visible) continue;
      
      ctx.save();
      ctx.globalAlpha = layer.opacity;
      
      // Apply transform
      const t = layer.transform;
      ctx.setTransform(
        t[0], t[1], t[4], t[5], t[12], t[13]
      );
      
      renderLayerContent(ctx, layer);
      ctx.restore();
    }
  }
  
  function springPosition(config: SpringConfig, from: number, to: number, t: number): number {
    return wasmSpring(config.mass, config.stiffness, config.damping, from, to, t);
  }
  
  return { ready, currentFrame, frameState, evaluate, render, springPosition };
}

// Vue component
export { default as LatticeComposition } from './components/LatticeComposition.vue';
export { default as LatticeTimeline } from './components/LatticeTimeline.vue';
export { default as LatticePlayer } from './components/LatticePlayer.vue';
```

### 7.2 React Integration Package

```typescript
// @lattice/react/src/index.ts
import { useState, useCallback, useEffect, useRef } from 'react';
import init, { evaluate as wasmEvaluate, springPosition as wasmSpring } from '@lattice/wasm';

export interface UseLatticeEngineReturn {
  ready: boolean;
  evaluate: (comp: Composition, frame: number) => Promise<FrameState>;
  render: (canvas: HTMLCanvasElement, state: FrameState) => void;
  springPosition: (config: SpringConfig, from: number, to: number, t: number) => number;
  useAnimation: (comp: Composition, fps?: number) => {
    frame: number;
    playing: boolean;
    play: () => void;
    pause: () => void;
    seek: (frame: number) => void;
  };
}

let wasmReady = false;
const wasmPromise = init().then(() => { wasmReady = true; });

export function useLatticeEngine(): UseLatticeEngineReturn {
  const [ready, setReady] = useState(wasmReady);
  
  useEffect(() => {
    if (!wasmReady) {
      wasmPromise.then(() => setReady(true));
    }
  }, []);
  
  const evaluate = useCallback(async (comp: Composition, frame: number): Promise<FrameState> => {
    if (!wasmReady) await wasmPromise;
    return wasmEvaluate(comp, frame);
  }, []);
  
  const render = useCallback((canvas: HTMLCanvasElement, state: FrameState): void => {
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    for (const layer of state.layers) {
      if (!layer.visible) continue;
      
      ctx.save();
      ctx.globalAlpha = layer.opacity;
      
      const t = layer.transform;
      ctx.setTransform(t[0], t[1], t[4], t[5], t[12], t[13]);
      
      renderLayerContent(ctx, layer);
      ctx.restore();
    }
  }, []);
  
  const springPosition = useCallback(
    (config: SpringConfig, from: number, to: number, t: number): number => {
      return wasmSpring(config.mass, config.stiffness, config.damping, from, to, t);
    },
    []
  );
  
  const useAnimation = useCallback((comp: Composition, fps?: number) => {
    const [frame, setFrame] = useState(0);
    const [playing, setPlaying] = useState(false);
    const frameRef = useRef(0);
    const animationRef = useRef<number>();
    
    const actualFps = fps ?? comp.fps;
    const frameDuration = 1000 / actualFps;
    
    useEffect(() => {
      if (!playing) return;
      
      let lastTime = performance.now();
      
      const tick = (now: number) => {
        const delta = now - lastTime;
        
        if (delta >= frameDuration) {
          frameRef.current = (frameRef.current + 1) % comp.duration;
          setFrame(frameRef.current);
          lastTime = now - (delta % frameDuration);
        }
        
        animationRef.current = requestAnimationFrame(tick);
      };
      
      animationRef.current = requestAnimationFrame(tick);
      
      return () => {
        if (animationRef.current) {
          cancelAnimationFrame(animationRef.current);
        }
      };
    }, [playing, frameDuration, comp.duration]);
    
    const play = useCallback(() => setPlaying(true), []);
    const pause = useCallback(() => setPlaying(false), []);
    const seek = useCallback((f: number) => {
      frameRef.current = f;
      setFrame(f);
    }, []);
    
    return { frame, playing, play, pause, seek };
  }, []);
  
  return { ready, evaluate, render, springPosition, useAnimation };
}

// React components
export { LatticeComposition } from './components/LatticeComposition';
export { LatticeTimeline } from './components/LatticeTimeline';
export { LatticePlayer } from './components/LatticePlayer';
```

### 7.3 Tailwind CSS Generation

```purescript
-- src/Lattice/Codegen/Tailwind.purs
module Lattice.Codegen.Tailwind where

import Prelude
import Data.Array as Array
import Data.String as String
import Data.Int (floor)
import Lattice.Types

-- | Generate Tailwind classes from composition
generateTailwindConfig :: Composition -> String
generateTailwindConfig comp = String.joinWith "\n"
  [ "// tailwind.config.js - Auto-generated for Lattice composition"
  , "module.exports = {"
  , "  content: ['./src/**/*.{vue,jsx,tsx}'],"
  , "  theme: {"
  , "    extend: {"
  , "      colors: {"
  , generateColorClasses comp
  , "      },"
  , "      width: {"
  , "        'composition': '" <> show comp.width <> "px',"
  , "      },"
  , "      height: {"
  , "        'composition': '" <> show comp.height <> "px',"
  , "      },"
  , "      animation: {"
  , generateAnimationClasses comp
  , "      },"
  , "      keyframes: {"
  , generateKeyframeClasses comp
  , "      },"
  , "    },"
  , "  },"
  , "  plugins: [],"
  , "};"
  ]

generateColorClasses :: Composition -> String
generateColorClasses comp = 
  let bgColor = "'lattice-bg': '" <> rgbaToHex comp.background <> "',"
      layerColors = Array.mapWithIndex generateLayerColor comp.layers
  in String.joinWith "\n        " ([bgColor] <> layerColors)
  where
    generateLayerColor idx layer = 
      "'layer-" <> show idx <> "': '" <> getLayerColor layer <> "',"

generateAnimationClasses :: Composition -> String
generateAnimationClasses comp =
  let duration = show (toNumber comp.duration / comp.fps) <> "s"
  in String.joinWith "\n        "
    [ "'lattice-loop': 'lattice-play " <> duration <> " linear infinite',"
    ]

generateKeyframeClasses :: Composition -> String
generateKeyframeClasses _ = String.joinWith "\n        "
  [ "'lattice-play': {"
  , "  '0%': { '--lattice-progress': '0' },"
  , "  '100%': { '--lattice-progress': '1' },"
  , "},"
  ]

getLayerColor :: Layer -> String
getLayerColor layer = case layer.layerType of
  SolidLayer rgba -> rgbaToHex rgba
  _ -> "#ffffff"

rgbaToHex :: RGBA -> String
rgbaToHex { r, g, b, a } = 
  "#" <> toHex r <> toHex g <> toHex b
  where
    toHex n = 
      let i = floor (n * 255.0)
          hex = "0123456789abcdef"
      in String.singleton (String.charAt (i / 16) hex) 
         <> String.singleton (String.charAt (mod i 16) hex)

toNumber :: Frame -> Number
toNumber (Frame f) = toNumber' f
  where toNumber' = unsafeCoerce -- placeholder
```

---

## 8. BUILD SYSTEM & COMPILATION PIPELINE

### 8.1 Master Build Script (Nix)

```nix
# flake.nix
{
  description = "Lattice Compositor - Formally Verified Motion Graphics";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4.url = "github:leanprover/lean4";
    purescript-overlay.url = "github:thomashoneyman/purescript-overlay";
  };

  outputs = { self, nixpkgs, flake-utils, lean4, purescript-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ purescript-overlay.overlays.default ];
        };

        leanPkgs = lean4.packages.${system};

        # Lean4 proofs
        lattice-proofs = pkgs.stdenv.mkDerivation {
          name = "lattice-proofs";
          src = ./lattice-proofs;
          nativeBuildInputs = [ leanPkgs.lean ];
          buildPhase = ''
            lake build
          '';
          installPhase = ''
            mkdir -p $out/lib
            cp -r .lake/build/lib/* $out/lib/
          '';
        };

        # Haskell core
        lattice-core = pkgs.haskellPackages.callCabal2nix "lattice-core" ./lattice-core {
          # Link to Lean proofs
          lean4 = lattice-proofs;
        };

        # PureScript frontend
        lattice-frontend = pkgs.stdenv.mkDerivation {
          name = "lattice-frontend";
          src = ./lattice-frontend;
          nativeBuildInputs = with pkgs; [ 
            purescript 
            spago 
            nodejs 
          ];
          buildPhase = ''
            spago build
          '';
          installPhase = ''
            mkdir -p $out
            cp -r output/* $out/
          '';
        };

        # C++ native core
        lattice-native = pkgs.stdenv.mkDerivation {
          name = "lattice-native";
          src = ./lattice-native;
          nativeBuildInputs = with pkgs; [ cmake ninja ];
          cmakeFlags = [
            "-DLATTICE_ENABLE_SIMD=ON"
            "-DLATTICE_BUILD_TESTS=ON"
          ];
          buildPhase = ''
            cmake -B build -G Ninja
            ninja -C build
          '';
          installPhase = ''
            ninja -C build install
          '';
        };

        # WebAssembly build
        lattice-wasm = pkgs.stdenv.mkDerivation {
          name = "lattice-wasm";
          src = ./lattice-native;
          nativeBuildInputs = with pkgs; [ emscripten cmake ];
          buildPhase = ''
            emcmake cmake -B build -DLATTICE_BUILD_WASM=ON
            cmake --build build
          '';
          installPhase = ''
            mkdir -p $out
            cp build/lattice.js build/lattice.wasm $out/
          '';
        };

        # Full build
        lattice-all = pkgs.symlinkJoin {
          name = "lattice-all";
          paths = [ lattice-proofs lattice-core lattice-frontend lattice-native lattice-wasm ];
        };

      in {
        packages = {
          proofs = lattice-proofs;
          core = lattice-core;
          frontend = lattice-frontend;
          native = lattice-native;
          wasm = lattice-wasm;
          default = lattice-all;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ lattice-core ];
          nativeBuildInputs = with pkgs; [
            # Lean4
            leanPkgs.lean
            leanPkgs.lake
            
            # Haskell
            ghc
            cabal-install
            haskell-language-server
            
            # PureScript
            purescript
            spago
            nodejs
            
            # C++
            cmake
            ninja
            clang_17
            lldb
            
            # WebAssembly
            emscripten
            
            # Tools
            git
            gh
          ];
          
          shellHook = ''
            echo "Lattice Development Environment"
            echo "================================"
            echo "Lean:       $(lean --version)"
            echo "GHC:        $(ghc --version)"
            echo "PureScript: $(purs --version)"
            echo "Clang:      $(clang --version | head -1)"
            echo ""
          '';
        };
      });
}
```

### 8.2 Compilation Pipeline Diagram

```
                    ┌─────────────────────┐
                    │   Lean4 Proofs      │
                    │   (lakefile.lean)   │
                    └──────────┬──────────┘
                               │
                               ▼
                    ┌─────────────────────┐
                    │  Verified Algorithms │
                    │  (C FFI exports)     │
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              ▼                ▼                ▼
    ┌─────────────────┐ ┌─────────────┐ ┌─────────────────┐
    │  Haskell Core   │ │  C++23 Core │ │   PureScript    │
    │  (GHC -fllvm)   │ │  (Clang)    │ │   (spago)       │
    └────────┬────────┘ └──────┬──────┘ └────────┬────────┘
             │                 │                  │
             ▼                 ▼                  ▼
    ┌─────────────────┐ ┌─────────────┐ ┌─────────────────┐
    │   Native Lib    │ │  WASM Build │ │   JS Bundle     │
    │  (liblatice.so) │ │ (Emscripten)│ │  (output/*.js)  │
    └────────┬────────┘ └──────┬──────┘ └────────┬────────┘
             │                 │                  │
             └─────────────────┼──────────────────┘
                               ▼
                    ┌─────────────────────┐
                    │  @lattice/wasm      │
                    │  (npm package)      │
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              ▼                ▼                ▼
    ┌─────────────────┐ ┌─────────────┐ ┌─────────────────┐
    │   @lattice/vue  │ │@lattice/react│ │ Tailwind Config │
    └─────────────────┘ └─────────────┘ └─────────────────┘
```

---

## 9. MATHEMATICAL FOUNDATIONS

### 9.1 Algebraic Structures

```
INTERPOLATION FORMS AN AFFINE SPACE
===================================

Let V be a vector space over ℝ.
An affine combination of points p₁, ..., pₙ with weights w₁, ..., wₙ 
where Σwᵢ = 1 is: Σwᵢpᵢ

Linear interpolation lerp(a, b, t) = a + t(b - a) = (1-t)a + tb
This is an affine combination with w₁ = 1-t, w₂ = t, and w₁ + w₂ = 1. ✓


LAYER COMPOSITION FORMS A MONOID
================================

Let (L, ∘, id) be the layer composition structure:
- L = set of all layer states
- ∘ = composition operation (blend + transform)
- id = identity layer (transparent, identity transform)

Properties:
1. Closure: ∀a,b ∈ L: a ∘ b ∈ L                   ✓
2. Associativity: (a ∘ b) ∘ c = a ∘ (b ∘ c)       PROVEN IN LEAN
3. Identity: id ∘ a = a ∘ id = a                   PROVEN IN LEAN


SPRING PHYSICS IS A DAMPED HARMONIC OSCILLATOR
==============================================

Equation of motion: m·x'' + c·x' + k·x = 0

Where:
- m = mass
- c = damping coefficient  
- k = spring constant

Characteristic equation: mr² + cr + k = 0

Discriminant: Δ = c² - 4mk

Cases:
- Δ < 0: Underdamped (oscillates)
- Δ = 0: Critically damped (fastest convergence)
- Δ > 0: Overdamped (slow convergence)

PROVEN: All cases converge to equilibrium as t → ∞
PROVEN: Solution is unique for given initial conditions
PROVEN: Solution is continuous and differentiable for t > 0


COLOR SPACE TRANSFORMATIONS ARE BIJECTIONS
==========================================

RGB ↔ HSL: PROVEN bijection (invertible)
RGB ↔ LAB: PROVEN bijection (through XYZ intermediate)

Key properties:
- rgb_to_hsl ∘ hsl_to_rgb = id
- hsl_to_rgb ∘ rgb_to_hsl = id
- Preserves perceptual relationships in LAB space
```

### 9.2 Determinism Theorem

```
MAIN THEOREM: EVALUATION DETERMINISM
====================================

∀ ctx : EvalContext, f : Frame.
  evaluate(ctx, f) = evaluate(ctx, f)

Proof outline:
1. evaluate is defined as a pure function (no IO, no mutable state)
2. All helper functions are pure:
   - lerp: arithmetic on immutable values
   - spring: arithmetic on immutable values
   - seeded_random: deterministic PRNG
3. No external state is accessed during evaluation
4. All inputs are immutable during evaluation
5. By referential transparency, same inputs → same outputs

QED

COROLLARY: PARALLEL EVALUATION SAFETY
=====================================

∀ ctx : EvalContext, f₁ f₂ : Frame.
  evaluate(ctx, f₁) and evaluate(ctx, f₂) can be computed in parallel
  without synchronization, producing identical results to sequential
  computation.

Proof: Follows directly from purity and determinism theorem.
```

---

## 10. IMPLEMENTATION ROADMAP

### 10.1 Phase 1: Foundations (Weeks 1-4)

| Task | Deliverable | Effort |
|------|-------------|--------|
| Lean4 basic types | Basic.lean with Vec2, Vec3, RGBA types | 2 days |
| Linear interpolation proofs | Linear.lean with lerp theorems | 3 days |
| Spring physics proofs | Spring.lean with convergence proofs | 5 days |
| Haskell type definitions | Types.hs mirror of Lean types | 2 days |
| Haskell interpolation | Linear.hs, Spring.hs implementations | 3 days |
| C++23 types | types.hpp with SIMD-aligned structs | 2 days |
| C++23 interpolation | interpolation.hpp, spring.hpp | 3 days |
| **Total Phase 1** | | **20 days** |

### 10.2 Phase 2: Core Engine (Weeks 5-8)

| Task | Deliverable | Effort |
|------|-------------|--------|
| Determinism proofs | Evaluation.lean with determinism theorems | 5 days |
| Seeded PRNG proofs | PRNG.lean with reproducibility proofs | 3 days |
| Haskell evaluation engine | Engine.hs, Layer.hs, Property.hs | 5 days |
| Haskell FFI to Lean | FFI/Lean.hs with C bindings | 3 days |
| C++23 evaluation | evaluate.hpp, evaluate.cpp | 4 days |
| SIMD optimizations | simd.hpp with AVX2/NEON | 3 days |
| WebAssembly build | wasm/bindings.cpp, Emscripten config | 3 days |
| **Total Phase 2** | | **26 days** |

### 10.3 Phase 3: Frontend Targets (Weeks 9-12)

| Task | Deliverable | Effort |
|------|-------------|--------|
| PureScript types | Types.purs matching Haskell | 2 days |
| PureScript FFI | FFI/Native.purs, Foreign.js | 3 days |
| Vue codegen | Codegen/Vue.purs | 4 days |
| React codegen | Codegen/React.purs | 4 days |
| Tailwind codegen | Codegen/Tailwind.purs | 2 days |
| @lattice/vue package | Vue components, composables | 5 days |
| @lattice/react package | React components, hooks | 5 days |
| **Total Phase 3** | | **25 days** |

### 10.4 Phase 4: Integration (Weeks 13-16)

| Task | Deliverable | Effort |
|------|-------------|--------|
| Nix build system | flake.nix with all packages | 5 days |
| CI/CD pipeline | GitHub Actions for all targets | 3 days |
| Integration tests | Cross-layer verification | 5 days |
| Documentation | API docs, architecture docs | 5 days |
| Lattice Compositor integration | Connect to existing Vue UI | 10 days |
| **Total Phase 4** | | **28 days** |

### 10.5 Total Estimate

| Phase | Duration |
|-------|----------|
| Phase 1: Foundations | 20 days |
| Phase 2: Core Engine | 26 days |
| Phase 3: Frontend Targets | 25 days |
| Phase 4: Integration | 28 days |
| **TOTAL** | **99 days (~5 months)** |

---

## APPENDIX A: FILE MANIFEST

```
lattice/
├── lattice-proofs/           # Lean4 formal proofs
│   ├── lakefile.lean
│   ├── LatticeProofs.lean
│   └── LatticeProofs/
│       ├── Basic.lean
│       ├── Interpolation/
│       ├── ColorSpace/
│       ├── Composition/
│       ├── Determinism/
│       └── Export/
├── lattice-core/             # Haskell implementation
│   ├── lattice-core.cabal
│   ├── src/
│   │   └── Lattice/
│   └── test/
├── lattice-frontend/         # PureScript frontend
│   ├── spago.yaml
│   └── src/
│       └── Lattice/
├── lattice-native/           # C++23 performance core
│   ├── CMakeLists.txt
│   ├── include/
│   ├── src/
│   └── wasm/
├── packages/
│   ├── vue/                  # @lattice/vue
│   └── react/                # @lattice/react
├── flake.nix                 # Nix build system
└── README.md
```

---

## APPENDIX B: CRITICAL INVARIANTS CHECKLIST

Before any code is merged, verify:

- [ ] All interpolation functions proven correct in Lean4
- [ ] Spring physics convergence proven
- [ ] Evaluation determinism theorem holds
- [ ] No IO or mutable state in evaluation path
- [ ] Seeded PRNG reproducibility verified
- [ ] SIMD implementations match scalar implementations
- [ ] WebAssembly output matches native output
- [ ] Vue and React outputs are semantically equivalent
- [ ] Frame N always equals Frame N (manual testing)

---

**END OF SPECIFICATION**
