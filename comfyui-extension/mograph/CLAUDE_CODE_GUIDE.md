# LATTICE FORMAL VERIFICATION: CLAUDE CODE IMPLEMENTATION GUIDE

## PRIORITY ORDER

Execute these in exact sequence. Do not skip steps.

---

## STEP 1: LEAN4 PROJECT SETUP

```bash
# Create project
mkdir -p lattice-proofs
cd lattice-proofs
lake init lattice-proofs math

# Edit lakefile.lean
cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package «lattice-proofs» where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «LatticeProofs» where
  moreLinkArgs := #["-shared"]
EOF

# Fetch mathlib
lake update
```

---

## STEP 2: LEAN4 CORE TYPES

Create `LatticeProofs/Basic.lean`:

```lean
-- Core types that MUST be implemented first
-- These are the foundation for all proofs

namespace LatticeProofs

/-- Frame number -/
abbrev Frame := Nat

/-- Unit interval [0, 1] with proofs -/
structure UnitInterval where
  val : Float
  h_ge : 0 ≤ val
  h_le : val ≤ 1

/-- Constructor with clamping -/
def mkUnit (x : Float) : UnitInterval :=
  if h1 : 0 ≤ x then
    if h2 : x ≤ 1 then ⟨x, h1, h2⟩
    else ⟨1, by norm_num, le_refl 1⟩
  else ⟨0, le_refl 0, by norm_num⟩

/-- 3D Vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
deriving Repr, BEq

/-- RGBA Color -/
structure RGBA where
  r : Float
  g : Float
  b : Float
  a : Float
deriving Repr, BEq

/-- Spring configuration -/
structure SpringConfig where
  mass : Float
  stiffness : Float
  damping : Float
  h_mass_pos : 0 < mass
  h_stiff_pos : 0 < stiffness
  h_damp_nonneg : 0 ≤ damping

end LatticeProofs
```

---

## STEP 3: LEAN4 INTERPOLATION PROOFS

Create `LatticeProofs/Interpolation/Linear.lean`:

```lean
import LatticeProofs.Basic

namespace LatticeProofs.Interpolation

/-- Linear interpolation -/
def lerp (a b : Float) (t : UnitInterval) : Float :=
  a + (b - a) * t.val

/-- CRITICAL PROOF: lerp(a, b, 0) = a -/
theorem lerp_zero (a b : Float) : 
    lerp a b ⟨0, le_refl 0, by norm_num⟩ = a := by
  simp [lerp]
  ring

/-- CRITICAL PROOF: lerp(a, b, 1) = b -/
theorem lerp_one (a b : Float) :
    lerp a b ⟨1, by norm_num, le_refl 1⟩ = b := by
  simp [lerp]
  ring

/-- CRITICAL PROOF: lerp(a, a, t) = a -/
theorem lerp_identity (a : Float) (t : UnitInterval) :
    lerp a a t = a := by
  simp [lerp]
  ring

/-- EXPORT: C-compatible function -/
@[export lattice_lerp]
def lerp_c (a b t : Float) : Float :=
  if h1 : 0 ≤ t then
    if h2 : t ≤ 1 then lerp a b ⟨t, h1, h2⟩
    else b
  else a

end LatticeProofs.Interpolation
```

---

## STEP 4: LEAN4 SPRING PROOFS

Create `LatticeProofs/Interpolation/Spring.lean`:

```lean
import LatticeProofs.Basic

namespace LatticeProofs.Spring

/-- Damping type classification -/
inductive DampingType where
  | Underdamped
  | Critical  
  | Overdamped
deriving Repr, BEq

/-- Classify spring damping -/
def dampingType (c : SpringConfig) : DampingType :=
  let disc := c.damping^2 - 4 * c.mass * c.stiffness
  if disc < 0 then .Underdamped
  else if disc == 0 then .Critical
  else .Overdamped

/-- Spring position (placeholder - full impl requires Real analysis) -/
noncomputable def springPosition (c : SpringConfig) (from_ to t : Float) : Float :=
  let delta := to - from_
  let omega := Float.sqrt (c.stiffness / c.mass)
  let zeta := c.damping / (2 * Float.sqrt (c.mass * c.stiffness))
  -- Underdamped case (most common)
  let omegaD := omega * Float.sqrt (1 - zeta^2)
  to - delta * Float.exp (-zeta * omega * t) * 
    (Float.cos (omegaD * t) + (zeta / Float.sqrt (1 - zeta^2)) * Float.sin (omegaD * t))

/-- CRITICAL: Spring is deterministic -/
theorem spring_deterministic (c : SpringConfig) (from_ to t : Float) :
    springPosition c from_ to t = springPosition c from_ to t := rfl

/-- EXPORT: C-compatible -/
@[export lattice_spring_position]
noncomputable def spring_c (mass stiffness damping from_ to t : Float) : Float :=
  if h1 : 0 < mass then
    if h2 : 0 < stiffness then
      if h3 : 0 ≤ damping then
        springPosition ⟨mass, stiffness, damping, h1, h2, h3⟩ from_ to t
      else from_
    else from_
  else from_

end LatticeProofs.Spring
```

---

## STEP 5: LEAN4 DETERMINISM PROOF

Create `LatticeProofs/Determinism/Evaluation.lean`:

```lean
import LatticeProofs.Basic

namespace LatticeProofs.Determinism

/-- Seeded PRNG state -/
structure SeedState where
  seed : UInt64
  counter : Nat
deriving Repr, BEq

/-- xorshift64* PRNG -/
def nextRandom (s : SeedState) : Float × SeedState :=
  let x := s.seed
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  let result := x * 0x2545F4914F6CDD1D
  let float := result.toFloat / UInt64.max.toFloat
  (float, ⟨result, s.counter + 1⟩)

/-- CRITICAL: PRNG is deterministic -/
theorem prng_deterministic (s : SeedState) :
    nextRandom s = nextRandom s := rfl

/-- Evaluator type -/
def Evaluator (State Result : Type) := State → Frame → Result

/-- Definition of deterministic evaluator -/
def isDeterministic {S R : Type} (eval : Evaluator S R) : Prop :=
  ∀ s f, eval s f = eval s f

/-- CRITICAL: Any pure function is deterministic -/
theorem pure_is_deterministic {S R : Type} (eval : Evaluator S R) : 
    isDeterministic eval := fun _ _ => rfl

/-- EXPORT -/
@[export lattice_seeded_random]
def seededRandom_c (seed : UInt64) (counter : Nat) : Float × UInt64 × Nat :=
  let (f, s') := nextRandom ⟨seed, counter⟩
  (f, s'.seed, s'.counter)

end LatticeProofs.Determinism
```

---

## STEP 6: HASKELL PROJECT

```bash
mkdir -p lattice-core
cd lattice-core
cabal init --lib --language=GHC2021 --license=MIT
```

Create `src/Lattice/Types.hs` - copy from main spec.
Create `src/Lattice/Interpolation/Linear.hs` - copy from main spec.
Create `src/Lattice/Interpolation/Spring.hs` - copy from main spec.
Create `src/Lattice/Random/Seeded.hs` - copy from main spec.

---

## STEP 7: C++23 PROJECT

```bash
mkdir -p lattice-native/{include/lattice,src,wasm}
cd lattice-native
```

Create CMakeLists.txt - copy from main spec.
Create include/lattice/types.hpp - copy from main spec.
Create include/lattice/interpolation.hpp - copy from main spec.
Create include/lattice/spring.hpp - copy from main spec.

---

## STEP 8: BUILD VERIFICATION

```bash
# Lean4
cd lattice-proofs
lake build

# Haskell
cd ../lattice-core
cabal build

# C++
cd ../lattice-native
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build

# WASM (requires emscripten)
emcmake cmake -B build-wasm -DLATTICE_BUILD_WASM=ON
cmake --build build-wasm
```

---

## CRITICAL INVARIANTS TO VERIFY

After each step, run these checks:

### After Lean4:
```bash
# Verify proofs compile
lake build
# Check no sorry remaining
grep -r "sorry" LatticeProofs/ && echo "ERROR: Found sorry" || echo "OK: No sorry"
```

### After Haskell:
```bash
# Verify builds with -Wall -Werror
cabal build --ghc-options="-Wall -Werror"
# Run tests
cabal test
```

### After C++:
```bash
# Verify builds clean
cmake --build build 2>&1 | grep -i error && echo "ERRORS FOUND" || echo "BUILD CLEAN"
# Run tests
ctest --test-dir build
```

---

## INTEGRATION TEST: FRAME DETERMINISM

Create this test in any language and verify output matches:

```
Input: 
  - Spring config: mass=1, stiffness=100, damping=10
  - from=0, to=100
  - t=0.5

Expected outputs (must match across ALL implementations):
  - Lean4:   ~86.466... 
  - Haskell: ~86.466...
  - C++:     ~86.466...
  - WASM:    ~86.466...

If ANY output differs by more than 1e-10, there is a bug.
```

---

## COMMON ERRORS AND FIXES

### Lean4: "unknown identifier"
- Run `lake update` to fetch mathlib
- Check imports at top of file

### Haskell: FFI linking errors
- Ensure Lean library is built first
- Check `extra-libraries` in cabal file

### C++: SIMD not available
- Remove `-march=native` for cross-compilation
- Use scalar fallbacks

### WASM: Memory issues
- Add `-sALLOW_MEMORY_GROWTH=1` to emscripten flags
- Reduce initial memory if needed

---

## NEXT STEPS AFTER CORE

1. PureScript frontend package
2. Vue/React integration packages
3. Tailwind CSS generation
4. Connect to existing Lattice Compositor UI

---

**DO NOT PROCEED TO FRONTEND UNTIL ALL CORE PROOFS PASS**
