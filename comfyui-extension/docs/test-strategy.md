# Test Strategy: Pre-Migration vs Post-Migration

> **Purpose:** Define test strategy for TypeScript → Haskell/PureScript/Lean4 migration
> **Generated:** 2026-01-22
> **Status:** 🔄 Strategy Document - To be executed

---

## Executive Summary

**Recommendation: Write SPECIFICATION tests NOW in Haskell/PureScript/Lean4**

**Rationale:**
1. Tests written AFTER migration may just verify migrated code works, not that it's CORRECT
2. Tests written BEFORE migration verify BEHAVIOR/INVARIANTS, not implementation
3. Property-based tests in Haskell/PureScript are stronger than TypeScript tests
4. Existing TypeScript tests can serve as REFERENCE, not source of truth

**Strategy:**
- Write tests in TARGET languages (Haskell/PureScript/Lean4) from the start
- Test BEHAVIOR/INVARIANTS, not implementation details
- Use property-based testing (QuickCheck for Haskell, similar for PureScript)
- Migrate existing TypeScript test CASES, not test CODE

---

## Current State

### Existing TypeScript Tests

**Test Files:** 146 files in `ui/src/__tests__/`

**Test Categories:**
- **Property Tests:** 30+ files using `fast-check`
  - `keyframeStore.property.test.ts`
  - `keyframeStore.all-layers.property.test.ts`
  - `keyframeStore.advanced-systems.property.test.ts`
  - `keyframeStore.timewarp-text-audio.property.test.ts`
  - `keyframeStore.mesh-warp-pose.property.test.ts`
  - `types/*.property.test.ts` (effects, shapes, animation, etc.)
  - `services/*.property.test.ts` (interpolation, expressions, etc.)
- **Unit Tests:** 50+ files
- **Integration Tests:** 10+ files
- **Browser Tests:** 5+ files
- **Regression Tests:** 10+ files

**Test Coverage:** Unknown (no coverage report found)

**Test Quality:** Good - Uses property-based testing with `fast-check`

### Haskell Test Status

**Current Status:** 0% test coverage for Haskell modules

**Existing Test Infrastructure:**
- `test/lattice/` directory exists
- `test/Main.hs` exists
- No actual test files found

---

## Test Strategy: Pre-Migration vs Post-Migration

### Option A: Write Tests AFTER Migration ❌

**Pros:**
- Tests match migrated code exactly
- No need to translate test code
- Faster initial migration

**Cons:**
- Tests may verify migrated code works, not that it's CORRECT
- Risk of locking in bugs from migration
- No verification that migration preserved behavior
- Tests may be written to fit the code, not verify correctness

**Risk Level:** 🔴 HIGH - May miss behavioral regressions

### Option B: Write Tests BEFORE Migration ✅ **RECOMMENDED**

**Pros:**
- Tests verify BEHAVIOR/INVARIANTS, not implementation
- Can catch behavioral regressions during migration
- Tests serve as SPECIFICATION for migration
- Property-based tests are stronger in Haskell/PureScript
- Tests written in target languages from the start

**Cons:**
- Requires understanding behavior before migration
- May need to reference TypeScript implementation
- Slower initial progress

**Risk Level:** 🟢 LOW - Verifies correctness throughout migration

### Option C: Write Tests DURING Migration ⚠️

**Pros:**
- Tests written as each module migrates
- Can verify migration correctness incrementally

**Cons:**
- Risk of writing tests to fit migrated code
- May miss cross-module behavioral regressions
- Inconsistent test quality

**Risk Level:** 🟡 MEDIUM - Better than post-migration, worse than pre-migration

---

## Recommended Approach: Pre-Migration Specification Tests

### Phase 1: Extract Test Specifications from TypeScript Tests

**Goal:** Understand WHAT to test, not HOW to test it

**Process:**
1. Read existing TypeScript property tests
2. Extract test SPECIFICATIONS (invariants, properties)
3. Document in Haskell/PureScript test files
4. Write tests in target languages

**Example:**

**TypeScript Test (Reference):**
```typescript
test.prop("keyframes are sorted by frame", [fc.array(keyframeArb)])(
  (keyframes) => {
    const sorted = sortKeyframes(keyframes);
    for (let i = 1; i < sorted.length; i++) {
      expect(sorted[i].frame).toBeGreaterThanOrEqual(sorted[i-1].frame);
    }
  }
);
```

**Haskell Test Specification (Target):**
```haskell
prop_keyframesSorted :: [Keyframe] -> Property
prop_keyframesSorted keyframes =
  let sorted = sortKeyframes keyframes
  in property $ all (uncurry (<=)) $ zipWith (\k1 k2 -> frame k1 <= frame k2) sorted (tail sorted)
```

### Phase 2: Write Property Tests in Haskell/PureScript

**Test Framework:**
- **Haskell:** `QuickCheck` or `hedgehog`
- **PureScript:** `purescript-quickcheck` or `purescript-hedgehog`
- **Lean4:** Built-in property testing (if needed)

**Test Structure:**
```
test/
├── lattice/
│   ├── State/
│   │   ├── Keyframe/
│   │   │   ├── CRUDSpec.hs      -- CRUD operations
│   │   │   ├── InterpolationSpec.hs  -- Interpolation properties
│   │   │   ├── SortingSpec.hs   -- Sorting invariants
│   │   │   └── DeterminismSpec.hs  -- Determinism properties
│   │   ├── Layer/
│   │   │   ├── CRUDSpec.hs
│   │   │   └── HierarchySpec.hs
│   │   └── Animation/
│   │       └── PlaybackSpec.hs
│   ├── Services/
│   │   ├── InterpolationSpec.hs
│   │   └── PropertyEvaluatorSpec.hs
│   └── Types/
│       ├── KeyframeSpec.hs
│       └── LayerSpec.hs
```

### Phase 3: Test Categories

#### 3.1 Invariant Tests

**Purpose:** Verify properties that MUST hold for all inputs

**Examples:**
- Keyframes are always sorted by frame
- Layer hierarchy is acyclic
- No duplicate keyframe IDs
- All numeric values are finite (no NaN/Infinity)
- All IDs are deterministic (UUID5)

**Haskell Example:**
```haskell
prop_keyframesAlwaysSorted :: [Keyframe] -> Property
prop_keyframesAlwaysSorted keyframes =
  let sorted = sortKeyframes keyframes
  in property $ isSortedBy frame sorted

prop_noDuplicateIds :: [Keyframe] -> Property
prop_noDuplicateIds keyframes =
  let ids = map keyframeId keyframes
  in property $ length ids == length (nub ids)
```

#### 3.2 Roundtrip Tests

**Purpose:** Verify serialization/deserialization preserves data

**Examples:**
- JSON roundtrip: `toJSON . fromJSON = id`
- Project save/load preserves all data
- Keyframe serialization preserves all properties

**Haskell Example:**
```haskell
prop_keyframeJSONRoundtrip :: Keyframe -> Property
prop_keyframeJSONRoundtrip kf =
  let json = toJSON kf
      parsed = fromJSON json
  in case parsed of
    Success kf' -> kf === kf'
    Error _ -> property False
```

#### 3.3 Determinism Tests

**Purpose:** Verify deterministic behavior (critical for AI video generation)

**Examples:**
- Same inputs → same outputs (no randomness)
- Frame evaluation is deterministic
- ID generation is deterministic (UUID5)

**Haskell Example:**
```haskell
prop_deterministicFrameEvaluation :: Layer -> Frame -> Property
prop_deterministicFrameEvaluation layer frame =
  let eval1 = evaluatePropertyAtFrame layer "opacity" frame
      eval2 = evaluatePropertyAtFrame layer "opacity" frame
  in eval1 === eval2
```

#### 3.4 Edge Case Tests

**Purpose:** Verify behavior at boundaries

**Examples:**
- Empty keyframe lists
- Single keyframe (no interpolation)
- Maximum frame values
- Zero/negative values where applicable

**Haskell Example:**
```haskell
prop_emptyKeyframeList :: Property
prop_emptyKeyframeList =
  let result = interpolateValue [] 100
  in result === defaultValue

prop_singleKeyframe :: Keyframe -> Property
prop_singleKeyframe kf =
  let result = interpolateValue [kf] (frame kf)
  in result === value kf
```

#### 3.5 Cross-Domain Tests

**Purpose:** Verify cross-domain actions work correctly

**Examples:**
- Audio → Keyframe conversion preserves amplitude
- Expression → Keyframe baking evaluates correctly
- Layer → Selection coordination

**Haskell Example:**
```haskell
prop_audioToKeyframeConversion :: AudioAnalysis -> LayerId -> PropertyPath -> Property
prop_audioToKeyframeConversion analysis layerId propPath =
  let keyframes = convertAudioToKeyframes analysis layerId propPath
      frames = map frame keyframes
      values = map value keyframes
  in property $
    all (\f -> f >= 0 && f < frameCount) frames &&
    all (\v -> v >= 0 && v <= 1) values  -- Normalized amplitude
```

### Phase 4: Test Execution Strategy

#### 4.1 Pre-Migration Tests (NOW)

**Write tests for:**
1. ✅ Keyframe Store (already migrated, needs tests)
2. ✅ Animation Store (already migrated, needs tests)
3. ✅ Expression Store (already migrated, needs tests)
4. ⏳ Layer Store (partially migrated, write tests for migrated parts)
5. ⏳ Types (all migrated, write tests)

**Test Framework Setup:**
```haskell
-- test/Spec.hs
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "Lattice.State.Keyframe" $ do
    it "sorts keyframes by frame" $ property prop_keyframesSorted
    it "has no duplicate IDs" $ property prop_noDuplicateIds
    it "roundtrips JSON" $ property prop_keyframeJSONRoundtrip
  describe "Lattice.State.Animation" $ do
    it "evaluates frames deterministically" $ property prop_deterministicFrameEvaluation
```

#### 4.2 During Migration Tests

**As each module migrates:**
1. Run pre-migration tests against migrated code
2. Fix any failures (indicates migration bug)
3. Add new tests for newly migrated functionality
4. Verify all tests pass

#### 4.3 Post-Migration Tests

**After migration complete:**
1. Run full test suite
2. Verify coverage ≥70% for critical modules
3. Add integration tests for FFI boundaries
4. Add end-to-end tests for workflows

---

## Test Implementation Plan

### Step 1: Set Up Test Infrastructure (Week 1)

**Tasks:**
- [ ] Add `QuickCheck` to `flake.nix` dependencies
- [ ] Create `test/Spec.hs` test runner
- [ ] Set up test directory structure
- [ ] Add test command to `flake.nix` (`nix build .#checks.haskell-tests`)

### Step 2: Extract Test Specifications (Week 1-2)

**Tasks:**
- [ ] Read all TypeScript property tests
- [ ] Extract test specifications (invariants, properties)
- [ ] Document in `docs/TEST_SPECIFICATIONS.md`
- [ ] Prioritize by migration status

### Step 3: Write Keyframe Store Tests (Week 2-3)

**Tasks:**
- [ ] Write `test/lattice/State/Keyframe/CRUDSpec.hs`
- [ ] Write `test/lattice/State/Keyframe/InterpolationSpec.hs`
- [ ] Write `test/lattice/State/Keyframe/SortingSpec.hs`
- [ ] Write `test/lattice/State/Keyframe/DeterminismSpec.hs`
- [ ] Run tests, fix any failures in migrated code

### Step 4: Write Animation Store Tests (Week 3)

**Tasks:**
- [ ] Write `test/lattice/State/Animation/PlaybackSpec.hs`
- [ ] Write `test/lattice/State/Animation/WorkAreaSpec.hs`
- [ ] Run tests, fix any failures

### Step 5: Write Expression Store Tests (Week 3)

**Tasks:**
- [ ] Write `test/lattice/State/Expression/EvaluationSpec.hs`
- [ ] Write `test/lattice/State/Expression/DriverSpec.hs`
- [ ] Run tests, fix any failures

### Step 6: Write Type Tests (Week 4)

**Tasks:**
- [ ] Write `test/lattice/Types/KeyframeSpec.hs`
- [ ] Write `test/lattice/Types/LayerSpec.hs`
- [ ] Write `test/lattice/Types/ProjectSpec.hs`
- [ ] Write JSON roundtrip tests for all types

### Step 7: Write Service Tests (Week 5+)

**Tasks:**
- [ ] Write `test/lattice/Services/InterpolationSpec.hs`
- [ ] Write `test/lattice/Services/PropertyEvaluatorSpec.hs`
- [ ] Continue as services migrate

---

## Test Quality Standards

### Coverage Requirements

- **Critical Modules:** ≥70% coverage
  - Keyframe Store
  - Animation Store
  - Expression Store
  - Property Evaluator
  - Interpolation

- **Standard Modules:** ≥50% coverage
  - Layer Store
  - Other State modules
  - Service modules

- **Utility Modules:** ≥30% coverage
  - Utils
  - Helpers

### Test Types Required

**For Each Module:**
1. ✅ Invariant tests (property-based)
2. ✅ Roundtrip tests (JSON serialization)
3. ✅ Edge case tests
4. ✅ Determinism tests (if applicable)
5. ✅ Cross-domain tests (if applicable)

### Test Execution

**Pre-Commit:**
- All tests must pass
- No test failures allowed
- Coverage must meet requirements

**CI/CD:**
- Run full test suite on every commit
- Fail build if tests fail
- Generate coverage report

---

## Migration Verification Strategy

### Before Migration

1. ✅ Write test specifications
2. ✅ Write tests in Haskell/PureScript
3. ✅ Run tests against TypeScript implementation (via FFI if needed)
4. ✅ Document expected behavior

### During Migration

1. ✅ Run tests against migrated Haskell code
2. ✅ Fix any test failures (indicates migration bug)
3. ✅ Add new tests for newly migrated functionality
4. ✅ Verify all tests pass

### After Migration

1. ✅ Run full test suite
2. ✅ Verify coverage requirements met
3. ✅ Add integration tests
4. ✅ Add end-to-end tests

---

## Example: Keyframe Store Test Migration

### TypeScript Test (Reference)

```typescript
test.prop("keyframes are sorted", [fc.array(keyframeArb)])(
  (keyframes) => {
    const sorted = sortKeyframes(keyframes);
    for (let i = 1; i < sorted.length; i++) {
      expect(sorted[i].frame).toBeGreaterThanOrEqual(sorted[i-1].frame);
    }
  }
);
```

### Haskell Test (Target)

```haskell
-- test/lattice/State/Keyframe/SortingSpec.hs
module Lattice.State.Keyframe.SortingSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Lattice.State.Keyframe.Sorting
import Lattice.Types.Keyframe

spec :: Spec
spec = describe "Keyframe Sorting" $ do
  it "sorts keyframes by frame" $ property prop_keyframesSorted

prop_keyframesSorted :: [Keyframe] -> Property
prop_keyframesSorted keyframes =
  let sorted = sortKeyframes keyframes
  in property $ isSortedBy frame sorted

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = all (uncurry (<=)) $ zipWith (\x y -> f x <= f y) xs (tail xs)
```

---

## Conclusion

**Recommendation: Write SPECIFICATION tests NOW in Haskell/PureScript/Lean4**

**Benefits:**
1. Tests verify BEHAVIOR, not implementation
2. Catch behavioral regressions during migration
3. Tests serve as SPECIFICATION for migration
4. Property-based tests are stronger in Haskell/PureScript
5. Tests written in target languages from the start

**Next Steps:**
1. Set up test infrastructure (`QuickCheck`, test runner)
2. Extract test specifications from TypeScript tests
3. Write tests for migrated modules (Keyframe, Animation, Expression)
4. Continue writing tests as migration progresses

---

*Document Version: 1.0*
*Last Updated: 2026-01-22*
*Next Update: After test infrastructure setup*
