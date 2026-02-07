# Large-Scale Migration Protocol

**Date:** 2026-01-XX  
**Purpose:** Systematic protocol for migrating 291k+ lines of TypeScript/Vue/Python to Haskell/Nix/C++

---

## Core Principle

```
MIGRATE ONE MODULE AT A TIME
VERIFY BEFORE MOVING ON
NO SHORTCUTS
EVERY CHANGE IS TRACED
```

---

## Phase 0: Base Schema Migration (MANDATORY - DO FIRST)

**CRITICAL:** Before migrating ANY module, migrate the base schemas first.

**Base Schemas (in order):**
1. **Primitives** (`primitives-schema.ts`) → `Lattice.Types.Primitives`
2. **AnimatableProperty** (`animation.ts`) → `Lattice.Types.Animation`
3. **LatticeProject** (`project.ts`) → `Lattice.Types.Project`

**Why:** Everything depends on these. Migrating dependent types before base schemas will fail.

**See:** `docs/BASE_SCHEMA_ANALYSIS.md` for complete analysis.

---

## Phase 0.5: Pre-Migration Analysis (MANDATORY)

**Before migrating ANY module (after base schemas are done):**

### Step 0.1: Complete File Reading
```
┌─────────────────────────────────────────────────────────┐
│  GREP IS BANNED                                         │
│  HEAD/TAIL IS BANNED                                    │
│  PARTIAL READS ARE BANNED                               │
│  SEARCH PATTERNS ARE BANNED                             │
│  "RELEVANT SECTIONS" ARE BANNED                         │
└─────────────────────────────────────────────────────────┘
```

**Procedure:**
1. Read the COMPLETE source file (chunk into ≤500 line segments if needed)
2. Read ALL imports/dependencies completely
3. Trace ALL consumers (who uses this module?)
4. Map the dependency graph (upstream and downstream)

**Example:**
```
Migrating: ui/src/types/project.ts (2200 lines)

Step 0.1.1: Read project.ts completely (chunks 1-5)
Step 0.1.2: Read all imports:
  - animation.ts (complete)
  - effects.ts (complete)
  - layerStyles.ts (complete)
  - masks.ts (complete)
  - particles.ts (complete)
  - shapes.ts (complete)
  - spline.ts (complete)
  - text.ts (complete)
  - transform.ts (complete)
Step 0.1.3: Find all consumers:
  - grep -r "from.*types/project" ui/src/
  - Read each consumer file completely
Step 0.1.4: Map dependency graph:
  - project.ts → 50+ files
  - Each consumer → its own dependencies
```

### Step 0.2: Dependency Mapping

**Create a dependency map:**
```
Source Module: project.ts
├── Upstream (imports):
│   ├── animation.ts → (read complete)
│   ├── effects.ts → (read complete)
│   └── ... (all imports)
├── Downstream (consumers):
│   ├── services/projectService.ts → (read complete)
│   ├── stores/projectStore.ts → (read complete)
│   └── ... (all consumers)
└── Transitive:
    ├── projectService.ts → (its dependencies)
    └── projectStore.ts → (its dependencies)
```

**Document in:** `docs/migrations/MODULE_NAME_dependencies.md`

### Step 0.3: Type Analysis

**For each type in the module:**
1. **Identify type category:**
   - Core type (Vec3, Point) → Simple migration
   - Complex type (Layer, Project) → Requires careful mapping
   - Generic type (AnimatableProperty<T>) → Requires type parameter design
   - Union type (BlendMode) → Sum type design

2. **Identify dependencies:**
   - What other types does it depend on?
   - Are those types already migrated?
   - If not, what's the migration order?

3. **Identify invariants:**
   - What constraints must be preserved?
   - What validation exists?
   - What proofs are needed?

**Document in:** `docs/migrations/MODULE_NAME_types.md`

### Step 0.4: Migration Plan

**Create a step-by-step plan:**
```
Module: project.ts
├── Step 1: Migrate core types (Point, BoundingBox)
├── Step 2: Migrate utility types (BlendMode, ColorSpace)
├── Step 3: Migrate simple data types (ProjectMeta, Marker)
├── Step 4: Migrate complex types (Composition, Layer)
└── Step 5: Migrate functions (createEmptyProject, normalizeLayerTiming)

Each step:
  - Migrate types
  - Write tests
  - Verify JSON roundtrip
  - Update consumers (if needed)
  - Document changes
```

**Document in:** `docs/migrations/MODULE_NAME_plan.md`

---

## Phase 1: Type Migration

### Step 1.1: Create Haskell Module Structure

**File naming:** `src/lattice/Types/MODULE_NAME.hs`

**Module structure:**
```haskell
-- |
-- Module      : Lattice.Types.MODULE_NAME
-- Description : [Description from TypeScript]
-- 
-- Migrated from ui/src/types/MODULE_NAME.ts
-- [Date]
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.MODULE_NAME
  ( -- Export all types
  ) where

import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)
-- ... other imports
```

**Constraint:** File must be <500 lines. Split if needed.

### Step 1.2: Migrate Types One-by-One

**For each type:**

1. **Read TypeScript definition completely**
2. **Identify Haskell equivalent:**
   - `interface` → `data`
   - `type` (union) → `data` (sum type)
   - `type` (alias) → `type` or `newtype`
   - `number` → `Double` (or `Int` if appropriate)
   - `string` → `Text`
   - `boolean` → `Bool`
   - `T | null` → `Maybe T`
   - `T | undefined` → `Maybe T`
   - `T[]` → `[T]`
   - `Record<string, T>` → `Map Text T` or `HashMap Text T`

3. **Write Haskell definition:**
   ```haskell
   -- TypeScript:
   -- export interface Vec3 {
   --   x: number;
   --   y: number;
   --   z: number;
   -- }
   
   data Vec3 = Vec3
     { vec3X :: Double
     , vec3Y :: Double
     , vec3Z :: Double
     }
     deriving (Eq, Show, Generic, ToJSON, FromJSON)
   ```

4. **Add JSON field mapping:**
   ```haskell
   instance ToJSON Vec3 where
     toJSON (Vec3 x y z) = object
       [ "x" .= x
       , "y" .= y
       , "z" .= z
       ]
   
   instance FromJSON Vec3 where
     parseJSON = withObject "Vec3" $ \o ->
       Vec3 <$> o .: "x"
            <*> o .: "y"
            <*> o .: "z"
   ```

5. **Verify compilation:**
   ```bash
   ghc -c src/lattice/Types/MODULE_NAME.hs
   ```

### Step 1.3: Create Roundtrip Tests

**For each migrated type:**

```haskell
-- tests/Lattice/Types/MODULE_NAMESpec.hs
module Lattice.Types.MODULE_NAMESpec (spec) where

import Test.Hspec
import Data.Aeson (encode, decode)
import Lattice.Types.MODULE_NAME

spec :: Spec
spec = describe "Vec3 JSON roundtrip" $ do
  it "roundtrips correctly" $ do
    let original = Vec3 1.0 2.0 3.0
    let json = encode original
    let decoded = decode json :: Maybe Vec3
    decoded `shouldBe` Just original
```

**Run tests:**
```bash
stack test  # or cabal test
```

### Step 1.4: Update Consumers (If Needed)

**If consumers need updates:**

1. **Read consumer file completely**
2. **Identify changes needed**
3. **Update consumer to use Haskell types** (via FFI or JSON)
4. **Test consumer still works**

**Document changes:** `docs/migrations/MODULE_NAME_changes.md`

---

## Phase 2: Function Migration

### Step 2.1: Identify Pure Functions

**Separate pure logic from side effects:**

- **Pure functions** → Migrate to Haskell directly
- **Functions with side effects** → Keep in TypeScript (UI) or migrate to Haskell scripts

### Step 2.2: Migrate Pure Functions

**For each function:**

1. **Read function completely**
2. **Identify dependencies:**
   - What types does it use?
   - What other functions does it call?
   - Are those already migrated?

3. **Write Haskell equivalent:**
   ```haskell
   -- TypeScript:
   -- export function createDefaultTransform(): LayerTransform {
   --   return { ... };
   -- }
   
   createDefaultTransform :: LayerTransform
   createDefaultTransform = LayerTransform
     { transformPosition = Vec3 0.0 0.0 0.0
     , transformOrigin = Vec3 0.0 0.0 0.0
     -- ... etc
     }
   ```

4. **Write property tests:**
   ```haskell
   -- Property: createDefaultTransform should always return valid transform
   prop_createDefaultTransform_valid :: Property
   prop_createDefaultTransform_valid =
     let t = createDefaultTransform
     in transformScale t `shouldBe` Vec3 100.0 100.0 100.0
   ```

5. **Verify:**
   ```bash
   ghc -c src/lattice/Types/MODULE_NAME.hs
   stack test
   ```

---

## Phase 3: Verification

### Step 3.1: Compilation Check

```bash
# Check all Haskell modules compile
find src/lattice -name "*.hs" -exec ghc -c {} \;
```

### Step 3.2: Test Suite

```bash
# Run all tests
stack test

# Check coverage
stack test --coverage
```

### Step 3.3: JSON Roundtrip Verification

**For each migrated type:**

1. **Generate test data** (TypeScript)
2. **Serialize to JSON** (TypeScript)
3. **Deserialize in Haskell** (Haskell)
4. **Serialize back to JSON** (Haskell)
5. **Deserialize in TypeScript** (TypeScript)
6. **Compare:** Original === Final

**Document results:** `docs/migrations/MODULE_NAME_verification.md`

### Step 3.4: Integration Test

**Test with real project files:**

1. **Load real project JSON** (from TypeScript)
2. **Parse in Haskell**
3. **Serialize back**
4. **Load in TypeScript**
5. **Verify:** Project loads correctly

---

## Phase 4: Documentation

### Step 4.1: Update Migration Status

**Update:** `docs/MIGRATION_PROGRESS.md`

```markdown
## Module: project.ts → Lattice.Types.Project

**Status:** ✅ Complete
**Date:** 2026-01-XX
**Files:**
- `src/lattice/Types/Project.hs` (450 lines)
- `src/lattice/Types/Layer.hs` (380 lines)
- `src/lattice/Types/Composition.hs` (320 lines)

**Tests:** ✅ All passing
**JSON Roundtrip:** ✅ Verified
**Integration:** ✅ Verified
```

### Step 4.2: Update Type Index

**Update:** `src/lattice/Types/Index.hs`

```haskell
module Lattice.Types.Index
  ( module Lattice.Types.Core
  , module Lattice.Types.Transform
  , module Lattice.Types.Project
  -- ... etc
  ) where

import Lattice.Types.Core
import Lattice.Types.Transform
import Lattice.Types.Project
-- ... etc
```

### Step 4.3: Create Migration Guide

**Document:** `docs/migrations/MODULE_NAME_guide.md`

- What was migrated
- What changed
- How to use new types
- Migration notes for consumers

---

## Phase 5: Cleanup

### Step 5.1: Remove Legacy Code (After Verification)

**Only after:**
- ✅ All tests pass
- ✅ JSON roundtrip verified
- ✅ Integration tests pass
- ✅ All consumers updated

**Then:**
- Move TypeScript file to `ui/src/types/legacy/`
- Add deprecation notice
- Update imports to use Haskell types (via FFI/JSON)

### Step 5.2: Update Build System

**Update:** `flake.nix` or `cabal.project`

```nix
packages.lattice-types = pkgs.haskellPackages.callCabal2nix
  "lattice-types"
  ./src/lattice/Types
  {};
```

---

## Checklist Per Module

**Before starting migration:**
- [ ] Read source file completely (no grep, no partial)
- [ ] Read all imports completely
- [ ] Read all consumers completely
- [ ] Map dependency graph
- [ ] Create migration plan
- [ ] Document types and invariants

**During migration:**
- [ ] Migrate types one-by-one
- [ ] Verify compilation after each type
- [ ] Write tests for each type
- [ ] Verify JSON roundtrip
- [ ] Update consumers (if needed)
- [ ] Document changes

**After migration:**
- [ ] All tests pass
- [ ] JSON roundtrip verified
- [ ] Integration tests pass
- [ ] Documentation updated
- [ ] Migration status updated
- [ ] Build system updated

**Before marking complete:**
- [ ] File size <500 lines
- [ ] No banned constructs
- [ ] All types explicit
- [ ] All functions total (or documented partial)
- [ ] Documentation complete

---

## Error Handling

**If migration fails:**

1. **STOP immediately**
2. **Document the failure:**
   - What was attempted
   - What failed
   - Why it failed
   - What information is needed

3. **Analyze root cause:**
   - Was dependency missing?
   - Was invariant violated?
   - Was type mapping incorrect?

4. **Fix root cause** (don't work around)
5. **Retry migration**

**BANNED:**
- Skipping verification steps
- Marking incomplete migrations as done
- Working around type errors
- Partial migrations without documentation

---

## Progress Tracking

**Track in:** `docs/migrations/PROGRESS.md`

```markdown
## Module Migration Status

| Module | Status | Lines Migrated | Tests | JSON | Integration |
|--------|--------|----------------|-------|------|-------------|
| transform.ts | ✅ Complete | 78 | ✅ | ✅ | ✅ |
| core.ts | ✅ Complete | 120 | ✅ | ✅ | ✅ |
| project.ts | ⏳ In Progress | 450/2200 | ⏳ | ⏳ | ⏳ |
| animation.ts | ⏳ Pending | 0/800 | - | - | - |
```

---

## Time Estimates

**Per module (average):**
- Small module (<200 lines): 1-2 days
- Medium module (200-500 lines): 3-5 days
- Large module (500-1000 lines): 1-2 weeks
- Very large module (>1000 lines): 2-4 weeks

**Total estimate:** 3-6 months for complete migration

---

## Notes

- **One module at a time** - Don't start new module until current is complete
- **Verify everything** - No assumptions, everything is tested
- **Document everything** - Every decision is documented
- **No shortcuts** - Follow protocol exactly
- **Ask for help** - If stuck, document and ask (don't guess)

---

## Success Criteria

A module migration is complete when:

1. ✅ All types migrated
2. ✅ All functions migrated (or documented as deferred)
3. ✅ All tests pass
4. ✅ JSON roundtrip verified
5. ✅ Integration tests pass
6. ✅ Documentation complete
7. ✅ File size <500 lines
8. ✅ No banned constructs
9. ✅ Build system updated
10. ✅ Migration status updated

**Not before.**
