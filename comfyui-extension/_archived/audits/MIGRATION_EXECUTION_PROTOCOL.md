# Migration Execution Protocol

**Date:** 2026-01-XX  
**Purpose:** Step-by-step execution protocol for large-scale migrations

---

## Core Principle

```
BASE FIRST
ONE MODULE AT A TIME
VERIFY BEFORE MOVING ON
NO SHORTCUTS
```

---

## Execution Order (MANDATORY)

### Stage 0: Base Schema Migration ⭐ **CRITICAL - DO FIRST**

**Must complete before ANY other migration:**

1. **Primitives** (`ui/src/schemas/layers/primitives-schema.ts`)
   - Migrate to: `src/lattice/Types/Primitives.hs`
   - Dependencies: None (foundational)
   - Verification: Compiles, JSON roundtrip, tests pass

2. **AnimatableProperty** (`ui/src/types/animation.ts`)
   - Migrate to: `src/lattice/Types/Animation.hs`
   - Dependencies: Primitives (Vec2, Vec3, finiteNumber)
   - Verification: Compiles, JSON roundtrip, tests pass

3. **LatticeProject** (`ui/src/types/project.ts` - root type only)
   - Migrate to: `src/lattice/Types/Project.hs`
   - Dependencies: AnimatableProperty, Primitives, all layer types
   - Verification: Compiles, JSON roundtrip, tests pass

**Why base first:**
- Everything depends on these types
- Migrating dependent types before base will fail
- Base defines the ontology of the system

**See:** `docs/BASE_SCHEMA_ANALYSIS.md` for complete dependency analysis.

---

### Stage 1: Core Types Migration

**After base schemas complete:**

1. **Transform Types** (`ui/src/types/transform.ts`)
   - Dependencies: AnimatableProperty ✅
   - Status: ✅ Examples created (`src/lattice/Types/Transform.hs`)

2. **Core Types** (`ui/src/types/project.ts` - utility types)
   - Dependencies: Primitives ✅
   - Status: ✅ Examples created (`src/lattice/Types/Core.hs`)

---

### Stage 2: Layer Data Types Migration

**After core types complete:**

**Order (by dependency):**
1. Simple layer data (Solid, Null, Control) - No dependencies
2. Asset-based layers (Image, Video, Audio) - Depends on AssetReference
3. Complex layers (Spline, Text, Particles) - Depends on AnimatableProperty
4. 3D layers (Model, PointCloud, Camera) - Depends on Vec3, Transform

---

### Stage 3: Service Migration

**After types complete:**

1. Pure functions first (no side effects)
2. State management (Pinia stores → Haskell state)
3. Effects/IO last (keep in TypeScript for UI)

---

## Per-Module Execution Protocol

### Step 1: Pre-Migration Analysis

**Read completely (no grep, no partial):**
- [ ] Source file completely read
- [ ] All imports read completely
- [ ] All consumers identified and read
- [ ] Dependency graph mapped
- [ ] Migration plan created

**Document in:** `docs/migrations/MODULE_NAME_analysis.md`

### Step 2: Base Schema Check

**Before starting:**
- [ ] Are base schemas migrated? (Primitives, AnimatableProperty, LatticeProject)
- [ ] If not, STOP and migrate base schemas first
- [ ] Verify base schemas compile and pass tests

### Step 3: Type Migration

**For each type:**
- [ ] Read TypeScript definition completely
- [ ] Map to Haskell equivalent
- [ ] Write Haskell definition
- [ ] Add JSON serialization
- [ ] Verify compilation (`ghc -c`)
- [ ] Write roundtrip test
- [ ] Verify test passes

**Document in:** `docs/migrations/MODULE_NAME_types.md`

### Step 4: Function Migration

**For each function:**
- [ ] Identify if pure or has side effects
- [ ] If pure → migrate to Haskell
- [ ] If side effects → document (keep in TypeScript or migrate to Haskell script)
- [ ] Write tests
- [ ] Verify compilation and tests

**Document in:** `docs/migrations/MODULE_NAME_functions.md`

### Step 5: Verification

**Before marking complete:**
- [ ] All types compile
- [ ] All functions compile
- [ ] All tests pass
- [ ] JSON roundtrip verified
- [ ] Integration test passes (if applicable)
- [ ] File size <500 lines
- [ ] No banned constructs
- [ ] Documentation complete

**Document in:** `docs/migrations/MODULE_NAME_verification.md`

### Step 6: Update Dependencies

**After migration complete:**
- [ ] Update all consumers to use new Haskell types (via FFI/JSON)
- [ ] Verify consumers still compile
- [ ] Update build system (`flake.nix` or `cabal.project`)
- [ ] Update migration status

---

## Base Schema Migration Protocol (Special)

### Primitives Migration

**File:** `ui/src/schemas/layers/primitives-schema.ts` → `src/lattice/Types/Primitives.hs`

**Types to migrate:**
- `finiteNumber` → Validation function (not a type in Haskell)
- `Vec2`, `Vec3` → Data types
- `RGBAColor`, `HexColor` → Data types
- `Rect`, `BoundingBox` → Data types
- `EntityId` → Newtype wrapper
- `BlendMode` → Sum type

**Verification:**
```bash
ghc -c src/lattice/Types/Primitives.hs
stack test --test-arguments="--match Primitives"
```

**JSON Roundtrip:**
- Generate Vec2/Vec3 in TypeScript
- Serialize to JSON
- Parse in Haskell
- Serialize back
- Parse in TypeScript
- Compare

---

### AnimatableProperty Migration

**File:** `ui/src/types/animation.ts` → `src/lattice/Types/Animation.hs`

**Types to migrate:**
- `Keyframe<T>` → Generic data type
- `BezierHandle` → Data type
- `PropertyValue` → Sum type
- `AnimatableProperty<T>` → Generic data type ⭐ **CRITICAL**

**Challenges:**
- Generic type parameter `T` in Haskell
- JSON serialization for generic types
- Type-safe property value union

**Verification:**
```bash
ghc -c src/lattice/Types/Animation.hs
stack test --test-arguments="--match Animation"
```

**JSON Roundtrip:**
- Generate AnimatableProperty<number> in TypeScript
- Generate AnimatableProperty<Vec3> in TypeScript
- Serialize both to JSON
- Parse both in Haskell
- Verify types preserved

---

### LatticeProject Migration

**File:** `ui/src/types/project.ts` → `src/lattice/Types/Project.hs`

**Types to migrate:**
- `LatticeProject` → Root data type
- `ProjectMeta` → Data type
- `Composition` → Data type
- `CompositionSettings` → Data type

**Challenges:**
- Large type (2200+ lines)
- Many dependencies
- Must split into multiple modules (<500 lines each)

**Strategy:**
- Split into: `Project.hs`, `Composition.hs`, `Layer.hs`, `Asset.hs`
- Each module <500 lines
- Use qualified imports

**Verification:**
```bash
ghc -c src/lattice/Types/Project.hs
ghc -c src/lattice/Types/Composition.hs
ghc -c src/lattice/Types/Layer.hs
ghc -c src/lattice/Types/Asset.hs
stack test --test-arguments="--match Project"
```

**JSON Roundtrip:**
- Load real project JSON file
- Parse in Haskell
- Serialize back
- Load in TypeScript
- Verify project loads correctly

---

## Error Handling

**If base schema migration fails:**

1. **STOP immediately**
2. **Document failure:**
   - What was attempted
   - What failed
   - Why it failed
   - What's needed to proceed

3. **DO NOT proceed** with dependent type migrations
4. **Fix base schema** before continuing

**BANNED:**
- Migrating dependent types before base schemas
- Working around base schema issues
- Skipping base schema verification

---

## Progress Tracking

**Track in:** `docs/migrations/BASE_SCHEMA_STATUS.md`

```markdown
## Base Schema Migration Status

| Schema | Status | Dependencies | Tests | JSON | Integration |
|--------|--------|--------------|-------|------|-------------|
| Primitives | ⏳ Pending | None | - | - | - |
| AnimatableProperty | ⏳ Pending | Primitives | - | - | - |
| LatticeProject | ⏳ Pending | AnimatableProperty, All layers | - | - | - |

## Blockers

- Cannot migrate AnimatableProperty until Primitives complete
- Cannot migrate LatticeProject until AnimatableProperty complete
- Cannot migrate any layer types until AnimatableProperty complete
```

---

## Success Criteria

**Base schema migration is complete when:**

1. ✅ Primitives migrated and verified
2. ✅ AnimatableProperty migrated and verified
3. ✅ LatticeProject migrated and verified
4. ✅ All compile with zero warnings
5. ✅ All tests pass
6. ✅ JSON roundtrip verified
7. ✅ Integration tests pass
8. ✅ Documentation complete
9. ✅ Build system updated

**Only then can dependent types be migrated.**

---

## Notes

- **Base schemas are immutable** - Once migrated, they rarely change
- **Everything depends on base** - Can't proceed without base
- **Base defines ontology** - The base schemas define what the system IS
- **No shortcuts** - Base schemas must be perfect

**The base is the foundation. Everything else builds on it.**
